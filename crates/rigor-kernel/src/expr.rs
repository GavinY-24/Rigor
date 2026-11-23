//! Core expressions over a hash-consed DAG arena (de Bruijn indices).
//! In-process pointer (arena ID) equality is meaningful only inside one arena,
//! and a structural hash hit is always confirmed by exact node comparison
//! (the arena map is keyed by the full node).

use crate::level::Level;
use rigor_spec::BigUint;
use std::collections::HashMap;

pub type NameId = u32;
pub type ExprId = u32;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NamePart {
    Anon,
    Str(String),
    Num(u64),
}

/// A stable scoped name identity. Distinct definitions with identical
/// spelling in different scopes cannot collide by construction.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Name(pub Vec<NamePart>);

impl Name {
    pub fn root(s: &str) -> Self {
        Name(vec![NamePart::Str(s.to_string())])
    }
    pub fn join(&self, s: &str) -> Self {
        let mut v = self.0.clone();
        v.push(NamePart::Str(s.to_string()));
        Name(v)
    }
    pub fn from_dotted(s: &str) -> Self {
        if s.is_empty() {
            return Name(vec![NamePart::Anon]);
        }
        Name(
            s.split('.')
                .map(|part| {
                    if let Ok(n) = part.parse::<u64>() {
                        if part.chars().all(|c| c.is_ascii_digit()) && !part.is_empty() {
                            // keep purely numeric components numeric only in trailing position-ish;
                            // dotted names in practice are identifiers, so prefer Str unless exact "_n" style
                            return NamePart::Str(part.to_string());
                        }
                        let _ = n;
                    }
                    NamePart::Str(part.to_string())
                })
                .collect(),
        )
    }
    pub fn to_dotted(&self) -> String {
        self.0
            .iter()
            .map(|p| match p {
                NamePart::Anon => "_".to_string(),
                NamePart::Str(s) => s.clone(),
                NamePart::Num(n) => n.to_string(),
            })
            .collect::<Vec<_>>()
            .join(".")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

impl BinderInfo {
    pub fn to_tag(self) -> u8 {
        match self {
            BinderInfo::Default => 0,
            BinderInfo::Implicit => 1,
            BinderInfo::StrictImplicit => 2,
            BinderInfo::InstImplicit => 3,
        }
    }
    pub fn from_tag(t: u8) -> Option<Self> {
        match t {
            0 => Some(Self::Default),
            1 => Some(Self::Implicit),
            2 => Some(Self::StrictImplicit),
            3 => Some(Self::InstImplicit),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    BVar(u32),
    Const(NameId, Vec<Level>),
    Sort(Level),
    Pi(NameId, BinderInfo, ExprId, ExprId),
    Lam(NameId, BinderInfo, ExprId, ExprId),
    App(ExprId, ExprId),
    Let(NameId, ExprId, ExprId, ExprId),
    Proj(NameId, u32, ExprId),
    LitNat(BigUint),
    LitStr(String),
}

#[derive(Debug, Default)]
pub struct NameArena {
    pub names: Vec<Name>,
    map: HashMap<Name, NameId>,
}

impl NameArena {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn intern(&mut self, name: Name) -> NameId {
        if let Some(&id) = self.map.get(&name) {
            return id;
        }
        let id = self.names.len() as NameId;
        self.map.insert(name.clone(), id);
        self.names.push(name);
        id
    }
    pub fn intern_str(&mut self, s: &str) -> NameId {
        self.intern(Name::from_dotted(s))
    }
    pub fn get(&self, id: NameId) -> &Name {
        &self.names[id as usize]
    }
    pub fn lookup(&self, s: &str) -> Option<NameId> {
        self.map.get(&Name::from_dotted(s)).copied()
    }
    pub fn display(&self, id: NameId) -> String {
        self.get(id).to_dotted()
    }
}

#[derive(Debug, Default)]
pub struct ExprArena {
    pub nodes: Vec<Expr>,
    map: HashMap<Expr, ExprId>,
}

impl ExprArena {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn intern(&mut self, e: Expr) -> ExprId {
        if let Some(&id) = self.map.get(&e) {
            return id;
        }
        let id = self.nodes.len() as ExprId;
        self.map.insert(e.clone(), id);
        self.nodes.push(e);
        id
    }
    pub fn get(&self, id: ExprId) -> &Expr {
        &self.nodes[id as usize]
    }
    pub fn get_clone(&self, id: ExprId) -> Expr {
        self.nodes[id as usize].clone()
    }
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    // --- convenience constructors ---
    pub fn bvar(&mut self, i: u32) -> ExprId {
        self.intern(Expr::BVar(i))
    }
    pub fn sort(&mut self, l: Level) -> ExprId {
        self.intern(Expr::Sort(l))
    }
    pub fn prop(&mut self) -> ExprId {
        self.sort(Level::Zero)
    }
    pub fn type0(&mut self) -> ExprId {
        self.sort(Level::Succ(Box::new(Level::Zero)))
    }
    pub fn const_(&mut self, name: NameId, levels: Vec<Level>) -> ExprId {
        self.intern(Expr::Const(name, levels))
    }
    pub fn app(&mut self, f: ExprId, a: ExprId) -> ExprId {
        self.intern(Expr::App(f, a))
    }
    pub fn apps(&mut self, f: ExprId, args: &[ExprId]) -> ExprId {
        let mut cur = f;
        for &a in args {
            cur = self.app(cur, a);
        }
        cur
    }
    pub fn pi(&mut self, n: NameId, info: BinderInfo, dom: ExprId, cod: ExprId) -> ExprId {
        self.intern(Expr::Pi(n, info, dom, cod))
    }
    pub fn lam(&mut self, n: NameId, info: BinderInfo, dom: ExprId, body: ExprId) -> ExprId {
        self.intern(Expr::Lam(n, info, dom, body))
    }

    /// Shift free variables >= cutoff by `by` (may be negative via shift_down).
    pub fn shift(&mut self, e: ExprId, by: i64, cutoff: u32) -> ExprId {
        if by == 0 {
            return e;
        }
        match self.get_clone(e) {
            Expr::BVar(i) => {
                if i >= cutoff {
                    let ni = (i as i64 + by).max(0) as u32;
                    self.bvar(ni)
                } else {
                    e
                }
            }
            Expr::Const(_, _) | Expr::Sort(_) | Expr::LitNat(_) | Expr::LitStr(_) => e,
            Expr::Pi(n, info, d, c) => {
                let d2 = self.shift(d, by, cutoff);
                let c2 = self.shift(c, by, cutoff + 1);
                self.pi(n, info, d2, c2)
            }
            Expr::Lam(n, info, d, b) => {
                let d2 = self.shift(d, by, cutoff);
                let b2 = self.shift(b, by, cutoff + 1);
                self.lam(n, info, d2, b2)
            }
            Expr::App(f, a) => {
                let f2 = self.shift(f, by, cutoff);
                let a2 = self.shift(a, by, cutoff);
                self.app(f2, a2)
            }
            Expr::Let(n, t, v, b) => {
                let t2 = self.shift(t, by, cutoff);
                let v2 = self.shift(v, by, cutoff);
                let b2 = self.shift(b, by, cutoff + 1);
                self.intern(Expr::Let(n, t2, v2, b2))
            }
            Expr::Proj(s, i, t) => {
                let t2 = self.shift(t, by, cutoff);
                self.intern(Expr::Proj(s, i, t2))
            }
        }
    }

    /// Substitute `repl` for BVar(depth) at the current traversal depth,
    /// removing that binder (variables above it decrement).
    fn subst_at(&mut self, e: ExprId, depth: u32, repl: ExprId) -> ExprId {
        match self.get_clone(e) {
            Expr::BVar(i) => {
                if i == depth {
                    self.shift(repl, depth as i64, 0)
                } else if i > depth {
                    self.bvar(i - 1)
                } else {
                    e
                }
            }
            Expr::Const(_, _) | Expr::Sort(_) | Expr::LitNat(_) | Expr::LitStr(_) => e,
            Expr::Pi(n, info, d, c) => {
                let d2 = self.subst_at(d, depth, repl);
                let c2 = self.subst_at(c, depth + 1, repl);
                self.pi(n, info, d2, c2)
            }
            Expr::Lam(n, info, d, b) => {
                let d2 = self.subst_at(d, depth, repl);
                let b2 = self.subst_at(b, depth + 1, repl);
                self.lam(n, info, d2, b2)
            }
            Expr::App(f, a) => {
                let f2 = self.subst_at(f, depth, repl);
                let a2 = self.subst_at(a, depth, repl);
                self.app(f2, a2)
            }
            Expr::Let(n, t, v, b) => {
                let t2 = self.subst_at(t, depth, repl);
                let v2 = self.subst_at(v, depth, repl);
                let b2 = self.subst_at(b, depth + 1, repl);
                self.intern(Expr::Let(n, t2, v2, b2))
            }
            Expr::Proj(s, i, t) => {
                let t2 = self.subst_at(t, depth, repl);
                self.intern(Expr::Proj(s, i, t2))
            }
        }
    }

    /// Instantiate the outermost binder: replace BVar(0), decrement others.
    pub fn subst_top(&mut self, e: ExprId, repl: ExprId) -> ExprId {
        self.subst_at(e, 0, repl)
    }

    /// Instantiate a telescope of binders: `args[0]` is the outermost variable.
    ///
    /// This must be a single pass (Lean's `instantiate`): iterating
    /// `subst_top` from the innermost binder outward is *wrong*, because
    /// each `subst_top` decrements every free variable above its target —
    /// including variables inside the ambient terms substituted for
    /// earlier binders, which refer to the caller's context and must not
    /// move. In one pass, a free `BVar(i)` at binder depth `d` names
    /// telescope position `i - d` counted from the innermost binder, i.e.
    /// `args[args.len() - 1 - (i - d)]`, shifted by `d`; variables beyond
    /// the telescope drop by the telescope length.
    pub fn subst_telescope(&mut self, e: ExprId, args: &[ExprId]) -> ExprId {
        if args.is_empty() {
            return e;
        }
        self.instantiate(e, args, 0)
    }

    fn instantiate(&mut self, e: ExprId, args: &[ExprId], depth: u32) -> ExprId {
        match self.get_clone(e) {
            Expr::BVar(i) => {
                if i < depth {
                    e
                } else {
                    let rel = (i - depth) as usize;
                    if rel < args.len() {
                        let repl = args[args.len() - 1 - rel];
                        self.shift(repl, depth as i64, 0)
                    } else {
                        self.bvar(i - args.len() as u32)
                    }
                }
            }
            Expr::Const(_, _) | Expr::Sort(_) | Expr::LitNat(_) | Expr::LitStr(_) => e,
            Expr::Pi(n, info, d, c) => {
                let d2 = self.instantiate(d, args, depth);
                let c2 = self.instantiate(c, args, depth + 1);
                self.pi(n, info, d2, c2)
            }
            Expr::Lam(n, info, d, b) => {
                let d2 = self.instantiate(d, args, depth);
                let b2 = self.instantiate(b, args, depth + 1);
                self.lam(n, info, d2, b2)
            }
            Expr::App(f, a) => {
                let f2 = self.instantiate(f, args, depth);
                let a2 = self.instantiate(a, args, depth);
                self.app(f2, a2)
            }
            Expr::Let(n, t, v, b) => {
                let t2 = self.instantiate(t, args, depth);
                let v2 = self.instantiate(v, args, depth);
                let b2 = self.instantiate(b, args, depth + 1);
                self.intern(Expr::Let(n, t2, v2, b2))
            }
            Expr::Proj(s, i, t) => {
                let t2 = self.instantiate(t, args, depth);
                self.intern(Expr::Proj(s, i, t2))
            }
        }
    }

    /// Substitute universe levels inside an expression.
    pub fn subst_levels(&mut self, e: ExprId, subst: &[Level]) -> ExprId {
        if subst.is_empty() {
            // still need to check: empty substitution is identity only if no params expected
            return e;
        }
        match self.get_clone(e) {
            Expr::BVar(_) | Expr::LitNat(_) | Expr::LitStr(_) => e,
            Expr::Const(n, levels) => {
                let ls: Vec<Level> = levels.iter().map(|l| l.subst(subst)).collect();
                self.const_(n, ls)
            }
            Expr::Sort(l) => self.sort(l.subst(subst)),
            Expr::Pi(n, info, d, c) => {
                let d2 = self.subst_levels(d, subst);
                let c2 = self.subst_levels(c, subst);
                self.pi(n, info, d2, c2)
            }
            Expr::Lam(n, info, d, b) => {
                let d2 = self.subst_levels(d, subst);
                let b2 = self.subst_levels(b, subst);
                self.lam(n, info, d2, b2)
            }
            Expr::App(f, a) => {
                let f2 = self.subst_levels(f, subst);
                let a2 = self.subst_levels(a, subst);
                self.app(f2, a2)
            }
            Expr::Let(n, t, v, b) => {
                let t2 = self.subst_levels(t, subst);
                let v2 = self.subst_levels(v, subst);
                let b2 = self.subst_levels(b, subst);
                self.intern(Expr::Let(n, t2, v2, b2))
            }
            Expr::Proj(s, i, t) => {
                let t2 = self.subst_levels(t, subst);
                self.intern(Expr::Proj(s, i, t2))
            }
        }
    }

    pub fn contains_const(&self, e: ExprId, target: NameId) -> bool {
        match self.get(e) {
            Expr::Const(n, _) => *n == target,
            Expr::BVar(_) | Expr::Sort(_) | Expr::LitNat(_) | Expr::LitStr(_) => false,
            Expr::Pi(_, _, d, c) | Expr::Lam(_, _, d, c) => {
                let (d, c) = (*d, *c);
                self.contains_const(d, target) || self.contains_const(c, target)
            }
            Expr::App(f, a) => {
                let (f, a) = (*f, *a);
                self.contains_const(f, target) || self.contains_const(a, target)
            }
            Expr::Let(_, t, v, b) => {
                let (t, v, b) = (*t, *v, *b);
                self.contains_const(t, target)
                    || self.contains_const(v, target)
                    || self.contains_const(b, target)
            }
            Expr::Proj(_, _, t) => {
                let t = *t;
                self.contains_const(t, target)
            }
        }
    }

    /// Collect all global constants referenced (for dependency closures).
    pub fn collect_consts(&self, e: ExprId, out: &mut Vec<NameId>) {
        match self.get_clone(e) {
            Expr::Const(n, _) => {
                if !out.contains(&n) {
                    out.push(n);
                }
            }
            Expr::BVar(_) | Expr::Sort(_) | Expr::LitNat(_) | Expr::LitStr(_) => {}
            Expr::Pi(_, _, d, c) | Expr::Lam(_, _, d, c) => {
                self.collect_consts(d, out);
                self.collect_consts(c, out);
            }
            Expr::App(f, a) => {
                self.collect_consts(f, out);
                self.collect_consts(a, out);
            }
            Expr::Let(_, t, v, b) => {
                self.collect_consts(t, out);
                self.collect_consts(v, out);
                self.collect_consts(b, out);
            }
            Expr::Proj(s, _, t) => {
                if !out.contains(&s) {
                    out.push(s);
                }
                self.collect_consts(t, out);
            }
        }
    }
}

/// Decompose an application spine: returns (head, args in application order).
pub fn spine(arena: &ExprArena, mut e: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut args = Vec::new();
    while let Expr::App(f, a) = arena.get_clone(e) {
        args.push(a);
        e = f;
    }
    args.reverse();
    (e, args)
}

/// Strip a Pi telescope: returns (binders [(name, info, domain)], body).
/// Domains are in the context of the preceding binders.
pub fn pi_telescope(arena: &ExprArena, mut e: ExprId) -> (Vec<(NameId, BinderInfo, ExprId)>, ExprId) {
    let mut binders = Vec::new();
    while let Expr::Pi(n, info, d, c) = arena.get_clone(e) {
        binders.push((n, info, d));
        e = c;
    }
    (binders, e)
}
