//! Elaborator: surface terms and tactic blocks become named core terms,
//! checked step by step against the kernel. The elaborator is *not*
//! trusted: every closed proof is rechecked by `rigor-kernel` when the
//! declaration is admitted, and the final bundle is independently
//! verified by `rigor-runtime`.

use crate::ast::*;
use rigor_certificates::linarith::{nat_farkas_proof, NatIneq};
use rigor_certificates::poly::{poly_identity_proof, PolyExpr};
use rigor_certificates::sat::{unsat_case_proof, Formula};
use rigor_kernel::{lower, to_named, Context, Expr, ExprId, Kernel, Level, LocalDecl, NExpr};
use rigor_spec::BigUint;
use std::collections::{HashMap, HashSet};

// ---------------------------------------------------------------------------
// Named-term utilities
// ---------------------------------------------------------------------------

pub fn fv(e: &NExpr) -> HashSet<String> {
    let mut out = HashSet::new();
    fv_into(e, &mut out);
    out
}

fn fv_into(e: &NExpr, out: &mut HashSet<String>) {
    match e {
        NExpr::Var(s) => {
            out.insert(s.clone());
        }
        NExpr::App(f, a) => {
            fv_into(f, out);
            fv_into(a, out);
        }
        NExpr::Pi(n, _, d, c) | NExpr::Lam(n, _, d, c) => {
            fv_into(d, out);
            let mut inner = HashSet::new();
            fv_into(c, &mut inner);
            inner.remove(n);
            out.extend(inner);
        }
        NExpr::Let(n, t, v, b) => {
            fv_into(t, out);
            fv_into(v, out);
            let mut inner = HashSet::new();
            fv_into(b, &mut inner);
            inner.remove(n);
            out.extend(inner);
        }
        NExpr::Proj(_, _, t) => fv_into(t, out),
        _ => {}
    }
}

fn fresh(base: &str, avoid: &HashSet<String>) -> String {
    let mut cand = base.to_string();
    let mut i = 0;
    while avoid.contains(&cand) {
        i += 1;
        cand = format!("{base}{i}");
    }
    cand
}

/// Capture-avoiding substitution of `name` by `repl` in `e`.
pub fn subst(e: &NExpr, name: &str, repl: &NExpr) -> NExpr {
    match e {
        NExpr::Var(s) => {
            if s == name {
                repl.clone()
            } else {
                e.clone()
            }
        }
        NExpr::App(f, a) => NExpr::app(subst(f, name, repl), subst(a, name, repl)),
        NExpr::Pi(n, info, d, c) => {
            let d2 = subst(d, name, repl);
            if n == name {
                NExpr::Pi(n.clone(), *info, Box::new(d2), c.clone())
            } else {
                let mut avoid = fv(repl);
                avoid.extend(fv(c));
                if avoid.contains(n) {
                    let n2 = fresh(n, &avoid);
                    let c2 = subst(c, n, &NExpr::var(&n2));
                    NExpr::Pi(n2, *info, Box::new(d2), Box::new(subst(&c2, name, repl)))
                } else {
                    NExpr::Pi(n.clone(), *info, Box::new(d2), Box::new(subst(c, name, repl)))
                }
            }
        }
        NExpr::Lam(n, info, d, c) => {
            let d2 = subst(d, name, repl);
            if n == name {
                NExpr::Lam(n.clone(), *info, Box::new(d2), c.clone())
            } else {
                let mut avoid = fv(repl);
                avoid.extend(fv(c));
                if avoid.contains(n) {
                    let n2 = fresh(n, &avoid);
                    let c2 = subst(c, n, &NExpr::var(&n2));
                    NExpr::Lam(n2, *info, Box::new(d2), Box::new(subst(&c2, name, repl)))
                } else {
                    NExpr::Lam(n.clone(), *info, Box::new(d2), Box::new(subst(c, name, repl)))
                }
            }
        }
        NExpr::Let(n, t, v, b) => {
            let t2 = subst(t, name, repl);
            let v2 = subst(v, name, repl);
            if n == name {
                NExpr::Let(n.clone(), Box::new(t2), Box::new(v2), b.clone())
            } else {
                NExpr::Let(n.clone(), Box::new(t2), Box::new(v2), Box::new(subst(b, name, repl)))
            }
        }
        NExpr::Proj(s, i, t) => NExpr::Proj(s.clone(), *i, Box::new(subst(t, name, repl))),
        _ => e.clone(),
    }
}

/// Instantiate the universe parameters of a named term (e.g. a recursor or
/// inductive type read from a declaration) with concrete levels.
pub fn subst_level_params(e: &NExpr, inst: &[Level]) -> NExpr {
    if inst.is_empty() {
        return e.clone();
    }
    match e {
        NExpr::Const(n, lv) => NExpr::Const(n.clone(), lv.iter().map(|l| l.subst(inst)).collect()),
        NExpr::Sort(l) => NExpr::Sort(l.subst(inst)),
        NExpr::App(f, a) => NExpr::app(subst_level_params(f, inst), subst_level_params(a, inst)),
        NExpr::Pi(n, info, d, c) => NExpr::Pi(
            n.clone(),
            *info,
            Box::new(subst_level_params(d, inst)),
            Box::new(subst_level_params(c, inst)),
        ),
        NExpr::Lam(n, info, d, c) => NExpr::Lam(
            n.clone(),
            *info,
            Box::new(subst_level_params(d, inst)),
            Box::new(subst_level_params(c, inst)),
        ),
        NExpr::Let(n, t, v, b) => NExpr::Let(
            n.clone(),
            Box::new(subst_level_params(t, inst)),
            Box::new(subst_level_params(v, inst)),
            Box::new(subst_level_params(b, inst)),
        ),
        NExpr::Proj(s, i, t) => NExpr::Proj(s.clone(), *i, Box::new(subst_level_params(t, inst))),
        _ => e.clone(),
    }
}

/// Replace every syntactic occurrence of `pat` by `repl`.
pub fn replace_all(e: &NExpr, pat: &NExpr, repl: &NExpr) -> NExpr {
    if e == pat {
        return repl.clone();
    }
    match e {
        NExpr::App(f, a) => NExpr::app(replace_all(f, pat, repl), replace_all(a, pat, repl)),
        NExpr::Pi(n, info, d, c) => NExpr::Pi(
            n.clone(),
            *info,
            Box::new(replace_all(d, pat, repl)),
            Box::new(replace_all(c, pat, repl)),
        ),
        NExpr::Lam(n, info, d, c) => NExpr::Lam(
            n.clone(),
            *info,
            Box::new(replace_all(d, pat, repl)),
            Box::new(replace_all(c, pat, repl)),
        ),
        NExpr::Let(n, t, v, b) => NExpr::Let(
            n.clone(),
            Box::new(replace_all(t, pat, repl)),
            Box::new(replace_all(v, pat, repl)),
            Box::new(replace_all(b, pat, repl)),
        ),
        NExpr::Proj(s, i, t) => NExpr::Proj(s.clone(), *i, Box::new(replace_all(t, pat, repl))),
        _ => e.clone(),
    }
}

/// Simple beta reduction (used to normalize recursor minor types and
/// motive applications in induction goals).
pub fn beta_reduce(e: &NExpr) -> NExpr {
    match e {
        NExpr::App(f, a) => {
            let f2 = beta_reduce(f);
            let a2 = beta_reduce(a);
            match f2 {
                NExpr::Lam(n, _, _, body) => beta_reduce(&subst(&body, &n, &a2)),
                _ => NExpr::app(f2, a2),
            }
        }
        NExpr::Pi(n, i, d, c) => NExpr::Pi(n.clone(), *i, Box::new(beta_reduce(d)), Box::new(beta_reduce(c))),
        NExpr::Lam(n, i, d, c) => NExpr::Lam(n.clone(), *i, Box::new(beta_reduce(d)), Box::new(beta_reduce(c))),
        NExpr::Let(n, ty, v, b) => NExpr::Let(
            n.clone(),
            Box::new(beta_reduce(ty)),
            Box::new(beta_reduce(v)),
            Box::new(beta_reduce(b)),
        ),
        NExpr::Proj(s, i, t) => NExpr::Proj(s.clone(), *i, Box::new(beta_reduce(t))),
        _ => e.clone(),
    }
}

pub fn spine(e: &NExpr) -> (NExpr, Vec<NExpr>) {
    let mut args = Vec::new();
    let mut cur = e.clone();
    while let NExpr::App(f, a) = cur {
        args.push((*a).clone());
        cur = (*f).clone();
    }
    args.reverse();
    (cur, args)
}

pub fn apps(f: NExpr, args: &[NExpr]) -> NExpr {
    let mut cur = f;
    for a in args {
        cur = NExpr::app(cur, a.clone());
    }
    cur
}

pub fn pi_chain(e: &NExpr) -> (Vec<(String, NExpr)>, NExpr) {
    let mut binders = Vec::new();
    let mut cur = e.clone();
    while let NExpr::Pi(n, _, d, c) = cur {
        binders.push((n, (*d).clone()));
        cur = (*c).clone();
    }
    (binders, cur)
}

fn nat_const(op: &str) -> NExpr {
    NExpr::const_(op)
}

fn bool_and(a: NExpr, b: NExpr) -> NExpr {
    // Mirrors rigor-certificates' Formula encoding so `solve sat` can read it back.
    apps(
        NExpr::const_levels("Bool.rec", vec![Level::Succ(Box::new(Level::Zero))]),
        &[
            NExpr::lam("_", NExpr::const_("Bool"), NExpr::const_("Bool")),
            b,
            NExpr::const_("Bool.false"),
            a,
        ],
    )
}

fn bool_or(a: NExpr, b: NExpr) -> NExpr {
    apps(
        NExpr::const_levels("Bool.rec", vec![Level::Succ(Box::new(Level::Zero))]),
        &[
            NExpr::lam("_", NExpr::const_("Bool"), NExpr::const_("Bool")),
            NExpr::const_("Bool.true"),
            b,
            a,
        ],
    )
}

fn bool_not(a: NExpr) -> NExpr {
    apps(
        NExpr::const_levels("Bool.rec", vec![Level::Succ(Box::new(Level::Zero))]),
        &[
            NExpr::lam("_", NExpr::const_("Bool"), NExpr::const_("Bool")),
            NExpr::const_("Bool.false"),
            NExpr::const_("Bool.true"),
            a,
        ],
    )
}

// ---------------------------------------------------------------------------
// Goals and proof state
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct CtxLocal {
    pub name: String,
    pub ty: NExpr,
    /// Type lowered into the kernel arena under the *entering* context
    /// (only the preceding locals in scope), as kernel contexts require.
    pub ty_id: ExprId,
    pub value: Option<NExpr>,
    pub value_id: Option<ExprId>,
    pub assuming: bool,
}

#[derive(Debug, Clone)]
pub enum PrefixItem {
    Lam(String, NExpr),
    Have(String, NExpr, NExpr),
}

#[derive(Debug, Clone)]
pub struct Goal {
    pub id: usize,
    /// Placeholder variable name through which the parent proof refers to
    /// this goal's eventual proof (`__rigor_goal_{id}`).
    pub marker: String,
    pub ctx: Vec<CtxLocal>,
    pub target: NExpr,
    pub tag: String,
    pub prefix: Vec<PrefixItem>,
    pub assign: Option<NExpr>,
}

#[derive(Debug, Clone, Default)]
pub struct ProofState {
    pub goals: Vec<Goal>,
    pub focus: Option<usize>,
    pub next_id: usize,
}

impl ProofState {
    pub fn new(root_ctx: Vec<CtxLocal>, root_target: NExpr) -> Self {
        let root = Goal {
            id: 0,
            marker: "__rigor_root".to_string(),
            ctx: root_ctx,
            target: root_target,
            tag: "main".to_string(),
            prefix: Vec::new(),
            assign: None,
        };
        ProofState { goals: vec![root], focus: Some(0), next_id: 1 }
    }

    pub fn focused(&self) -> Option<&Goal> {
        self.focus.and_then(|id| self.goals.iter().find(|g| g.id == id))
    }

    pub fn focused_mut(&mut self) -> Option<&mut Goal> {
        let id = self.focus?;
        self.goals.iter_mut().find(|g| g.id == id)
    }

    pub fn add_goal(&mut self, ctx: Vec<CtxLocal>, target: NExpr, tag: String) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.goals.push(Goal {
            id,
            marker: format!("__rigor_goal_{id}"),
            ctx,
            target,
            tag,
            prefix: Vec::new(),
            assign: None,
        });
        id
    }

    pub fn refocus(&mut self) {
        self.focus = self.goals.iter().find(|g| g.assign.is_none()).map(|g| g.id);
    }

    pub fn open_goals(&self) -> Vec<&Goal> {
        self.goals.iter().filter(|g| g.assign.is_none()).collect()
    }

    /// Fully substitute subgoal proofs into a goal's assigned proof and
    /// apply its intro/have prefix.
    pub fn assemble(&self, goal: &Goal) -> Result<NExpr, String> {
        let mut body = goal
            .assign
            .clone()
            .ok_or_else(|| format!("goal '{}' is not closed", goal.tag))?;
        body = self.resolve_markers(body)?;
        for item in goal.prefix.iter().rev() {
            match item {
                PrefixItem::Lam(name, dom) => {
                    body = NExpr::lam(name, dom.clone(), body);
                }
                PrefixItem::Have(name, ty, proof) => {
                    let p2 = self.resolve_markers(proof.clone())?;
                    body = NExpr::app(NExpr::lam(name, ty.clone(), body), p2);
                }
            }
        }
        Ok(body)
    }

    fn resolve_markers(&self, mut body: NExpr) -> Result<NExpr, String> {
        loop {
            let vars = fv(&body);
            let marker = vars.iter().find(|v| v.starts_with("__rigor_goal_") || v.starts_with("__rigor_hole_")).cloned();
            match marker {
                None => return Ok(body),
                Some(m) => {
                    let child = self
                        .goals
                        .iter()
                        .find(|g| g.marker == m)
                        .ok_or_else(|| format!("internal: unknown subgoal marker {m}"))?;
                    let child_proof = self.assemble(child)?;
                    body = subst(&body, &m, &child_proof);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Elaborator
// ---------------------------------------------------------------------------

pub struct Elab {
    pub kernel: Kernel,
    pub strict: bool,
    /// Registered named contexts for conversion tickets (bundle contexts).
    pub contexts: Vec<Vec<rigor_codec::CtxEntry>>,
    pub tickets: Vec<rigor_codec::PortableTicket>,
    /// Level parameter names of the declaration currently being elaborated.
    pub level_scope: Vec<String>,
}

pub type EResult<T> = Result<T, String>;

impl Elab {
    pub fn new(kernel: Kernel) -> Self {
        Elab { kernel, strict: true, contexts: Vec::new(), tickets: Vec::new(), level_scope: Vec::new() }
    }

    // ---- kernel plumbing ----

    pub fn lower_in(&mut self, ctx: &[CtxLocal], e: &NExpr) -> EResult<ExprId> {
        let mut scope: Vec<String> = ctx.iter().map(|l| l.name.clone()).collect();
        lower(&mut self.kernel.arena, &mut self.kernel.names, &mut scope, e).map_err(|err| err.0)
    }

    pub fn kernel_ctx(&mut self, ctx: &[CtxLocal]) -> Context {
        ctx.iter()
            .map(|l| {
                let nid = self.kernel.name(&l.name);
                LocalDecl { name: nid, ty: l.ty_id, value: l.value_id }
            })
            .collect()
    }

    pub fn infer_nexpr(&mut self, ctx: &[CtxLocal], e: &NExpr) -> EResult<NExpr> {
        let id = self.lower_in(ctx, e)?;
        let kc = self.kernel_ctx(ctx);
        let ty = self.kernel.infer(&kc, id).map_err(|err| format!("cannot infer type: {err}"))?;
        let mut scope: Vec<String> = ctx.iter().map(|l| l.name.clone()).collect();
        Ok(beta_reduce(&to_named(&self.kernel.arena, &self.kernel.names, ty, &mut scope)))
    }

    pub fn check_nexpr(&mut self, ctx: &[CtxLocal], proof: &NExpr, target: &NExpr) -> EResult<()> {
        let pid = self.lower_in(ctx, proof)?;
        let tid = self.lower_in(ctx, target)?;
        let kc = self.kernel_ctx(ctx);
        self.kernel.check(&kc, pid, tid).map_err(|err| format!("type error: {err}"))
    }

    /// Sort level of a type term: `u` with `ty : Sort u`, if it is one.
    pub fn sort_level_of(&mut self, ctx: &[CtxLocal], ty: &NExpr) -> EResult<Level> {
        let id = self.lower_in(ctx, ty)?;
        let kc = self.kernel_ctx(ctx);
        let s = self.kernel.infer(&kc, id).map_err(|err| err.to_string())?;
        match self.kernel.arena.get_clone(s) {
            Expr::Sort(l) => Ok(l),
            _ => Err("expected a type (its type is not a Sort)".into()),
        }
    }

    /// Name of the head constant of a term's type (e.g. "Nat"), if any.
    pub fn head_type_name(&mut self, ctx: &[CtxLocal], e: &NExpr) -> Option<String> {
        let ty = self.infer_nexpr(ctx, e).ok()?;
        let (head, _) = spine(&ty);
        match head {
            NExpr::Const(n, _) => Some(n),
            _ => None,
        }
    }

    pub fn register_ctx(&mut self, ctx: &[CtxLocal]) -> u32 {
        let entries: Vec<rigor_codec::CtxEntry> = ctx
            .iter()
            .map(|l| {
                let nid = self.kernel.name(&l.name);
                rigor_codec::CtxEntry { is_let: l.value_id.is_some(), name: nid, ty: l.ty_id, value: l.value_id }
            })
            .collect();
        if let Some(pos) = self.contexts.iter().position(|c| *c == entries) {
            return pos as u32;
        }
        self.contexts.push(entries);
        (self.contexts.len() - 1) as u32
    }

    pub fn default_levels(&mut self, name: &str) -> Vec<Level> {
        if let Some(nid) = self.kernel.names.lookup(name) {
            if let Some(decl) = self.kernel.env.get(nid) {
                return vec![Level::Zero; decl.level_params.len()];
            }
        }
        Vec::new()
    }

    /// Constants applied to arguments frequently need their universe
    /// arguments inferred from the first type-valued arguments (e.g.
    /// `Eq.symm Nat x y h` needs `Eq.symm.{1}`, not the default `.{0}`).
    /// For each level parameter, take the sort level of the first
    /// not-yet-consumed argument whose type is a Sort. The kernel re-checks
    /// the result, so a wrong guess is an error, never a soundness issue.
    fn fix_const_levels(&mut self, ctx: &[CtxLocal], e: NExpr) -> NExpr {
        let (head, args) = spine(&e);
        let (name, levels) = match &head {
            NExpr::Const(n, lv) if !lv.is_empty() => (n.clone(), lv.clone()),
            _ => return e,
        };
        let nparams = match self.kernel.names.lookup(&name).and_then(|id| self.kernel.env.get(id)) {
            Some(d) => d.level_params.len(),
            None => return e,
        };
        if nparams != levels.len() || nparams == 0 {
            return e;
        }
        // Zero is the "not yet inferred" sentinel from default_levels.
        // Fill each still-zero parameter from the sort level of the next
        // type-valued argument, in order. (Requiring *all* levels to be
        // zero first — the old precondition — meant multi-parameter
        // constants like Prod.{u,v} only ever got their first universe
        // inferred, one application node at a time.)
        let mut new_levels = levels.clone();
        let mut param_i = 0usize;
        for arg in &args {
            while param_i < nparams && !matches!(new_levels[param_i], Level::Zero) {
                param_i += 1;
            }
            if param_i >= nparams {
                break;
            }
            if let Ok(ty) = self.infer_nexpr(ctx, arg) {
                if let NExpr::Sort(l) = ty {
                    new_levels[param_i] = l;
                    param_i += 1;
                }
            }
        }
        if new_levels == levels {
            e
        } else {
            apps(NExpr::Const(name, new_levels), &args)
        }
    }

    // ---- term elaboration ----

    /// Elaborate a surface term in a local context. Division/modulo by a
    /// denominator that is not a positive literal, under the strict
    /// profile, records a proof obligation into `obs` (as
    /// (context, obligation type)); outside a proof these are errors.
    pub fn elaborate(&mut self, ctx: &[CtxLocal], t: &STerm, obs: &mut Vec<(Vec<CtxLocal>, NExpr)>) -> EResult<NExpr> {
        match t {
            STerm::Ident(s) => {
                if s == "Prop" {
                    return Ok(NExpr::sort(Level::Zero));
                }
                if s == "Type" {
                    return Ok(NExpr::sort(Level::Succ(Box::new(Level::Zero))));
                }
                if ctx.iter().any(|l| l.name == *s) {
                    return Ok(NExpr::var(s));
                }
                // Field access written `r.num` lexes as a dotted identifier:
                if let Some(dot) = s.find('.') {
                    let (base, field) = (&s[..dot], &s[dot + 1..]);
                    if ctx.iter().any(|l| l.name == base) && !field.is_empty() {
                        return self.elaborate(ctx, &STerm::Access(Box::new(STerm::Ident(base.to_string())), field.to_string()), obs);
                    }
                }
                let levels = self.default_levels(s);
                Ok(NExpr::Const(s.clone(), levels))
            }
            STerm::Lit(n) => Ok(NExpr::LitNat(n.clone())),
            STerm::Str(s) => Ok(NExpr::LitStr(s.clone())),
            STerm::Hole => Err("hole '_' is only allowed inside refine".into()),
            STerm::App(f, a) => {
                // Tuple sugar `(x, y)` is parsed as `Prod.mk x y`, but the
                // core constructor also takes the component types
                // explicitly. Insert them from the components' types.
                {
                    let mut args: Vec<&STerm> = vec![a.as_ref()];
                    let mut head = f.as_ref();
                    while let STerm::App(f2, a2) = head {
                        args.push(a2.as_ref());
                        head = f2.as_ref();
                    }
                    args.reverse();
                    if let STerm::Ident(name) = head {
                        if name == "Prod.mk" && args.len() == 2 {
                            let x = self.elaborate(ctx, args[0], obs)?;
                            let y = self.elaborate(ctx, args[1], obs)?;
                            let tx = self.infer_nexpr(ctx, &x)?;
                            let ty = self.infer_nexpr(ctx, &y)?;
                            let lu = self.sort_level_of(ctx, &tx)?;
                            let lv = self.sort_level_of(ctx, &ty)?;
                            let mk = NExpr::const_levels("Prod.mk", vec![lu, lv]);
                            return Ok(apps(mk, &[tx, ty, x, y]));
                        }
                    }
                }
                let f2 = self.elaborate(ctx, f, obs)?;
                let a2 = self.elaborate(ctx, a, obs)?;
                let e = NExpr::app(f2, a2);
                Ok(self.fix_const_levels(ctx, e))
            }
            STerm::ULevels(inner, names) => match &**inner {
                STerm::Ident(s) => {
                    let mut levels = Vec::new();
                    for n in names {
                        match self.level_scope.iter().position(|p| p == n) {
                            Some(i) => levels.push(Level::Param(i as u32)),
                            None => return Err(format!("universe parameter '{n}' is not declared on this declaration")),
                        }
                    }
                    Ok(NExpr::Const(s.clone(), levels))
                }
                _ => Err("universe arguments can only follow a constant name".into()),
            },
            STerm::Neg(inner) => match &**inner {
                STerm::Lit(n) => {
                    if n.is_zero() {
                        Ok(apps(NExpr::const_("Int.ofNat"), &[NExpr::LitNat(n.clone())]))
                    } else {
                        Ok(apps(NExpr::const_("Int.negSucc"), &[NExpr::LitNat(n.sub(&BigUint::one()))]))
                    }
                }
                _ => {
                    let e = self.elaborate(ctx, inner, obs)?;
                    Ok(apps(NExpr::const_("Int.neg"), &[e]))
                }
            },
            STerm::Not(inner) => {
                let e = self.elaborate(ctx, inner, obs)?;
                match self.head_type_name(ctx, &e).as_deref() {
                    Some("Bool") => Ok(bool_not(e)),
                    _ => Ok(apps(NExpr::const_("Not"), &[e])),
                }
            }
            STerm::Access(target, field) => {
                let e = self.elaborate(ctx, target, obs)?;
                let ty = self.infer_nexpr(ctx, &e)?;
                let (head, _) = spine(&ty);
                let struct_name = match &head {
                    NExpr::Const(n, _) => n.clone(),
                    _ => return Err(format!("field access on non-structure type {}", rigor_kernel::pretty_named(&ty))),
                };
                let idx = if field.chars().all(|c| c.is_ascii_digit()) {
                    field.parse::<u32>().map_err(|_| "bad projection index".to_string())?
                } else {
                    self.field_index(&struct_name, field)?
                };
                Ok(NExpr::Proj(struct_name, idx, Box::new(e)))
            }
            STerm::Lam(binders, body) => {
                let mut ctx2: Vec<CtxLocal> = ctx.to_vec();
                let mut obs2 = Vec::new();
                let mut doms: Vec<(String, NExpr)> = Vec::new();
                for (name, ty) in binders {
                    let dom = match ty {
                        Some(t) => self.elaborate(&ctx2, t, &mut obs2)?,
                        None => return Err(format!("lambda binder '{name}' needs a type annotation")),
                    };
                    let local = self.make_local(&ctx2, name, dom.clone(), None, false)?;
                    ctx2.push(local);
                    doms.push((name.clone(), dom));
                }
                if !obs2.is_empty() {
                    return Err("division in a lambda body creates an obligation that cannot be discharged here".into());
                }
                let mut out = self.elaborate(&ctx2, body, obs)?;
                for (name, dom) in doms.iter().rev() {
                    out = NExpr::lam(name, dom.clone(), out);
                }
                Ok(out)
            }
            STerm::Pi(binders, body) => {
                let mut ctx2: Vec<CtxLocal> = ctx.to_vec();
                let mut obs2 = Vec::new();
                let mut doms: Vec<(String, NExpr)> = Vec::new();
                for (name, ty) in binders {
                    let dom = match ty {
                        Some(t) => self.elaborate(&ctx2, t, &mut obs2)?,
                        None => return Err(format!("Pi binder '{name}' needs a type annotation")),
                    };
                    let local = self.make_local(&ctx2, name, dom.clone(), None, false)?;
                    ctx2.push(local);
                    doms.push((name.clone(), dom));
                }
                let mut out = self.elaborate(&ctx2, body, obs)?;
                for (name, dom) in doms.iter().rev() {
                    out = NExpr::pi(name, dom.clone(), out);
                }
                Ok(out)
            }
            STerm::Arrow(a, b) => {
                let a2 = self.elaborate(ctx, a, obs)?;
                let b2 = self.elaborate(ctx, b, obs)?;
                Ok(NExpr::pi("_", a2, b2))
            }
            STerm::Let(name, ty, val, body) => {
                let mut obs2 = Vec::new();
                let v = self.elaborate(ctx, val, &mut obs2)?;
                let ty2 = match ty {
                    Some(t) => self.elaborate(ctx, t, &mut obs2)?,
                    None => self.infer_nexpr(ctx, &v)?,
                };
                let local = self.make_local(ctx, name, ty2.clone(), Some(v.clone()), false)?;
                let mut ctx2: Vec<CtxLocal> = ctx.to_vec();
                ctx2.push(local);
                let b = self.elaborate(&ctx2, body, obs)?;
                Ok(NExpr::Let(name.clone(), Box::new(ty2), Box::new(v), Box::new(b)))
            }
            STerm::Bin(op, a, b) => self.elaborate_bin(ctx, *op, a, b, obs),
        }
    }

    fn field_index(&mut self, struct_name: &str, field: &str) -> EResult<u32> {
        let nid = self.kernel.names.lookup(struct_name).ok_or_else(|| format!("unknown structure {struct_name}"))?;
        let decl = self.kernel.env.get(nid).cloned().ok_or_else(|| format!("unknown structure {struct_name}"))?;
        let info = decl.inductive.clone().ok_or_else(|| format!("{struct_name} is not an inductive type"))?;
        if info.constructors.len() != 1 {
            return Err(format!("{struct_name} is not a structure (it has {} constructors)", info.constructors.len()));
        }
        let ctor = self.kernel.env.get(info.constructors[0]).cloned().ok_or("missing constructor")?;
        let scope: Vec<String> = Vec::new();
        let cty = to_named(&self.kernel.arena, &self.kernel.names, ctor.ty, &mut scope.clone());
        let (binders, _) = pi_chain(&cty);
        let fields = &binders[(info.num_params as usize)..];
        fields
            .iter()
            .position(|(n, _)| n == field)
            .map(|i| i as u32)
            .ok_or_else(|| format!("structure {struct_name} has no field '{field}'"))
    }

    pub fn make_local(&mut self, ctx: &[CtxLocal], name: &str, ty: NExpr, value: Option<NExpr>, assuming: bool) -> EResult<CtxLocal> {
        let ty_id = self.lower_in(ctx, &ty)?;
        let value_id = match &value {
            Some(v) => Some(self.lower_in(ctx, v)?),
            None => None,
        };
        Ok(CtxLocal { name: name.to_string(), ty, ty_id, value, value_id, assuming })
    }

    fn elaborate_bin(&mut self, ctx: &[CtxLocal], op: BinOp, a: &STerm, b: &STerm, obs: &mut Vec<(Vec<CtxLocal>, NExpr)>) -> EResult<NExpr> {
        use BinOp::*;
        match op {
            Eq | Ne => {
                let a2 = self.elaborate(ctx, a, obs)?;
                let b2 = self.elaborate(ctx, b, obs)?;
                let ty = self.infer_nexpr(ctx, &a2)?;
                let lvl = self.sort_level_of(ctx, &ty)?;
                let eq = apps(NExpr::Const("Eq".into(), vec![lvl]), &[ty, a2, b2]);
                if op == Eq {
                    Ok(eq)
                } else {
                    Ok(NExpr::pi("_", eq, NExpr::const_("False")))
                }
            }
            And | Or => {
                let a2 = self.elaborate(ctx, a, obs)?;
                let b2 = self.elaborate(ctx, b, obs)?;
                match self.head_type_name(ctx, &a2).as_deref() {
                    Some("Bool") => Ok(if op == And { bool_and(a2, b2) } else { bool_or(a2, b2) }),
                    _ => Ok(apps(NExpr::const_(if op == And { "And" } else { "Or" }), &[a2, b2])),
                }
            }
            Le | Lt | Ge | Gt => {
                let mut a2 = self.elaborate(ctx, a, obs)?;
                let mut b2 = self.elaborate(ctx, b, obs)?;
                if op == Ge || op == Gt {
                    std::mem::swap(&mut a2, &mut b2);
                }
                let ns = self.head_type_name(ctx, &a2).unwrap_or_else(|| "Nat".into());
                let strict_op = op == Lt || op == Gt;
                let cname = match (ns.as_str(), strict_op) {
                    ("Int", false) => "Int.le",
                    ("Rat", false) => "Rat.le",
                    ("Nat", false) => "Nat.le",
                    ("Nat", true) => "Nat.lt",
                    _ => return Err(format!("comparison not available for {ns}")),
                };
                Ok(apps(NExpr::const_(cname), &[a2, b2]))
            }
            Add | Sub | Mul | Div | Mod | Pow => {
                let a2 = self.elaborate(ctx, a, obs)?;
                let b2 = self.elaborate(ctx, b, obs)?;
                let ns = self.head_type_name(ctx, &a2).unwrap_or_else(|| "Nat".into());
                if (op == Div || op == Mod) && self.strict {
                    let literal_ok = matches!(b, STerm::Lit(n) if !n.is_zero());
                    if !literal_ok {
                        // Obligation: the denominator is nonzero. It must be
                        // *proved* in the surrounding proof; it is never
                        // silently added as a hypothesis.
                        let (eq_ty, zero) = if ns == "Int" {
                            (NExpr::const_("Int"), apps(NExpr::const_("Int.ofNat"), &[NExpr::LitNat(BigUint::zero())]))
                        } else {
                            (nat_const("Nat"), NExpr::LitNat(BigUint::zero()))
                        };
                        let lvl = self.sort_level_of(ctx, &eq_ty)?;
                        let eq = apps(NExpr::Const("Eq".into(), vec![lvl]), &[eq_ty, b2.clone(), zero]);
                        let obligation = NExpr::pi("_", eq, NExpr::const_("False"));
                        obs.push((ctx.to_vec(), obligation));
                    }
                }
                let cname = match (ns.as_str(), op) {
                    ("Int", Add) => "Int.add",
                    ("Int", Sub) => "Int.sub",
                    ("Int", Mul) => "Int.mul",
                    ("Rat", Add) => "Rat.add",
                    ("Rat", Mul) => "Rat.mul",
                    ("Nat", Add) => "Nat.add",
                    ("Nat", Sub) => "Nat.sub",
                    ("Nat", Mul) => "Nat.mul",
                    ("Nat", Div) => "Nat.div",
                    ("Nat", Mod) => "Nat.mod",
                    ("Nat", Pow) => "Nat.pow",
                    _ => return Err(format!("operator {} not available for {ns}", op.symbol())),
                };
                Ok(apps(NExpr::const_(cname), &[a2, b2]))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tactic execution
// ---------------------------------------------------------------------------

fn goal_marker(id: usize) -> String {
    format!("__rigor_goal_{id}")
}

impl Elab {
    fn focused_goal(&self, state: &ProofState) -> EResult<Goal> {
        state.focused().cloned().ok_or_else(|| "no focused goal".to_string())
    }

    fn set_assign(&self, state: &mut ProofState, id: usize, proof: NExpr) {
        if let Some(g) = state.goals.iter_mut().find(|g| g.id == id) {
            g.assign = Some(proof);
        }
    }

    fn push_obligations(&self, state: &mut ProofState, obs: Vec<(Vec<CtxLocal>, NExpr)>) {
        for (octx, oty) in obs {
            state.add_goal(octx, oty, "denominator_nonzero".to_string());
        }
    }

    pub fn run_tactics(&mut self, state: &mut ProofState, tactics: &[Tactic]) -> EResult<()> {
        for tac in tactics {
            self.run_tactic(state, tac)?;
        }
        Ok(())
    }

    pub fn run_tactic(&mut self, state: &mut ProofState, tac: &Tactic) -> EResult<()> {
        match tac {
            Tactic::Case(name) => {
                let g = state
                    .goals
                    .iter()
                    .find(|g| g.assign.is_none() && g.tag == *name)
                    .ok_or_else(|| {
                        let open: Vec<String> = state.open_goals().iter().map(|g| g.tag.clone()).collect();
                        format!("no open goal tagged '{name}'; open goals: {open:?}")
                    })?;
                state.focus = Some(g.id);
                Ok(())
            }
            Tactic::Exact(t) => self.tactic_exact(state, t),
            Tactic::Refine(t) => self.tactic_refine(state, t),
            Tactic::Have { name, ty, proof } => self.tactic_have(state, name, ty, proof),
            Tactic::Intro(names) => {
                for n in names {
                    self.tactic_intro(state, n)?;
                }
                Ok(())
            }
            Tactic::Apply(t) => self.tactic_apply(state, t),
            Tactic::Rewrite { term, reverse } => self.tactic_rewrite(state, term, *reverse),
            Tactic::Induction(x) => self.tactic_induction(state, x, true),
            Tactic::Cases(x) => self.tactic_induction(state, x, false),
            Tactic::Branch(x) => self.tactic_induction(state, x, false),
            Tactic::Show(t) => {
                let goal = self.focused_goal(state)?;
                let mut obs = Vec::new();
                let new_target = self.elaborate(&goal.ctx, t, &mut obs)?;
                self.push_obligations(state, obs);
                let a = self.lower_in(&goal.ctx, &goal.target)?;
                let b = self.lower_in(&goal.ctx, &new_target)?;
                let kc = self.kernel_ctx(&goal.ctx);
                if !self.kernel.is_def_eq(&kc, a, b).map_err(|e| e.to_string())? {
                    return Err("show: new goal is not definitionally equal to the current goal".into());
                }
                if let Some(g) = state.focused_mut() {
                    g.target = new_target;
                }
                Ok(())
            }
            Tactic::Calc(steps) => self.tactic_calc(state, steps),
            Tactic::Solve(kind) => self.tactic_solve(state, kind),
            Tactic::Assumption => {
                let goal = self.focused_goal(state)?;
                for local in &goal.ctx {
                    let cand = NExpr::var(&local.name);
                    if self.check_nexpr(&goal.ctx, &cand, &goal.target).is_ok() {
                        self.set_assign(state, goal.id, cand);
                        state.refocus();
                        return Ok(());
                    }
                }
                Err("assumption: no hypothesis matches the goal".into())
            }
            Tactic::Trivial => {
                if self.run_tactic(state, &Tactic::Assumption).is_ok() {
                    return Ok(());
                }
                let goal = self.focused_goal(state)?;
                let (head, args) = spine(&goal.target);
                if let NExpr::Const(n, lv) = &head {
                    if n == "Eq" && args.len() == 3 {
                        let cand = apps(NExpr::Const("Eq.refl".into(), lv.clone()), &[args[0].clone(), args[1].clone()]);
                        self.check_nexpr(&goal.ctx, &cand, &goal.target)?;
                        self.set_assign(state, goal.id, cand);
                        state.refocus();
                        return Ok(());
                    }
                    if n == "True" {
                        let cand = NExpr::const_("True.intro");
                        self.check_nexpr(&goal.ctx, &cand, &goal.target)?;
                        self.set_assign(state, goal.id, cand);
                        state.refocus();
                        return Ok(());
                    }
                }
                Err("trivial: goal is neither an assumption, a reflexive equality, nor True".into())
            }
            Tactic::Constructor => {
                let goal = self.focused_goal(state)?;
                let (head, _) = spine(&goal.target);
                let ind_name = match &head {
                    NExpr::Const(n, _) => n.clone(),
                    _ => return Err("constructor: goal is not an inductive type".into()),
                };
                let nid = self.kernel.names.lookup(&ind_name).ok_or("constructor: unknown inductive")?;
                let decl = self.kernel.env.get(nid).cloned().ok_or("constructor: unknown inductive")?;
                let info = decl.inductive.ok_or("constructor: not an inductive")?;
                let ctor = info.constructors.first().ok_or("constructor: no constructors")?;
                let ctor_name = self.kernel.names.display(*ctor);
                self.tactic_apply(state, &STerm::Ident(ctor_name))
            }
            Tactic::Left => self.tactic_apply(state, &STerm::Ident("Or.inl".into())),
            Tactic::Right => self.tactic_apply(state, &STerm::Ident("Or.inr".into())),
        }
    }

    fn tactic_exact(&mut self, state: &mut ProofState, t: &STerm) -> EResult<()> {
        let goal = self.focused_goal(state)?;
        let mut obs = Vec::new();
        let proof = self.elaborate(&goal.ctx, t, &mut obs)?;
        self.push_obligations(state, obs);
        // Kernel-check now (early, precise errors), and record a CHECK_CORE
        // conversion ticket when the proof's inferred type differs
        // syntactically from the goal.
        let pid = self.lower_in(&goal.ctx, &proof)?;
        let tid = self.lower_in(&goal.ctx, &goal.target)?;
        let kc = self.kernel_ctx(&goal.ctx);
        let inferred = self.kernel.infer(&kc, pid).map_err(|e| format!("exact: cannot infer the proof's type: {e}"))?;
        self.kernel.check(&kc, pid, tid).map_err(|e| format!("exact: type error: {e}"))?;
        if inferred != tid {
            let ctx_idx = self.register_ctx(&goal.ctx);
            self.tickets.push(rigor_codec::PortableTicket {
                op: rigor_spec::TicketOpcode::CheckCore as u8,
                ctx: ctx_idx,
                x: inferred,
                y: tid,
                z: 0,
                refs: Vec::new(),
            });
        }
        self.set_assign(state, goal.id, proof);
        state.refocus();
        Ok(())
    }

    fn tactic_refine(&mut self, state: &mut ProofState, t: &STerm) -> EResult<()> {
        let goal = self.focused_goal(state)?;
        // Elaborate with holes as placeholders; the expected type of each
        // hole is taken from the Pi telescope of the head's type.
        let mut holes: Vec<(String, NExpr)> = Vec::new(); // (marker, expected type)
        let proof = self.elaborate_refine(&goal, t, &goal.target.clone(), &mut holes)?;
        self.set_assign(state, goal.id, proof);
        let mut first_child = None;
        for (marker, expected) in holes {
            let id = state.add_goal(goal.ctx.clone(), expected, format!("refine {marker}"));
            if let Some(g) = state.goals.iter_mut().find(|g| g.id == id) {
                g.marker = marker;
            }
            if first_child.is_none() {
                first_child = Some(id);
            }
        }
        state.focus = first_child.or(state.focus);
        if first_child.is_none() {
            state.refocus();
        }
        Ok(())
    }

    fn elaborate_refine(
        &mut self,
        goal: &Goal,
        t: &STerm,
        expected: &NExpr,
        holes: &mut Vec<(String, NExpr)>,
    ) -> EResult<NExpr> {
        match t {
            STerm::Hole => {
                let id = holes.len();
                let marker = format!("__rigor_hole_{}", goal.id * 1000 + id);
                holes.push((marker.clone(), expected.clone()));
                Ok(NExpr::var(&marker))
            }
            STerm::App(_, _) => {
                // collect spine
                let mut args: Vec<&STerm> = Vec::new();
                let mut head = t;
                while let STerm::App(f, a) = head {
                    args.push(a);
                    head = f;
                }
                args.reverse();
                let mut obs = Vec::new();
                let head_e = self.elaborate(&goal.ctx, head, &mut obs)?;
                if !obs.is_empty() {
                    return Err("division obligation inside refine is not supported".into());
                }
                let head_ty = self.infer_nexpr(&goal.ctx, &head_e)?;
                let (binders, _cod) = pi_chain(&head_ty);
                let mut out = head_e;
                let mut subst_map: Vec<(String, NExpr)> = Vec::new();
                for (i, a) in args.iter().enumerate() {
                    let dom = binders.get(i).map(|(_, d)| {
                        let mut d = d.clone();
                        for (n, v) in &subst_map {
                            d = subst(&d, n, v);
                        }
                        d
                    });
                    let dom = match dom {
                        Some(d) => d,
                        None => return Err("refine: too many arguments for the head's type".into()),
                    };
                    let ae = self.elaborate_refine(goal, a, &dom, holes)?;
                    if let STerm::Hole = a {
                        // marker var already recorded with this domain
                    }
                    if let Some((bname, _)) = binders.get(i) {
                        subst_map.push((bname.clone(), ae.clone()));
                    }
                    out = NExpr::app(out, ae);
                }
                Ok(out)
            }
            _ => {
                let mut obs = Vec::new();
                let e = self.elaborate(&goal.ctx, t, &mut obs)?;
                if !obs.is_empty() {
                    return Err("division obligation inside refine is not supported".into());
                }
                // a hole-free term in a non-spine position: check against expected
                self.check_nexpr(&goal.ctx, &e, expected)?;
                Ok(e)
            }
        }
    }

    fn tactic_have(&mut self, state: &mut ProofState, name: &str, ty: &STerm, proof: &HaveProof) -> EResult<()> {
        let goal = self.focused_goal(state)?;
        let mut obs = Vec::new();
        let ty_e = self.elaborate(&goal.ctx, ty, &mut obs)?;
        self.push_obligations(state, obs);
        match proof {
            HaveProof::Term(t) => {
                let mut obs2 = Vec::new();
                let p = self.elaborate(&goal.ctx, t, &mut obs2)?;
                self.push_obligations(state, obs2);
                self.check_nexpr(&goal.ctx, &p, &ty_e)?;
                let local = self.make_local(&goal.ctx, name, ty_e.clone(), None, true)?;
                if let Some(g) = state.focused_mut() {
                    g.prefix.push(PrefixItem::Have(name.to_string(), ty_e, p));
                    g.ctx.push(local);
                }
                Ok(())
            }
            HaveProof::Block(tactics) => {
                let child_id = state.add_goal(goal.ctx.clone(), ty_e.clone(), format!("have {name}"));
                let marker = goal_marker(child_id);
                if let Some(g) = state.goals.iter_mut().find(|g| g.id == child_id) {
                    g.marker = marker.clone();
                }
                let local = self.make_local(&goal.ctx, name, ty_e.clone(), None, true)?;
                if let Some(g) = state.focused_mut() {
                    g.prefix.push(PrefixItem::Have(name.to_string(), ty_e, NExpr::var(&marker)));
                    g.ctx.push(local);
                }
                state.focus = Some(child_id);
                // Run the sub-block against the child goal; afterwards focus
                // returns to the continuation (the parent goal).
                self.run_tactics(state, tactics)?;
                if state.goals.iter().any(|g| g.id == goal.id && g.assign.is_none()) {
                    state.focus = Some(goal.id);
                } else {
                    state.refocus();
                }
                Ok(())
            }
        }
    }

    fn tactic_intro(&mut self, state: &mut ProofState, name: &str) -> EResult<()> {
        let goal = self.focused_goal(state)?;
        match &goal.target {
            NExpr::Pi(binder, _, dom, cod) => {
                let (binder, dom, cod) = (binder.clone(), (**dom).clone(), (**cod).clone());
                let cod2 = if binder == *name {
                    cod
                } else {
                    subst(&cod, &binder, &NExpr::var(name))
                };
                let local = self.make_local(&goal.ctx, name, dom.clone(), None, false)?;
                if let Some(g) = state.focused_mut() {
                    g.prefix.push(PrefixItem::Lam(name.to_string(), dom));
                    g.ctx.push(local);
                    g.target = cod2;
                }
                Ok(())
            }
            _ => Err(format!("intro: goal is not a Pi type: {}", rigor_kernel::pretty_named(&goal.target))),
        }
    }

    // ---- apply with first-order unification ----

    fn tactic_apply(&mut self, state: &mut ProofState, t: &STerm) -> EResult<()> {
        let goal = self.focused_goal(state)?;
        let mut obs = Vec::new();
        let head = self.elaborate(&goal.ctx, t, &mut obs)?;
        self.push_obligations(state, obs);
        let ty = self.infer_nexpr(&goal.ctx, &head)?;
        let (mut binders, cod) = pi_chain(&ty);
        // Freshen binders against the local context and each other.
        let mut avoid: HashSet<String> = goal.ctx.iter().map(|l| l.name.clone()).collect();
        let mut renames: Vec<(String, String)> = Vec::new();
        for (n, dom) in binders.iter_mut() {
            let mut dom2 = dom.clone();
            for (old, new) in &renames {
                dom2 = subst(&dom2, old, &NExpr::var(new));
            }
            *dom = dom2;
            if avoid.contains(n) {
                let n2 = fresh(n, &avoid);
                renames.push((n.clone(), n2.clone()));
                *n = n2;
            }
            avoid.insert(n.clone());
        }
        let mut cod = cod;
        for (old, new) in &renames {
            cod = subst(&cod, old, &NExpr::var(new));
        }
        let mvars: HashSet<String> = binders.iter().map(|(n, _)| n.clone()).collect();
        let mut subst_map: HashMap<String, NExpr> = HashMap::new();
        if !unify(&cod, &goal.target, &mvars, &mut subst_map) {
            // Fallback: after partial substitution, ask the kernel.
            let cod2 = apply_subst_multi(&cod, &subst_map);
            let a = self.lower_in(&goal.ctx, &cod2)?;
            let b = self.lower_in(&goal.ctx, &goal.target)?;
            let kc = self.kernel_ctx(&goal.ctx);
            let defeq = self.kernel.is_def_eq(&kc, a, b).unwrap_or(false);
            if !defeq {
                return Err(format!(
                    "apply: conclusion {} does not unify with goal {}",
                    rigor_kernel::pretty_named(&cod),
                    rigor_kernel::pretty_named(&goal.target)
                ));
            }
        }
        // Build arguments; undetermined binders become subgoals.
        let mut args: Vec<NExpr> = Vec::new();
        let mut children: Vec<(Vec<CtxLocal>, NExpr, String)> = Vec::new();
        let mut local_subst: Vec<(String, NExpr)> = Vec::new();
        for (name, dom) in &binders {
            let mut dom2 = dom.clone();
            for (n, v) in &local_subst {
                dom2 = subst(&dom2, n, v);
            }
            if let Some(v) = subst_map.get(name) {
                let mut v2 = v.clone();
                for (n, vv) in &local_subst {
                    v2 = subst(&v2, n, vv);
                }
                args.push(v2.clone());
                local_subst.push((name.clone(), v2));
            } else {
                let marker = format!("__rigor_apply_{}_{}", goal.id, children.len());
                args.push(NExpr::var(&marker));
                children.push((goal.ctx.clone(), dom2, format!("apply {name}")));
                local_subst.push((name.clone(), NExpr::var(&marker)));
            }
        }
        let proof = apps(head, &args);
        self.set_assign(state, goal.id, proof);
        let mut first = None;
        for (cctx, ctarget, tag) in children {
            let id = state.add_goal(cctx, ctarget, tag);
            let _ = id;
            if first.is_none() {
                first = Some(id);
            }
        }
        // The argument markers embedded in the proof use
        // __rigor_apply_{goal}_{i}; rename them to the canonical goal
        // markers in creation order.
        self.fix_apply_markers(state, goal.id);
        match first {
            Some(id) => state.focus = Some(id),
            None => state.refocus(),
        }
        Ok(())
    }

    fn fix_apply_markers(&self, state: &mut ProofState, parent: usize) {
        // Collect child goals of this parent in creation order: they are the
        // goals whose marker is still canonical and which were just added.
        // We instead rename by scanning the parent proof for __rigor_apply_
        // vars in left-to-right occurrence order and matching them to the
        // most recently added open goals in order.
        let parent_idx = match state.goals.iter().position(|g| g.id == parent) {
            Some(i) => i,
            None => return,
        };
        let proof = match &state.goals[parent_idx].assign {
            Some(p) => p.clone(),
            None => return,
        };
        let mut markers: Vec<String> = Vec::new();
        collect_apply_markers(&proof, &mut markers);
        // children added after the parent are at positions > parent_idx with
        // canonical markers, in the same order.
        let children: Vec<String> = state.goals[parent_idx + 1..]
            .iter()
            .filter(|g| g.tag.starts_with("apply "))
            .map(|g| g.marker.clone())
            .collect();
        let mut new_proof = proof;
        for (old, new) in markers.iter().zip(children.iter()) {
            new_proof = subst(&new_proof, old, &NExpr::var(new));
        }
        if let Some(g) = state.goals.iter_mut().find(|g| g.id == parent) {
            g.assign = Some(new_proof);
        }
    }

    // ---- induction / cases ----

    fn tactic_induction(&mut self, state: &mut ProofState, var: &str, gen_ih: bool) -> EResult<()> {
        let goal = self.focused_goal(state)?;
        let local = goal
            .ctx
            .iter()
            .find(|l| l.name == var)
            .cloned()
            .ok_or_else(|| format!("induction: no local named '{var}'"))?;
        let (head, targs) = spine(&local.ty);
        let (ind_name, ind_levels) = match &head {
            NExpr::Const(n, lv) => (n.clone(), lv.clone()),
            _ => return Err(format!("induction: '{var}' does not have an inductive type")),
        };
        let ind_id = self.kernel.names.lookup(&ind_name).ok_or_else(|| format!("induction: unknown inductive {ind_name}"))?;
        let ind_decl = self.kernel.env.get(ind_id).cloned().ok_or("induction: missing declaration")?;
        let info = ind_decl.inductive.clone().ok_or_else(|| format!("induction: {ind_name} is not inductive"))?;
        let block_members: Vec<String> = self
            .kernel
            .env
            .decls
            .iter()
            .filter(|d| d.inductive.as_ref().map(|i| i.block_id) == Some(info.block_id))
            .map(|d| self.kernel.names.display(d.name))
            .collect();
        if block_members.len() > 1 {
            return Err(format!(
                "induction on mutual inductive block {block_members:?} is not supported by the surface tactic; apply the core recursor {} directly",
                format!("{ind_name}.rec")
            ));
        }
        let num_params = info.num_params as usize;
        let num_indices = info.num_indices as usize;
        if targs.len() != num_params + num_indices {
            return Err("induction: malformed inductive type application".into());
        }
        let param_values: Vec<NExpr> = targs[..num_params].to_vec();
        let index_values: Vec<NExpr> = targs[num_params..].to_vec();

        // Recursor type, named. The declaration's own universe parameters
        // must be instantiated (inductive levels, then the elimination
        // universe) or the motive/minor types would mention free level
        // parameters that do not exist in the goal.
        let u_rec = self.sort_level_of(&goal.ctx, &goal.target)?;
        let rec_name = format!("{ind_name}.rec");
        let rec_id = self.kernel.names.lookup(&rec_name).ok_or_else(|| format!("induction: recursor {rec_name} not found"))?;
        let rec_decl = self.kernel.env.get(rec_id).cloned().ok_or("induction: missing recursor")?;
        let mut scope0: Vec<String> = goal.ctx.iter().map(|l| l.name.clone()).collect();
        let rec_ty_named = to_named(&self.kernel.arena, &self.kernel.names, rec_decl.ty, &mut scope0);
        let rec_inst: Vec<Level> = ind_levels.iter().cloned().chain(std::iter::once(u_rec.clone())).collect();
        let rec_ty = subst_level_params(&rec_ty_named, &rec_inst);
        let (rec_binders, _) = pi_chain(&rec_ty);
        let num_ctors = info.constructors.len();
        // layout: params, motive, minors..., indices..., target
        if rec_binders.len() < num_params + 1 + num_ctors + num_indices + 1 {
            return Err("induction: unexpected recursor telescope".into());
        }
        let param_binders: Vec<(String, NExpr)> = rec_binders[..num_params].to_vec();
        let motive_binder = rec_binders[num_params].0.clone();
        let minor_tys: Vec<NExpr> = rec_binders[num_params + 1..num_params + 1 + num_ctors].iter().map(|(_, d)| d.clone()).collect();

        // Motive: abstract the indices and the target variable in the goal.
        let ind_ty_named = {
            let mut s: Vec<String> = Vec::new();
            let raw = to_named(&self.kernel.arena, &self.kernel.names, ind_decl.ty, &mut s);
            subst_level_params(&raw, &ind_levels)
        };
        let (ind_binders, _) = pi_chain(&ind_ty_named);
        let mut avoid: HashSet<String> = fv(&goal.target);
        avoid.extend(goal.ctx.iter().map(|l| l.name.clone()));
        let idx_names: Vec<String> = (0..num_indices)
            .map(|j| fresh(&format!("__idx{j}"), &avoid))
            .collect();
        let tgt_name = fresh("__tgt", &avoid);
        let mut motive_body = goal.target.clone();
        for (j, iv) in index_values.iter().enumerate() {
            motive_body = replace_all(&motive_body, iv, &NExpr::var(&idx_names[j]));
        }
        motive_body = replace_all(&motive_body, &NExpr::var(var), &NExpr::var(&tgt_name));
        // Index types with parameters substituted.
        let mut motive = {
            let ind_app = apps(
                NExpr::Const(ind_name.clone(), ind_levels.clone()),
                &{
                    let mut v: Vec<NExpr> = param_values.clone();
                    v.extend(idx_names.iter().map(|n| NExpr::var(n)));
                    v
                },
            );
            let mut m = NExpr::lam(&tgt_name, ind_app, motive_body);
            for j in (0..num_indices).rev() {
                let mut ity = ind_binders[num_params + j].1.clone();
                for (k, (pname, _)) in ind_binders[..num_params].iter().enumerate() {
                    ity = subst(&ity, pname, &param_values[k]);
                }
                m = NExpr::lam(&idx_names[j], ity, m);
            }
            m
        };
        let _ = &mut motive;

        let mut rec_levels = ind_levels.clone();
        rec_levels.push(u_rec);
        let rec_const = NExpr::Const(rec_name.clone(), rec_levels);

        // Parent proof term.
        let mut rec_args: Vec<NExpr> = param_values.clone();
        rec_args.push(motive.clone());
        let mut child_specs: Vec<(Vec<CtxLocal>, NExpr, String, Vec<PrefixItem>)> = Vec::new();
        for (ci, ctor_id) in info.constructors.iter().enumerate() {
            let ctor_decl = self.kernel.env.get(*ctor_id).cloned().ok_or("induction: missing constructor")?;
            let ctor_name = self.kernel.names.display(*ctor_id);
            let short = ctor_name.rsplit('.').next().unwrap_or(&ctor_name).to_string();
            // Field names from the constructor's own telescope.
            let ctor_ty_named = {
                let mut s: Vec<String> = Vec::new();
                to_named(&self.kernel.arena, &self.kernel.names, ctor_decl.ty, &mut s)
            };
            let (ctor_binders, _) = pi_chain(&ctor_ty_named);
            let ctor_info = ctor_decl.ctor.clone().ok_or("induction: missing ctor info")?;
            let num_fields = ctor_info.num_fields as usize;
            let field_names: Vec<String> = ctor_binders[num_params..num_params + num_fields]
                .iter()
                .map(|(n, _)| n.clone())
                .collect();

            // Minor type with parameters and motive substituted.
            let mut minor = minor_tys[ci].clone();
            for (k, (pname, _)) in param_binders.iter().enumerate() {
                minor = subst(&minor, pname, &param_values[k]);
            }
            // Peel the minor telescope. Classification of induction
            // hypotheses must happen *before* motive substitution.
            let mut ctx2: Vec<CtxLocal> = goal.ctx.clone();
            let mut prefix: Vec<PrefixItem> = Vec::new();
            let mut minor_rest = minor.clone();
            let mut field_idx = 0usize;
            let mut ih_idx = 0usize;
            loop {
                match minor_rest.clone() {
                    NExpr::Pi(bname, _, dom, cod) => {
                        let is_ih = {
                            let mut d = (*dom).clone();
                            loop {
                                match d.clone() {
                                    NExpr::Pi(_, _, _, c) => d = (*c).clone(),
                                    NExpr::App(_, _) => {
                                        let (h, _) = spine(&d);
                                        break matches!(&h, NExpr::Var(n) if n == &motive_binder);
                                    }
                                    NExpr::Var(n) => break n == motive_binder,
                                    _ => break false,
                                }
                            }
                        };
                        // Substitute the motive for classification-clean types.
                        let dom_sub = beta_reduce(&subst(&dom, &motive_binder, &motive));
                        if is_ih {
                            let ih_name = if gen_ih {
                                let base = if field_idx > 0 {
                                    format!("ih_{}", field_names.get(field_idx - 1).cloned().unwrap_or_default())
                                } else {
                                    "ih".to_string()
                                };
                                let mut cand = base.clone();
                                let mut k = 0;
                                while ctx2.iter().any(|l| l.name == cand) {
                                    k += 1;
                                    cand = format!("{base}{k}");
                                }
                                cand
                            } else {
                                format!("__ih{ih_idx}")
                            };
                            ih_idx += 1;
                            prefix.push(PrefixItem::Lam(ih_name.clone(), dom_sub.clone()));
                            if gen_ih {
                                let local = self.make_local(&ctx2, &ih_name, dom_sub, None, false)?;
                                ctx2.push(local);
                            }
                            minor_rest = subst(&cod, &bname, &NExpr::var(&ih_name));
                        } else {
                            let fname = field_names.get(field_idx).cloned().unwrap_or_else(|| format!("f{field_idx}"));
                            field_idx += 1;
                            let mut fname2 = fname.clone();
                            let mut k = 0;
                            while ctx2.iter().any(|l| l.name == fname2) {
                                k += 1;
                                fname2 = format!("{fname}'{k}");
                            }
                            prefix.push(PrefixItem::Lam(fname2.clone(), dom_sub.clone()));
                            let local = self.make_local(&ctx2, &fname2, dom_sub, None, false)?;
                            ctx2.push(local);
                            minor_rest = subst(&cod, &bname, &NExpr::var(&fname2));
                        }
                    }
                    _ => break,
                }
            }
            let target2 = beta_reduce(&subst(&minor_rest, &motive_binder, &motive));
            child_specs.push((ctx2, target2, short, prefix));
        }

        // Register children first so markers exist, then set parent proof.
        let mut markers = Vec::new();
        let mut first_child = None;
        for (cctx, ctarget, tag, prefix) in child_specs {
            let id = state.add_goal(cctx, ctarget, tag.clone());
            let idx = state.goals.iter().position(|g| g.id == id).unwrap();
            state.goals[idx].prefix = prefix;
            markers.push(state.goals[idx].marker.clone());
            if first_child.is_none() {
                first_child = Some(id);
            }
        }
        for m in &markers {
            rec_args.push(NExpr::var(m));
        }
        rec_args.extend(index_values.iter().cloned());
        rec_args.push(NExpr::var(var));
        let proof = apps(rec_const, &rec_args);
        self.set_assign(state, goal.id, proof);
        state.focus = first_child;
        Ok(())
    }

    // ---- rewrite ----

    fn tactic_rewrite(&mut self, state: &mut ProofState, term: &STerm, reverse: bool) -> EResult<()> {
        let goal = self.focused_goal(state)?;
        let mut obs = Vec::new();
        let h = self.elaborate(&goal.ctx, term, &mut obs)?;
        self.push_obligations(state, obs);
        let hty = self.infer_nexpr(&goal.ctx, &h)?;
        let (head, args) = spine(&hty);
        let (alpha, mut a, mut b) = match (&head, args.len()) {
            (NExpr::Const(n, _), 3) if n == "Eq" => (args[0].clone(), args[1].clone(), args[2].clone()),
            _ => return Err(format!("rewrite: proof has type {}, not an equality", rigor_kernel::pretty_named(&hty))),
        };
        if reverse {
            std::mem::swap(&mut a, &mut b);
        }
        // child goal: target with a replaced by b
        let new_target = replace_all(&goal.target, &a, &b);
        if new_target == goal.target {
            return Err("rewrite: left-hand side does not occur in the goal".into());
        }
        // Transport: child proves M b; parent gets M a via Eq.rec on symm h.
        let eq_level = match &head {
            NExpr::Const(_, lv) => lv.first().cloned().unwrap_or(Level::Zero),
            _ => Level::Zero,
        };
        let u_rec = self.sort_level_of(&goal.ctx, &goal.target)?;
        let mut avoid: HashSet<String> = fv(&goal.target);
        avoid.extend(goal.ctx.iter().map(|l| l.name.clone()));
        let yv = fresh("__rw_y", &avoid);
        let hv = fresh("__rw_h", &avoid);
        let motive = NExpr::lam(
            &yv,
            alpha.clone(),
            NExpr::lam(
                &hv,
                apps(NExpr::Const("Eq".into(), vec![eq_level.clone()]), &[alpha.clone(), b.clone(), NExpr::var(&yv)]),
                replace_all(&goal.target, &a, &NExpr::var(&yv)),
            ),
        );
        let child_id = state.add_goal(goal.ctx.clone(), new_target, "rewrite".to_string());
        let marker = state.goals.iter().find(|g| g.id == child_id).unwrap().marker.clone();
        let symm_h = apps(
            NExpr::Const("Eq.symm".into(), vec![eq_level.clone()]),
            &[alpha.clone(), a.clone(), b.clone(), h],
        );
        let proof = apps(
            NExpr::Const("Eq.rec".into(), vec![eq_level, u_rec]),
            &[alpha, b, motive, NExpr::var(&marker), a, symm_h],
        );
        self.set_assign(state, goal.id, proof);
        state.focus = Some(child_id);
        Ok(())
    }

    // ---- calc ----

    fn tactic_calc(&mut self, state: &mut ProofState, steps: &[(Option<STerm>, STerm, STerm)]) -> EResult<()> {
        let goal = self.focused_goal(state)?;
        let (head, args) = spine(&goal.target);
        let (alpha, start_lhs, goal_rhs, eq_level) = match (&head, args.len()) {
            (NExpr::Const(n, lv), 3) if n == "Eq" => {
                (args[0].clone(), args[1].clone(), args[2].clone(), lv.first().cloned().unwrap_or(Level::Zero))
            }
            _ => return Err("calc: goal is not an equality".into()),
        };
        let chain_start = start_lhs.clone();
        let mut cur_lhs = start_lhs;
        let mut proof: Option<NExpr> = None;
        for (lhs, rhs, p) in steps {
            let lhs_e = match lhs {
                Some(l) => {
                    let mut obs = Vec::new();
                    let e = self.elaborate(&goal.ctx, l, &mut obs)?;
                    self.push_obligations(state, obs);
                    e
                }
                None => cur_lhs.clone(),
            };
            let mut obs = Vec::new();
            let rhs_e = self.elaborate(&goal.ctx, rhs, &mut obs)?;
            self.push_obligations(state, obs);
            let mut obs = Vec::new();
            let step_proof = self.elaborate(&goal.ctx, p, &mut obs)?;
            self.push_obligations(state, obs);
            let step_ty = apps(
                NExpr::Const("Eq".into(), vec![eq_level.clone()]),
                &[alpha.clone(), lhs_e.clone(), rhs_e.clone()],
            );
            self.check_nexpr(&goal.ctx, &step_proof, &step_ty)?;
            proof = Some(match proof {
                None => step_proof,
                Some(prev) => apps(
                    NExpr::Const("Eq.trans".into(), vec![eq_level.clone()]),
                    &[alpha.clone(), chain_start.clone(), lhs_e.clone(), rhs_e.clone(), prev, step_proof],
                ),
            });
            cur_lhs = rhs_e;
        }
        let proof = proof.ok_or("calc: no steps")?;
        // Final: cur_lhs must be the goal's rhs (checked next by kernel).
        let _ = goal_rhs;
        self.check_nexpr(&goal.ctx, &proof, &goal.target)?;
        self.set_assign(state, goal.id, proof);
        state.refocus();
        Ok(())
    }

    // ---- certificate solvers ----

    fn tactic_solve(&mut self, state: &mut ProofState, kind: &SolveKind) -> EResult<()> {
        let goal = self.focused_goal(state)?;
        match kind {
            SolveKind::Poly => {
                let (head, args) = spine(&goal.target);
                match (&head, args.len()) {
                    (NExpr::Const(n, _), 3) if n == "Eq" => {}
                    _ => return Err("solve poly: goal is not an equality".into()),
                }
                let tyname = self.head_type_name(&goal.ctx, &args[1]).unwrap_or_default();
                if tyname != "Nat" {
                    return Err(format!("solve poly: goal equality is over {tyname}, not Nat"));
                }
                let vars: Vec<String> = goal
                    .ctx
                    .iter()
                    .filter(|l| matches!(&l.ty, NExpr::Const(n, _) if n == "Nat"))
                    .map(|l| l.name.clone())
                    .collect();
                let lhs = nexpr_to_poly(&args[1], &vars)?;
                let rhs = nexpr_to_poly(&args[2], &vars)?;
                let proof = poly_identity_proof(&lhs, &rhs, &vars)?;
                self.check_nexpr(&goal.ctx, &proof, &goal.target)?;
                self.set_assign(state, goal.id, proof);
                state.refocus();
                Ok(())
            }
            SolveKind::Farkas(mults) => {
                let (head, args) = spine(&goal.target);
                match (&head, args.len()) {
                    (NExpr::Const(n, _), 2) if n == "Nat.le" => {}
                    _ => return Err("solve farkas: goal is not a Nat.le".into()),
                }
                let vars: Vec<String> = goal
                    .ctx
                    .iter()
                    .filter(|l| matches!(&l.ty, NExpr::Const(n, _) if n == "Nat"))
                    .map(|l| l.name.clone())
                    .collect();
                let goal_ineq = parse_nat_ineq(&args[0], &args[1], &vars)?;
                let mut hyps = Vec::new();
                for local in &goal.ctx {
                    let (h2, a2) = spine(&local.ty);
                    if let (NExpr::Const(n, _), 2) = (&h2, a2.len()) {
                        if n == "Nat.le" {
                            if let Ok(ineq) = parse_nat_ineq(&a2[0], &a2[1], &vars) {
                                hyps.push(NatIneq { proof_name: local.name.clone(), ..ineq });
                            }
                        }
                    }
                }
                if mults.len() != hyps.len() {
                    return Err(format!(
                        "solve farkas: {} multipliers given but {} Nat.le hypotheses in context",
                        mults.len(),
                        hyps.len()
                    ));
                }
                // The plugin proves the inequality in its canonical form
                // (0 + c1*x1 + ... shapes). The surface goal may state the
                // same linear forms in another association/order; transport
                // the canonical proof along polynomial identities on both
                // sides of Nat.le. All steps are kernel-checked core proofs.
                let proof = nat_farkas_proof(&hyps, &goal_ineq, mults, &vars)?;
                let le_form = form_poly(&goal_ineq.le_side, &goal_ineq.le_const);
                let ge_form = form_poly(&goal_ineq.ge_side, &goal_ineq.ge_const);
                let lc = rigor_certificates::poly::poly_to_nexpr(&le_form, &vars);
                let rc = rigor_certificates::poly::poly_to_nexpr(&ge_form, &vars);
                let canonical = apps(NExpr::const_("Nat.le"), &[lc.clone(), rc.clone()]);
                self.check_nexpr(&goal.ctx, &proof, &canonical)?;
                let surf_le = nexpr_to_poly(&args[0], &vars)?;
                let surf_ge = nexpr_to_poly(&args[1], &vars)?;
                let eq_l = poly_identity_proof(&le_form, &surf_le, &vars)?; // Eq lc ls
                let eq_r = poly_identity_proof(&ge_form, &surf_ge, &vars)?; // Eq rc rs
                let p1 = transport_le(proof, &lc, &rc, &args[0], eq_l, true);
                let p2 = transport_le(p1, &args[0], &rc, &args[1], eq_r, false);
                self.check_nexpr(&goal.ctx, &p2, &goal.target)?;
                self.set_assign(state, goal.id, p2);
                state.refocus();
                Ok(())
            }
            SolveKind::Sat => {
                // Goal: forall v0..vn : Bool, Eq Bool f false
                let mut binders: Vec<String> = Vec::new();
                let mut body = goal.target.clone();
                loop {
                    match body.clone() {
                        NExpr::Pi(n, _, dom, cod) => {
                            if !matches!(&*dom, NExpr::Const(dn, _) if dn == "Bool") {
                                return Err("solve sat: binder is not Bool".into());
                            }
                            binders.push(n);
                            body = (*cod).clone();
                        }
                        _ => break,
                    }
                }
                let (head, args) = spine(&body);
                match (&head, args.len()) {
                    (NExpr::Const(n, _), 3) if n == "Eq" => {}
                    _ => return Err("solve sat: goal body is not an Eq".into()),
                }
                if !matches!(&args[2], NExpr::Const(n, _) if n == "Bool.false") {
                    return Err("solve sat: goal must state the formula equals Bool.false".into());
                }
                // When the Bool variables live in the local context rather
                // than under Pi binders in the goal, the plugin's
                // universally quantified proof is applied to them.
                let from_ctx = binders.is_empty();
                if from_ctx {
                    binders = goal
                        .ctx
                        .iter()
                        .filter(|l| matches!(&l.ty, NExpr::Const(n, _) if n == "Bool"))
                        .map(|l| l.name.clone())
                        .collect();
                }
                let f = formula_of(&args[1], &binders)?;
                let n = binders.len();
                let mut proof = unsat_case_proof(&f, n)?;
                if from_ctx {
                    let app_args: Vec<NExpr> = binders.iter().map(|b| NExpr::var(b)).collect();
                    proof = apps(proof, &app_args);
                }
                // The plugin builds the proof for variables named v0..vn-1;
                // rename to the goal's binder names (via fresh temps).
                let temps: Vec<String> = (0..n).map(|i| format!("__sat_tmp_{i}")).collect();
                for i in 0..n {
                    proof = subst(&proof, &format!("v{i}"), &NExpr::var(&temps[i]));
                }
                for i in 0..n {
                    proof = subst(&proof, &temps[i], &NExpr::var(&binders[i]));
                }
                self.check_nexpr(&goal.ctx, &proof, &goal.target)?;
                self.set_assign(state, goal.id, proof);
                state.refocus();
                Ok(())
            }
        }
    }
}

fn collect_apply_markers(e: &NExpr, out: &mut Vec<String>) {
    match e {
        NExpr::Var(s) => {
            if s.starts_with("__rigor_apply_") && !out.contains(s) {
                out.push(s.clone());
            }
        }
        NExpr::App(f, a) => {
            collect_apply_markers(f, out);
            collect_apply_markers(a, out);
        }
        NExpr::Pi(_, _, d, c) | NExpr::Lam(_, _, d, c) => {
            collect_apply_markers(d, out);
            collect_apply_markers(c, out);
        }
        NExpr::Let(_, t, v, b) => {
            collect_apply_markers(t, out);
            collect_apply_markers(v, out);
            collect_apply_markers(b, out);
        }
        NExpr::Proj(_, _, t) => collect_apply_markers(t, out),
        _ => {}
    }
}

fn apply_subst_multi(e: &NExpr, subst_map: &HashMap<String, NExpr>) -> NExpr {
    let mut out = e.clone();
    for _ in 0..16 {
        let mut changed = false;
        for (k, v) in subst_map {
            let n = subst(&out, k, v);
            if n != out {
                changed = true;
            }
            out = n;
        }
        if !changed {
            break;
        }
    }
    out
}

/// First-order unification of a lemma conclusion against the goal.
/// Metavariables are the Pi binder names of the lemma type.
pub fn unify(pat: &NExpr, tgt: &NExpr, mvars: &HashSet<String>, subst_map: &mut HashMap<String, NExpr>) -> bool {
    if pat == tgt {
        return true;
    }
    match pat {
        NExpr::Var(m) if mvars.contains(m) => {
            if let Some(existing) = subst_map.get(m) {
                return existing == tgt;
            }
            subst_map.insert(m.clone(), tgt.clone());
            true
        }
        NExpr::App(_, _) => {
            let (ph, pargs) = spine(pat);
            if let NExpr::Var(m) = &ph {
                if mvars.contains(m) && !subst_map.contains_key(m) {
                    // Pattern unification only for distinct variable args.
                    let mut names = Vec::new();
                    let mut ok = true;
                    for a in &pargs {
                        match a {
                            NExpr::Var(v) if !mvars.contains(v) => names.push(v.clone()),
                            _ => {
                                ok = false;
                                break;
                            }
                        }
                    }
                    if ok {
                        let mut body = tgt.clone();
                        for n in names.iter().rev() {
                            body = NExpr::lam(n, NExpr::sort(Level::Zero), body);
                        }
                        subst_map.insert(m.clone(), body);
                        return true;
                    }
                }
            }
            let (th, targs) = spine(tgt);
            if pargs.len() != targs.len() {
                return false;
            }
            if !unify(&ph, &th, mvars, subst_map) {
                return false;
            }
            for (p, t) in pargs.iter().zip(targs.iter()) {
                if !unify(p, t, mvars, subst_map) {
                    return false;
                }
            }
            true
        }
        NExpr::Pi(n, _, d, c) => match tgt {
            NExpr::Pi(n2, _, d2, c2) => {
                if !unify(d, d2, mvars, subst_map) {
                    return false;
                }
                let c2r = subst(c2, n2, &NExpr::var(n));
                unify(c, &c2r, mvars, subst_map)
            }
            _ => false,
        },
        NExpr::Lam(n, _, d, c) => match tgt {
            NExpr::Lam(n2, _, d2, c2) => {
                if !unify(d, d2, mvars, subst_map) {
                    return false;
                }
                let c2r = subst(c2, n2, &NExpr::var(n));
                unify(c, &c2r, mvars, subst_map)
            }
            _ => false,
        },
        NExpr::Const(n1, l1) => match tgt {
            NExpr::Const(n2, l2) => n1 == n2 && l1 == l2,
            _ => false,
        },
        NExpr::LitNat(a) => matches!(tgt, NExpr::LitNat(b) if a == b),
        NExpr::Sort(a) => matches!(tgt, NExpr::Sort(b) if a == b),
        _ => false,
    }
}

/// The plugin's canonical linear form as a PolyExpr: konst + sum of terms in
/// coefficient order (mirrors rigor-certificates' form_to_poly).
fn form_poly(coeffs: &[(usize, BigUint)], konst: &BigUint) -> PolyExpr {
    let mut result = PolyExpr::Const(konst.clone());
    for (var, coeff) in coeffs {
        let term = if coeff.is_one() {
            PolyExpr::Var(*var)
        } else {
            PolyExpr::Mul(Box::new(PolyExpr::Const(coeff.clone())), Box::new(PolyExpr::Var(*var)))
        };
        result = PolyExpr::Add(Box::new(result), Box::new(term));
    }
    result
}

/// Transport `p : Nat.le a b` along `e : Eq Nat from to`, where {from,to} is
/// the left side if `vary_left`, the right side otherwise (Eq.rec transport).
fn transport_le(p: NExpr, left_fixed: &NExpr, right_fixed: &NExpr, to: &NExpr, e: NExpr, vary_left: bool) -> NExpr {
    let from = if vary_left { left_fixed.clone() } else { right_fixed.clone() };
    let motive_body = if vary_left {
        apps(NExpr::const_("Nat.le"), &[NExpr::var("__tle_m"), right_fixed.clone()])
    } else {
        apps(NExpr::const_("Nat.le"), &[left_fixed.clone(), NExpr::var("__tle_m")])
    };
    let motive = NExpr::lam(
        "__tle_m",
        NExpr::const_("Nat"),
        NExpr::lam(
            "__tle_h",
            apps(
                NExpr::Const("Eq".into(), vec![Level::Succ(Box::new(Level::Zero))]),
                &[NExpr::const_("Nat"), from.clone(), NExpr::var("__tle_m")],
            ),
            motive_body,
        ),
    );
    apps(
        NExpr::const_levels("Eq.rec", vec![Level::Succ(Box::new(Level::Zero)), Level::Zero]),
        &[NExpr::const_("Nat"), from, motive, p, to.clone(), e],
    )
}

// ---------------------------------------------------------------------------
// Solver input parsing
// ---------------------------------------------------------------------------

pub fn nexpr_to_poly(e: &NExpr, vars: &[String]) -> EResult<PolyExpr> {
    match e {
        NExpr::LitNat(n) => Ok(PolyExpr::Const(n.clone())),
        NExpr::Var(name) => {
            let idx = vars.iter().position(|v| v == name).ok_or_else(|| format!("solve poly: '{name}' is not a Nat variable in scope"))?;
            Ok(PolyExpr::Var(idx))
        }
        NExpr::App(_, _) => {
            let (head, args) = spine(e);
            match (&head, args.len()) {
                (NExpr::Const(n, _), 2) if n == "Nat.add" => Ok(PolyExpr::add(nexpr_to_poly(&args[0], vars)?, nexpr_to_poly(&args[1], vars)?)),
                (NExpr::Const(n, _), 2) if n == "Nat.mul" => Ok(PolyExpr::mul(nexpr_to_poly(&args[0], vars)?, nexpr_to_poly(&args[1], vars)?)),
                (NExpr::Const(n, _), 2) if n == "Nat.pow" => match &args[1] {
                    NExpr::LitNat(k) => {
                        let k = k.to_u64().ok_or("solve poly: exponent too large")? as u32;
                        Ok(PolyExpr::Pow(Box::new(nexpr_to_poly(&args[0], vars)?), k))
                    }
                    _ => Err("solve poly: exponent must be a literal".into()),
                },
                (NExpr::Const(n, _), 1) if n == "Nat.succ" => Ok(PolyExpr::add(nexpr_to_poly(&args[0], vars)?, PolyExpr::konst(1))),
                _ => Err(format!("solve poly: unsupported term {}", rigor_kernel::pretty_named(e))),
            }
        }
        NExpr::Const(n, _) if n == "Nat.zero" => Ok(PolyExpr::konst(0)),
        _ => Err(format!("solve poly: unsupported term {}", rigor_kernel::pretty_named(e))),
    }
}

fn parse_linear(e: &NExpr, vars: &[String], coeffs: &mut HashMap<usize, BigUint>, konst: &mut BigUint) -> EResult<()> {
    match e {
        NExpr::LitNat(n) => {
            *konst = konst.add(n);
            Ok(())
        }
        NExpr::Const(n, _) if n == "Nat.zero" => Ok(()),
        NExpr::Var(name) => {
            let idx = vars.iter().position(|v| v == name).ok_or_else(|| format!("farkas: '{name}' is not a Nat variable in scope"))?;
            let entry = coeffs.entry(idx).or_insert_with(BigUint::zero);
            *entry = entry.add(&BigUint::one());
            Ok(())
        }
        NExpr::App(_, _) => {
            let (head, args) = spine(e);
            match (&head, args.len()) {
                (NExpr::Const(n, _), 2) if n == "Nat.add" => {
                    parse_linear(&args[0], vars, coeffs, konst)?;
                    parse_linear(&args[1], vars, coeffs, konst)
                }
                (NExpr::Const(n, _), 1) if n == "Nat.succ" => {
                    let mut dummy = HashMap::new();
                    let mut sub_const = BigUint::zero();
                    parse_linear(&args[0], vars, &mut dummy, &mut sub_const)?;
                    for (k, v) in dummy {
                        let entry = coeffs.entry(k).or_insert_with(BigUint::zero);
                        *entry = entry.add(&v);
                    }
                    *konst = konst.add(&sub_const).add(&BigUint::one());
                    Ok(())
                }
                (NExpr::Const(n, _), 2) if n == "Nat.mul" => {
                    let (c, v) = match (&args[0], &args[1]) {
                        (NExpr::LitNat(c), NExpr::Var(v)) => (c.clone(), v.clone()),
                        (NExpr::Var(v), NExpr::LitNat(c)) => (c.clone(), v.clone()),
                        _ => return Err("farkas: multiplication is not linear".into()),
                    };
                    let idx = vars.iter().position(|x| x == &v).ok_or_else(|| format!("farkas: '{v}' is not a Nat variable in scope"))?;
                    let entry = coeffs.entry(idx).or_insert_with(BigUint::zero);
                    *entry = entry.add(&c);
                    Ok(())
                }
                _ => Err(format!("farkas: unsupported term {}", rigor_kernel::pretty_named(e))),
            }
        }
        _ => Err(format!("farkas: unsupported term {}", rigor_kernel::pretty_named(e))),
    }
}

pub fn parse_nat_ineq(le_expr: &NExpr, ge_expr: &NExpr, vars: &[String]) -> EResult<NatIneq> {
    let mut le_coeffs = HashMap::new();
    let mut le_const = BigUint::zero();
    parse_linear(le_expr, vars, &mut le_coeffs, &mut le_const)?;
    let mut ge_coeffs = HashMap::new();
    let mut ge_const = BigUint::zero();
    parse_linear(ge_expr, vars, &mut ge_coeffs, &mut ge_const)?;
    let mut le_side: Vec<(usize, BigUint)> = le_coeffs.into_iter().filter(|(_, c)| !c.is_zero()).collect();
    le_side.sort_by_key(|(i, _)| *i);
    let mut ge_side: Vec<(usize, BigUint)> = ge_coeffs.into_iter().filter(|(_, c)| !c.is_zero()).collect();
    ge_side.sort_by_key(|(i, _)| *i);
    Ok(NatIneq { le_side, le_const, ge_side, ge_const, proof_name: String::new() })
}

pub fn formula_of(e: &NExpr, binders: &[String]) -> EResult<Formula> {
    match e {
        NExpr::Var(name) => {
            let idx = binders.iter().position(|b| b == name).ok_or_else(|| format!("solve sat: '{name}' is not a Bool variable"))?;
            Ok(Formula::Var(idx))
        }
        NExpr::Const(n, _) if n == "Bool.true" => Ok(Formula::Lit(true)),
        NExpr::Const(n, _) if n == "Bool.false" => Ok(Formula::Lit(false)),
        NExpr::App(_, _) => {
            let (head, args) = spine(e);
            match (&head, args.len()) {
                (NExpr::Const(n, _), 4) if n == "Bool.rec" => {
                    let (m_true, m_false, target) = (&args[1], &args[2], &args[3]);
                    let is_false = matches!(m_false, NExpr::Const(n, _) if n == "Bool.false");
                    let is_true = matches!(m_true, NExpr::Const(n, _) if n == "Bool.true");
                    if is_true && is_false {
                        return Err("solve sat: ambiguous Bool.rec".into());
                    }
                    if matches!(m_true, NExpr::Const(n, _) if n == "Bool.false") && matches!(m_false, NExpr::Const(n, _) if n == "Bool.true") {
                        return Ok(Formula::Not(Box::new(formula_of(target, binders)?)));
                    }
                    if is_false {
                        return Ok(Formula::And(Box::new(formula_of(target, binders)?), Box::new(formula_of(m_true, binders)?)));
                    }
                    if is_true {
                        return Ok(Formula::Or(Box::new(formula_of(target, binders)?), Box::new(formula_of(m_false, binders)?)));
                    }
                    Err("solve sat: unsupported Bool.rec shape".into())
                }
                _ => Err(format!("solve sat: unsupported term {}", rigor_kernel::pretty_named(e))),
            }
        }
        _ => Err(format!("solve sat: unsupported term {}", rigor_kernel::pretty_named(e))),
    }
}
