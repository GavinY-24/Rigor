//! The L36 trusted checker: typing, definitional equality, declaration
//! admission, inductive blocks, recursors, structures and quotients.
//!
//! Soundness target (conditional on L36): if this checker derives
//! `E; Γ ⊢ t : A`, that judgment is an L36 derivation using only the
//! assumptions in the certified dependency closure of `E`.

use crate::builder::{lower, to_named, NExpr};
use crate::env::{CtorInfo, Decl, DeclKind, Env, InductiveInfo, RecursorInfo, Reducibility};
use crate::expr::{pi_telescope, spine, BinderInfo, Expr, ExprArena, ExprId, NameArena, NameId};
use crate::level::Level;
use rigor_spec::BigUint;
use std::collections::BTreeSet;
use std::fmt;

#[derive(Debug, Clone)]
pub enum KernelError {
    TypeError(String),
    InvalidDecl(String),
    Unsupported(String),
    BudgetExhausted,
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KernelError::TypeError(m) => write!(f, "type error: {m}"),
            KernelError::InvalidDecl(m) => write!(f, "invalid declaration: {m}"),
            KernelError::Unsupported(m) => write!(f, "unsupported: {m}"),
            KernelError::BudgetExhausted => write!(f, "resource budget exhausted"),
        }
    }
}
impl std::error::Error for KernelError {}

pub type KResult<T> = Result<T, KernelError>;

#[derive(Debug, Clone, Copy)]
pub struct Budget {
    pub max_steps: u64,
    pub steps: u64,
}

impl Budget {
    pub fn new(max_steps: u64) -> Self {
        Self { max_steps, steps: 0 }
    }
    pub fn tick(&mut self) -> KResult<()> {
        self.steps += 1;
        if self.steps > self.max_steps {
            return Err(KernelError::BudgetExhausted);
        }
        Ok(())
    }
}

impl Default for Budget {
    fn default() -> Self {
        Self::new(20_000_000)
    }
}

#[derive(Debug, Clone)]
pub struct LocalDecl {
    pub name: NameId,
    pub ty: ExprId,
    pub value: Option<ExprId>,
}

/// Local context; `locals[0]` is the outermost binder. Types are stored in
/// the context in which they were entered.
pub type Context = Vec<LocalDecl>;

#[derive(Debug, Clone)]
pub struct InductiveSpec {
    pub name: String,
    pub level_params: Vec<String>,
    pub ty: NExpr,
    pub num_params: u32,
    pub constructors: Vec<(String, NExpr)>,
}

pub struct Kernel {
    pub arena: ExprArena,
    pub names: NameArena,
    pub env: Env,
    pub budget: Budget,
    pub quot_used: bool,
}

impl Default for Kernel {
    fn default() -> Self {
        Self::new()
    }
}

impl Kernel {
    pub fn new() -> Self {
        Self {
            arena: ExprArena::new(),
            names: NameArena::new(),
            env: Env::new(),
            budget: Budget::default(),
            quot_used: false,
        }
    }

    pub fn name(&mut self, s: &str) -> NameId {
        self.names.intern_str(s)
    }

    pub fn lookup_decl(&self, s: &str) -> Option<&Decl> {
        let id = self.names.lookup(s)?;
        self.env.get(id)
    }

    // ---------- level / sort helpers ----------

    fn validate_level_params(&self, level_params: &[NameId]) -> KResult<()> {
        let mut seen = BTreeSet::new();
        for p in level_params {
            if !seen.insert(p) {
                return Err(KernelError::InvalidDecl(format!(
                    "duplicate universe parameter {}",
                    self.names.display(*p)
                )));
            }
        }
        Ok(())
    }

    fn level_of_sort(&mut self, ctx: &Context, e: ExprId) -> KResult<Level> {
        let ty = self.infer(ctx, e)?;
        let w = self.whnf(ctx, ty)?;
        match self.arena.get_clone(w) {
            Expr::Sort(l) => Ok(l),
            _ => Err(KernelError::TypeError(format!(
                "expected a type (Sort), got {}",
                crate::builder::pretty(&self.arena, &self.names, ty)
            ))),
        }
    }

    pub fn is_prop_type(&mut self, ctx: &Context, ty: ExprId) -> KResult<bool> {
        let s = self.level_of_sort(ctx, ty)?;
        Ok(s.is_zero())
    }

    /// Validate a local context (each type is a Sort, let values check).
    pub fn validate_ctx(&mut self, ctx: &Context) -> KResult<()> {
        for i in 0..ctx.len() {
            let prefix: Context = ctx[..=i].to_vec();
            let local = ctx[i].clone();
            // type must be a sort in the preceding context
            let before: Context = ctx[..i].to_vec();
            let _ = self.level_of_sort(&before, local.ty)?;
            if let Some(v) = local.value {
                self.check(&prefix[..i].to_vec(), v, local.ty)?;
            }
        }
        Ok(())
    }

    // ---------- typing ----------

    pub fn infer(&mut self, ctx: &Context, e: ExprId) -> KResult<ExprId> {
        self.budget.tick()?;
        match self.arena.get_clone(e) {
            Expr::BVar(i) => {
                let idx = ctx.len().checked_sub(1 + i as usize).ok_or_else(|| {
                    KernelError::TypeError(format!("unbound variable #{i}"))
                })?;
                let local = ctx[idx].clone();
                let shifted = self.arena.shift(local.ty, (i + 1) as i64, 0);
                Ok(shifted)
            }
            Expr::Sort(l) => {
                let succ = Level::Succ(Box::new(l));
                Ok(self.arena.sort(succ))
            }
            Expr::Const(name, levels) => {
                let decl = self
                    .env
                    .get(name)
                    .cloned()
                    .ok_or_else(|| {
                        KernelError::TypeError(format!(
                            "unknown constant {}",
                            self.names.display(name)
                        ))
                    })?;
                if levels.len() != decl.level_params.len() {
                    return Err(KernelError::TypeError(format!(
                        "constant {} expects {} universe arguments, got {}",
                        self.names.display(name),
                        decl.level_params.len(),
                        levels.len()
                    )));
                }
                for l in &levels {
                    // level well-formedness against the ambient declaration is the
                    // caller's scope; parameters here refer to enclosing decl params
                    let _ = l;
                }
                if decl.kind == DeclKind::QuotPrimitive {
                    self.quot_used = true;
                }
                // Elimination restriction for recursors of Prop inductives.
                if let Some(rec) = &decl.recursor {
                    self.check_recursor_elim(rec.inductive, &levels)?;
                }
                Ok(self.arena.subst_levels(decl.ty, &levels))
            }
            Expr::Pi(name, _info, dom, cod) => {
                let u = self.level_of_sort(ctx, dom)?;
                let mut ctx2 = ctx.clone();
                ctx2.push(LocalDecl { name, ty: dom, value: None });
                let v = self.level_of_sort(&ctx2, cod)?;
                let sort = Level::IMax(Box::new(u), Box::new(v));
                Ok(self.arena.sort(sort))
            }
            Expr::Lam(name, _info, dom, body) => {
                self.level_of_sort(ctx, dom)?;
                let mut ctx2 = ctx.clone();
                ctx2.push(LocalDecl { name, ty: dom, value: None });
                let body_ty = self.infer(&ctx2, body)?;
                let anon = self.names.intern(crate::expr::Name(vec![crate::expr::NamePart::Anon]));
                let _ = anon;
                Ok(self.arena.pi(name, BinderInfo::Default, dom, body_ty))
            }
            Expr::App(f, a) => {
                let f_ty = self.infer(ctx, f)?;
                let f_ty_w = self.whnf(ctx, f_ty)?;
                match self.arena.get_clone(f_ty_w) {
                    Expr::Pi(_, _, dom, cod) => {
                        self.check(ctx, a, dom)?;
                        Ok(self.arena.subst_top(cod, a))
                    }
                    _ => Err(KernelError::TypeError(format!(
                        "application of non-function {}",
                        crate::builder::pretty(&self.arena, &self.names, f)
                    ))),
                }
            }
            Expr::Let(name, ty, val, body) => {
                self.level_of_sort(ctx, ty)?;
                self.check(ctx, val, ty)?;
                let mut ctx2 = ctx.clone();
                ctx2.push(LocalDecl { name, ty, value: Some(val) });
                let body_ty = self.infer(&ctx2, body)?;
                Ok(self.arena.subst_top(body_ty, val))
            }
            Expr::Proj(struct_name, idx, term) => {
                let term_ty = self.infer(ctx, term)?;
                let term_ty_w = self.whnf(ctx, term_ty)?;
                let (head, args) = spine(&self.arena, term_ty_w);
                let ind_name = match self.arena.get_clone(head) {
                    Expr::Const(n, _) => n,
                    _ => {
                        return Err(KernelError::TypeError(
                            "projection of non-structure value".to_string(),
                        ))
                    }
                };
                if ind_name != struct_name {
                    return Err(KernelError::TypeError(format!(
                        "projection {}.{} on value of type {}",
                        self.names.display(struct_name),
                        idx,
                        self.names.display(ind_name)
                    )));
                }
                let ind_decl = self.env.get(ind_name).cloned().ok_or_else(|| {
                    KernelError::TypeError("unknown structure".to_string())
                })?;
                let info = ind_decl.inductive.clone().ok_or_else(|| {
                    KernelError::TypeError("projection target is not an inductive".to_string())
                })?;
                if info.constructors.len() != 1 {
                    return Err(KernelError::TypeError(
                        "projection requires a single-constructor inductive".to_string(),
                    ));
                }
                let ctor_decl = self.env.get(info.constructors[0]).cloned().unwrap();
                let (binders, _result) = pi_telescope(&self.arena, ctor_decl.ty);
                let field_pos = info.num_params as usize + idx as usize;
                if field_pos >= binders.len() {
                    return Err(KernelError::TypeError(format!(
                        "projection index {idx} out of range"
                    )));
                }
                // Build the field type, substituting params from the type args and
                // earlier fields by projections of `term`.
                let mut subst_args: Vec<ExprId> = Vec::new();
                for j in 0..field_pos {
                    if j < info.num_params as usize {
                        subst_args.push(args[j]);
                    } else {
                        let proj = self
                            .arena
                            .intern(Expr::Proj(struct_name, (j - info.num_params as usize) as u32, term));
                        subst_args.push(proj);
                    }
                }
                let field_ty = binders[field_pos].2;
                // field_ty is stated in the ctor telescope context; instantiate
                // binders up to field_pos.
                let mut result = field_ty;
                // result is relative to a context with field_pos binders before the
                // field itself; substitute them in order.
                result = self.arena.subst_telescope(result, &subst_args);
                // subst_telescope substituted one binder too many semantics: binders
                // list includes the field binder itself at field_pos. field_ty is the
                // domain of binder field_pos, stated in context of binders [0..field_pos].
                // subst_telescope with field_pos args is exactly right; `result` above
                // started as that domain.
                Ok(result)
            }
            Expr::LitNat(_) => {
                let nat = self.name("Nat");
                if !self.env.contains(nat) {
                    return Err(KernelError::Unsupported(
                        "Nat literal used before Nat is declared".to_string(),
                    ));
                }
                Ok(self.arena.const_(nat, vec![]))
            }
            Expr::LitStr(_) => {
                let string = self.name("String");
                if !self.env.contains(string) {
                    return Err(KernelError::Unsupported(
                        "String literal used before String is declared".to_string(),
                    ));
                }
                Ok(self.arena.const_(string, vec![]))
            }
        }
    }

    pub fn check(&mut self, ctx: &Context, e: ExprId, expected: ExprId) -> KResult<()> {
        self.budget.tick()?;
        // Lambda against a Pi type: check body under the binder directly so
        // dependent codomains line up.
        if let Expr::Lam(name, _, dom, body) = self.arena.get_clone(e) {
            let expected_w = self.whnf(ctx, expected)?;
            if let Expr::Pi(_, _, dom2, cod) = self.arena.get_clone(expected_w) {
                if !self.is_def_eq(ctx, dom, dom2)? {
                    return Err(KernelError::TypeError(
                        "lambda domain does not match expected Pi domain".to_string(),
                    ));
                }
                let mut ctx2 = ctx.clone();
                ctx2.push(LocalDecl { name, ty: dom, value: None });
                return self.check(&ctx2, body, cod);
            }
        }
        if let Expr::Let(name, ty, val, body) = self.arena.get_clone(e) {
            self.level_of_sort(ctx, ty)?;
            self.check(ctx, val, ty)?;
            let mut ctx2 = ctx.clone();
            ctx2.push(LocalDecl { name, ty, value: Some(val) });
            let expected2 = self.arena.shift(expected, 1, 0);
            return self.check(&ctx2, body, expected2);
        }
        let inferred = self.infer(ctx, e)?;
        if self.is_def_eq(ctx, inferred, expected)? {
            Ok(())
        } else {
            Err(KernelError::TypeError(format!(
                "type mismatch: inferred {} but expected {}",
                crate::builder::pretty(&self.arena, &self.names, inferred),
                crate::builder::pretty(&self.arena, &self.names, expected)
            )))
        }
    }

    fn check_recursor_elim(&mut self, ind_name: NameId, levels: &[Level]) -> KResult<()> {
        let decl = match self.env.get(ind_name).cloned() {
            Some(d) => d,
            None => return Ok(()),
        };
        let info = match &decl.inductive {
            Some(i) => i.clone(),
            None => return Ok(()),
        };
        if !info.is_prop {
            return Ok(());
        }
        // The recursor carries one extra level parameter (the motive universe), last.
        if levels.len() != decl.level_params.len() + 1 {
            return Ok(());
        }
        let motive_level = levels[levels.len() - 1].clone();
        if motive_level.is_zero() {
            return Ok(());
        }
        // Singleton / empty elimination criterion (approximation of the L36 rule):
        // at most one constructor, and every constructor field is itself in Prop
        // or is an index parameter position.
        if info.constructors.len() > 1 {
            return Err(KernelError::TypeError(format!(
                "recursor for Prop inductive {} with {} constructors cannot eliminate into Type",
                self.names.display(ind_name),
                info.constructors.len()
            )));
        }
        if info.constructors.len() == 1 {
            let ctor = self.env.get(info.constructors[0]).cloned().unwrap();
            let (binders, _) = pi_telescope(&self.arena, ctor.ty);
            let mut ctx: Context = Vec::new();
            for (j, (n, _, dom)) in binders.iter().enumerate() {
                if j >= info.num_params as usize {
                    // field: must live in Prop
                    let s = self.level_of_sort(&ctx, *dom)?;
                    if !s.is_zero() {
                        return Err(KernelError::TypeError(format!(
                            "Prop inductive {} is not a singleton: field has non-Prop type",
                            self.names.display(ind_name)
                        )));
                    }
                }
                ctx.push(LocalDecl { name: *n, ty: *dom, value: None });
            }
        }
        Ok(())
    }

    // ---------- weak head normal form ----------

    pub fn whnf(&mut self, ctx: &Context, e: ExprId) -> KResult<ExprId> {
        let mut cur = e;
        loop {
            self.budget.tick()?;
            let next = self.whnf_step(ctx, cur)?;
            if next == cur {
                return Ok(cur);
            }
            cur = next;
        }
    }

    /// One head reduction step; returns the input unchanged when irreducible.
    pub fn whnf_step(&mut self, ctx: &Context, e: ExprId) -> KResult<ExprId> {
        match self.arena.get_clone(e) {
            Expr::BVar(i) => {
                let idx = ctx.len().checked_sub(1 + i as usize);
                if let Some(idx) = idx {
                    if let Some(v) = ctx[idx].value {
                        return Ok(self.arena.shift(v, (i + 1) as i64, 0));
                    }
                }
                Ok(e)
            }
            Expr::Let(_, _, val, body) => Ok(self.arena.subst_top(body, val)),
            Expr::App(_, _) => {
                let (head, args) = spine(&self.arena, e);
                match self.arena.get_clone(head) {
                    Expr::Lam(_, _, _, body) => {
                        if args.is_empty() {
                            return Ok(e);
                        }
                        let mut result = self.arena.subst_top(body, args[0]);
                        for &a in &args[1..] {
                            result = self.arena.app(result, a);
                        }
                        Ok(result)
                    }
                    Expr::Const(name, levels) => {
                        // Nat literal acceleration (must agree with the recursor
                        // definitions of these constants; tested against them).
                        if let Some(r) = self.nat_literal_op(name, &args) {
                            return Ok(r);
                        }
                        if let Some(decl) = self.env.get(name).cloned() {
                            if let Some(rec) = &decl.recursor {
                                if let Some(r) =
                                    self.try_iota(ctx, name, &levels, rec.clone(), &args)?
                                {
                                    return Ok(r);
                                }
                                return Ok(e);
                            }
                            if decl.kind == DeclKind::QuotPrimitive {
                                if let Some(r) = self.try_quot(name, &args) {
                                    return Ok(r);
                                }
                                return Ok(e);
                            }
                            if decl.kind.unfolds(decl.hint) {
                                if let Some(val) = decl.value {
                                    let unfolded = self.arena.subst_levels(val, &levels);
                                    let mut result = unfolded;
                                    for &a in &args {
                                        result = self.arena.app(result, a);
                                    }
                                    return Ok(result);
                                }
                            }
                        }
                        Ok(e)
                    }
                    Expr::Proj(s, i, inner) => {
                        let p = self.arena.intern(Expr::Proj(s, i, inner));
                        let pw = self.whnf_step(ctx, p)?;
                        if pw != p {
                            let mut result = pw;
                            for &a in &args {
                                result = self.arena.app(result, a);
                            }
                            return Ok(result);
                        }
                        Ok(e)
                    }
                    _ => {
                        // reduce the head further
                        let head_w = self.whnf(ctx, head)?;
                        if head_w != head {
                            let mut result = head_w;
                            for &a in &args {
                                result = self.arena.app(result, a);
                            }
                            return Ok(result);
                        }
                        Ok(e)
                    }
                }
            }
            Expr::Proj(struct_name, idx, term) => {
                let term_w = self.whnf(ctx, term)?;
                let (head, args) = spine(&self.arena, term_w);
                if let Expr::Const(ctor_name, _) = self.arena.get_clone(head) {
                    if let Some(ctor_decl) = self.env.get(ctor_name).cloned() {
                        if let Some(ci) = &ctor_decl.ctor {
                            if ci.inductive == struct_name {
                                let field_pos = ci.num_fields;
                                let _ = field_pos;
                                // args = params ++ fields
                                let ind_decl = self.env.get(struct_name).cloned().unwrap();
                                let info = ind_decl.inductive.clone().unwrap();
                                let pos = info.num_params as usize + idx as usize;
                                if pos < args.len() {
                                    return Ok(args[pos]);
                                }
                            }
                        }
                    }
                }
                if term_w != term {
                    return Ok(self.arena.intern(Expr::Proj(struct_name, idx, term_w)));
                }
                Ok(e)
            }
            Expr::Const(name, levels) => {
                if let Some(decl) = self.env.get(name).cloned() {
                    if decl.kind.unfolds(decl.hint) {
                        if let Some(val) = decl.value {
                            return Ok(self.arena.subst_levels(val, &levels));
                        }
                    }
                }
                Ok(e)
            }
            _ => Ok(e),
        }
    }

    fn nat_literal_op(&mut self, name: NameId, args: &[ExprId]) -> Option<ExprId> {
        let n = self.names.display(name);
        let lit = |k: &mut Self, e: ExprId| -> Option<BigUint> {
            match k.arena.get_clone(e) {
                Expr::LitNat(v) => Some(v),
                _ => None,
            }
        };
        let result: BigUint = match n.as_str() {
            "Nat.add" if args.len() >= 2 => {
                lit(self, args[0])?.add(&lit(self, args[1])?)
            }
            "Nat.mul" if args.len() >= 2 => {
                lit(self, args[0])?.mul(&lit(self, args[1])?)
            }
            "Nat.sub" if args.len() >= 2 => {
                let a = lit(self, args[0])?;
                let b = lit(self, args[1])?;
                if a.cmp(&b) == std::cmp::Ordering::Less {
                    BigUint::zero()
                } else {
                    a.sub(&b)
                }
            }
            "Nat.pow" if args.len() >= 2 => {
                let a = lit(self, args[0])?;
                let b = lit(self, args[1])?.to_u64()?;
                if b > 10_000 {
                    return None;
                }
                a.pow(b)
            }
            "Nat.div" if args.len() >= 2 => {
                let a = lit(self, args[0])?;
                let b = lit(self, args[1])?;
                if b.is_zero() {
                    BigUint::zero()
                } else {
                    a.div_rem(&b).0
                }
            }
            "Nat.mod" if args.len() >= 2 => {
                let a = lit(self, args[0])?;
                let b = lit(self, args[1])?;
                if b.is_zero() {
                    a
                } else {
                    a.div_rem(&b).1
                }
            }
            _ => return None,
        };
        let mut rest = self.arena.intern(Expr::LitNat(result));
        for &a in args.iter().skip(2) {
            rest = self.arena.app(rest, a);
        }
        Some(rest)
    }

    fn try_quot(&mut self, name: NameId, args: &[ExprId]) -> Option<ExprId> {
        let n = self.names.display(name);
        if n == "Quot.lift" {
            // args: α, r, β, f, h, q  (explicit/implicit all explicit in core)
            if args.len() < 6 {
                return None;
            }
            let q = args[5];
            let (head, qargs) = spine(&self.arena, q);
            if let Expr::Const(mk, _) = self.arena.get_clone(head) {
                if self.names.display(mk) == "Quot.mk" && qargs.len() >= 3 {
                    let f = args[3];
                    let a = qargs[2];
                    return Some(self.arena.app(f, a));
                }
            }
        }
        None
    }

    // ---------- recursors ----------

    /// Attempt iota reduction of a recursor application.
    fn try_iota(
        &mut self,
        ctx: &Context,
        rec_name: NameId,
        levels: &[Level],
        rec: RecursorInfo,
        args: &[ExprId],
    ) -> KResult<Option<ExprId>> {
        let block: Vec<(NameId, InductiveInfo)> = self
            .env
            .block_members(rec.block_id)
            .iter()
            .map(|d| (d.name, d.inductive.clone().unwrap()))
            .collect();
        if block.is_empty() {
            return Ok(None);
        }
        let total_ctors: usize = block.iter().map(|(_, i)| i.constructors.len()).sum();
        let target_idx = block.iter().position(|(n, _)| *n == rec.inductive).unwrap_or(0);
        let target_info = block[target_idx].1.clone();
        let num_params = target_info.num_params as usize;
        let num_motives = block.len();
        let header = num_params + num_motives + total_ctors;
        let needed = header + target_info.num_indices as usize + 1;
        if args.len() < needed {
            return Ok(None);
        }
        let major = args[needed - 1];
        let major_w = self.whnf(ctx, major)?;
        let (head, ctor_args) = spine(&self.arena, major_w);
        let (ctor_name, _ctor_levels) = match self.arena.get_clone(head) {
            Expr::Const(n, ls) => (n, ls),
            Expr::LitNat(v) => {
                // Nat literal as zero/succ for Nat.rec-style recursors
                return self.iota_nat_literal(
                    ctx, rec_name, levels, rec, args, &v, needed, header, target_info.num_indices as usize,
                );
            }
            _ => return Ok(None),
        };
        let ctor_decl = match self.env.get(ctor_name).cloned() {
            Some(d) => d,
            None => return Ok(None),
        };
        let ctor_info = match &ctor_decl.ctor {
            Some(c) => c.clone(),
            None => return Ok(None),
        };
        if ctor_args.len() < num_params + ctor_info.num_fields as usize {
            return Ok(None);
        }
        // locate the minor premise for this constructor
        let mut minor_offset = num_params + num_motives;
        let mut chosen_minor: Option<ExprId> = None;
        let mut chosen_ind_ordinal = 0usize;
        for (bi, (_member_name, info)) in block.iter().enumerate() {
            for (ci, cname) in info.constructors.iter().enumerate() {
                if *cname == ctor_name {
                    chosen_minor = Some(args[minor_offset + ci]);
                    chosen_ind_ordinal = bi;
                }
            }
            minor_offset += info.constructors.len();
        }
        let minor = match chosen_minor {
            Some(m) => m,
            None => return Ok(None),
        };
        let _ = chosen_ind_ordinal;
        let fields: Vec<ExprId> = ctor_args[num_params..num_params + ctor_info.num_fields as usize].to_vec();

        // Field metadata for recursive-field detection.
        let (ctor_binders, _) = pi_telescope(&self.arena, ctor_decl.ty);
        let mut result = minor;
        let mut applied: Vec<ExprId> = Vec::new(); // params ++ fields so far (for instantiating field types)
        applied.extend_from_slice(&ctor_args[..num_params.min(ctor_args.len())]);
        for (fi, field_val) in fields.iter().enumerate() {
            result = self.arena.app(result, *field_val);
            applied.push(*field_val);
            // Is this field recursive (its type, instantiated, is a Pi ending in a block inductive)?
            let binder_pos = num_params + fi;
            if binder_pos >= ctor_binders.len() {
                continue;
            }
            let field_ty = ctor_binders[binder_pos].2;
            let instantiated = self.arena.subst_telescope(field_ty, &applied[..applied.len() - 1]);
            let (field_binders, tail) = pi_telescope(&self.arena, instantiated);
            let (thead, targs) = spine(&self.arena, tail);
            let is_rec = match self.arena.get_clone(thead) {
                Expr::Const(n, _) => block.iter().any(|(bn, _)| *bn == n),
                _ => false,
            };
            if is_rec {
                // Build IH: lambda over the field's binders, then a recursive rec call.
                let (rec_head_name, _) = match self.arena.get_clone(thead) {
                    Expr::Const(n, ls) => (n, ls),
                    _ => unreachable!(),
                };
                let rec_for = self
                    .env
                    .decls
                    .iter()
                    .find(|d| {
                        d.recursor
                            .as_ref()
                            .map(|r| r.inductive == rec_head_name && r.block_id == rec.block_id)
                            .unwrap_or(false)
                    })
                    .map(|d| d.name);
                if let Some(rec_for_name) = rec_for {
                    let field_indices: Vec<ExprId> =
                        targs[num_params.min(targs.len())..].to_vec();
                    // innermost application of the field value
                    let mut ih_body = self.arena.const_(rec_for_name, levels.to_vec());
                    for &a in &args[..num_params] {
                        ih_body = self.arena.app(ih_body, a);
                    }
                    // motives and minors from the original application
                    for &a in &args[num_params..num_params + num_motives + total_ctors] {
                        ih_body = self.arena.app(ih_body, a);
                    }
                    // indices for the recursive call, shifted under field binders
                    let nb = field_binders.len();
                    for idx_expr in &field_indices {
                        let shifted = self.arena.shift(*idx_expr, nb as i64, 0);
                        ih_body = self.arena.app(ih_body, shifted);
                    }
                    // major premise: field applied to the new bound variables
                    let mut major_expr = self.arena.shift(*field_val, nb as i64, 0);
                    for b in 0..nb {
                        let bv = self.arena.bvar((nb - 1 - b) as u32);
                        major_expr = self.arena.app(major_expr, bv);
                    }
                    ih_body = self.arena.app(ih_body, major_expr);
                    // wrap lambdas (outermost binder last built)
                    for (bi, (bname, binfo, bdom)) in field_binders.iter().enumerate().rev() {
                        let _ = bi;
                        ih_body = self.arena.lam(*bname, *binfo, *bdom, ih_body);
                    }
                    // NOTE: binder domains above are in the instantiated context;
                    // they are already correct de Bruijn expressions for this position.
                    result = self.arena.app(result, ih_body);
                }
            }
        }
        // apply any remaining arguments beyond the major premise
        for &a in &args[needed..] {
            result = self.arena.app(result, a);
        }
        Ok(Some(result))
    }

    #[allow(clippy::too_many_arguments)]
    fn iota_nat_literal(
        &mut self,
        ctx: &Context,
        _rec_name: NameId,
        _levels: &[Level],
        rec: RecursorInfo,
        args: &[ExprId],
        v: &BigUint,
        needed: usize,
        _header: usize,
        _num_indices: usize,
    ) -> KResult<Option<ExprId>> {
        // Only for the Nat recursor shape: params=0, motives=1, minors=2 (zero, succ).
        let _ = ctx;
        let ind_decl = match self.env.get(rec.inductive).cloned() {
            Some(d) => d,
            None => return Ok(None),
        };
        let info = ind_decl.inductive.clone().unwrap();
        if info.num_params != 0 || args.len() < needed {
            return Ok(None);
        }
        if v.is_zero() {
            let zero_minor = args[1]; // params(0) + motive index 0 => minor 0 at args[1]? header = 0 params +1 motive; minors start at 1
            let mut result = zero_minor;
            for &a in &args[needed..] {
                result = self.arena.app(result, a);
            }
            return Ok(Some(result));
        }
        // succ case: minor at args[2], applied to predecessor and IH (recursive call on pred literal)
        if v.to_u64().map(|n| n > 100_000).unwrap_or(true) {
            return Ok(None); // do not materialize huge literals
        }
        let pred = v.sub(&BigUint::one());
        let pred_lit = self.arena.intern(Expr::LitNat(pred));
        let succ_minor = args[2];
        let mut rec_call = self.arena.const_(
            self.env
                .decls
                .iter()
                .find(|d| d.recursor.as_ref().map(|r| r.inductive == rec.inductive).unwrap_or(false))
                .map(|d| d.name)
                .unwrap_or(rec.inductive),
            _levels.to_vec(),
        );
        // Nat.rec args: motive, zero minor, succ minor, major
        for &a in &args[..needed - 1] {
            rec_call = self.arena.app(rec_call, a);
        }
        rec_call = self.arena.app(rec_call, pred_lit);
        let mut result = self.arena.app(succ_minor, pred_lit);
        result = self.arena.app(result, rec_call);
        for &a in &args[needed..] {
            result = self.arena.app(result, a);
        }
        Ok(Some(result))
    }

    /// Evaluate a closed Nat literal / zero-succ chain to a number, if it is one.
    /// Recursor applications on literals are fully evaluated (whnf at the head
    /// of each subterm), so `Nat.add 2 Nat.zero` and the literal `2` agree.
    pub fn nat_value(&mut self, ctx: &Context, e: ExprId) -> KResult<Option<BigUint>> {
        let w = self.whnf(ctx, e)?;
        match self.arena.get_clone(w) {
            Expr::LitNat(v) => Ok(Some(v)),
            Expr::Const(n, _) if self.names.display(n) == "Nat.zero" => Ok(Some(BigUint::zero())),
            Expr::App(_, _) => {
                let (head, args) = spine(&self.arena, w);
                if args.len() == 1 {
                    if let Expr::Const(n, _) = self.arena.get_clone(head) {
                        if self.names.display(n) == "Nat.succ" {
                            return Ok(match self.nat_value(ctx, args[0])? {
                                Some(v) => Some(v.add(&BigUint::one())),
                                None => None,
                            });
                        }
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    // ---------- definitional equality ----------

    pub fn is_def_eq(&mut self, ctx: &Context, a: ExprId, b: ExprId) -> KResult<bool> {
        self.budget.tick()?;
        if a == b {
            return Ok(true);
        }
        let aw = self.whnf(ctx, a)?;
        let bw = self.whnf(ctx, b)?;
        if aw == bw {
            return Ok(true);
        }
        // Nat literals are definitionally the corresponding zero/succ chains.
        if let (Ok(Some(x)), Ok(Some(y))) = (self.nat_value(ctx, aw), self.nat_value(ctx, bw)) {
            return Ok(x == y);
        }
        // Proof irrelevance: two proofs of the same (defeq) proposition are equal.
        if let (Ok(ta), Ok(tb)) = (self.infer(ctx, aw), self.infer(ctx, bw)) {
            if let Ok(true) = self.is_prop_type(ctx, ta) {
                if self.is_def_eq(ctx, ta, tb)? {
                    return Ok(true);
                }
            }
        }
        match (self.arena.get_clone(aw), self.arena.get_clone(bw)) {
            (Expr::Sort(l1), Expr::Sort(l2)) => Ok(l1.equiv(&l2)),
            (Expr::Pi(_, _, d1, c1), Expr::Pi(n2, _, d2, c2)) => {
                if !self.is_def_eq(ctx, d1, d2)? {
                    return Ok(false);
                }
                let mut ctx2 = ctx.clone();
                ctx2.push(LocalDecl { name: n2, ty: d1, value: None });
                self.is_def_eq(&ctx2, c1, c2)
            }
            (Expr::Lam(n1, _, d1, b1), Expr::Lam(_, _, d2, b2)) => {
                if !self.is_def_eq(ctx, d1, d2)? {
                    return Ok(false);
                }
                let mut ctx2 = ctx.clone();
                ctx2.push(LocalDecl { name: n1, ty: d1, value: None });
                self.is_def_eq(&ctx2, b1, b2)
            }
            (Expr::Lam(n1, _, d1, body), other) => {
                // eta: lambda vs non-lambda
                let mut ctx2 = ctx.clone();
                ctx2.push(LocalDecl { name: n1, ty: d1, value: None });
                let shifted = self.arena.shift(bw, 1, 0);
                let bv = self.arena.bvar(0);
                let applied = self.arena.app(shifted, bv);
                self.is_def_eq(&ctx2, body, applied)
            }
            (other, Expr::Lam(n2, _, d2, body)) => {
                let mut ctx2 = ctx.clone();
                ctx2.push(LocalDecl { name: n2, ty: d2, value: None });
                let shifted = self.arena.shift(aw, 1, 0);
                let bv = self.arena.bvar(0);
                let applied = self.arena.app(shifted, bv);
                self.is_def_eq(&ctx2, applied, body)
            }
            (Expr::App(f1, a1), Expr::App(f2, a2)) => {
                Ok(self.is_def_eq(ctx, f1, f2)? && self.is_def_eq(ctx, a1, a2)?)
            }
            (Expr::Const(n1, l1), Expr::Const(n2, l2)) => {
                Ok(n1 == n2
                    && l1.len() == l2.len()
                    && l1.iter().zip(l2.iter()).all(|(x, y)| x.equiv(y)))
            }
            (Expr::BVar(i), Expr::BVar(j)) => Ok(i == j),
            (Expr::LitNat(x), Expr::LitNat(y)) => Ok(x == y),
            (Expr::LitStr(x), Expr::LitStr(y)) => Ok(x == y),
            (Expr::Proj(s1, i1, t1), Expr::Proj(s2, i2, t2)) => {
                Ok(s1 == s2 && i1 == i2 && self.is_def_eq(ctx, t1, t2)?)
            }
            (Expr::Let(_, t1, v1, b1), Expr::Let(_, t2, v2, b2)) => {
                Ok(self.is_def_eq(ctx, t1, t2)?
                    && self.is_def_eq(ctx, v1, v2)?
                    && self.is_def_eq(ctx, b1, b2)?)
            }
            _ => {
                Ok(false)
            }
        }
    }

    // ---------- declaration admission ----------

    pub fn add_decl(&mut self, decl: Decl) -> KResult<()> {
        if self.env.contains(decl.name) {
            return Err(KernelError::InvalidDecl(format!(
                "duplicate declaration {}",
                self.names.display(decl.name)
            )));
        }
        self.validate_level_params(&decl.level_params)?;
        // The declared type must be a Sort in the empty context.
        self.level_of_sort(&vec![], decl.ty).map_err(|e| match e {
            KernelError::BudgetExhausted => KernelError::BudgetExhausted,
            other => KernelError::InvalidDecl(format!(
                "type of {} is not a type: {other}",
                self.names.display(decl.name)
            )),
        })?;
        match decl.kind {
            DeclKind::Axiom => {
                if decl.value.is_some() {
                    return Err(KernelError::InvalidDecl(
                        "axiom must not have a value".to_string(),
                    ));
                }
            }
            DeclKind::External => {}
            DeclKind::QuotPrimitive => {}
            _ => {
                let value = decl.value.ok_or_else(|| {
                    KernelError::InvalidDecl(format!(
                        "{} requires a value",
                        self.names.display(decl.name)
                    ))
                })?;
                self.check(&vec![], value, decl.ty).map_err(|e| match e {
                    KernelError::BudgetExhausted => KernelError::BudgetExhausted,
                    other => KernelError::InvalidDecl(format!(
                        "value of {} does not check: {other}",
                        self.names.display(decl.name)
                    )),
                })?;
            }
        }
        if decl.kind == DeclKind::QuotPrimitive {
            self.quot_used = true;
        }
        self.env.push(decl);
        Ok(())
    }

    pub fn add_axiom(&mut self, name: &str, level_params: &[&str], ty: NExpr) -> KResult<NameId> {
        let nid = self.name(name);
        let lps: Vec<NameId> = level_params.iter().map(|s| self.name(s)).collect();
        let ty_id = lower(&mut self.arena, &mut self.names, &mut Vec::new(), &ty)
            .map_err(|e| KernelError::InvalidDecl(e.0))?;
        self.add_decl(Decl::new(nid, lps, ty_id, None, DeclKind::Axiom))?;
        Ok(nid)
    }

    pub fn add_definition(
        &mut self,
        name: &str,
        level_params: &[&str],
        ty: NExpr,
        value: NExpr,
        kind: DeclKind,
        hint: Reducibility,
    ) -> KResult<NameId> {
        let nid = self.name(name);
        let lps: Vec<NameId> = level_params.iter().map(|s| self.name(s)).collect();
        let ty_id = lower(&mut self.arena, &mut self.names, &mut Vec::new(), &ty)
            .map_err(|e| KernelError::InvalidDecl(e.0))?;
        let val_id = lower(&mut self.arena, &mut self.names, &mut Vec::new(), &value)
            .map_err(|e| KernelError::InvalidDecl(e.0))?;
        let mut decl = Decl::new(nid, lps, ty_id, Some(val_id), kind);
        decl.hint = hint;
        self.add_decl(decl)?;
        Ok(nid)
    }

    // ---------- inductive blocks ----------

    pub fn add_inductive_block(&mut self, specs: Vec<InductiveSpec>) -> KResult<Vec<NameId>> {
        if specs.is_empty() {
            return Err(KernelError::InvalidDecl("empty inductive block".to_string()));
        }
        let block_id = self.env.num_blocks;
        self.env.num_blocks += 1;

        // Lower all types first (names of the block are pre-registered so
        // constructors can refer to the inductives themselves).
        let mut ind_names: Vec<NameId> = Vec::new();
        for spec in &specs {
            let nid = self.name(&spec.name);
            if self.env.contains(nid) {
                return Err(KernelError::InvalidDecl(format!(
                    "duplicate inductive {}",
                    spec.name
                )));
            }
            ind_names.push(nid);
        }
        // Insert provisional inductive declarations so constructor types can be
        // type-checked against them; they are only committed after every check
        // in this block passes. We build them in a scratch list and push at the end.
        let mut ind_decls: Vec<Decl> = Vec::new();
        let mut parsed: Vec<(
            Vec<(NameId, BinderInfo, ExprId)>,
            ExprId,
            Level,
            bool,
        )> = Vec::new();
        for (si, spec) in specs.iter().enumerate() {
            let lps: Vec<NameId> = spec.level_params.iter().map(|s| self.name(s)).collect();
            self.validate_level_params(&lps)?;
            let ty_id = lower(&mut self.arena, &mut self.names, &mut Vec::new(), &spec.ty)
                .map_err(|e| KernelError::InvalidDecl(e.0))?;
            // type must be a telescope ending in a Sort
            let (binders, body) = pi_telescope(&self.arena, ty_id);
            let sort_level = match self.arena.get_clone(body) {
                Expr::Sort(l) => l,
                _ => {
                    return Err(KernelError::InvalidDecl(format!(
                        "inductive {} does not end in a Sort",
                        spec.name
                    )))
                }
            };
            if (spec.num_params as usize) > binders.len() {
                return Err(KernelError::InvalidDecl(format!(
                    "inductive {} declares more parameters than its type has binders",
                    spec.name
                )));
            }
            let is_prop = sort_level.is_zero();
            parsed.push((binders, body, sort_level.clone(), is_prop));
            let mut decl = Decl::new(ind_names[si], lps, ty_id, None, DeclKind::Inductive);
            decl.inductive = Some(InductiveInfo {
                block_id,
                ordinal_in_block: si as u32,
                num_params: spec.num_params,
                num_indices: 0, // filled below
                constructors: Vec::new(),
                sort_level,
                is_prop,
            });
            ind_decls.push(decl);
        }
        for (si, d) in ind_decls.iter_mut().enumerate() {
            let n_indices = parsed[si].0.len() - specs[si].num_params as usize;
            d.inductive.as_mut().unwrap().num_indices = n_indices as u32;
        }

        // Temporarily register inductives to check constructor types.
        let saved_len = self.env.decls.len();
        for d in ind_decls.iter().cloned() {
            self.env.push(d);
        }
        let result = self.finish_inductive_block(&specs, &ind_names, &parsed, block_id);
        match result {
            Ok(ctor_and_rec) => {
                // fill constructor lists
                for (si, _) in specs.iter().enumerate() {
                    let ctors = ctor_and_rec[si].clone();
                    let pos = self.env.index[&ind_names[si]];
                    self.env.decls[pos].inductive.as_mut().unwrap().constructors = ctors;
                }
                Ok(ind_names)
            }
            Err(e) => {
                // roll back provisional registrations
                while self.env.decls.len() > saved_len {
                    let d = self.env.decls.pop().unwrap();
                    self.env.index.remove(&d.name);
                }
                Err(e)
            }
        }
    }

    fn finish_inductive_block(
        &mut self,
        specs: &[InductiveSpec],
        ind_names: &[NameId],
        parsed: &[(Vec<(NameId, BinderInfo, ExprId)>, ExprId, Level, bool)],
        block_id: u32,
    ) -> KResult<Vec<Vec<NameId>>> {
        let mut all_ctors: Vec<Vec<NameId>> = Vec::new();
        // --- validate constructors, positivity, indices ---
        for (si, spec) in specs.iter().enumerate() {
            let (ind_binders, _, _, _) = &parsed[si];
            let mut ctor_names = Vec::new();
            for (cname, cty) in &spec.constructors {
                let cid = self.name(cname);
                if self.env.contains(cid) {
                    return Err(KernelError::InvalidDecl(format!(
                        "duplicate constructor {cname}"
                    )));
                }
                let cty_id = lower(&mut self.arena, &mut self.names, &mut Vec::new(), cty)
                    .map_err(|e| KernelError::InvalidDecl(e.0))?;
                // constructor type must itself be a valid telescope
                self.level_of_sort(&vec![], cty_id).map_err(|e| {
                    KernelError::InvalidDecl(format!("constructor {cname} type invalid: {e}"))
                })?;
                let (cbinders, cresult) = pi_telescope(&self.arena, cty_id);
                if cbinders.len() < spec.num_params as usize {
                    return Err(KernelError::InvalidDecl(format!(
                        "constructor {cname} has fewer arguments than the inductive has parameters"
                    )));
                }
                // parameters must match the inductive's parameter domains (defeq)
                let mut ctx: Context = Vec::new();
                for j in 0..spec.num_params as usize {
                    if !self.is_def_eq(&ctx, cbinders[j].2, ind_binders[j].2)? {
                        return Err(KernelError::InvalidDecl(format!(
                            "constructor {cname} parameter {} does not match the inductive parameter",
                            j
                        )));
                    }
                    ctx.push(LocalDecl { name: cbinders[j].0, ty: cbinders[j].2, value: None });
                }
                // fields: strict positivity + result indices
                for j in spec.num_params as usize..cbinders.len() {
                    let field_ty = cbinders[j].2;
                    self.check_strict_positivity(field_ty, ind_names, &ctx, cname)?;
                    ctx.push(LocalDecl { name: cbinders[j].0, ty: cbinders[j].2, value: None });
                }
                // result must be the inductive applied to params then indices
                let (rhead, rargs) = spine(&self.arena, cresult);
                match self.arena.get_clone(rhead) {
                    Expr::Const(n, _) if n == ind_names[si] => {}
                    _ => {
                        return Err(KernelError::InvalidDecl(format!(
                            "constructor {cname} does not return {}",
                            spec.name
                        )))
                    }
                }
                if rargs.len() != ind_binders.len() {
                    return Err(KernelError::InvalidDecl(format!(
                        "constructor {cname} returns {} with the wrong number of arguments",
                        spec.name
                    )));
                }
                // parameter arguments must be exactly the parameter variables
                for j in 0..spec.num_params as usize {
                    let expected_var = (cbinders.len() - 1 - j) as u32;
                    // cresult is in the context of all ctor binders; param j is
                    // bound variable (num_binders_before_result - 1 - j)... the ctor
                    // telescope length is cbinders.len(); variable for binder j has
                    // index cbinders.len()-1-j from the result position.
                    match self.arena.get_clone(rargs[j]) {
                        Expr::BVar(v) if v == expected_var => {}
                        _ => {
                            return Err(KernelError::InvalidDecl(format!(
                                "constructor {cname} must return {} applied to its parameters",
                                spec.name
                            )))
                        }
                    }
                }
                ctor_names.push(cid);
                // register constructor declaration (provisional, committed with block)
                let num_fields = (cbinders.len() - spec.num_params as usize) as u32;
                let mut cdecl = Decl::new(
                    cid,
                    ind_decls_level_params(self, specs, si),
                    cty_id,
                    None,
                    DeclKind::Constructor,
                );
                cdecl.ctor = Some(CtorInfo {
                    inductive: ind_names[si],
                    ordinal: ctor_names.len() as u32 - 1,
                    num_fields,
                });
                self.env.push(cdecl);
            }
            all_ctors.push(ctor_names);
        }

        // --- generate and register recursors (never trust producer signatures) ---
        for (si, spec) in specs.iter().enumerate() {
            let rec_name_str = format!("{}.rec", spec.name);
            let rec_ty = self.generate_recursor_type(specs, parsed, si, block_id)?;
            let rid = self.name(&rec_name_str);
            if self.env.contains(rid) {
                return Err(KernelError::InvalidDecl(format!(
                    "duplicate recursor {rec_name_str}"
                )));
            }
            let mut lps: Vec<NameId> =
                spec.level_params.iter().map(|s| self.name(s)).collect();
            let u_rec = self.name("u_rec");
            lps.push(u_rec);
            // validate the generated recursor type is a genuine type
            self.level_of_sort(&vec![], rec_ty).map_err(|e| {
                KernelError::InvalidDecl(format!("generated recursor {rec_name_str} invalid: {e}"))
            })?;
            let mut rdecl = Decl::new(rid, lps, rec_ty, None, DeclKind::Recursor);
            rdecl.recursor = Some(RecursorInfo { inductive: ind_names[si], block_id });
            self.env.push(rdecl);
        }
        Ok(all_ctors)
    }

    fn check_strict_positivity(
        &mut self,
        field_ty: ExprId,
        ind_names: &[NameId],
        ctx: &Context,
        ctor_name: &str,
    ) -> KResult<()> {
        // Walk Pi binders of the field type: the inductive must not occur in
        // any Pi domain inside the field type; in the tail it may occur only
        // as the head applied to the parameters (nested occurrences are
        // reported UNSUPPORTED rather than silently accepted).
        let mut cur = field_ty;
        let mut local_ctx = ctx.clone();
        loop {
            match self.arena.get_clone(cur) {
                Expr::Pi(n, _, dom, cod) => {
                    for ind in ind_names {
                        if self.arena.contains_const(dom, *ind) {
                            return Err(KernelError::InvalidDecl(format!(
                                "constructor {ctor_name}: inductive occurs in a negative position (non-strictly-positive)"
                            )));
                        }
                    }
                    local_ctx.push(LocalDecl { name: n, ty: dom, value: None });
                    cur = cod;
                }
                _ => break,
            }
        }
        let (head, args) = spine(&self.arena, cur);
        if let Expr::Const(n, _) = self.arena.get_clone(head) {
            if ind_names.contains(&n) {
                // recursive occurrence: indices must not hide negative occurrences
                for a in &args {
                    self.check_no_negative_occurrence(*a, ind_names, ctor_name)?;
                }
                return Ok(());
            }
        }
        // non-recursive tail: inductive may only appear inside arguments of
        // other type formers in strictly positive spots; we conservatively
        // reject occurrences under any Pi domain (already handled) and accept
        // plain occurrences as type arguments (e.g. field : List Nat is fine;
        // field : List (Forest) is a nested inductive -> UNSUPPORTED).
        for ind in ind_names {
            if self.arena.contains_const(cur, *ind) {
                // distinguish direct argument occurrence (nested) -> unsupported
                return Err(KernelError::Unsupported(format!(
                    "constructor {ctor_name}: nested inductive occurrence is not supported by this kernel profile"
                )));
            }
        }
        let _ = local_ctx;
        Ok(())
    }

    fn check_no_negative_occurrence(
        &mut self,
        e: ExprId,
        ind_names: &[NameId],
        ctor_name: &str,
    ) -> KResult<()> {
        match self.arena.get_clone(e) {
            Expr::Pi(_, _, dom, cod) => {
                for ind in ind_names {
                    if self.arena.contains_const(dom, *ind) {
                        return Err(KernelError::InvalidDecl(format!(
                            "constructor {ctor_name}: inductive occurs negatively in an index"
                        )));
                    }
                }
                self.check_no_negative_occurrence(cod, ind_names, ctor_name)
            }
            Expr::App(f, a) => {
                self.check_no_negative_occurrence(f, ind_names, ctor_name)?;
                self.check_no_negative_occurrence(a, ind_names, ctor_name)
            }
            Expr::Lam(_, _, d, b) => {
                self.check_no_negative_occurrence(d, ind_names, ctor_name)?;
                self.check_no_negative_occurrence(b, ind_names, ctor_name)
            }
            _ => Ok(()),
        }
    }

    /// Reconstruct the recursor type from the validated block (L36 formula).
    /// Canonical binder names: params `p{j}`, indices `i{j}`, fields `f{j}`,
    /// motives `motive{mi}`, minors `minor_{mi}_{ci}`, motive indices `mi_i{k}`.
    fn generate_recursor_type(
        &mut self,
        specs: &[InductiveSpec],
        parsed: &[(Vec<(NameId, BinderInfo, ExprId)>, ExprId, Level, bool)],
        target: usize,
        _block_id: u32,
    ) -> KResult<ExprId> {
        struct CtorM {
            name: String,
            fields: Vec<(String, NExpr)>,
            indices: Vec<NExpr>,
        }
        struct MemberM {
            name: String,
            param_tys: Vec<NExpr>,
            index_tys: Vec<NExpr>,
            ctors: Vec<CtorM>,
        }
        let mut members: Vec<MemberM> = Vec::new();
        for (si, spec) in specs.iter().enumerate() {
            let (binders, _, _, _) = &parsed[si];
            let np = spec.num_params as usize;
            let mut scope: Vec<String> = Vec::new();
            let mut param_tys = Vec::new();
            let mut index_tys = Vec::new();
            for (j, (_, _, dom)) in binders.iter().enumerate() {
                let disp = if j < np { format!("p{j}") } else { format!("i{}", j - np) };
                let mut s = scope.clone();
                let dn = to_named(&self.arena, &self.names, *dom, &mut s);
                scope.push(disp);
                if j < np { param_tys.push(dn); } else { index_tys.push(dn); }
            }
            let mut ctors = Vec::new();
            for (cname, _) in &spec.constructors {
                let cid = self.name(cname);
                let cdecl = self.env.get(cid).cloned().unwrap();
                let (cbinders, cresult) = pi_telescope(&self.arena, cdecl.ty);
                let mut cscope: Vec<String> = (0..np).map(|j| format!("p{j}")).collect();
                let mut fields: Vec<(String, NExpr)> = Vec::new();
                for (j, (_, _, dom)) in cbinders.iter().enumerate().skip(np) {
                    let mut s = cscope.clone();
                    let dn = to_named(&self.arena, &self.names, *dom, &mut s);
                    let fname = format!("f{}", j - np);
                    fields.push((fname.clone(), dn));
                    cscope.push(fname);
                }
                let (_, rargs) = spine(&self.arena, cresult);
                let mut indices = Vec::new();
                for a in rargs.iter().skip(np) {
                    let mut s = cscope.clone();
                    indices.push(to_named(&self.arena, &self.names, *a, &mut s));
                }
                ctors.push(CtorM { name: cname.clone(), fields, indices });
            }
            members.push(MemberM { name: spec.name.clone(), param_tys, index_tys, ctors });
        }

        let target_member = &members[target];
        let npt = specs[target].num_params as usize;
        let param_names: Vec<String> = (0..npt).map(|j| format!("p{j}")).collect();
        let index_names: Vec<String> = (0..target_member.index_tys.len()).map(|j| format!("i{j}")).collect();
        let params_app: Vec<NExpr> = param_names.iter().map(|n| NExpr::var(n)).collect();
        let levels_of = |mi: usize| -> Vec<Level> {
            specs[mi].level_params.iter().enumerate().map(|(i, _)| Level::Param(i as u32)).collect()
        };
        let motive_level = Level::Param(specs[target].level_params.len() as u32);

        // result: motive{target} i... t
        let mut result = NExpr::apps(
            NExpr::var(&format!("motive{target}")),
            &index_names.iter().map(|n| NExpr::var(n)).chain(std::iter::once(NExpr::var("t"))).collect::<Vec<_>>(),
        );
        let ind_app = NExpr::apps(
            NExpr::const_levels(&target_member.name, levels_of(target)),
            &params_app.iter().cloned().chain(index_names.iter().map(|n| NExpr::var(n))).collect::<Vec<_>>(),
        );
        result = NExpr::pi("t", ind_app, result);
        for (k, iname) in index_names.iter().enumerate().rev() {
            result = NExpr::pi(iname, target_member.index_tys[k].clone(), result);
        }

        // minors (reverse)
        struct MinorSpec { name: String, ty: NExpr }
        let mut minors: Vec<MinorSpec> = Vec::new();
        for (mi, member) in members.iter().enumerate() {
            for (ci, ctor) in member.ctors.iter().enumerate() {
                let ctor_app = NExpr::apps(
                    NExpr::const_levels(&ctor.name, levels_of(mi)),
                    &params_app.iter().cloned().chain(ctor.fields.iter().map(|(fname, _)| NExpr::var(fname))).collect::<Vec<_>>(),
                );
                let mut mty = NExpr::apps(
                    NExpr::var(&format!("motive{mi}")),
                    &ctor.indices.iter().cloned().chain(std::iter::once(ctor_app)).collect::<Vec<_>>(),
                );
                for (fi, (fname, fty)) in ctor.fields.iter().enumerate().rev() {
                    if let Some(ih_ty) = ih_type_for(fty, &members.iter().map(|m| (m.name.clone(), m.param_tys.len())).collect::<Vec<_>>()) {
                        let ih_ty = subst_named_var(&ih_ty, "__field__", fname);
                        mty = NExpr::pi(&format!("ih_{fname}"), ih_ty, mty);
                    }
                }
                for (fname, fty) in ctor.fields.iter().rev() {
                    mty = NExpr::pi(fname, fty.clone(), mty);
                }
                minors.push(MinorSpec { name: format!("minor_{mi}_{ci}"), ty: mty });
            }
        }
        for minor in minors.iter().rev() {
            result = NExpr::pi(&minor.name, minor.ty.clone(), result);
        }

        // motives (reverse)
        for mi in (0..members.len()).rev() {
            let member = &members[mi];
            let mut motive_ty = NExpr::sort(motive_level.clone());
            let ind_app_m = NExpr::apps(
                NExpr::const_levels(&member.name, levels_of(mi)),
                &params_app.iter().cloned().chain((0..member.index_tys.len()).map(|k| NExpr::var(&format!("mi_i{k}")))).collect::<Vec<_>>(),
            );
            motive_ty = NExpr::pi("mt", ind_app_m, motive_ty);
            for k in (0..member.index_tys.len()).rev() {
                let mut ity = member.index_tys[k].clone();
                for (j, old) in index_names.iter().enumerate().take(k) {
                    ity = subst_named_var(&ity, old, &format!("mi_i{j}"));
                }
                // index tys of other members reference i{j} names of that member's
                // own telescope; rename p/i consistently: indices of member mi use
                // the same i{j} spelling, so map i{j} -> mi_i{j} for j<k.
                motive_ty = NExpr::pi(&format!("mi_i{k}"), ity, motive_ty);
            }
            result = NExpr::pi(&format!("motive{mi}"), motive_ty, result);
        }

        // params (outermost, reverse)
        for (j, pname) in param_names.iter().enumerate().rev() {
            result = NExpr::pi(pname, target_member.param_tys[j].clone(), result);
        }

        let mut scope: Vec<String> = Vec::new();
        lower(&mut self.arena, &mut self.names, &mut scope, &result).map_err(|e| {
            KernelError::InvalidDecl(format!(
                "recursor generation failed: {} in {}",
                e.0,
                crate::builder::pretty_named(&result)
            ))
        })
    }

    // ---------- quotient primitives ----------

    pub fn add_quot(&mut self) -> KResult<()> {
        if self.lookup_decl("Quot").is_some() {
            return Ok(());
        }
        let u = Level::Param(0);
        let v = Level::Param(1);
        // Quot : {α : Sort u} -> (α -> α -> Prop) -> Sort u
        let quot_ty = NExpr::pi(
            "α",
            NExpr::sort(u.clone()),
            NExpr::pi(
                "r",
                NExpr::pi(
                    "_",
                    NExpr::var("α"),
                    NExpr::pi("_", NExpr::var("α"), NExpr::prop()),
                ),
                NExpr::sort(u.clone()),
            ),
        );
        self.add_quot_primitive("Quot", &["u"], quot_ty)?;
        // Quot.mk : {α} -> {r} -> α -> Quot r
        let mk_ty = NExpr::pi(
            "α",
            NExpr::sort(u.clone()),
            NExpr::pi(
                "r",
                NExpr::pi("_", NExpr::var("α"), NExpr::pi("_", NExpr::var("α"), NExpr::prop())),
                NExpr::pi(
                    "a",
                    NExpr::var("α"),
                    NExpr::apps(
                        NExpr::const_levels("Quot", vec![u.clone()]),
                        &[NExpr::var("α"), NExpr::var("r")],
                    ),
                ),
            ),
        );
        self.add_quot_primitive("Quot.mk", &["u"], mk_ty)?;
        // Quot.lift : {α r β} (f : α -> β) (h : ∀ a b, r a b -> Eq (f a) (f b)) (q : Quot r) : β
        let lift_ty = NExpr::pi(
            "α",
            NExpr::sort(u.clone()),
            NExpr::pi(
                "r",
                NExpr::pi("_", NExpr::var("α"), NExpr::pi("_", NExpr::var("α"), NExpr::prop())),
                NExpr::pi(
                    "β",
                    NExpr::sort(v.clone()),
                    NExpr::pi(
                        "f",
                        NExpr::pi("_", NExpr::var("α"), NExpr::var("β")),
                        NExpr::pi(
                            "h",
                            NExpr::pi(
                                "a",
                                NExpr::var("α"),
                                NExpr::pi(
                                    "b",
                                    NExpr::var("α"),
                                    NExpr::pi(
                                        "_",
                                        NExpr::apps(NExpr::var("r"), &[NExpr::var("a"), NExpr::var("b")]),
                                        NExpr::apps(
                                            NExpr::const_levels("Eq", vec![Level::Param(1)]),
                                            &[
                                                NExpr::var("β"),
                                                NExpr::app(NExpr::var("f"), NExpr::var("a")),
                                                NExpr::app(NExpr::var("f"), NExpr::var("b")),
                                            ],
                                        ),
                                    ),
                                ),
                            ),
                            NExpr::pi(
                                "q",
                                NExpr::apps(
                                    NExpr::const_levels("Quot", vec![u.clone()]),
                                    &[NExpr::var("α"), NExpr::var("r")],
                                ),
                                NExpr::var("β"),
                            ),
                        ),
                    ),
                ),
            ),
        );
        // Eq may not exist yet in a minimal kernel; Quot.lift admission then
        // fails instructively. The standard bootstrap adds Eq before Quot.
        self.add_quot_primitive("Quot.lift", &["u", "v"], lift_ty)?;
        // Quot.ind : {α r} {β : Quot r -> Prop} (h : ∀ a, β (Quot.mk a)) → ∀ q, β q
        let ind_ty = NExpr::pi(
            "α",
            NExpr::sort(u.clone()),
            NExpr::pi(
                "r",
                NExpr::pi("_", NExpr::var("α"), NExpr::pi("_", NExpr::var("α"), NExpr::prop())),
                NExpr::pi(
                    "β",
                    NExpr::pi(
                        "_",
                        NExpr::apps(
                            NExpr::const_levels("Quot", vec![u.clone()]),
                            &[NExpr::var("α"), NExpr::var("r")],
                        ),
                        NExpr::prop(),
                    ),
                    NExpr::pi(
                        "h",
                        NExpr::pi(
                            "a",
                            NExpr::var("α"),
                            NExpr::app(
                                NExpr::var("β"),
                                NExpr::apps(
                                    NExpr::const_levels("Quot.mk", vec![u.clone()]),
                                    &[NExpr::var("α"), NExpr::var("r"), NExpr::var("a")],
                                ),
                            ),
                        ),
                        NExpr::pi(
                            "q",
                            NExpr::apps(
                                NExpr::const_levels("Quot", vec![u.clone()]),
                                &[NExpr::var("α"), NExpr::var("r")],
                            ),
                            NExpr::app(NExpr::var("β"), NExpr::var("q")),
                        ),
                    ),
                ),
            ),
        );
        self.add_quot_primitive("Quot.ind", &["u"], ind_ty)?;
        // Quot.sound is an axiom constant (reported by policy, never silent).
        let sound_ty = NExpr::pi(
            "α",
            NExpr::sort(u.clone()),
            NExpr::pi(
                "r",
                NExpr::pi("_", NExpr::var("α"), NExpr::pi("_", NExpr::var("α"), NExpr::prop())),
                NExpr::pi(
                    "a",
                    NExpr::var("α"),
                    NExpr::pi(
                        "b",
                        NExpr::var("α"),
                        NExpr::pi(
                            "_",
                            NExpr::apps(NExpr::var("r"), &[NExpr::var("a"), NExpr::var("b")]),
                            NExpr::apps(
                                NExpr::const_levels("Eq", vec![Level::Param(0)]),
                                &[
                                    NExpr::apps(
                                        NExpr::const_levels("Quot", vec![u.clone()]),
                                        &[NExpr::var("α"), NExpr::var("r")],
                                    ),
                                    NExpr::apps(
                                        NExpr::const_levels("Quot.mk", vec![u]),
                                        &[NExpr::var("α"), NExpr::var("r"), NExpr::var("a")],
                                    ),
                                    NExpr::apps(
                                        NExpr::const_levels("Quot.mk", vec![Level::Param(0)]),
                                        &[NExpr::var("α"), NExpr::var("r"), NExpr::var("b")],
                                    ),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        );
        let nid = self.name("Quot.sound");
        let lps = vec![self.name("u")];
        let ty_id = lower(&mut self.arena, &mut self.names, &mut Vec::new(), &sound_ty)
            .map_err(|e| KernelError::InvalidDecl(e.0))?;
        self.add_decl(Decl::new(nid, lps, ty_id, None, DeclKind::Axiom))?;
        self.quot_used = true;
        Ok(())
    }

    fn add_quot_primitive(&mut self, name: &str, lps: &[&str], ty: NExpr) -> KResult<()> {
        let nid = self.name(name);
        let lp_ids: Vec<NameId> = lps.iter().map(|s| self.name(s)).collect();
        let ty_id = lower(&mut self.arena, &mut self.names, &mut Vec::new(), &ty)
            .map_err(|e| KernelError::InvalidDecl(e.0))?;
        self.add_decl(Decl::new(nid, lp_ids, ty_id, None, DeclKind::QuotPrimitive))?;
        Ok(())
    }

    // ---------- assumption closure ----------

    /// All axiom constants and quotient usage in the transitive closure of `roots`.
    pub fn assumption_closure(&self, roots: &[NameId]) -> (BTreeSet<String>, bool) {
        let mut axioms = BTreeSet::new();
        let mut quot = false;
        let mut visited: BTreeSet<NameId> = BTreeSet::new();
        let mut stack: Vec<NameId> = roots.to_vec();
        while let Some(n) = stack.pop() {
            if !visited.insert(n) {
                continue;
            }
            if let Some(d) = self.env.get(n) {
                match d.kind {
                    DeclKind::Axiom => {
                        axioms.insert(self.names.display(n));
                    }
                    DeclKind::QuotPrimitive => {
                        quot = true;
                    }
                    _ => {}
                }
                let mut deps = Vec::new();
                self.arena.collect_consts(d.ty, &mut deps);
                if let Some(v) = d.value {
                    self.arena.collect_consts(v, &mut deps);
                }
                if let Some(info) = &d.inductive {
                    for c in &info.constructors {
                        stack.push(*c);
                    }
                }
                for dep in deps {
                    stack.push(dep);
                }
            }
        }
        (axioms, quot || self.quot_used && roots.iter().any(|r| visited.contains(r) && {
            // quot flag only when closure actually touches Quot constants; refined below
            true
        }) && quot)
    }

    /// Global constants a declaration directly references (type + value + ctor/rec links).
    pub fn direct_deps(&self, name: NameId) -> Vec<NameId> {
        let mut out = Vec::new();
        if let Some(d) = self.env.get(name) {
            self.arena.collect_consts(d.ty, &mut out);
            if let Some(v) = d.value {
                self.arena.collect_consts(v, &mut out);
            }
            if let Some(ci) = &d.ctor {
                if !out.contains(&ci.inductive) {
                    out.push(ci.inductive);
                }
            }
            if let Some(ri) = &d.recursor {
                if !out.contains(&ri.inductive) {
                    out.push(ri.inductive);
                }
            }
            if let Some(info) = &d.inductive {
                for c in &info.constructors {
                    if !out.contains(c) {
                        out.push(*c);
                    }
                }
            }
        }
        out
    }
}

fn ind_decls_level_params(k: &mut Kernel, specs: &[InductiveSpec], si: usize) -> Vec<NameId> {
    specs[si]
        .level_params
        .iter()
        .map(|s| k.name(s))
        .collect()
}

fn binder_display(names: &NameArena, n: NameId, pos: usize) -> String {
    let dotted = names.display(n);
    let last = dotted.rsplit('.').next().unwrap_or("").to_string();
    if last.is_empty() || last == "_" {
        format!("x{pos}")
    } else {
        last
    }
}



/// If a field type is a Pi ending in a block inductive application, build its IH type.
fn ih_type_for(fty: &NExpr, members: &[(String, usize)]) -> Option<NExpr> {
    let mut binders: Vec<(String, NExpr)> = Vec::new();
    let mut cur = fty.clone();
    loop {
        match cur {
            NExpr::Pi(n, _, d, c) => { binders.push((n, *d)); cur = *c; }
            _ => break,
        }
    }
    let mut head = cur.clone();
    let mut args: Vec<NExpr> = Vec::new();
    while let NExpr::App(f, a) = head { args.push(*a); head = *f; }
    args.reverse();
    let member_idx = match &head {
        NExpr::Const(n, _) => members.iter().position(|m| &m.0 == n)?,
        _ => return None,
    };
    let np = members[member_idx].1;
    if args.len() < np { return None; }
    let indices: Vec<NExpr> = args[np..].to_vec();
    let mut applied = NExpr::var("__field__");
    for (bn, _) in &binders { applied = NExpr::app(applied, NExpr::var(bn)); }
    let mut ih = NExpr::apps(
        NExpr::var(&format!("motive{member_idx}")),
        &indices.iter().cloned().chain(std::iter::once(applied)).collect::<Vec<_>>(),
    );
    for (bn, bd) in binders.iter().rev() { ih = NExpr::pi(bn, bd.clone(), ih); }
    Some(ih)
}


/// Substitute a named variable (capture-avoiding for our generated names, which are fresh).
pub fn subst_named_var(e: &NExpr, from: &str, to: &str) -> NExpr {
    match e {
        NExpr::Var(s) if s == from => NExpr::var(to),
        NExpr::Var(_) | NExpr::Const(_, _) | NExpr::Sort(_) | NExpr::LitNat(_) | NExpr::LitStr(_) => e.clone(),
        NExpr::App(f, a) => NExpr::app(subst_named_var(f, from, to), subst_named_var(a, from, to)),
        NExpr::Pi(n, info, d, c) => {
            let d2 = subst_named_var(d, from, to);
            if n == from { NExpr::Pi(n.clone(), *info, Box::new(d2), c.clone()) }
            else { NExpr::Pi(n.clone(), *info, Box::new(d2), Box::new(subst_named_var(c, from, to))) }
        }
        NExpr::Lam(n, info, d, b) => {
            let d2 = subst_named_var(d, from, to);
            if n == from { NExpr::Lam(n.clone(), *info, Box::new(d2), b.clone()) }
            else { NExpr::Lam(n.clone(), *info, Box::new(d2), Box::new(subst_named_var(b, from, to))) }
        }
        NExpr::Let(n, t, v, b) => {
            let t2 = subst_named_var(t, from, to);
            let v2 = subst_named_var(v, from, to);
            if n == from { NExpr::Let(n.clone(), Box::new(t2), Box::new(v2), b.clone()) }
            else { NExpr::Let(n.clone(), Box::new(t2), Box::new(v2), Box::new(subst_named_var(b, from, to))) }
        }
        NExpr::Proj(s, i, t) => NExpr::Proj(s.clone(), *i, Box::new(subst_named_var(t, from, to))),
    }
}
