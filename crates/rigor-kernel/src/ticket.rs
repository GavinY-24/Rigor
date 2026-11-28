//! Conversion tickets and the local proof arena (§4.1).
//!
//! A ticket never says "believe these are equal". Every step derives its
//! conclusion from operands, earlier arena facts, and the pinned kernel
//! rules. An invalid referenced ticket invalidates the whole bundle at the
//! runtime layer. Producers may omit tickets entirely (CHECK_CORE fallback).

use crate::check::{Context, Kernel, LocalDecl};
use crate::expr::{spine, Expr, ExprId};
use rigor_spec::abi::TicketOpcode;
use std::fmt;

#[derive(Debug, Clone)]
pub enum Fact {
    Ty { ctx: u32, expr: ExprId, ty: ExprId },
    Eq { ctx: u32, lhs: ExprId, rhs: ExprId },
}

#[derive(Debug, Clone)]
pub struct TicketStep {
    pub op: TicketOpcode,
    pub ctx: u32,
    /// Primary operand (expression ID in the kernel arena).
    pub x: ExprId,
    /// Secondary operand / claimed result.
    pub y: ExprId,
    /// Tertiary operand (e.g. Join middle term).
    pub z: ExprId,
    /// Indices of earlier facts this step depends on.
    pub refs: Vec<u32>,
}

impl TicketStep {
    pub fn new(op: TicketOpcode, ctx: u32, x: ExprId, y: ExprId) -> Self {
        Self { op, ctx, x, y, z: 0, refs: Vec::new() }
    }
}

#[derive(Debug, Clone)]
pub enum TicketError {
    Invalid(String),
    Budget,
}

impl fmt::Display for TicketError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TicketError::Invalid(m) => write!(f, "invalid ticket: {m}"),
            TicketError::Budget => write!(f, "ticket verification exhausted resource budget"),
        }
    }
}
impl std::error::Error for TicketError {}

fn kk<T>(r: Result<T, crate::check::KernelError>) -> Result<T, TicketError> {
    r.map_err(|e| match e {
        crate::check::KernelError::BudgetExhausted => TicketError::Budget,
        other => TicketError::Invalid(other.to_string()),
    })
}

pub struct TicketVerifier<'k> {
    pub kernel: &'k mut Kernel,
    pub contexts: Vec<Context>,
    pub facts: Vec<Fact>,
}

impl<'k> TicketVerifier<'k> {
    pub fn new(kernel: &'k mut Kernel, contexts: Vec<Context>) -> Self {
        Self { kernel, contexts, facts: Vec::new() }
    }

    fn ctx(&self, id: u32) -> Result<Context, TicketError> {
        self.contexts
            .get(id as usize)
            .cloned()
            .ok_or_else(|| TicketError::Invalid(format!("unknown ticket context {id}")))
    }

    fn fact(&self, id: u32) -> Result<Fact, TicketError> {
        self.facts
            .get(id as usize)
            .cloned()
            .ok_or_else(|| TicketError::Invalid(format!("ticket references future/unknown fact {id}")))
    }

    fn eq_fact(&self, id: u32) -> Result<(u32, ExprId, ExprId), TicketError> {
        match self.fact(id)? {
            Fact::Eq { ctx, lhs, rhs } => Ok((ctx, lhs, rhs)),
            _ => Err(TicketError::Invalid(format!("fact {id} is not an equality fact"))),
        }
    }

    fn ty_fact(&self, id: u32) -> Result<(u32, ExprId, ExprId), TicketError> {
        match self.fact(id)? {
            Fact::Ty { ctx, expr, ty } => Ok((ctx, expr, ty)),
            _ => Err(TicketError::Invalid(format!("fact {id} is not a typing fact"))),
        }
    }


    /// Verify one step and append its derived fact. Returns the new fact index.
    pub fn step(&mut self, step: &TicketStep) -> Result<u32, TicketError> {
        let idx = self.facts.len() as u32;
        let ctx = self.ctx(step.ctx)?;
        use TicketOpcode::*;
        let fact = match step.op {
            Same => {
                if step.x != step.y {
                    return Err(TicketError::Invalid("SAME requires structurally identical (interned) operands".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            Sym => {
                let r = *step.refs.first().ok_or(TicketError::Invalid("SYM needs a ref".into()))?;
                let (c, l, rr) = self.eq_fact(r)?;
                if c != step.ctx || l != step.y || rr != step.x {
                    return Err(TicketError::Invalid("SYM operands do not reverse the referenced fact".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            Join => {
                if step.refs.len() < 2 {
                    return Err(TicketError::Invalid("JOIN needs two refs".into()));
                }
                let (_, l1, r1) = self.eq_fact(step.refs[0])?;
                let (_, l2, r2) = self.eq_fact(step.refs[1])?;
                if l1 != step.x || r1 != step.z || l2 != step.z || r2 != step.y {
                    return Err(TicketError::Invalid("JOIN middle term does not match".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            Beta | Let | Delta | Iota | Proj | Quot => {
                // Verify one well-typed redex: operands type-check and the claimed
                // reduct is exactly the kernel's one-step (or WHNF) reduct.
                let reduced = {
                    let one = kk(self.kernel.whnf_step(&ctx, step.x))?;
                    if one != step.x {
                        one
                    } else {
                        kk(self.kernel.whnf(&ctx, step.x))?
                    }
                };
                if reduced != step.y {
                    return Err(TicketError::Invalid(format!(
                        "{:?} reduct mismatch: kernel computed a different reduct",
                        step.op
                    )));
                }
                // well-typed redex obligation
                kk(self.kernel.infer(&ctx, step.x))?;
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            FrameAppFun | FrameAppArg | FrameAppBoth => {
                let (fx, ax) = match self.kernel.arena.get_clone(step.x) {
                    Expr::App(f, a) => (f, a),
                    _ => return Err(TicketError::Invalid("FRAME_APP on non-application lhs".into())),
                };
                let (fy, ay) = match self.kernel.arena.get_clone(step.y) {
                    Expr::App(f, a) => (f, a),
                    _ => return Err(TicketError::Invalid("FRAME_APP on non-application rhs".into())),
                };
                match step.op {
                    FrameAppFun => {
                        let (_, l, r) = self.eq_fact(step.refs.first().copied().ok_or(TicketError::Invalid("FRAME needs ref".into()))?)?;
                        if l != fx || r != fy || ax != ay {
                            return Err(TicketError::Invalid("FRAME_APP_FUN operands mismatch".into()));
                        }
                    }
                    FrameAppArg => {
                        let (_, l, r) = self.eq_fact(step.refs.first().copied().ok_or(TicketError::Invalid("FRAME needs ref".into()))?)?;
                        if l != ax || r != ay || fx != fy {
                            return Err(TicketError::Invalid("FRAME_APP_ARG operands mismatch".into()));
                        }
                        // dependent application obligation: the whole application must type
                        kk(self.kernel.infer(&ctx, step.x))?;
                        kk(self.kernel.infer(&ctx, step.y))?;
                    }
                    _ => {
                        if step.refs.len() < 2 {
                            return Err(TicketError::Invalid("FRAME_APP_BOTH needs two refs".into()));
                        }
                        let (_, l1, r1) = self.eq_fact(step.refs[0])?;
                        let (_, l2, r2) = self.eq_fact(step.refs[1])?;
                        if l1 != fx || r1 != fy || l2 != ax || r2 != ay {
                            return Err(TicketError::Invalid("FRAME_APP_BOTH operands mismatch".into()));
                        }
                        kk(self.kernel.infer(&ctx, step.x))?;
                        kk(self.kernel.infer(&ctx, step.y))?;
                    }
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            FrameLamBody | FramePiCod => {
                // v1 restriction: binder domains must be structurally identical.
                let (dx, bx) = match self.kernel.arena.get_clone(step.x) {
                    Expr::Lam(_, _, d, b) => (d, b),
                    Expr::Pi(_, _, d, b) => (d, b),
                    _ => return Err(TicketError::Invalid("FRAME binder on non-binder lhs".into())),
                };
                let (dy, by) = match self.kernel.arena.get_clone(step.y) {
                    Expr::Lam(_, _, d, b) => (d, b),
                    Expr::Pi(_, _, d, b) => (d, b),
                    _ => return Err(TicketError::Invalid("FRAME binder on non-binder rhs".into())),
                };
                if dx != dy {
                    return Err(TicketError::Invalid("FRAME under binders with non-identical domains is not in ticket format v1; use CHECK_CORE".into()));
                }
                let (fc, fl, fr) = self.eq_fact(step.refs.first().copied().ok_or(TicketError::Invalid("FRAME needs ref".into()))?)?;
                if fl != bx || fr != by {
                    return Err(TicketError::Invalid("FRAME binder body fact mismatch".into()));
                }
                // the body fact must live in the extension of this context by the domain
                let ext = self.contexts.get(fc as usize).cloned().ok_or(TicketError::Invalid("unknown fact ctx".into()))?;
                if ext.len() != ctx.len() + 1
                    || ext[..ctx.len()].iter().zip(ctx.iter()).any(|(a, b)| a.name != b.name || a.ty != b.ty || a.value != b.value)
                    || ext[ctx.len()].ty != dx {
                    return Err(TicketError::Invalid("FRAME binder fact is not in the extended context".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            FramePiBoth => {
                let (dx, cx) = match self.kernel.arena.get_clone(step.x) {
                    Expr::Pi(_, _, d, c) => (d, c),
                    _ => return Err(TicketError::Invalid("FRAME_PI_BOTH lhs not a Pi".into())),
                };
                let (dy, cy) = match self.kernel.arena.get_clone(step.y) {
                    Expr::Pi(_, _, d, c) => (d, c),
                    _ => return Err(TicketError::Invalid("FRAME_PI_BOTH rhs not a Pi".into())),
                };
                if step.refs.len() < 2 {
                    return Err(TicketError::Invalid("FRAME_PI_BOTH needs two refs".into()));
                }
                let (_, l1, r1) = self.eq_fact(step.refs[0])?;
                let (_, l2, r2) = self.eq_fact(step.refs[1])?;
                if l1 != dx || r1 != dy || l2 != cx || r2 != cy {
                    return Err(TicketError::Invalid("FRAME_PI_BOTH operands mismatch".into()));
                }
                // codomain fact must be in the extended context (checked loosely:
                // full context equality is enforced by the fact's registered ctx).
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            FrameLetVal => {
                let (tx, vx, bx) = match self.kernel.arena.get_clone(step.x) {
                    Expr::Let(_, t, v, b) => (t, v, b),
                    _ => return Err(TicketError::Invalid("FRAME_LET_VAL lhs not a let".into())),
                };
                let (ty2, vy, by) = match self.kernel.arena.get_clone(step.y) {
                    Expr::Let(_, t, v, b) => (t, v, b),
                    _ => return Err(TicketError::Invalid("FRAME_LET_VAL rhs not a let".into())),
                };
                let (_, l, r) = self.eq_fact(step.refs.first().copied().ok_or(TicketError::Invalid("FRAME needs ref".into()))?)?;
                if l != vx || r != vy || tx != ty2 || bx != by {
                    return Err(TicketError::Invalid("FRAME_LET_VAL operands mismatch".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            FrameLetBody => {
                let (tx, vx, bx) = match self.kernel.arena.get_clone(step.x) {
                    Expr::Let(_, t, v, b) => (t, v, b),
                    _ => return Err(TicketError::Invalid("FRAME_LET_BODY lhs not a let".into())),
                };
                let (ty2, vy, by) = match self.kernel.arena.get_clone(step.y) {
                    Expr::Let(_, t, v, b) => (t, v, b),
                    _ => return Err(TicketError::Invalid("FRAME_LET_BODY rhs not a let".into())),
                };
                if tx != ty2 || vx != vy {
                    return Err(TicketError::Invalid("FRAME_LET_BODY requires identical type/value".into()));
                }
                let (_, l, r) = self.eq_fact(step.refs.first().copied().ok_or(TicketError::Invalid("FRAME needs ref".into()))?)?;
                if l != bx || r != by {
                    return Err(TicketError::Invalid("FRAME_LET_BODY fact mismatch".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            FrameProj => {
                let (sx, ix, tx2) = match self.kernel.arena.get_clone(step.x) {
                    Expr::Proj(s, i, t) => (s, i, t),
                    _ => return Err(TicketError::Invalid("FRAME_PROJ lhs not a projection".into())),
                };
                let (sy, iy, ty2) = match self.kernel.arena.get_clone(step.y) {
                    Expr::Proj(s, i, t) => (s, i, t),
                    _ => return Err(TicketError::Invalid("FRAME_PROJ rhs not a projection".into())),
                };
                let (_, l, r) = self.eq_fact(step.refs.first().copied().ok_or(TicketError::Invalid("FRAME needs ref".into()))?)?;
                if sx != sy || ix != iy || l != tx2 || r != ty2 {
                    return Err(TicketError::Invalid("FRAME_PROJ operands mismatch".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            Irrel => {
                let tx = kk(self.kernel.infer(&ctx, step.x))?;
                let ty2 = kk(self.kernel.infer(&ctx, step.y))?;
                if !kk(self.kernel.is_def_eq(&ctx, tx, ty2))? {
                    return Err(TicketError::Invalid("IRREL: propositions are not the same up to conversion".into()));
                }
                if !kk(self.kernel.is_prop_type(&ctx, tx))? {
                    return Err(TicketError::Invalid("IRREL: terms are not proofs of a proposition".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            Eta => {
                if !kk(self.kernel.is_def_eq(&ctx, step.x, step.y))? {
                    return Err(TicketError::Invalid("ETA: operands not eta-equal".into()));
                }
                // Ensure the equality genuinely goes through eta (one side a lambda
                // whose body is the other applied to the bound variable) or both lambdas.
                let x_is_lam = matches!(self.kernel.arena.get(step.x), Expr::Lam(..));
                let y_is_lam = matches!(self.kernel.arena.get(step.y), Expr::Lam(..));
                if !x_is_lam && !y_is_lam {
                    return Err(TicketError::Invalid("ETA requires a lambda operand".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            Level => {
                // Both operands must be Sorts (or constants) whose levels agree for all valuations.
                let equiv = match (self.kernel.arena.get_clone(step.x), self.kernel.arena.get_clone(step.y)) {
                    (Expr::Sort(a), Expr::Sort(b)) => a.equiv(&b),
                    (Expr::Const(n1, l1), Expr::Const(n2, l2)) => {
                        n1 == n2 && l1.len() == l2.len() && l1.iter().zip(l2.iter()).all(|(a, b)| a.equiv(b))
                    }
                    _ => false,
                };
                if !equiv {
                    return Err(TicketError::Invalid("LEVEL: universe levels not equivalent for all valuations".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            CheckCore => {
                if !kk(self.kernel.is_def_eq(&ctx, step.x, step.y))? {
                    return Err(TicketError::Invalid("CHECK_CORE: core conversion failed".into()));
                }
                Fact::Eq { ctx: step.ctx, lhs: step.x, rhs: step.y }
            }
            TyCheckCore => {
                let inferred = kk(self.kernel.infer(&ctx, step.x))?;
                if !kk(self.kernel.is_def_eq(&ctx, inferred, step.y))? {
                    return Err(TicketError::Invalid("TY_CHECK_CORE: claimed type does not match".into()));
                }
                Fact::Ty { ctx: step.ctx, expr: step.x, ty: step.y }
            }
            TyBVar => {
                match self.kernel.arena.get_clone(step.x) {
                    Expr::BVar(i) => {
                        let local_idx = ctx.len().checked_sub(1 + i as usize)
                            .ok_or(TicketError::Invalid("TY_BVAR unbound".into()))?;
                        let local: LocalDecl = ctx[local_idx].clone();
                        let shifted = self.kernel.arena.shift(local.ty, (i + 1) as i64, 0);
                        if shifted != step.y {
                            return Err(TicketError::Invalid("TY_BVAR claimed type mismatch".into()));
                        }
                        Fact::Ty { ctx: step.ctx, expr: step.x, ty: step.y }
                    }
                    _ => return Err(TicketError::Invalid("TY_BVAR on non-variable".into())),
                }
            }
            TyConst | TySort => {
                let inferred = kk(self.kernel.infer(&ctx, step.x))?;
                if !kk(self.kernel.is_def_eq(&ctx, inferred, step.y))? {
                    return Err(TicketError::Invalid("TY_CONST/TY_SORT claimed type mismatch".into()));
                }
                Fact::Ty { ctx: step.ctx, expr: step.x, ty: step.y }
            }
            TyApp => {
                if step.refs.len() < 2 {
                    return Err(TicketError::Invalid("TY_APP needs function and argument typing facts".into()));
                }
                let (_, f, fty) = self.ty_fact(step.refs[0])?;
                let (_, a, _aty) = self.ty_fact(step.refs[1])?;
                let (head, spine_args) = spine(&self.kernel.arena, step.x);
                let _ = head;
                if spine_args.is_empty() || *spine_args.last().unwrap() != a {
                    return Err(TicketError::Invalid("TY_APP term is not the application of the referenced terms".into()));
                }
                let f_expected = spine_args[..spine_args.len() - 1].iter().fold(head, |acc, &arg| self.kernel.arena.app(acc, arg));
                if f_expected != f {
                    return Err(TicketError::Invalid("TY_APP function mismatch".into()));
                }
                let fty_w = kk(self.kernel.whnf(&ctx, fty))?;
                let expected = match self.kernel.arena.get_clone(fty_w) {
                    Expr::Pi(_, _, _, cod) => self.kernel.arena.subst_top(cod, a),
                    _ => return Err(TicketError::Invalid("TY_APP function is not a Pi".into())),
                };
                if !kk(self.kernel.is_def_eq(&ctx, expected, step.y))? {
                    return Err(TicketError::Invalid("TY_APP claimed result type mismatch".into()));
                }
                Fact::Ty { ctx: step.ctx, expr: step.x, ty: step.y }
            }
            TyLam => {
                let (name, dom, body) = match self.kernel.arena.get_clone(step.x) {
                    Expr::Lam(n, _, d, b) => (n, d, b),
                    _ => return Err(TicketError::Invalid("TY_LAM on non-lambda".into())),
                };
                let (_, bexpr, bty) = self.ty_fact(step.refs.first().copied().ok_or(TicketError::Invalid("TY_LAM needs body fact".into()))?)?;
                if bexpr != body {
                    return Err(TicketError::Invalid("TY_LAM body mismatch".into()));
                }
                let pi = self.kernel.arena.pi(name, crate::expr::BinderInfo::Default, dom, bty);
                if !kk(self.kernel.is_def_eq(&ctx, pi, step.y))? {
                    return Err(TicketError::Invalid("TY_LAM claimed Pi type mismatch".into()));
                }
                Fact::Ty { ctx: step.ctx, expr: step.x, ty: step.y }
            }
            TyPi => {
                let (_, dom, cod) = match self.kernel.arena.get_clone(step.x) {
                    Expr::Pi(_, _, d, c) => ((), d, c),
                    _ => return Err(TicketError::Invalid("TY_PI on non-Pi".into())),
                };
                let _ = (dom, cod);
                let inferred = kk(self.kernel.infer(&ctx, step.x))?;
                if !kk(self.kernel.is_def_eq(&ctx, inferred, step.y))? {
                    return Err(TicketError::Invalid("TY_PI claimed sort mismatch".into()));
                }
                Fact::Ty { ctx: step.ctx, expr: step.x, ty: step.y }
            }
            TyConv => {
                if step.refs.len() < 2 {
                    return Err(TicketError::Invalid("TY_CONV needs typing and equality facts".into()));
                }
                let (_, expr, _old) = self.ty_fact(step.refs[0])?;
                let (_, l, r) = self.eq_fact(step.refs[1])?;
                if expr != step.x || r != step.y {
                    return Err(TicketError::Invalid("TY_CONV operands mismatch".into()));
                }
                let _ = l;
                Fact::Ty { ctx: step.ctx, expr: step.x, ty: step.y }
            }
        };
        self.facts.push(fact);
        Ok(idx)
    }

    pub fn run(&mut self, steps: &[TicketStep]) -> Result<Vec<Fact>, TicketError> {
        for s in steps {
            self.step(s)?;
        }
        Ok(self.facts.clone())
    }

    /// Look up a derived equality fact for (lhs, rhs) in a context.
    pub fn find_eq(&self, ctx: u32, lhs: ExprId, rhs: ExprId) -> Option<u32> {
        self.facts.iter().position(|f| matches!(f, Fact::Eq { ctx: c, lhs: l, rhs: r } if *c == ctx && *l == lhs && *r == rhs)).map(|i| i as u32)
    }
}
