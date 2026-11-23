//! Named intermediate terms and lowering to de Bruijn core expressions.
//! This builder is what recursor generation, the elaborator, and certificate
//! proof-term constructors use, so binder handling lives in exactly one place.

use crate::expr::{BinderInfo, Expr, ExprArena, ExprId, Name, NameArena, NameId};
use crate::level::Level;
use rigor_spec::BigUint;

#[derive(Debug, Clone, PartialEq)]
pub enum NExpr {
    Var(String),
    Const(String, Vec<Level>),
    Sort(Level),
    Pi(String, BinderInfo, Box<NExpr>, Box<NExpr>),
    Lam(String, BinderInfo, Box<NExpr>, Box<NExpr>),
    App(Box<NExpr>, Box<NExpr>),
    Let(String, Box<NExpr>, Box<NExpr>, Box<NExpr>),
    Proj(String, u32, Box<NExpr>),
    LitNat(BigUint),
    LitStr(String),
}

impl NExpr {
    pub fn var(s: &str) -> Self {
        NExpr::Var(s.to_string())
    }
    pub fn const_(s: &str) -> Self {
        NExpr::Const(s.to_string(), Vec::new())
    }
    pub fn const_levels(s: &str, levels: Vec<Level>) -> Self {
        NExpr::Const(s.to_string(), levels)
    }
    pub fn app(f: NExpr, a: NExpr) -> Self {
        NExpr::App(Box::new(f), Box::new(a))
    }
    pub fn apps(f: NExpr, args: &[NExpr]) -> NExpr {
        let mut cur = f;
        for a in args {
            cur = NExpr::app(cur, a.clone());
        }
        cur
    }
    pub fn pi(name: &str, dom: NExpr, cod: NExpr) -> Self {
        NExpr::Pi(name.to_string(), BinderInfo::Default, Box::new(dom), Box::new(cod))
    }
    pub fn lam(name: &str, dom: NExpr, body: NExpr) -> Self {
        NExpr::Lam(name.to_string(), BinderInfo::Default, Box::new(dom), Box::new(body))
    }
    pub fn sort(l: Level) -> Self {
        NExpr::Sort(l)
    }
    pub fn prop() -> Self {
        NExpr::Sort(Level::Zero)
    }
    pub fn type0() -> Self {
        NExpr::Sort(Level::Succ(Box::new(Level::Zero)))
    }
}

#[derive(Debug, Clone)]
pub struct LowerError(pub String);

pub fn lower(
    arena: &mut ExprArena,
    names: &mut NameArena,
    scope: &mut Vec<String>,
    e: &NExpr,
) -> Result<ExprId, LowerError> {
    match e {
        NExpr::Var(s) => {
            // scope is outermost-first; de Bruijn index counts from the innermost.
            for (i, name) in scope.iter().rev().enumerate() {
                if name == s {
                    return Ok(arena.bvar(i as u32));
                }
            }
            Err(LowerError(format!("unbound variable '{s}' in scope {scope:?}")))
        }
        NExpr::Const(s, levels) => {
            let id = names.intern(Name::from_dotted(s));
            Ok(arena.const_(id, levels.clone()))
        }
        NExpr::Sort(l) => Ok(arena.sort(l.clone())),
        NExpr::Pi(name, info, dom, cod) => {
            let d = lower(arena, names, scope, dom)?;
            scope.push(name.clone());
            let c = lower(arena, names, scope, cod);
            scope.pop();
            let c = c?;
            let nid = names.intern(Name::root(name));
            Ok(arena.pi(nid, *info, d, c))
        }
        NExpr::Lam(name, info, dom, body) => {
            let d = lower(arena, names, scope, dom)?;
            scope.push(name.clone());
            let b = lower(arena, names, scope, body);
            scope.pop();
            let b = b?;
            let nid = names.intern(Name::root(name));
            Ok(arena.lam(nid, *info, d, b))
        }
        NExpr::App(f, a) => {
            let f2 = lower(arena, names, scope, f)?;
            let a2 = lower(arena, names, scope, a)?;
            Ok(arena.app(f2, a2))
        }
        NExpr::Let(name, ty, val, body) => {
            let t = lower(arena, names, scope, ty)?;
            let v = lower(arena, names, scope, val)?;
            scope.push(name.clone());
            let b = lower(arena, names, scope, body);
            scope.pop();
            let b = b?;
            let nid = names.intern(Name::root(name));
            Ok(arena.intern(Expr::Let(nid, t, v, b)))
        }
        NExpr::Proj(s, idx, t) => {
            let t2 = lower(arena, names, scope, t)?;
            let sid = names.intern(Name::from_dotted(s));
            Ok(arena.intern(Expr::Proj(sid, *idx, t2)))
        }
        NExpr::LitNat(n) => Ok(arena.intern(Expr::LitNat(n.clone()))),
        NExpr::LitStr(s) => Ok(arena.intern(Expr::LitStr(s.clone()))),
    }
}

pub fn lower_closed(arena: &mut ExprArena, names: &mut NameArena, e: &NExpr) -> Result<ExprId, LowerError> {
    lower(arena, names, &mut Vec::new(), e)
}

/// Decompile a core expression back to named form under `scope`
/// (outermost-first display names, invented where binders are anonymous).
pub fn to_named(arena: &ExprArena, names: &NameArena, e: ExprId, scope: &mut Vec<String>) -> NExpr {
    match arena.get_clone(e) {
        Expr::BVar(i) => {
            let idx = scope.len().saturating_sub(1 + i as usize);
            let name = scope.get(idx).cloned().unwrap_or_else(|| format!("x{}", i));
            NExpr::Var(name)
        }
        Expr::Const(n, levels) => NExpr::Const(names.display(n), levels),
        Expr::Sort(l) => NExpr::Sort(l),
        Expr::Pi(n, info, d, c) => {
            let dn = to_named(arena, names, d, scope);
            let binder = binder_name(names, n, scope.len());
            scope.push(binder.clone());
            let cn = to_named(arena, names, c, scope);
            scope.pop();
            NExpr::Pi(binder, info, Box::new(dn), Box::new(cn))
        }
        Expr::Lam(n, info, d, b) => {
            let dn = to_named(arena, names, d, scope);
            let binder = binder_name(names, n, scope.len());
            scope.push(binder.clone());
            let bn = to_named(arena, names, b, scope);
            scope.pop();
            NExpr::Lam(binder, info, Box::new(dn), Box::new(bn))
        }
        Expr::App(f, a) => {
            let f2 = to_named(arena, names, f, scope);
            let a2 = to_named(arena, names, a, scope);
            NExpr::app(f2, a2)
        }
        Expr::Let(n, t, v, b) => {
            let tn = to_named(arena, names, t, scope);
            let vn = to_named(arena, names, v, scope);
            let binder = binder_name(names, n, scope.len());
            scope.push(binder.clone());
            let bn = to_named(arena, names, b, scope);
            scope.pop();
            NExpr::Let(binder, Box::new(tn), Box::new(vn), Box::new(bn))
        }
        Expr::Proj(s, i, t) => {
            let tn = to_named(arena, names, t, scope);
            NExpr::Proj(names.display(s), i, Box::new(tn))
        }
        Expr::LitNat(n) => NExpr::LitNat(n),
        Expr::LitStr(s) => NExpr::LitStr(s),
    }
}

fn binder_name(names: &NameArena, n: NameId, depth: usize) -> String {
    let dotted = names.display(n);
    let last = dotted.rsplit('.').next().unwrap_or("x").to_string();
    if last.is_empty() || last == "_" {
        format!("x{depth}")
    } else {
        last
    }
}

/// Human-readable rendering of a core expression (presentation only; never semantics).
pub fn pretty(arena: &ExprArena, names: &NameArena, e: ExprId) -> String {
    let named = to_named(arena, names, e, &mut Vec::new());
    pretty_named(&named)
}

pub fn pretty_named(e: &NExpr) -> String {
    match e {
        NExpr::Var(s) => s.clone(),
        NExpr::Const(s, levels) => {
            if levels.is_empty() {
                s.clone()
            } else {
                format!(
                    "{}.{{{}}}",
                    s,
                    levels.iter().map(|l| l.to_string()).collect::<Vec<_>>().join(", ")
                )
            }
        }
        NExpr::Sort(l) => match l {
            Level::Zero => "Prop".to_string(),
            Level::Succ(inner) if **inner == Level::Zero => "Type".to_string(),
            _ => format!("Sort {l}"),
        },
        NExpr::Pi(name, _, dom, cod) => {
            // render non-dependent arrows compactly
            if !contains_var(cod, name) {
                format!("({} -> {})", pretty_named(dom), pretty_named(cod))
            } else {
                format!("(forall {name} : {}, {})", pretty_named(dom), pretty_named(cod))
            }
        }
        NExpr::Lam(name, _, dom, body) => {
            format!("(fun {name} : {} => {})", pretty_named(dom), pretty_named(body))
        }
        NExpr::App(f, a) => format!("({} {})", pretty_named(f), pretty_named(a)),
        NExpr::Let(name, ty, val, body) => {
            format!("(let {name} : {} := {} in {})", pretty_named(ty), pretty_named(val), pretty_named(body))
        }
        NExpr::Proj(s, i, t) => format!("{}.proj{i}({})", s, pretty_named(t)),
        NExpr::LitNat(n) => n.decimal(),
        NExpr::LitStr(s) => format!("{s:?}"),
    }
}

fn contains_var(e: &NExpr, name: &str) -> bool {
    match e {
        NExpr::Var(s) => s == name,
        NExpr::App(f, a) => contains_var(f, name) || contains_var(a, name),
        NExpr::Pi(n, _, d, c) | NExpr::Lam(n, _, d, c) => {
            contains_var(d, name) || (n != name && contains_var(c, name))
        }
        NExpr::Let(n, t, v, b) => {
            contains_var(t, name) || contains_var(v, name) || (n != name && contains_var(b, name))
        }
        NExpr::Proj(_, _, t) => contains_var(t, name),
        _ => false,
    }
}
