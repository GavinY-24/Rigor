//! Deterministic tactic suggestions for agent-driven proof search.
//!
//! Suggestions are only producer-side hints. Applying one still elaborates to
//! core terms and is checked by the kernel; a bad suggestion can fail, but it
//! cannot make an invalid proof pass.

use crate::elab::{formula_of, fv, nexpr_to_poly, spine, Elab, Goal};
use rigor_kernel::NExpr;

#[derive(Debug, Clone, PartialEq)]
pub struct Suggestion {
    pub tactic: String,
    pub reason: String,
    /// Higher is more promising. Scores are stable ordering hints only.
    pub score: u32,
}

fn suggestion(tactic: impl Into<String>, reason: impl Into<String>, score: u32) -> Suggestion {
    Suggestion { tactic: tactic.into(), reason: reason.into(), score }
}

fn contains_expr(e: &NExpr, needle: &NExpr) -> bool {
    if e == needle {
        return true;
    }
    match e {
        NExpr::App(f, a) => contains_expr(f, needle) || contains_expr(a, needle),
        NExpr::Pi(_, _, d, c) | NExpr::Lam(_, _, d, c) => contains_expr(d, needle) || contains_expr(c, needle),
        NExpr::Let(_, t, v, b) => contains_expr(t, needle) || contains_expr(v, needle) || contains_expr(b, needle),
        NExpr::Proj(_, _, t) => contains_expr(t, needle),
        _ => false,
    }
}

fn eq_parts(target: &NExpr) -> Option<(NExpr, NExpr, NExpr)> {
    let (head, args) = spine(target);
    match head {
        NExpr::Const(n, _) if n == "Eq" && args.len() == 3 => Some((args[0].clone(), args[1].clone(), args[2].clone())),
        _ => None,
    }
}

fn const_head(target: &NExpr) -> Option<(String, Vec<NExpr>)> {
    let (head, args) = spine(target);
    match head {
        NExpr::Const(n, _) => Some((n, args)),
        _ => None,
    }
}

fn head_const_name(e: &NExpr) -> Option<String> {
    let (head, _) = spine(e);
    match head {
        NExpr::Const(n, _) => Some(n),
        _ => None,
    }
}

fn nat_vars(goal: &Goal) -> Vec<String> {
    goal.ctx
        .iter()
        .filter(|l| matches!(&l.ty, NExpr::Const(n, _) if n == "Nat"))
        .map(|l| l.name.clone())
        .collect()
}

fn bool_vars(goal: &Goal) -> Vec<String> {
    goal.ctx
        .iter()
        .filter(|l| matches!(&l.ty, NExpr::Const(n, _) if n == "Bool"))
        .map(|l| l.name.clone())
        .collect()
}

fn fresh_name(base: &str, goal: &Goal) -> String {
    let mut used: std::collections::HashSet<String> = goal.ctx.iter().map(|l| l.name.clone()).collect();
    used.extend(fv(&goal.target));
    let base = if base == "_" || base.is_empty() { "h" } else { base };
    let mut out = base.to_string();
    let mut i = 1;
    while used.contains(&out) {
        out = format!("{base}{i}");
        i += 1;
    }
    out
}

/// Ranked, deterministic tactics for the focused goal. These are deliberately
/// conservative: certificate suggestions are emitted only when the public
/// solver input parsers accept the goal shape.
pub fn suggest_goal(elab: &Elab, goal: &Goal) -> Vec<Suggestion> {
    let mut out: Vec<Suggestion> = Vec::new();
    let mut push = |s: Suggestion| {
        if !out.iter().any(|old| old.tactic == s.tactic) {
            out.push(s);
        }
    };

    if let Some((ty, lhs, rhs)) = eq_parts(&goal.target) {
        if lhs == rhs {
            push(suggestion("trivial", "both sides of the equality are identical", 100));
        } else {
            push(suggestion("trivial", "reflexivity may close this after kernel reduction", 35));
        }
        if matches!(&ty, NExpr::Const(n, _) if n == "Nat") {
            let vars = nat_vars(goal);
            if nexpr_to_poly(&lhs, &vars).is_ok() && nexpr_to_poly(&rhs, &vars).is_ok() {
                push(suggestion("solve poly", "Nat polynomial identity accepted by the certificate parser", 96));
            }
        }
        if matches!(&ty, NExpr::Const(n, _) if n == "Bool") {
            let vars = bool_vars(goal);
            let false_rhs = matches!(&rhs, NExpr::Const(n, _) if n == "Bool.false");
            if false_rhs && formula_of(&lhs, &vars).is_ok() {
                push(suggestion("solve sat", "Boolean contradiction shape accepted by the SAT certificate parser", 95));
            }
        }
    }

    if matches!(&goal.target, NExpr::Const(n, _) if n == "True") {
        push(suggestion("trivial", "the goal is True", 100));
    }

    for local in &goal.ctx {
        if local.ty == goal.target {
            push(suggestion("assumption", format!("hypothesis '{}' exactly matches the goal", local.name), 98));
        }
        if let Some((_, lhs, rhs)) = eq_parts(&local.ty) {
            if lhs != rhs && contains_expr(&goal.target, &lhs) {
                push(suggestion(
                    format!("rewrite {}", local.name),
                    format!("hypothesis '{}' rewrites a subterm of the goal", local.name),
                    88,
                ));
            }
            if lhs != rhs && contains_expr(&goal.target, &rhs) {
                push(suggestion(
                    format!("rewrite < {}", local.name),
                    format!("the reverse of hypothesis '{}' rewrites a subterm of the goal", local.name),
                    86,
                ));
            }
        }
    }

    if let NExpr::Pi(name, _, _, _) = &goal.target {
        let chosen = fresh_name(name, goal);
        push(suggestion(format!("intro {chosen}"), "the goal is a Pi/implication", 82));
    }

    if let Some((head, _)) = const_head(&goal.target) {
        if head == "Or" {
            push(suggestion("left", "prove the left side of the disjunction", 55));
            push(suggestion("right", "prove the right side of the disjunction", 54));
        } else if head != "Eq" {
            // Eq's single constructor is reflexivity, not a generally useful
            // proof step; `trivial` already covers that case. For other
            // inductives, constructor is a real decomposition choice.
            if let Some(nid) = elab.kernel.names.lookup(&head) {
                if let Some(decl) = elab.kernel.env.get(nid) {
                    if let Some(info) = &decl.inductive {
                        if info.constructors.len() == 1 {
                            push(suggestion("constructor", format!("{head} has one constructor"), 70));
                        } else if !info.constructors.is_empty() {
                            push(suggestion("constructor", format!("try the first constructor of {head}"), 45));
                        }
                    }
                }
            }
        }
    }

    let target_fv = fv(&goal.target);
    let mut induction_candidates: Vec<&str> = Vec::new();
    for local in &goal.ctx {
        if !target_fv.contains(&local.name) {
            continue;
        }
        if let Some(type_head) = head_const_name(&local.ty) {
            if type_head == "Nat" || type_head == "Bool" {
                induction_candidates.push(&local.name);
            }
        }
    }
    if let Some(name) = induction_candidates.first() {
        push(suggestion(format!("induction {name}"), format!("decompose inductively on '{name}'"), 62));
    }

    if goal.ctx.iter().any(|l| l.assuming) {
        push(suggestion("assumption", "an assumption may match after kernel reduction", 30));
    }

    out.sort_by(|a, b| b.score.cmp(&a.score).then_with(|| a.tactic.cmp(&b.tactic)));
    out
}
