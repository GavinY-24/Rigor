//! Core-derived review/audit view (`rigor explain`).
//!
//! Everything shown here is recomputed from the bundle's core terms:
//! statements are rendered from the term table, assumptions are the
//! transitive axiom/quotient closure over actual term references, and
//! coercions are the recorded conversion tickets. Nothing is taken from
//! producer commentary (which is excluded from all content hashes).

use rigor_codec::{evidence_id_for, statement_ids, Bundle, LevelNode, TermNode};
use rigor_runtime::Receipt;
use rigor_spec::abi::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, Default)]
pub struct ExplainOpts {
    pub assumptions: bool,
    pub coercions: bool,
    pub statements: bool,
}

fn level_string(bundle: &Bundle, idx: u32) -> String {
    match &bundle.levels[idx as usize] {
        LevelNode::Zero => "0".into(),
        LevelNode::Succ(a) => format!("({} + 1)", level_string(bundle, *a)),
        LevelNode::Max(a, b) => format!("max {} {}", level_string(bundle, *a), level_string(bundle, *b)),
        LevelNode::IMax(a, b) => format!("imax {} {}", level_string(bundle, *a), level_string(bundle, *b)),
        LevelNode::Param(i) => format!("u{i}"),
    }
}

fn binder_display(bundle: &Bundle, name_idx: u32, depth: usize) -> String {
    let dotted = bundle.name_string(name_idx);
    let last = dotted.rsplit('.').next().unwrap_or("x").to_string();
    if last.is_empty() || last == "_" {
        format!("x{depth}")
    } else {
        last
    }
}

/// Render a bundle term with de Bruijn binders shown by name.
pub fn pretty_term(bundle: &Bundle, term: u32, scope: &mut Vec<String>) -> String {
    match &bundle.terms[term as usize] {
        TermNode::BVar(i) => {
            let pos = scope.len().saturating_sub(1 + *i as usize);
            scope.get(pos).cloned().unwrap_or_else(|| format!("x{i}"))
        }
        TermNode::Const(n, levels) => {
            let name = bundle.name_string(*n);
            if levels.is_empty() {
                name
            } else {
                let ls: Vec<String> = levels.iter().map(|l| level_string(bundle, *l)).collect();
                format!("{}.{{{}}}", name, ls.join(", "))
            }
        }
        TermNode::Sort(l) => match &bundle.levels[*l as usize] {
            LevelNode::Zero => "Prop".into(),
            LevelNode::Succ(a) if matches!(&bundle.levels[*a as usize], LevelNode::Zero) => "Type".into(),
            _ => format!("Sort {}", level_string(bundle, *l)),
        },
        TermNode::Pi(n, _, d, c) => {
            let dn = pretty_term(bundle, *d, scope);
            let bname = binder_display(bundle, *n, scope.len());
            scope.push(bname.clone());
            let cn = pretty_term(bundle, *c, scope);
            scope.pop();
            format!("(forall {bname} : {dn}, {cn})")
        }
        TermNode::Lam(n, _, d, b) => {
            let dn = pretty_term(bundle, *d, scope);
            let bname = binder_display(bundle, *n, scope.len());
            scope.push(bname.clone());
            let bn = pretty_term(bundle, *b, scope);
            scope.pop();
            format!("(fun {bname} : {dn} => {bn})")
        }
        TermNode::App(f, a) => {
            format!("({} {})", pretty_term(bundle, *f, scope), pretty_term(bundle, *a, scope))
        }
        TermNode::Let(n, t, v, b) => {
            let tn = pretty_term(bundle, *t, scope);
            let vn = pretty_term(bundle, *v, scope);
            let bname = binder_display(bundle, *n, scope.len());
            scope.push(bname.clone());
            let bn = pretty_term(bundle, *b, scope);
            scope.pop();
            format!("(let {bname} : {tn} := {vn} in {bn})")
        }
        TermNode::Proj(s, i, t) => format!("{}.proj{}({})", bundle.name_string(*s), i, pretty_term(bundle, *t, scope)),
        TermNode::LitNat(n) => n.decimal(),
        TermNode::LitStr(s) => format!("{s:?}"),
    }
}

fn term_consts(bundle: &Bundle, term: u32, out: &mut BTreeSet<u32>, visited: &mut BTreeSet<u32>) {
    if !visited.insert(term) {
        return;
    }
    match &bundle.terms[term as usize] {
        TermNode::Const(name, _) => {
            out.insert(*name);
        }
        TermNode::App(f, a) => {
            term_consts(bundle, *f, out, visited);
            term_consts(bundle, *a, out, visited);
        }
        TermNode::Pi(_, _, d, c) | TermNode::Lam(_, _, d, c) => {
            term_consts(bundle, *d, out, visited);
            term_consts(bundle, *c, out, visited);
        }
        TermNode::Let(_, t, v, b) => {
            term_consts(bundle, *t, out, visited);
            term_consts(bundle, *v, out, visited);
            term_consts(bundle, *b, out, visited);
        }
        TermNode::Proj(_, _, t) => term_consts(bundle, *t, out, visited),
        _ => {}
    }
}

/// Transitive assumption closure of a root: axioms referenced (directly or
/// through other declarations) by the root's statement and proof, plus
/// whether quotient computation is used anywhere in the closure.
pub fn assumption_closure(bundle: &Bundle, root_name_idx: u32) -> (Vec<String>, bool) {
    let by_name: BTreeMap<u32, &rigor_codec::PortableDecl> = bundle
        .declarations
        .iter()
        .map(|d| (d.name, d))
        .collect();
    let mut axioms: BTreeSet<String> = BTreeSet::new();
    let mut quot = false;
    let mut seen: BTreeSet<u32> = BTreeSet::new();
    let mut stack = vec![root_name_idx];
    while let Some(n) = stack.pop() {
        if !seen.insert(n) {
            continue;
        }
        let name = bundle.name_string(n);
        if name.starts_with("Quot.") {
            quot = true;
        }
        if let Some(decl) = by_name.get(&n) {
            if decl.kind == DECL_AXIOM {
                axioms.insert(name.clone());
            }
            let mut refs = BTreeSet::new();
            let mut visited = BTreeSet::new();
            term_consts(bundle, decl.ty, &mut refs, &mut visited);
            if let Some(v) = decl.value {
                term_consts(bundle, v, &mut refs, &mut visited);
            }
            for c in &decl.constructors {
                term_consts(bundle, c.ty, &mut refs, &mut visited);
            }
            for r in refs {
                stack.push(r);
            }
        }
    }
    (axioms.into_iter().collect(), quot)
}

pub fn explain(bundle: &Bundle, receipt: Option<&Receipt>, opts: ExplainOpts) -> String {
    let sids = statement_ids(bundle);
    let mut out = String::new();
    out.push_str(&format!("bundle: profile {} declarations {} terms {}\n", bundle.profile, bundle.declarations.len(), bundle.terms.len()));
    if let Some(r) = receipt {
        out.push_str(&format!(
            "receipt: verdict {:?} checker {} policy {} key {} workers {}\n",
            r.verdict, r.checker_build, r.policy, r.verification_key, r.workers
        ));
    }
    // Ticket / coercion summary.
    if opts.coercions {
        let mut hist: BTreeMap<String, usize> = BTreeMap::new();
        for t in &bundle.tickets {
            let name = rigor_spec::TicketOpcode::from_byte(t.op)
                .map(|op| format!("{op:?}"))
                .unwrap_or_else(|| format!("unknown({:#x})", t.op));
            *hist.entry(name).or_default() += 1;
        }
        out.push_str(&format!("conversion tickets: {} total across {} registered contexts\n", bundle.tickets.len(), bundle.contexts.len()));
        for (k, v) in &hist {
            out.push_str(&format!("  {k}: {v}\n"));
        }
    }
    for root in &bundle.roots {
        let name = bundle.name_string(*root);
        out.push_str(&format!("\nroot {name}\n"));
        if let Some(sid) = sids.get(&name) {
            out.push_str(&format!("  statement-id: {}\n", sid.to_hex()));
            let eid = evidence_id_for(bundle, &name, sid);
            out.push_str(&format!("  evidence-id: {}\n", eid.to_hex()));
        }
        if let Some(r) = receipt {
            if let Some(rr) = r.roots.iter().find(|x| x.name == name) {
                out.push_str(&format!("  verdict: {:?}\n", rr.verdict));
                if let Some(d) = &rr.diagnostic {
                    out.push_str(&format!("  diagnostic: {d}\n"));
                }
            }
        }
        if opts.statements {
            if let Some(decl) = bundle.declarations.iter().find(|d| d.name == *root) {
                out.push_str(&format!("  statement: {}\n", pretty_term(bundle, decl.ty, &mut Vec::new())));
            }
        }
        if opts.assumptions {
            let (axioms, quot) = assumption_closure(bundle, *root);
            if axioms.is_empty() {
                out.push_str("  assumptions: none (no axioms in the transitive closure)\n");
            } else {
                out.push_str(&format!("  assumptions: {}\n", axioms.join(", ")));
            }
            out.push_str(&format!("  quotient computation used: {quot}\n"));
        }
    }
    out
}
