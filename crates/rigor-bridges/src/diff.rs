//! Semantic diff between two bundles, keyed by StatementId.
//!
//! Reuse rules (mirroring the runtime's cache discipline):
//! - identical StatementId                     -> full reuse;
//! - a theorem/opaque whose *statement* is
//!   unchanged but whose proof changed         -> interface-only reuse: the
//!   interface (statement) is intact, dependent proofs keep working, only
//!   the proof body must be rechecked;
//! - a transparent definition (or inductive)
//!   whose content changed                     -> semantic invalidation:
//!   every declaration that transitively references it must be rechecked,
//!   because unfolding may expose the change anywhere.

use rigor_codec::{statement_ids, Bundle, TermNode};
use rigor_spec::abi::*;
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChangeKind {
    Added,
    Removed,
    Unchanged,
    /// Statement identical, proof body changed (opaque declarations only).
    ProofRepaired,
    /// Transparent definition changed: dependents invalidated.
    TransparentChanged,
    /// Statement (type) changed.
    StatementChanged,
    /// Declaration kind changed.
    KindChanged,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reuse {
    Full,
    InterfaceOnly,
    None,
}

#[derive(Debug, Clone)]
pub struct DeclChange {
    pub name: String,
    pub kind: ChangeKind,
    pub reuse: Reuse,
    pub old_statement: Option<String>,
    pub new_statement: Option<String>,
    /// Declarations in the *new* bundle invalidated by this change.
    pub invalidated: Vec<String>,
}

#[derive(Debug, Clone, Default)]
pub struct DiffReport {
    pub changes: Vec<DeclChange>,
    pub added: usize,
    pub removed: usize,
    pub unchanged: usize,
    pub proof_repaired: usize,
    pub invalidated_total: usize,
}

/// Constant names referenced by a bundle term table entry (transitively
/// through the acyclic term graph).
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

fn decl_deps(bundle: &Bundle, decl: &rigor_codec::PortableDecl) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut visited = BTreeSet::new();
    term_consts(bundle, decl.ty, &mut out, &mut visited);
    if let Some(v) = decl.value {
        term_consts(bundle, v, &mut out, &mut visited);
    }
    for c in &decl.constructors {
        term_consts(bundle, c.ty, &mut out, &mut visited);
    }
    out.iter().map(|i| bundle.name_string(*i)).collect()
}

/// Transitive dependents of `name` in the new bundle (reverse closure).
fn dependents_of(bundle: &Bundle, name: &str) -> Vec<String> {
    let mut rev: HashMap<String, Vec<String>> = HashMap::new();
    for d in &bundle.declarations {
        let dn = bundle.name_string(d.name);
        for dep in decl_deps(bundle, d) {
            rev.entry(dep).or_default().push(dn.clone());
        }
    }
    let mut out = BTreeSet::new();
    let mut stack = vec![name.to_string()];
    while let Some(n) = stack.pop() {
        if let Some(users) = rev.get(&n) {
            for u in users {
                if out.insert(u.clone()) {
                    stack.push(u.clone());
                }
            }
        }
    }
    out.into_iter().collect()
}

pub fn diff_bundles(old: &Bundle, new: &Bundle) -> DiffReport {
    let old_ids = statement_ids(old);
    let new_ids = statement_ids(new);
    let old_decls: BTreeMap<String, &rigor_codec::PortableDecl> = old
        .declarations
        .iter()
        .map(|d| (old.name_string(d.name), d))
        .collect();
    let new_decls: BTreeMap<String, &rigor_codec::PortableDecl> = new
        .declarations
        .iter()
        .map(|d| (new.name_string(d.name), d))
        .collect();
    let mut report = DiffReport::default();
    let mut names: BTreeSet<&String> = BTreeSet::new();
    names.extend(old_decls.keys());
    names.extend(new_decls.keys());
    for name in names {
        let o = old_decls.get(name);
        let n = new_decls.get(name);
        let (kind, reuse) = match (o, n) {
            (None, Some(_)) => {
                report.added += 1;
                (ChangeKind::Added, Reuse::None)
            }
            (Some(_), None) => {
                report.removed += 1;
                (ChangeKind::Removed, Reuse::None)
            }
            (Some(od), Some(nd)) => {
                if od.kind != nd.kind {
                    (ChangeKind::KindChanged, Reuse::None)
                } else if old_ids.get(name) == new_ids.get(name) {
                    if od.value != nd.value && od.kind != DECL_DEF {
                        // Same statement, new proof body: dependents reuse
                        // the interface; only this proof is rechecked.
                        report.proof_repaired += 1;
                        (ChangeKind::ProofRepaired, Reuse::InterfaceOnly)
                    } else {
                        report.unchanged += 1;
                        (ChangeKind::Unchanged, Reuse::Full)
                    }
                } else if od.kind == DECL_DEF || od.kind == DECL_INDUCTIVE {
                    (ChangeKind::TransparentChanged, Reuse::None)
                } else if od.ty == nd.ty {
                    // Same statement term, different proof/evidence: the
                    // interface is reusable, the proof must be rechecked.
                    report.proof_repaired += 1;
                    (ChangeKind::ProofRepaired, Reuse::InterfaceOnly)
                } else {
                    (ChangeKind::StatementChanged, Reuse::None)
                }
            }
            (None, None) => unreachable!(),
        };
        let invalidated = match kind {
            ChangeKind::TransparentChanged | ChangeKind::StatementChanged | ChangeKind::KindChanged | ChangeKind::Removed => {
                dependents_of(new, name)
            }
            _ => Vec::new(),
        };
        report.invalidated_total += invalidated.len();
        report.changes.push(DeclChange {
            name: name.clone(),
            kind,
            reuse,
            old_statement: old_ids.get(name).map(|s| s.to_hex()),
            new_statement: new_ids.get(name).map(|s| s.to_hex()),
            invalidated,
        });
    }
    report
}

pub fn render_diff(report: &DiffReport) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "semantic diff: {} added, {} removed, {} unchanged, {} proof-repaired, {} invalidated dependents\n",
        report.added, report.removed, report.unchanged, report.proof_repaired, report.invalidated_total
    ));
    for c in &report.changes {
        if c.kind == ChangeKind::Unchanged {
            continue;
        }
        out.push_str(&format!(
            "{:?} {} (reuse: {:?}) old={} new={}\n",
            c.kind,
            c.name,
            c.reuse,
            c.old_statement.as_deref().unwrap_or("-"),
            c.new_statement.as_deref().unwrap_or("-")
        ));
        if !c.invalidated.is_empty() {
            out.push_str(&format!("  invalidated: {}\n", c.invalidated.join(", ")));
        }
    }
    out
}
