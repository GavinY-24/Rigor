//! Bridges between Rigor and the outside world: the pinned Lean 4
//! core-declaration exchange format (`.rigx`), semantic bundle diffing,
//! and the core-derived audit view.
//!
//! Import trust rule: an imported artifact is only ever *input data*.
//! Third-party receipts, verdicts, or hashes inside an exchange file are
//! ignored — the imported declarations are re-admitted by the kernel and
//! the resulting bundle stands or falls by the runtime verifier.

pub mod diff;
pub mod exchange;
pub mod explain;

pub use diff::{diff_bundles, render_diff, ChangeKind, DeclChange, DiffReport, Reuse};
pub use exchange::{export_bundle_exchange, export_exchange, import_exchange, FeatureMatrix, Imported};
pub use explain::{assumption_closure, explain, pretty_term, ExplainOpts};
