//! Parallel DAG verification scheduler, atomic commit, assumption-policy
//! checking, and the VerificationKey-bound incremental cache (§5.2).
//!
//! No provisional theorem is ever exposed in the environment used to approve
//! its own proof: workers verify against dependency closures admitted in
//! topological order, and results are committed atomically only for roots
//! whose whole closure passed.

pub mod cache;
pub mod receipt;
pub mod verify;

pub use cache::{IfaceCache, VerifyCache};
pub use receipt::{Receipt, RootReceipt};
pub use verify::{verify_bundle, VerifyOptions};
