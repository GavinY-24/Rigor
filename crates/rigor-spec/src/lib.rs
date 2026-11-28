//! Rigor 1.0 specification crate: frozen ABI, SHA-256, arbitrary precision
//! arithmetic, assumption policies, content-addressed identifiers, and the
//! pure reference level semantics. No production search lives here.

pub mod abi;
pub mod bigint;
pub mod ids;
pub mod policy;
pub mod reference;
pub mod sha256;

pub use abi::*;
pub use bigint::{BigInt, BigRat, BigUint};
pub use ids::{ChallengeId, EvidenceId, InterfaceKey, StatementId, VerificationKey};
pub use policy::{Policy, PolicyError};
pub use sha256::{sha256, Sha256};
