//! Strict canonical RIGB1 (.rigorb) / RIGC1 (.rigorc) codec and
//! content-addressed identifiers. Hash canonical *uncompressed* payloads;
//! bounds are checked before allocation; unknown mandatory tags, invalid
//! UTF-8, trailing payload, out-of-bounds indices and non-backward
//! references are all rejected.

pub mod bundle;
pub mod challenge;
pub mod ids_compute;
pub mod leb;

pub use bundle::*;
pub use challenge::*;
pub use ids_compute::*;
