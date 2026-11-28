//! Certificate plugins and the standard mathematical library.
//!
//! Plugins may propose witnesses; acceptance always reduces to a core proof
//! rechecked by `rigor-kernel`. A solver returning `true`, a native binary's
//! output, and a hash of a result are never proofs in this crate.

pub mod certificates;
pub mod intervals;
pub mod linarith;
pub mod poly;
pub mod real;
pub mod sat;
pub mod stdlib;

pub use certificates::*;
pub use stdlib::{bootstrap_kernel, Stdlib};
