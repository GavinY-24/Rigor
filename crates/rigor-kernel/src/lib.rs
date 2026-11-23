//! Rigor L36 trusted kernel.
//!
//! Trusted components: decoder-adjacent arenas, levels, typing, conversion,
//! declaration admission, inductive/recursor generation, quotients, and
//! ticket replay. UI, search, solvers, and learned heuristics live outside
//! this crate and can never influence a verdict except through rechecked
//! core terms and tickets.

pub mod builder;
pub mod check;
pub mod env;
pub mod expr;
pub mod level;
pub mod ticket;

pub use builder::{lower, lower_closed, pretty, to_named, NExpr};
pub use check::{Budget, Context, InductiveSpec, Kernel, KernelError, KResult, LocalDecl};
pub use env::{CtorInfo, Decl, DeclKind, Env, InductiveInfo, RecursorInfo, Reducibility};
pub use expr::{pi_telescope, spine, BinderInfo, Expr, ExprArena, ExprId, Name, NameArena, NameId, NamePart};
pub use level::Level;
pub use ticket::{Fact, TicketError, TicketStep, TicketVerifier};
