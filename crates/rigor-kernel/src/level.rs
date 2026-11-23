//! Universe levels for L36: 0, parameters, succ, max, imax.
//! Equivalence of open levels must hold for all assignments.

use rigor_spec::reference::{LevelAtom, RefLevel};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
    Param(u32),
}

impl Level {
    pub fn zero() -> Self {
        Level::Zero
    }
    pub fn succ(self) -> Self {
        Level::Succ(Box::new(self))
    }
    pub fn max(self, o: Self) -> Self {
        Level::Max(Box::new(self), Box::new(o))
    }
    pub fn imax(self, o: Self) -> Self {
        Level::IMax(Box::new(self), Box::new(o))
    }
    pub fn param(i: u32) -> Self {
        Level::Param(i)
    }

    pub fn to_ref(&self) -> RefLevel {
        match self {
            Level::Zero => RefLevel::zero(),
            Level::Succ(l) => l.to_ref().succ(),
            Level::Max(a, b) => a.to_ref().lmax(&b.to_ref()),
            Level::IMax(a, b) => a.to_ref().imax(&b.to_ref()),
            Level::Param(p) => RefLevel::param(*p),
        }
    }

    /// Equivalence for *all* valuations of the parameters.
    pub fn equiv(&self, other: &Level) -> bool {
        self.to_ref() == other.to_ref()
    }

    pub fn is_zero(&self) -> bool {
        self.to_ref().is_zero()
    }

    /// Substitute level parameters: `subst[i]` replaces `Param(i)`.
    pub fn subst(&self, subst: &[Level]) -> Level {
        match self {
            Level::Zero => Level::Zero,
            Level::Succ(l) => Level::Succ(Box::new(l.subst(subst))),
            Level::Max(a, b) => Level::Max(Box::new(a.subst(subst)), Box::new(b.subst(subst))),
            Level::IMax(a, b) => Level::IMax(Box::new(a.subst(subst)), Box::new(b.subst(subst))),
            Level::Param(p) => subst
                .get(*p as usize)
                .cloned()
                .unwrap_or_else(|| Level::Param(*p)),
        }
    }

    pub fn max_param(&self) -> Option<u32> {
        match self {
            Level::Zero => None,
            Level::Succ(l) => l.max_param(),
            Level::Max(a, b) | Level::IMax(a, b) => match (a.max_param(), b.max_param()) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (x, y) => x.or(y),
            },
            Level::Param(p) => Some(*p),
        }
    }

    pub fn validate(&self, num_params: u32) -> Result<(), String> {
        if let Some(p) = self.max_param() {
            if p >= num_params {
                return Err(format!(
                    "level parameter {p} out of scope (declaration has {num_params} universe parameters)"
                ));
            }
        }
        Ok(())
    }

    /// Evaluate under a concrete assignment (used by the reference checker and tests).
    pub fn eval(&self, assign: &[u32]) -> u32 {
        self.to_ref().eval(assign)
    }

    pub fn atoms_debug(&self) -> Vec<LevelAtom> {
        self.to_ref().atoms
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Level::Zero => write!(f, "0"),
            Level::Succ(l) => write!(f, "succ {l}"),
            Level::Max(a, b) => write!(f, "max {a} {b}"),
            Level::IMax(a, b) => write!(f, "imax {a} {b}"),
            Level::Param(p) => write!(f, "u{p}"),
        }
    }
}

/// Sort of a Pi type: imax(u, v) where domain : Sort u and codomain : Sort v.
pub fn sort_of_pi(u: &Level, v: &Level) -> Level {
    Level::IMax(Box::new(u.clone()), Box::new(v.clone()))
}
