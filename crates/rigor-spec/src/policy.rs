//! Assumption policies (§5.3, §6). Named manifests are exact declaration sets,
//! not displayed names.

use crate::sha256::domain_hash;
use crate::DOMAIN_POLICY_ID;
use std::collections::BTreeSet;
use std::fmt;

pub const CHOICE_AXIOM: &str = "Classical.choice";
pub const PROPEXT_AXIOM: &str = "propext";
pub const QUOT_SOUND_AXIOM: &str = "Quot.sound";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Policy {
    pub name: String,
    /// Fully qualified axiom constant names permitted transitively.
    pub allowed_axioms: BTreeSet<String>,
    pub allow_quot: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolicyError(pub String);

impl fmt::Display for PolicyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "policy error: {}", self.0)
    }
}
impl std::error::Error for PolicyError {}

impl Policy {
    /// Constructive: no user axioms. Proof irrelevance remains a kernel rule of L36.
    pub fn constructive() -> Self {
        Self {
            name: "constructive".to_string(),
            allowed_axioms: BTreeSet::new(),
            allow_quot: true, // quotient is a primitive package, reported separately
        }
    }

    /// Classical: choice + propositional extensionality, quotient allowed. All reported.
    pub fn classical() -> Self {
        let mut allowed = BTreeSet::new();
        allowed.insert(CHOICE_AXIOM.to_string());
        allowed.insert(PROPEXT_AXIOM.to_string());
        allowed.insert(QUOT_SOUND_AXIOM.to_string());
        Self { name: "classical".to_string(), allowed_axioms: allowed, allow_quot: true }
    }

    pub fn custom(name: &str, axioms: impl IntoIterator<Item = String>, allow_quot: bool) -> Self {
        Self {
            name: name.to_string(),
            allowed_axioms: axioms.into_iter().collect(),
            allow_quot,
        }
    }

    pub fn allows_axiom(&self, name: &str) -> bool {
        self.allowed_axioms.contains(name)
    }

    pub fn allows_choice(&self) -> bool {
        self.allows_axiom(CHOICE_AXIOM)
    }
    pub fn allows_propext(&self) -> bool {
        self.allows_axiom(PROPEXT_AXIOM)
    }

    /// Canonical bytes: name, sorted axioms, quot flag, bootstrap/profile binding added by callers.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(self.name.as_bytes());
        out.push(0);
        for a in &self.allowed_axioms {
            out.extend_from_slice(a.as_bytes());
            out.push(0);
        }
        out.push(0xff);
        out.push(if self.allow_quot { 1 } else { 0 });
        out
    }

    pub fn policy_id(&self) -> [u8; 32] {
        domain_hash(DOMAIN_POLICY_ID, &[&self.canonical_bytes()])
    }

    pub fn parse(name: &str) -> Result<Self, PolicyError> {
        match name {
            "constructive" => Ok(Self::constructive()),
            "classical" => Ok(Self::classical()),
            other => Err(PolicyError(format!("unknown policy '{other}' (expected constructive|classical)"))),
        }
    }
}
