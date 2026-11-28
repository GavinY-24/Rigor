//! Three distinct content-addressed identifiers (§5.1) plus challenge/interface keys.

use crate::sha256::{domain_hash, to_hex};
use crate::{
    DOMAIN_CHALLENGE_ID, DOMAIN_EVIDENCE_ID, DOMAIN_IFACE_CACHE_KEY, DOMAIN_STATEMENT_ID,
    DOMAIN_VERIFICATION_KEY,
};
use std::fmt;

macro_rules! id_type {
    ($name:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub [u8; 32]);

        impl $name {
            pub fn to_hex(&self) -> String {
                to_hex(&self.0)
            }
            pub fn from_hex(s: &str) -> Option<Self> {
                let bytes = crate::sha256::from_hex(s)?;
                if bytes.len() != 32 {
                    return None;
                }
                let mut arr = [0u8; 32];
                arr.copy_from_slice(&bytes);
                Some(Self(arr))
            }
        }
        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&self.to_hex())
            }
        }
        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!(stringify!($name), "("))?;
                f.write_str(&self.to_hex())?;
                write!(f, ")")
            }
        }
    };
}

id_type!(StatementId);
id_type!(EvidenceId);
id_type!(VerificationKey);
id_type!(ChallengeId);
id_type!(InterfaceKey);

/// StatementId = H(domain || canonical closed statement bytes || sorted semantic dependency StatementIds).
/// Transparent definition bodies are part of the statement bytes; names are stable scoped identities.
pub fn statement_id(canonical_statement: &[u8], semantic_deps: &[[u8; 32]]) -> StatementId {
    let mut sorted: Vec<&[u8; 32]> = semantic_deps.iter().collect();
    sorted.sort();
    let mut fields: Vec<&[u8]> = vec![canonical_statement];
    for d in sorted {
        fields.push(d);
    }
    StatementId(domain_hash(DOMAIN_STATEMENT_ID, &fields))
}

/// EvidenceId additionally identifies proof bytes and imported proof references (sorted).
pub fn evidence_id(statement: &StatementId, proof_bytes: &[u8], imported_proofs: &[[u8; 32]]) -> EvidenceId {
    let mut sorted: Vec<&[u8; 32]> = imported_proofs.iter().collect();
    sorted.sort();
    let mut fields: Vec<&[u8]> = vec![&statement.0, proof_bytes];
    for d in sorted {
        fields.push(d);
    }
    EvidenceId(domain_hash(DOMAIN_EVIDENCE_ID, &fields))
}

/// VerificationKey binds checker build, profile, policy, covered roots and evidence closure.
/// A repaired proof, a policy change, or a checker change therefore cannot inherit an attestation.
pub fn verification_key(
    checker_build: &str,
    profile: &str,
    policy_id: &[u8; 32],
    evidence: &EvidenceId,
    covered_roots_sorted: &[[u8; 32]],
    ticket_rule_version: &str,
) -> VerificationKey {
    let mut fields: Vec<&[u8]> = vec![
        checker_build.as_bytes(),
        profile.as_bytes(),
        policy_id,
        &evidence.0,
        ticket_rule_version.as_bytes(),
    ];
    for r in covered_roots_sorted {
        fields.push(r);
    }
    VerificationKey(domain_hash(DOMAIN_VERIFICATION_KEY, &fields))
}

pub fn challenge_id(canonical_challenge: &[u8]) -> ChallengeId {
    ChallengeId(domain_hash(DOMAIN_CHALLENGE_ID, &[canonical_challenge]))
}

/// Interface cache key: deliberately coarser than VerificationKey. Only valid for
/// interface reuse decisions, never as a substitute for validation of a replacement proof.
pub fn interface_key(statement: &StatementId, policy_id: &[u8; 32], profile: &str) -> InterfaceKey {
    InterfaceKey(domain_hash(
        DOMAIN_IFACE_CACHE_KEY,
        &[&statement.0, policy_id, profile.as_bytes()],
    ))
}
