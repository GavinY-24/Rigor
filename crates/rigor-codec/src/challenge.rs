//! Sealed challenges (.rigorc, magic RIGC1): a resolved challenge, its
//! declaration-closure identities, selected roots, level binders and axiom
//! policy. A challenge is approved independently of any solution; any change
//! to it is visible in its ChallengeId.

use crate::bundle::Bundle;
use crate::ids_compute::canonical_term_subgraph;
use crate::leb::{write_str, write_usize, DecodeError, DResult, Reader};
use rigor_spec::abi::MAGIC_RIGC1;
use rigor_spec::ids;
use rigor_spec::{ChallengeId, StatementId};

#[derive(Debug, Clone, PartialEq)]
pub struct ChallengeRoot {
    pub name: String,
    pub statement_id: StatementId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Challenge {
    pub name: String,
    pub profile: String,
    /// Policy name (constructive/classical) — resolved to an exact manifest at verify time.
    pub policy: String,
    pub roots: Vec<ChallengeRoot>,
    /// StatementIds pinning the declaration closure the roots depend on.
    pub pinned_closure: Vec<StatementId>,
    /// Canonical bytes of each root statement subgraph (for exact replay comparison).
    pub root_statement_bytes: Vec<(String, Vec<u8>)>,
}

impl Challenge {
    pub fn challenge_id(&self) -> ChallengeId {
        ids::challenge_id(&self.canonical_bytes())
    }

    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(b"RIGC1-CANON");
        write_str(&mut out, &self.name);
        write_str(&mut out, &self.profile);
        write_str(&mut out, &self.policy);
        write_usize(&mut out, self.roots.len());
        for r in &self.roots {
            write_str(&mut out, &r.name);
            out.extend_from_slice(&r.statement_id.0);
        }
        let mut pinned: Vec<[u8; 32]> = self.pinned_closure.iter().map(|s| s.0).collect();
        pinned.sort();
        write_usize(&mut out, pinned.len());
        for p in pinned {
            out.extend_from_slice(&p);
        }
        for (name, bytes) in &self.root_statement_bytes {
            write_str(&mut out, name);
            write_usize(&mut out, bytes.len());
            out.extend_from_slice(bytes);
        }
        out
    }

    /// Build a challenge from a bundle: roots + their statement ids and full pinned closure.
    pub fn from_bundle(name: &str, bundle: &Bundle, root_names: &[String], policy: &str) -> Self {
        let stmt_ids = crate::ids_compute::statement_ids(bundle);
        let mut roots = Vec::new();
        let mut root_statement_bytes = Vec::new();
        for rn in root_names {
            let sid = stmt_ids.get(rn).copied().unwrap_or(StatementId([0u8; 32]));
            roots.push(ChallengeRoot { name: rn.clone(), statement_id: sid });
            if let Some(decl) = bundle.declarations.iter().find(|d| bundle.name_string(d.name) == *rn) {
                root_statement_bytes.push((rn.clone(), canonical_term_subgraph(bundle, &[decl.ty])));
            }
        }
        // pinned closure: statement ids of every declaration in the bundle
        let mut pinned: Vec<StatementId> = stmt_ids.values().copied().collect();
        pinned.sort();
        pinned.dedup();
        Self {
            name: name.to_string(),
            profile: bundle.profile.clone(),
            policy: policy.to_string(),
            roots,
            pinned_closure: pinned,
            root_statement_bytes,
        }
    }
}

pub fn encode_challenge(challenge: &Challenge) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(MAGIC_RIGC1);
    write_str(&mut out, &challenge.name);
    write_str(&mut out, &challenge.profile);
    write_str(&mut out, &challenge.policy);
    write_usize(&mut out, challenge.roots.len());
    for r in &challenge.roots {
        write_str(&mut out, &r.name);
        out.extend_from_slice(&r.statement_id.0);
    }
    write_usize(&mut out, challenge.pinned_closure.len());
    for p in &challenge.pinned_closure {
        out.extend_from_slice(&p.0);
    }
    write_usize(&mut out, challenge.root_statement_bytes.len());
    for (name, bytes) in &challenge.root_statement_bytes {
        write_str(&mut out, name);
        write_usize(&mut out, bytes.len());
        out.extend_from_slice(bytes);
    }
    out
}

pub fn decode_challenge(bytes: &[u8]) -> DResult<Challenge> {
    if bytes.len() > 64 * 1024 * 1024 {
        return Err(DecodeError("challenge exceeds size limit".into()));
    }
    let mut r = Reader::new(bytes);
    let magic = r.bytes(5)?;
    if magic != MAGIC_RIGC1 {
        return Err(DecodeError("bad magic (expected RIGC1)".into()));
    }
    let name = r.string()?;
    let profile = r.string()?;
    let policy = r.string()?;
    let nroots = r.usize()?;
    if nroots > 100_000 {
        return Err(DecodeError("too many challenge roots".into()));
    }
    let mut roots = Vec::new();
    for _ in 0..nroots {
        let rn = r.string()?;
        let raw = r.bytes(32)?;
        let mut arr = [0u8; 32];
        arr.copy_from_slice(raw);
        roots.push(ChallengeRoot { name: rn, statement_id: StatementId(arr) });
    }
    let npinned = r.usize()?;
    if npinned > 1_000_000 {
        return Err(DecodeError("too many pinned closure entries".into()));
    }
    let mut pinned = Vec::new();
    for _ in 0..npinned {
        let raw = r.bytes(32)?;
        let mut arr = [0u8; 32];
        arr.copy_from_slice(raw);
        pinned.push(StatementId(arr));
    }
    let nbytes = r.usize()?;
    let mut root_statement_bytes = Vec::new();
    for _ in 0..nbytes {
        let n = r.string()?;
        let b = r.take_bytes()?;
        root_statement_bytes.push((n, b));
    }
    if !r.is_done() {
        return Err(DecodeError("trailing payload in challenge".into()));
    }
    Ok(Challenge {
        name,
        profile,
        policy,
        roots,
        pinned_closure: pinned,
        root_statement_bytes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bundle::Bundle;

    #[test]
    fn challenge_roundtrip() {
        let bundle = Bundle::default();
        let ch = Challenge::from_bundle("Test", &bundle, &[], "constructive");
        let bytes = encode_challenge(&ch);
        let back = decode_challenge(&bytes).unwrap();
        assert_eq!(ch, back);
        assert_eq!(ch.challenge_id(), back.challenge_id());
    }
}
