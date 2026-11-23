//! Locally produced reports (.rigorr). A receipt is evidence that *this*
//! checker run produced this verdict; an unauthenticated third-party receipt
//! is never accepted as proof.

use rigor_spec::VerifyVerdict;
use std::collections::BTreeSet;
use std::fmt::Write as _;

#[derive(Debug, Clone)]
pub struct RootReceipt {
    pub name: String,
    pub verdict: VerifyVerdict,
    pub statement_id: String,
    pub evidence_id: String,
    pub assumptions: Vec<String>,
    pub quot_used: bool,
    pub diagnostic: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Receipt {
    pub verdict: VerifyVerdict,
    pub roots: Vec<RootReceipt>,
    pub profile: String,
    pub checker_build: String,
    pub policy: String,
    pub verification_key: String,
    pub challenge_id: Option<String>,
    pub covered_dependencies: Vec<String>,
    pub kernel_steps: u64,
    pub wall_ms: u64,
    pub workers: usize,
    pub bundle_bytes: usize,
}

impl Receipt {
    pub fn to_json(&self) -> String {
        let mut s = String::new();
        let _ = writeln!(s, "{{");
        let _ = writeln!(s, "  \"verdict\": {},", json_str(self.verdict.as_str()));
        let _ = writeln!(s, "  \"profile\": {},", json_str(&self.profile));
        let _ = writeln!(s, "  \"checker_build\": {},", json_str(&self.checker_build));
        let _ = writeln!(s, "  \"policy\": {},", json_str(&self.policy));
        let _ = writeln!(s, "  \"verification_key\": {},", json_str(&self.verification_key));
        match &self.challenge_id {
            Some(c) => {
                let _ = writeln!(s, "  \"challenge_id\": {},", json_str(c));
            }
            None => {
                let _ = writeln!(s, "  \"challenge_id\": null,");
            }
        }
        let _ = writeln!(s, "  \"kernel_steps\": {},", self.kernel_steps);
        let _ = writeln!(s, "  \"wall_ms\": {},", self.wall_ms);
        let _ = writeln!(s, "  \"workers\": {},", self.workers);
        let _ = writeln!(s, "  \"bundle_bytes\": {},", self.bundle_bytes);
        let _ = writeln!(s, "  \"covered_dependencies\": [");
        for (i, d) in self.covered_dependencies.iter().enumerate() {
            let comma = if i + 1 < self.covered_dependencies.len() { "," } else { "" };
            let _ = writeln!(s, "    {}{}", json_str(d), comma);
        }
        let _ = writeln!(s, "  ],");
        let _ = writeln!(s, "  \"roots\": [");
        for (i, r) in self.roots.iter().enumerate() {
            let comma = if i + 1 < self.roots.len() { "," } else { "" };
            let _ = writeln!(s, "    {{");
            let _ = writeln!(s, "      \"name\": {},", json_str(&r.name));
            let _ = writeln!(s, "      \"verdict\": {},", json_str(r.verdict.as_str()));
            let _ = writeln!(s, "      \"statement_id\": {},", json_str(&r.statement_id));
            let _ = writeln!(s, "      \"evidence_id\": {},", json_str(&r.evidence_id));
            let _ = writeln!(s, "      \"quot_used\": {},", r.quot_used);
            let _ = writeln!(s, "      \"assumptions\": [{}],", r.assumptions.iter().map(|a| json_str(a)).collect::<Vec<_>>().join(", "));
            match &r.diagnostic {
                Some(d) => {
                    let _ = writeln!(s, "      \"diagnostic\": {}", json_str(d));
                }
                None => {
                    let _ = writeln!(s, "      \"diagnostic\": null");
                }
            }
            let _ = writeln!(s, "    }}{}", comma);
        }
        let _ = writeln!(s, "  ]");
        let _ = writeln!(s, "}}");
        s
    }

    /// Parse a receipt JSON produced by `to_json` (for display only; the
    /// result carries an explicit untrusted marker at the CLI layer).
    pub fn from_json(text: &str) -> Option<Receipt> {
        // Minimal tolerant extraction for the fields we emit.
        let get_str = |key: &str| -> Option<String> {
            let pat = format!("\"{key}\"");
            let start = text.find(&pat)? + pat.len();
            let rest = &text[start..];
            let colon = rest.find(':')? + 1;
            let rest = &rest[colon..];
            let q1 = rest.find('"')? + 1;
            let rest = &rest[q1..];
            let q2 = rest.find('"')?;
            Some(rest[..q2].to_string())
        };
        let verdict_str = get_str("verdict")?;
        let verdict = match verdict_str.as_str() {
            "VERIFIED_MATCHED" => VerifyVerdict::VerifiedMatched,
            "VERIFIED_SELF_STATED" => VerifyVerdict::VerifiedSelfStated,
            "INVALID" => VerifyVerdict::Invalid,
            "UNSUPPORTED" => VerifyVerdict::Unsupported,
            "UNKNOWN_RESOURCE" => VerifyVerdict::UnknownResource,
            _ => VerifyVerdict::InternalError,
        };
        Some(Receipt {
            verdict,
            roots: Vec::new(),
            profile: get_str("profile").unwrap_or_default(),
            checker_build: get_str("checker_build").unwrap_or_default(),
            policy: get_str("policy").unwrap_or_default(),
            verification_key: get_str("verification_key").unwrap_or_default(),
            challenge_id: get_str("challenge_id"),
            covered_dependencies: Vec::new(),
            kernel_steps: 0,
            wall_ms: 0,
            workers: 0,
            bundle_bytes: 0,
        })
    }
}

pub fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

pub fn assumption_set(names: impl IntoIterator<Item = String>) -> BTreeSet<String> {
    names.into_iter().collect()
}
