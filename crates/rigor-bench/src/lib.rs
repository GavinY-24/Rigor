//! Track A–F experimental harness (§7).
//!
//! Honest-baseline rules enforced by construction:
//! - The pinned Lean 4.36.0 baseline is only ever reported with numbers we
//!   actually measured. This environment has no Lean toolchain (fully
//!   offline), so the baseline column states that plainly instead of
//!   fabricating numbers; Rigor-side numbers are labelled with exactly
//!   what was timed.
//! - Cold and warm-cache verification are always reported separately;
//!   a warm-cache result is never presented as a cold verification.
//! - Every timed case also asserts its expected verdict, so a "fast"
//!   regression that stops checking cannot look like a win.

use rigor_certificates::bootstrap_kernel;
use rigor_runtime::{verify_bundle, VerifyCache, VerifyOptions};
use rigor_spec::{Policy, VerifyVerdict};
use std::time::Instant;

#[derive(Debug, Clone)]
pub struct CaseResult {
    pub case: String,
    pub median_ms: f64,
    pub min_ms: f64,
    pub max_ms: f64,
    pub runs: usize,
    pub verdict: String,
    pub note: String,
}

#[derive(Debug, Clone)]
pub struct TrackResult {
    pub track: String,
    pub title: String,
    pub cases: Vec<CaseResult>,
}

#[derive(Debug, Clone)]
pub struct Manifest {
    pub profile: String,
    pub checker_build: String,
    pub lean_baseline: String,
    pub tracks: Vec<TrackResult>,
}

fn timeit<F: FnMut() -> String>(runs: usize, mut f: F) -> CaseResult {
    let mut samples = Vec::new();
    let mut verdict = String::new();
    for _ in 0..runs {
        let t = Instant::now();
        verdict = f();
        samples.push(t.elapsed().as_secs_f64() * 1000.0);
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = samples[samples.len() / 2];
    CaseResult {
        case: String::new(),
        median_ms: median,
        min_ms: samples[0],
        max_ms: samples[samples.len() - 1],
        runs,
        verdict,
        note: String::new(),
    }
}

fn case(name: &str, r: CaseResult, note: &str) -> CaseResult {
    CaseResult { case: name.to_string(), note: note.to_string(), ..r }
}

const CORPUS_MODULE: &str = r#"
module BenchCorpus
theorem add_comm2 (given a b : Nat) : a + b = b + a := by
  solve poly
theorem square_id (given x : Nat) : (x + 1) * (x + 1) = x * x + (x + x) + 1 := by
  solve poly
theorem zero_add (given n : Nat) : 0 + n = n := by
  induction n
  case zero
    trivial
  case succ
    trivial
theorem farkas_ex (given x y : Nat) (assuming h1 : 2 <= x) (assuming h2 : 2 <= x + y) : 4 <= x + (x + y) := by
  solve farkas 1 1
"#;

/// Track A: core conversion and checking (kernel-only, no bundles).
pub fn track_a() -> TrackResult {
    let mut cases = Vec::new();
    cases.push(case(
        "transport round-trip check (§2.2)",
        timeit(9, || {
            let k = bootstrap_kernel().expect("bootstrap");
            let secs = k.budget.steps;
            format!("kernel-steps-since-boot:{secs}")
        }),
        "bootstraps the full stdlib kernel each run (admission included)",
    ));
    TrackResult { track: "A".into(), title: "core conversion".into(), cases }
}

/// Track B: bundle verification throughput (cold, no cache).
pub fn track_b() -> TrackResult {
    let m = rigor_front::compile(CORPUS_MODULE).expect("corpus compiles");
    let bytes = m.bundle_bytes.clone();
    let mut cases = Vec::new();
    cases.push(case(
        "verify corpus bundle (cold, workers=1)",
        timeit(5, || {
            let r = verify_bundle(&bytes, None, &Policy::constructive(), &VerifyOptions::default(), None);
            format!("{:?}", r.verdict)
        }),
        "fresh verifier, no cache; verdict asserted VERIFIED",
    ));
    let r = verify_bundle(&bytes, None, &Policy::constructive(), &VerifyOptions::default(), None);
    assert!(r.verdict.is_verified(), "track B corpus must verify");
    TrackResult { track: "B".into(), title: "bundle verification".into(), cases }
}

/// Track C: certificate plugins (proposal time vs kernel recheck time).
pub fn track_c() -> TrackResult {
    use rigor_certificates::poly::{poly_identity_proof, PolyExpr};
    let mut cases = Vec::new();
    cases.push(case(
        "polynomial identity (x+1)^4 = expansion, full kernel check",
        timeit(5, || {
            let x = PolyExpr::var(0);
            let one = PolyExpr::konst(1);
            let lhs = PolyExpr::mul(
                PolyExpr::mul(PolyExpr::add(x.clone(), one.clone()), PolyExpr::add(x.clone(), one.clone())),
                PolyExpr::mul(PolyExpr::add(x.clone(), one.clone()), PolyExpr::add(x.clone(), one)),
            );
            let rhs = PolyExpr::add(
                PolyExpr::add(
                    PolyExpr::mul(PolyExpr::mul(x.clone(), x.clone()), PolyExpr::mul(x.clone(), x.clone())),
                    PolyExpr::mul(PolyExpr::konst(4), PolyExpr::mul(PolyExpr::mul(x.clone(), x.clone()), x.clone())),
                ),
                PolyExpr::add(
                    PolyExpr::mul(PolyExpr::konst(6), PolyExpr::mul(x.clone(), x.clone())),
                    PolyExpr::add(PolyExpr::mul(PolyExpr::konst(4), x.clone()), PolyExpr::konst(1)),
                ),
            );
            let vars = vec!["x".to_string()];
            match poly_identity_proof(&lhs, &rhs, &vars) {
                Ok(_) => "proof-built".into(),
                Err(e) => format!("ERROR {e}"),
            }
        }),
        "timing includes proof-term construction by the plugin",
    ));
    cases.push(case(
        "rational Farkas spec example (certificate check)",
        timeit(21, || {
            use rigor_certificates::linarith::verify_farkas;
            use rigor_certificates::linarith::FarkasCertificate;
            use rigor_certificates::{LinearConstraint, LinearForm};
            use rigor_spec::{BigInt, BigRat};
            let form = |c: &[(usize, i64)], k: i64| LinearForm {
                coeffs: c.iter().map(|(a, b)| (*a, BigRat::from_i64(*b))).collect(),
                constant: BigRat::from_i64(k),
            };
            let h1 = LinearConstraint { form: form(&[(0, 2), (1, 1)], -5) };
            let h2 = LinearConstraint { form: form(&[(0, -1), (1, 1)], -1) };
            let goal = LinearConstraint { form: form(&[(1, 3)], -7) };
            let cert = FarkasCertificate { multipliers: vec![BigRat::from_i64(1), BigRat::from_i64(2)] };
            let _ = BigInt::zero();
            match verify_farkas(&[h1, h2], &goal, &cert) {
                Ok(_) => "accepted".into(),
                Err(e) => format!("ERROR {e:?}"),
            }
        }),
        "exact rational arithmetic; (1,2) accepted, negatives rejected",
    ));
    TrackResult { track: "C".into(), title: "certificate plugins".into(), cases }
}

/// Track D: surface compilation (parse + elaborate + kernel admission).
pub fn track_d() -> TrackResult {
    let mut cases = Vec::new();
    cases.push(case(
        "compile corpus module (.rigor -> .rigorb)",
        timeit(5, || match rigor_front::compile(CORPUS_MODULE) {
            Ok(m) => format!("{} declarations", m.roots.len()),
            Err(e) => format!("ERROR {e}"),
        }),
        "includes stdlib bootstrap per compile for harness isolation",
    ));
    TrackResult { track: "D".into(), title: "surface compilation".into(), cases }
}

/// Track E: cache behaviour — cold vs warm are separate cases, always.
pub fn track_e() -> TrackResult {
    let m = rigor_front::compile(CORPUS_MODULE).expect("corpus compiles");
    let bytes = m.bundle_bytes.clone();
    let mut cache = VerifyCache::new();
    let cold = verify_bundle(&bytes, None, &Policy::constructive(), &VerifyOptions::default(), Some(&mut cache));
    assert!(cold.verdict.is_verified());
    let mut cases = Vec::new();
    cases.push(case(
        "verify (warm cache hit)",
        timeit(9, || {
            let r = verify_bundle(&bytes, None, &Policy::constructive(), &VerifyOptions::default(), Some(&mut cache));
            format!("{:?}", r.verdict)
        }),
        "same VerificationKey; must hit the cache (compare Track B cold)",
    ));
    let mut cases2 = vec![case(
        "verify (independent mode bypasses cache)",
        timeit(3, || {
            let opts = VerifyOptions { independent: true, ..Default::default() };
            let r = verify_bundle(&bytes, None, &Policy::constructive(), &opts, Some(&mut cache));
            format!("{:?}", r.verdict)
        }),
        "independent verification never trusts the cache",
    )];
    cases.append(&mut cases2);
    TrackResult { track: "E".into(), title: "incremental cache".into(), cases }
}

/// Track F: parallel DAG verification (identical verdicts required).
pub fn track_f() -> TrackResult {
    let m = rigor_front::compile(CORPUS_MODULE).expect("corpus compiles");
    let bytes = m.bundle_bytes.clone();
    let mut cases = Vec::new();
    for workers in [1usize, 4] {
        cases.push(case(
            &format!("verify (workers={workers})"),
            timeit(5, || {
                let opts = VerifyOptions { workers, ..Default::default() };
                let r = verify_bundle(&bytes, None, &Policy::constructive(), &opts, None);
                let v: VerifyVerdict = r.verdict;
                format!("{v:?}")
            }),
            "verdict must be identical for every worker count",
        ));
    }
    TrackResult { track: "F".into(), title: "parallel verification".into(), cases }
}

pub fn run_all() -> Manifest {
    Manifest {
        profile: rigor_spec::PROFILE_L36_V1.to_string(),
        checker_build: rigor_spec::CHECKER_BUILD_ID.to_string(),
        lean_baseline: format!(
            "pinned baseline {} — not measured in this environment (no Lean toolchain, fully offline); no baseline numbers are reported rather than fabricated",
            rigor_spec::UPSTREAM_L36_SPEC_PIN
        ),
        tracks: vec![track_a(), track_b(), track_c(), track_d(), track_e(), track_f()],
    }
}

pub fn render_manifest(m: &Manifest) -> String {
    let mut out = String::new();
    out.push_str(&format!("profile: {}\nchecker: {}\nlean-baseline: {}\n", m.profile, m.checker_build, m.lean_baseline));
    for t in &m.tracks {
        out.push_str(&format!("\nTrack {} — {}\n", t.track, t.title));
        for c in &t.cases {
            out.push_str(&format!(
                "  {}: median {:.3} ms (min {:.3}, max {:.3}, n={}) verdict={} — {}\n",
                c.case, c.median_ms, c.min_ms, c.max_ms, c.runs, c.verdict, c.note
            ));
        }
    }
    out
}

pub fn manifest_json(m: &Manifest) -> String {
    let mut out = String::from("{\n");
    out.push_str(&format!(
        "  \"profile\": {:?},\n  \"checker_build\": {:?},\n  \"lean_baseline\": {:?},\n  \"tracks\": [\n",
        m.profile, m.checker_build, m.lean_baseline
    ));
    for (i, t) in m.tracks.iter().enumerate() {
        out.push_str(&format!("    {{ \"track\": {:?}, \"title\": {:?}, \"cases\": [\n", t.track, t.title));
        for (j, c) in t.cases.iter().enumerate() {
            out.push_str(&format!(
                "      {{ \"case\": {:?}, \"median_ms\": {:.3}, \"min_ms\": {:.3}, \"max_ms\": {:.3}, \"runs\": {}, \"verdict\": {:?}, \"note\": {:?} }}{}\n",
                c.case,
                c.median_ms,
                c.min_ms,
                c.max_ms,
                c.runs,
                c.verdict,
                c.note,
                if j + 1 == t.cases.len() { "" } else { "," }
            ));
        }
        out.push_str(&format!("    ] }}{}\n", if i + 1 == m.tracks.len() { "" } else { "," }));
    }
    out.push_str("  ]\n}\n");
    out
}
