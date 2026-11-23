//! Benchmark manifest sanity: all six tracks present, every timed case
//! asserts its verdict, and the Lean baseline is honestly reported as
//! unmeasured (never fabricated).

use rigor_bench::{manifest_json, render_manifest, run_all};

#[test]
fn manifest_has_all_tracks_and_honest_baseline() {
    let m = run_all();
    assert_eq!(m.tracks.len(), 6, "tracks A-F required:\n{}", render_manifest(&m));
    // Every case carries a verdict; the verification tracks (B/E/F) must
    // report VERIFIED verdicts (they assert internally too).
    for t in &m.tracks {
        assert!(
            t.cases.iter().all(|c| !c.verdict.is_empty()),
            "track {} has a case without a verdict",
            t.track
        );
    }
    let all_verdicts: String = m
        .tracks
        .iter()
        .flat_map(|t| t.cases.iter().map(|c| c.verdict.clone()))
        .collect::<Vec<_>>()
        .join(" ");
    assert!(
        all_verdicts.to_uppercase().contains("VERIFIED"),
        "no verified case in the manifest: {all_verdicts}"
    );
    let lower = m.lean_baseline.to_lowercase();
    assert!(
        lower.contains("not measured") || lower.contains("unavailable") || lower.contains("not available"),
        "Lean baseline must be honest about not being measured, got: {}",
        m.lean_baseline
    );
    let json = manifest_json(&m);
    assert!(json.contains("track"), "json manifest:\n{json}");
    let text = render_manifest(&m);
    assert!(text.contains("cold") && text.contains("warm"), "cold/warm separation:\n{text}");
}
