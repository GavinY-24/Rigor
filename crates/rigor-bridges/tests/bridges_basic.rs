//! Bridges: .rigx exchange round-trip, semantic diff, explanation view.
//!
//! The trust rule under test: imported declarations are re-admitted by the
//! kernel from scratch; nothing about a third-party producer is believed.

use rigor_bridges::{
    diff_bundles, explain, export_exchange, import_exchange, render_diff, ChangeKind, ExplainOpts,
    Reuse,
};
use rigor_certificates::bootstrap_kernel;
use rigor_codec::{decode_bundle, encode_bundle};
use rigor_front::compile;
use rigor_runtime::{verify_bundle, VerifyOptions};
use rigor_spec::policy::Policy;
use rigor_spec::VerifyVerdict;

fn verify(bytes: &[u8]) -> rigor_runtime::Receipt {
    verify_bundle(bytes, None, &Policy::constructive(), &VerifyOptions::default(), None)
}

#[test]
fn exchange_roundtrip_reverifies() {
    let kernel = bootstrap_kernel().expect("stdlib bootstrap");
    let roots = vec!["Nat.add_zero".to_string(), "Nat.add".to_string()];
    let text = export_exchange(&kernel, &roots, "test export");
    assert!(text.contains("rigor-exchange 1"), "header missing:\n{}", &text[..200.min(text.len())]);

    let imported = import_exchange(&text, false).expect("import exchange");
    assert_eq!(imported.roots, roots);
    assert!(imported.matrix.declarations > 10, "matrix has {} declarations", imported.matrix.declarations);
    assert!(imported.matrix.unsupported.is_empty(), "unsupported: {}", imported.matrix.unsupported.join(", "));

    // The imported kernel encodes to a bundle that the runtime verifies
    // from scratch (no trust in the exchange producer).
    let bundle = rigor_codec::encode_kernel(&imported.kernel, &imported.roots, &[], &[], None);
    let bytes = encode_bundle(&bundle);
    let receipt = verify(&bytes);
    assert_eq!(
        receipt.verdict,
        VerifyVerdict::VerifiedSelfStated,
        "round-tripped bundle must verify: {:?}",
        receipt.roots.iter().map(|r| (&r.name, &r.verdict, &r.diagnostic)).collect::<Vec<_>>()
    );
}

#[test]
fn exchange_rejects_wrong_pin_without_override() {
    let kernel = bootstrap_kernel().expect("stdlib bootstrap");
    let text = export_exchange(&kernel, &["Nat.add".to_string()], "");
    let tampered = text.replacen(
        "lean4:v4.36.0-core-semantics-pin",
        "lean4:v0.0.0-unpinned",
        1,
    );
    assert!(tampered != text);
    let err = match import_exchange(&tampered, false) {
        Ok(_) => panic!("wrong pin must be rejected"),
        Err(e) => e,
    };
    assert!(err.contains("pin"), "error should name the pin: {err}");
    // The override path is explicit and reported.
    let imported = import_exchange(&tampered, true).expect("override import");
    assert!(imported.matrix.pin_override, "override must be reported in the feature matrix");
}

#[test]
fn bundle_exchange_roundtrip() {
    let module = compile(
        "module M\ntheorem t (given n : Nat) : n + 0 = n := by\n  exact Nat.add_zero n\n",
    )
    .expect("compile");
    let bundle = decode_bundle(&module.bundle_bytes, &rigor_spec::DecoderLimits::default())
        .expect("decode");
    let text = rigor_bridges::export_bundle_exchange(&bundle);
    let imported = import_exchange(&text, false).expect("import bundle exchange");
    let rebundled = rigor_codec::encode_kernel(&imported.kernel, &imported.roots, &[], &[], None);
    let receipt = verify(&encode_bundle(&rebundled));
    assert_eq!(receipt.verdict, VerifyVerdict::VerifiedSelfStated);
}

const SRC_V1: &str = "module M\n\
def two : Nat := 1 + 1\n\
theorem t (given n : Nat) : n + 0 = n := by\n  exact Nat.add_zero n\n\
theorem uses_two : two = two := by\n  exact Eq.refl Nat two\n";

#[test]
fn diff_proof_repair_vs_transparent_change() {
    let v1 = compile(SRC_V1).expect("v1");
    let b1 = decode_bundle(&v1.bundle_bytes, &rigor_spec::DecoderLimits::default()).unwrap();

    // Same statement, different proof term => interface-only reuse.
    let src_v2 = SRC_V1.replace(
        "exact Nat.add_zero n",
        "have h : n + 0 = n := Nat.add_zero n\n  exact h",
    );
    let v2 = compile(&src_v2).expect("v2");
    let b2 = decode_bundle(&v2.bundle_bytes, &rigor_spec::DecoderLimits::default()).unwrap();
    let report = diff_bundles(&b1, &b2);
    let t = report
        .changes
        .iter()
        .find(|c| c.name == "t")
        .unwrap_or_else(|| panic!("no diff entry for t:\n{}", render_diff(&report)));
    assert_eq!(t.kind, ChangeKind::ProofRepaired, "{}", render_diff(&report));
    assert_eq!(t.reuse, Reuse::InterfaceOnly);

    // Transparent definition change => the definition and its dependents
    // are semantically invalidated.
    let src_v3 = SRC_V1.replacen(":= 1 + 1", ":= 2", 1);
    let v3 = compile(&src_v3).expect("v3");
    let b3 = decode_bundle(&v3.bundle_bytes, &rigor_spec::DecoderLimits::default()).unwrap();
    let report = diff_bundles(&b1, &b3);
    let two = report
        .changes
        .iter()
        .find(|c| c.name == "two")
        .unwrap_or_else(|| panic!("no diff entry for two:\n{}", render_diff(&report)));
    assert_eq!(two.kind, ChangeKind::TransparentChanged, "{}", render_diff(&report));
    assert_eq!(two.reuse, Reuse::None);
    assert!(
        two.invalidated.iter().any(|n| n == "uses_two"),
        "dependent theorem must be invalidated: {}",
        render_diff(&report)
    );
}

#[test]
fn explain_reports_statement_and_assumptions() {
    let module = compile(
        "module M\ntheorem t (given n : Nat) : n + 0 = n := by\n  exact Nat.add_zero n\nchallenge c := t\n",
    )
    .expect("compile");
    let bundle = decode_bundle(&module.bundle_bytes, &rigor_spec::DecoderLimits::default()).unwrap();
    let receipt = verify(&module.bundle_bytes);
    let text = explain(
        &bundle,
        Some(&receipt),
        ExplainOpts { assumptions: true, coercions: true, statements: true },
    );
    assert!(text.contains("t"), "explain output:\n{text}");
    assert!(text.to_lowercase().contains("statement"), "explain output:\n{text}");
    // A constructive proof over the stdlib reports no axiom assumptions.
    let lower = text.to_lowercase();
    assert!(
        !lower.contains("classical.choice") && !lower.contains("quot.sound"),
        "unexpected assumptions in:\n{text}"
    );
}
