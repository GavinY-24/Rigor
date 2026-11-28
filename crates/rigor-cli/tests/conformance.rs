//! §8 conformance fixtures: the twelve must-pass behaviors, exercised
//! end-to-end (surface -> bundle -> runtime verdict -> Python checker
//! where applicable). Each fixture is named after the spec clause it pins.
//!
//! Honesty rules enforced by construction: unsupported constructs report
//! UNSUPPORTED (never a silent pass), resource exhaustion reports
//! UNKNOWN_RESOURCE (never a counterexample), and an invalid ticket
//! invalidates its bundle.

use rigor_certificates::bootstrap_kernel;
use rigor_codec::{decode_bundle, encode_bundle, encode_kernel, Bundle, PortableDecl, TermNode};
use rigor_front::{compile, compile_with};
use rigor_kernel::{lower_closed, DeclKind, InductiveSpec, Level, NExpr, Reducibility};
use rigor_runtime::{verify_bundle, Receipt, VerifyCache, VerifyOptions};
use rigor_spec::{DecoderLimits, Policy, VerifyVerdict};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

fn limits() -> DecoderLimits {
    DecoderLimits::default()
}

fn verify(bytes: &[u8], policy: &Policy) -> Receipt {
    verify_bundle(bytes, None, policy, &VerifyOptions::default(), None)
}

fn compile_ok(src: &str) -> rigor_front::CompiledModule {
    compile(src).unwrap_or_else(|e| panic!("compile failed: {e}\n--- source ---\n{src}"))
}

fn assert_verified(src: &str) -> rigor_front::CompiledModule {
    let m = compile_ok(src);
    let r = verify(&m.bundle_bytes, &Policy::constructive());
    assert_eq!(
        r.verdict,
        VerifyVerdict::VerifiedSelfStated,
        "roots: {:?}",
        r.roots.iter().map(|x| (&x.name, &x.verdict, &x.diagnostic)).collect::<Vec<_>>()
    );
    m
}

// ---------------- Fixture 1 (§2.2): dependent transport round-trip --------

const TRANSPORT_SRC: &str = r#"
module Transport
def transport (given alpha : Type) (given F : alpha -> Type) (given x : alpha) (given y : alpha) (given h : x = y) (given b : F x) : F y := by
  induction h
  case refl
    exact b
theorem transport_round_trip (given alpha : Type) (given F : alpha -> Type) (given x : alpha) (given y : alpha) (given h : x = y) (given b : F x) : transport alpha F y x (Eq.symm alpha x y h) (transport alpha F x y h b) = b := by
  induction h
  case refl
    trivial
"#;

#[test]
fn fixture01_transport_roundtrip() {
    let m = assert_verified(TRANSPORT_SRC);
    assert!(m.roots.iter().any(|r| r == "transport_round_trip"));
}

// ---------------- Fixture 2: indexed Vec append ---------------------------

const VEC_SRC: &str = r#"
module VecApp
def append (given A : Type) (given k : Nat) (given m : Nat) (given ys : Vec A m) (given xs : Vec A k) : Vec A (k + m) := by
  induction xs
  case nil
    exact ys
  case cons
    exact Vec.cons A (n + m) head ih_tail
theorem append_nil (given A : Type) (given m : Nat) (given ys : Vec A m) : append A 0 m ys (Vec.nil A) = ys := by
  trivial
theorem append_cons (given A : Type) (given k : Nat) (given m : Nat) (given x : A) (given ys : Vec A m) (given xs : Vec A k) : append A (Nat.succ k) m ys (Vec.cons A k x xs) = Vec.cons A (k + m) x (append A k m ys xs) := by
  trivial
"#;

#[test]
fn fixture02_vec_append() {
    assert_verified(VEC_SRC);
    // Index mismatches are rejected at admission, not at "runtime trust".
    let bad = compile(
        r#"
module VecBad
theorem bad (given A : Type) (given k : Nat) (given m : Nat) (given ys : Vec A m) (given xs : Vec A k) : Vec A (Nat.succ (k + m)) := append A k m ys xs
"#,
    );
    assert!(bad.is_err(), "append at the wrong index must be rejected");
}

// ---------------- Fixture 3: mutual inductive block ------------------------

#[test]
fn fixture03_mutual_trees() {
    let mut k = bootstrap_kernel().expect("stdlib");
    let tree = InductiveSpec {
        name: "Tree".to_string(),
        level_params: vec![],
        ty: NExpr::type0(),
        num_params: 0,
        constructors: vec![
            ("Tree.leaf".to_string(), NExpr::const_("Tree")),
            (
                "Tree.node".to_string(),
                NExpr::pi("f", NExpr::const_("Forest"), NExpr::const_("Tree")),
            ),
        ],
    };
    let forest = InductiveSpec {
        name: "Forest".to_string(),
        level_params: vec![],
        ty: NExpr::type0(),
        num_params: 0,
        constructors: vec![
            ("Forest.fnil".to_string(), NExpr::const_("Forest")),
            (
                "Forest.fcons".to_string(),
                NExpr::pi(
                    "t",
                    NExpr::const_("Tree"),
                    NExpr::pi("f", NExpr::const_("Forest"), NExpr::const_("Forest")),
                ),
            ),
        ],
    };
    k.add_inductive_block(vec![tree, forest]).expect("mutual block admitted");

    // countTree via the block recursor: motives for both members, minors
    // for all four constructors in block order.
    let one = NExpr::app(NExpr::const_("Nat.succ"), NExpr::const_("Nat.zero"));
    let count_ty = NExpr::pi("t", NExpr::const_("Tree"), NExpr::const_("Nat"));
    let count_val = NExpr::lam(
        "t",
        NExpr::const_("Tree"),
        NExpr::apps(
            NExpr::const_levels("Tree.rec", vec![Level::Succ(Box::new(Level::Zero))]),
            &[
                NExpr::lam("_", NExpr::const_("Tree"), NExpr::const_("Nat")),
                NExpr::lam("_", NExpr::const_("Forest"), NExpr::const_("Nat")),
                one.clone(),
                NExpr::lam(
                    "f",
                    NExpr::const_("Forest"),
                    NExpr::lam("ih", NExpr::const_("Nat"), NExpr::var("ih")),
                ),
                NExpr::const_("Nat.zero"),
                NExpr::lam(
                    "t",
                    NExpr::const_("Tree"),
                    NExpr::lam(
                        "f",
                        NExpr::const_("Forest"),
                        NExpr::lam(
                            "iht",
                            NExpr::const_("Nat"),
                            NExpr::lam(
                                "ihf",
                                NExpr::const_("Nat"),
                                NExpr::apps(
                                    NExpr::const_("Nat.add"),
                                    &[NExpr::var("iht"), NExpr::var("ihf")],
                                ),
                            ),
                        ),
                    ),
                ),
                NExpr::var("t"),
            ],
        ),
    );
    k.add_definition("countTree", &[], count_ty, count_val, DeclKind::Definition, Reducibility::Regular)
        .expect("countTree admitted");

    // countTree (node (fcons leaf fnil)) = 1, by refl: mutual iota must compute.
    let sample = NExpr::app(
        NExpr::const_("Tree.node"),
        NExpr::apps(
            NExpr::const_("Forest.fcons"),
            &[NExpr::const_("Tree.leaf"), NExpr::const_("Forest.fnil")],
        ),
    );
    let thm_ty = NExpr::apps(
        NExpr::const_levels("Eq", vec![Level::Succ(Box::new(Level::Zero))]),
        &[
            NExpr::const_("Nat"),
            NExpr::app(NExpr::const_("countTree"), sample.clone()),
            one.clone(),
        ],
    );
    let thm_val = NExpr::apps(
        NExpr::const_levels("Eq.refl", vec![Level::Succ(Box::new(Level::Zero))]),
        &[
            NExpr::const_("Nat"),
            NExpr::app(NExpr::const_("countTree"), sample),
        ],
    );
    k.add_definition("countTree_ex", &[], thm_ty, thm_val, DeclKind::Theorem, Reducibility::Opaque)
        .expect("mutual recursion computes on constructors");

    let bundle = encode_kernel(&k, &["countTree_ex".to_string()], &[], &[], None);
    let bytes = encode_bundle(&bundle);
    let r = verify(&bytes, &Policy::constructive());
    assert_eq!(r.verdict, VerifyVerdict::VerifiedSelfStated, "roots: {:?}", r.roots);
}

// ---------------- Fixture 4: quotient lift + Quot.sound policy -------------

const QUOT_SRC: &str = r#"
module QuotEx
theorem quot_compute (given alpha : Type) (given r : alpha -> alpha -> Prop) (given beta : Type) (given f : alpha -> beta) (given h : (a : alpha) -> (b : alpha) -> r a b -> f a = f b) (given a : alpha) : Quot.lift alpha r beta f h (Quot.mk alpha r a) = f a := by
  trivial
theorem quot_sound_ax (given alpha : Type) (given r : alpha -> alpha -> Prop) (given a : alpha) (given b : alpha) (given h : r a b) : Quot.mk alpha r a = Quot.mk alpha r b := by
  exact Quot.sound alpha r a b h
"#;

#[test]
fn fixture04_quotient_lift_and_policy() {
    let m = compile_ok(QUOT_SRC);
    // Constructive: the computation checks, the Quot.sound root does not.
    let r = verify(&m.bundle_bytes, &Policy::constructive());
    let compute = r.roots.iter().find(|x| x.name == "quot_compute").expect("root");
    let sound = r.roots.iter().find(|x| x.name == "quot_sound_ax").expect("root");
    assert!(compute.verdict.is_verified(), "quot computation must check: {:?}", compute.diagnostic);
    assert_eq!(sound.verdict, VerifyVerdict::Invalid, "Quot.sound must be refused constructively");
    assert!(
        sound.assumptions.iter().any(|a| a.contains("Quot.sound")),
        "assumption report must name Quot.sound: {:?}",
        sound.assumptions
    );
    // Classical: both check, and the assumption is reported, not hidden.
    let r = verify(&m.bundle_bytes, &Policy::classical());
    assert!(r.verdict.is_verified(), "classical must accept: {:?}", r.roots);
    let sound = r.roots.iter().find(|x| x.name == "quot_sound_ax").expect("root");
    assert!(sound.quot_used, "quotient usage must be flagged in the receipt");
}

// ---------------- Fixture 5: universe identity, no Type:Type -------------

#[test]
fn fixture05_universe_identity() {
    // Kernel level: idf.{u} : (α : Sort u) -> α -> α, instantiated at two
    // different universes; Sort 0 : Sort 0 is rejected.
    let mut k = bootstrap_kernel().expect("stdlib");
    let idf_ty = NExpr::pi(
        "α",
        NExpr::sort(Level::Param(0)),
        NExpr::pi("a", NExpr::var("α"), NExpr::var("α")),
    );
    let idf_val = NExpr::lam(
        "α",
        NExpr::sort(Level::Param(0)),
        NExpr::lam("a", NExpr::var("α"), NExpr::var("a")),
    );
    k.add_definition("idf", &["u"], idf_ty, idf_val, DeclKind::Definition, Reducibility::Regular)
        .expect("universe-polymorphic identity admitted");

    let three = NExpr::app(
        NExpr::const_("Nat.succ"),
        NExpr::app(
            NExpr::const_("Nat.succ"),
            NExpr::app(NExpr::const_("Nat.succ"), NExpr::const_("Nat.zero")),
        ),
    );
    let inst_nat = lower_closed(
        &mut k.arena,
        &mut k.names,
        &NExpr::apps(
            NExpr::const_levels("idf", vec![Level::Succ(Box::new(Level::Zero))]),
            &[NExpr::const_("Nat"), three],
        ),
    )
    .unwrap();
    let nat_ty = lower_closed(&mut k.arena, &mut k.names, &NExpr::const_("Nat")).unwrap();
    k.check(&vec![], inst_nat, nat_ty).expect("idf instantiated at Type");

    let inst_type = lower_closed(
        &mut k.arena,
        &mut k.names,
        &NExpr::apps(
            NExpr::const_levels("idf", vec![Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero))))]),
            &[NExpr::sort(Level::Succ(Box::new(Level::Zero))), NExpr::const_("Nat")],
        ),
    )
    .unwrap();
    let type_ty = lower_closed(
        &mut k.arena,
        &mut k.names,
        &NExpr::sort(Level::Succ(Box::new(Level::Zero))),
    )
    .unwrap();
    k.check(&vec![], inst_type, type_ty).expect("idf instantiated at Type 1 (the type of Nat is a value)");

    // No Type:Type: Sort 0 does not check against Sort 0.
    let s0 = lower_closed(&mut k.arena, &mut k.names, &NExpr::sort(Level::Zero)).unwrap();
    assert!(k.check(&vec![], s0, s0).is_err(), "Prop : Prop must be rejected");

    // Surface level: universe-polymorphic definitions elaborate; a
    // self-typing definition is refused.
    compile_ok("module U\ndef idf.{u} (given alpha : Type.{u}) (given a : alpha) : alpha := a\n");
    assert!(compile("module U\ndef oops : Type := Type\n").is_err(), "Type : Type must be rejected");
}

// ---------------- Fixture 6: name traps + cache isolation ------------------

fn temp_dir(tag: &str) -> PathBuf {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "rigor-conf-{tag}-{}-{}",
        std::process::id(),
        COUNTER.fetch_add(1, Ordering::SeqCst)
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn fixture06_name_traps_and_cache_isolation() {
    let a = compile_ok("module A\ntheorem t : 1 = 1 := by\n  trivial\n");
    let b = compile_ok("module B\ntheorem t : 2 = 2 := by\n  trivial\n");
    // Same theorem name, different modules/statements: distinct identities.
    assert_ne!(
        a.statement_ids.get("t"),
        b.statement_ids.get("t"),
        "statement identity must separate same-named theorems"
    );

    let dir = temp_dir("names");
    let mut cache = VerifyCache::with_disk(dir.clone());
    let ra = verify_bundle(&a.bundle_bytes, None, &Policy::constructive(), &VerifyOptions::default(), Some(&mut cache));
    assert!(ra.verdict.is_verified());
    // A warm cache from A must never satisfy B's same-named root.
    let rb = verify_bundle(&b.bundle_bytes, None, &Policy::constructive(), &VerifyOptions::default(), Some(&mut cache));
    assert!(rb.verdict.is_verified());
    assert_eq!(
        rb.roots[0].statement_id,
        b.statement_ids.get("t").cloned().unwrap(),
        "cache must be keyed by full statement identity, not by name"
    );
    assert_ne!(ra.verification_key, rb.verification_key);
    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------- Fixture 7: proof irrelevance, scoped ---------------------

#[test]
fn fixture07_proof_irrelevance_scoped() {
    // Two proofs of the *same* proposition are definitionally equal.
    assert_verified(
        r#"
module Irrel
theorem proof_irrel (given h1 : Nat.le 0 1) (given h2 : Nat.le 0 1) : Eq (Nat.le 0 1) h1 h2 := by
  exact Eq.refl (Nat.le 0 1) h1
"#,
    );

    // But irrelevance does not leak across propositions: refl at 0 and
    // refl at 1 (proofs of different Props) are not convertible.
    let mut k = bootstrap_kernel().expect("stdlib");
    let mk = |k: &mut rigor_kernel::Kernel, n: NExpr| {
        lower_closed(
            &mut k.arena,
            &mut k.names,
            &NExpr::apps(
                NExpr::const_levels("Eq.refl", vec![Level::Succ(Box::new(Level::Zero))]),
                &[NExpr::const_("Nat"), n],
            ),
        )
        .unwrap()
    };
    let p0 = mk(&mut k, NExpr::const_("Nat.zero"));
    let p1 = mk(&mut k, NExpr::app(NExpr::const_("Nat.succ"), NExpr::const_("Nat.zero")));
    assert!(
        !k.is_def_eq(&vec![], p0, p1).expect("defeq query"),
        "proof irrelevance must not identify proofs of different propositions"
    );
    assert!(k.is_def_eq(&vec![], p0, p0).expect("defeq query"));
}

// ---------------- Fixture 8: rational Farkas accept/reject -----------------

#[test]
fn fixture08_farkas_worked_example() {
    use rigor_certificates::linarith::{verify_farkas, FarkasCertificate, FarkasError};
    use rigor_certificates::{LinearConstraint, LinearForm};
    use rigor_spec::BigRat;
    use std::collections::BTreeMap;

    let form = |coeffs: &[(usize, i64)], konst: i64| LinearForm {
        coeffs: coeffs.iter().map(|(k, v)| (*k, BigRat::from_i64(*v))).collect::<BTreeMap<_, _>>(),
        constant: BigRat::from_i64(konst),
    };
    // §4.2: 2x + y >= 5, -x + y >= 1  ⊢  3y >= 7.
    let h1 = LinearConstraint { form: form(&[(0, 2), (1, 1)], -5) };
    let h2 = LinearConstraint { form: form(&[(0, -1), (1, 1)], -1) };
    let goal = LinearConstraint { form: form(&[(1, 3)], -7) };

    let good = FarkasCertificate { multipliers: vec![BigRat::from_i64(1), BigRat::from_i64(2)] };
    verify_farkas(&[h1.clone(), h2.clone()], &goal, &good).expect("(1, 2) must be accepted");

    let bad = FarkasCertificate { multipliers: vec![BigRat::from_i64(1), BigRat::from_i64(-2)] };
    assert!(
        matches!(
            verify_farkas(&[h1, h2], &goal, &bad),
            Err(FarkasError::NegativeMultiplier(1))
        ),
        "negative multipliers must be rejected even when the algebra could be rearranged"
    );
}

// ---------------- Fixture 9: sealed nonzero denominator --------------------

#[test]
fn fixture09_sealed_denominator() {
    let src = r#"
module Div
theorem div_ok (given n : Nat) (assuming h : n != 0) : n / n = n / n := by
  case denominator_nonzero
    exact h
  case denominator_nonzero
    exact h
  case main
    trivial
challenge main := div_ok
"#;
    let m = compile_with(src, "constructive").expect("compile");
    assert_eq!(m.challenges.len(), 1);
    let r = verify_bundle(
        &m.bundle_bytes,
        Some(&m.challenges[0]),
        &Policy::constructive(),
        &VerifyOptions::default(),
        None,
    );
    assert_eq!(r.verdict, VerifyVerdict::VerifiedMatched, "roots: {:?}", r.roots);

    // The undischarged variant fails at compile time: the obligation is
    // a real goal, never an assumed hypothesis.
    let bad = compile(
        "module DivBad\ntheorem div_bad (given n : Nat) : n / n = n / n := by\n  trivial\n",
    );
    assert!(bad.is_err(), "undischarged denominator obligation must fail");
}

// ---------------- Fixture 10: opaque vs transparent (diff) ------------------

const DIFF_V1: &str = r#"
module DiffEx
def two : Nat := 1 + 1
theorem t (given n : Nat) : n + 0 = n := by
  exact Nat.add_zero n
theorem u (given n : Nat) : n + 0 = n := by
  exact t n
theorem uses_two : two = two := by
  exact Eq.refl Nat two
"#;

#[test]
fn fixture10_opaque_vs_transparent() {
    use rigor_bridges::{diff_bundles, ChangeKind, Reuse};

    let v1 = compile_ok(DIFF_V1);
    let b1 = decode_bundle(&v1.bundle_bytes, &limits()).unwrap();

    // Proof repair of an opaque theorem: interface-only reuse, and no
    // dependent is invalidated.
    let src2 = DIFF_V1.replace(
        "exact Nat.add_zero n",
        "have h : n + 0 = n := Nat.add_zero n\n  exact h",
    );
    let v2 = compile_ok(&src2);
    let b2 = decode_bundle(&v2.bundle_bytes, &limits()).unwrap();
    let report = diff_bundles(&b1, &b2);
    let t = report.changes.iter().find(|c| c.name == "t").expect("diff for t");
    assert_eq!(t.kind, ChangeKind::ProofRepaired);
    assert_eq!(t.reuse, Reuse::InterfaceOnly);
    assert!(
        report.changes.iter().all(|c| !c.invalidated.iter().any(|n| n == "u")),
        "proof repair must not invalidate dependents: {:?}",
        report.changes
    );

    // Transparent change: the definition and its dependents invalidate.
    let src3 = DIFF_V1.replacen(":= 1 + 1", ":= 2", 1);
    let v3 = compile_ok(&src3);
    let b3 = decode_bundle(&v3.bundle_bytes, &limits()).unwrap();
    let report = diff_bundles(&b1, &b3);
    let two = report.changes.iter().find(|c| c.name == "two").expect("diff for two");
    assert_eq!(two.kind, ChangeKind::TransparentChanged);
    assert_eq!(two.reuse, Reuse::None);
    assert!(
        two.invalidated.iter().any(|n| n == "uses_two"),
        "dependents of a transparent change must invalidate: {:?}",
        two.invalidated
    );
}

// ---------------- Fixture 11: cache invalidation across policies -----------

#[test]
fn fixture11_policy_change_invalidates_cache() {
    let m = compile_ok(QUOT_SRC);
    let dir = temp_dir("policy");
    let mut cache = VerifyCache::with_disk(dir.clone());
    let r1 = verify_bundle(&m.bundle_bytes, None, &Policy::constructive(), &VerifyOptions::default(), Some(&mut cache));
    assert_eq!(r1.verdict, VerifyVerdict::Invalid);
    // Same cache, different policy: VerificationKey differs, so the
    // constructive INVALID is never replayed under classical policy.
    let r2 = verify_bundle(&m.bundle_bytes, None, &Policy::classical(), &VerifyOptions::default(), Some(&mut cache));
    assert!(r2.verdict.is_verified(), "roots: {:?}", r2.roots);
    assert_ne!(r1.verification_key, r2.verification_key, "policy must be inside the verification key");
    assert_eq!(r2.policy, "classical");
    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------- Fixture 12: mutually dependent theorems rejected ---------

#[test]
fn fixture12_mutual_theorem_cycle_rejected() {
    let m = compile_ok("module Cyc\ndef base : Nat := 0\ntheorem seed : base = base := by\n  trivial\n");
    let mut bundle: Bundle = decode_bundle(&m.bundle_bytes, &limits()).unwrap();
    let nat_term = bundle
        .terms
        .iter()
        .position(|t| matches!(t, TermNode::Const(n, lv) if bundle.names[*n as usize].to_dotted() == "Nat" && lv.is_empty()))
        .expect("Nat term node") as u32;

    let push_name = |bundle: &mut Bundle, s: &str| {
        bundle.names.push(rigor_kernel::Name::root(s));
        (bundle.names.len() - 1) as u32
    };
    let a_idx = push_name(&mut bundle, "cy_a");
    let b_idx = push_name(&mut bundle, "cy_b");
    let a_term = { bundle.terms.push(TermNode::Const(a_idx, vec![])); (bundle.terms.len() - 1) as u32 };
    let b_term = { bundle.terms.push(TermNode::Const(b_idx, vec![])); (bundle.terms.len() - 1) as u32 };
    for (name, value) in [(a_idx, b_term), (b_idx, a_term)] {
        bundle.declarations.push(PortableDecl {
            kind: rigor_spec::abi::DECL_THEOREM,
            name,
            level_params: vec![],
            ty: nat_term,
            value: Some(value),
            hint: rigor_spec::abi::HINT_OPAQUE,
            num_params: 0,
            constructors: vec![],
            block: None,
        });
    }
    bundle.roots.push(a_idx);
    let bytes = encode_bundle(&bundle);
    let r = verify(&bytes, &Policy::constructive());
    assert_eq!(r.verdict, VerifyVerdict::Invalid, "mutually dependent theorems must be rejected");
    let root = r.roots.iter().find(|x| x.name == "cy_a").expect("per-root verdict for cy_a");
    assert_eq!(root.verdict, VerifyVerdict::Invalid);
}

// ---------------- Fixture 13: per-root coverage, resource, tickets ---------

const TWO_ROOTS: &str = r#"
module TwoRoots
theorem good : 1 = 1 := by
  trivial
theorem bad : 2 = 2 := by
  trivial
"#;

#[test]
fn fixture13_per_root_coverage() {
    let m = compile_ok(TWO_ROOTS);
    let mut bundle = decode_bundle(&m.bundle_bytes, &limits()).unwrap();
    let value_of = |bundle: &Bundle, name: &str| {
        bundle
            .declarations
            .iter()
            .find(|d| bundle.names[d.name as usize].to_dotted() == name)
            .and_then(|d| d.value)
            .expect("decl value")
    };
    let good_value = value_of(&bundle, "good");
    for d in bundle.declarations.iter_mut() {
        if bundle.names[d.name as usize].to_dotted() == "bad" {
            d.value = Some(good_value);
        }
    }
    let bytes = encode_bundle(&bundle);
    let r = verify(&bytes, &Policy::constructive());
    // Per-root coverage: one verified root, one invalid root — the
    // failure is attributed, not smeared across the whole bundle.
    assert_eq!(r.roots.len(), 2, "every root must be covered: {:?}", r.roots);
    let good = r.roots.iter().find(|x| x.name == "good").unwrap();
    let bad = r.roots.iter().find(|x| x.name == "bad").unwrap();
    assert!(good.verdict.is_verified(), "good root: {:?}", good.diagnostic);
    assert_eq!(bad.verdict, VerifyVerdict::Invalid);
    assert_eq!(r.verdict, VerifyVerdict::Invalid);
}

#[test]
fn fixture13_resource_budget_reports_unknown() {
    let m = compile_ok(TWO_ROOTS);
    let r = verify_bundle(
        &m.bundle_bytes,
        None,
        &Policy::constructive(),
        &VerifyOptions { workers: 1, max_steps: 5, independent: false, base_bundle: None },
        None,
    );
    assert_eq!(
        r.verdict,
        VerifyVerdict::UnknownResource,
        "exhaustion is UNKNOWN_RESOURCE, never a counterexample: {:?}",
        r.roots
    );
}

#[test]
fn fixture13_invalid_ticket_invalidates_bundle() {
    let m = compile_ok(TWO_ROOTS);
    assert!(!m.bundle.tickets.is_empty(), "front end emits tickets");
    let mut bundle = m.bundle.clone();
    bundle.tickets[0].op = 0x00; // not a TicketOpcode
    let bytes = encode_bundle(&bundle);
    let r = verify(&bytes, &Policy::constructive());
    assert_eq!(
        r.verdict,
        VerifyVerdict::Invalid,
        "an invalid conversion ticket invalidates the bundle even when the core proof would check: {:?}",
        r.roots
    );
}

// ---------------- Fixture 14: packed/expanded, workers ----------------------

#[test]
fn fixture14_same_verdict_across_forms_and_workers() {
    let m = assert_verified(VEC_SRC);
    let reference = verify(&m.bundle_bytes, &Policy::constructive());
    let ref_ids: Vec<(String, String)> =
        reference.roots.iter().map(|r| (r.name.clone(), r.statement_id.clone())).collect();

    // Expanded form: decode and re-encode.
    let bundle = decode_bundle(&m.bundle_bytes, &limits()).unwrap();
    let expanded = encode_bundle(&bundle);
    for (label, bytes) in [("packed", &m.bundle_bytes), ("expanded", &expanded)] {
        for workers in [1usize, 4] {
            let r = verify_bundle(
                bytes,
                None,
                &Policy::constructive(),
                &VerifyOptions { workers, ..VerifyOptions::default() },
                None,
            );
            assert_eq!(r.verdict, reference.verdict, "{label} form with {workers} workers");
            let ids: Vec<(String, String)> =
                r.roots.iter().map(|x| (x.name.clone(), x.statement_id.clone())).collect();
            assert_eq!(ids, ref_ids, "statement ids must not depend on form or worker count");
        }
    }

    // Fully expanded through the exchange format and back.
    let text = rigor_bridges::export_bundle_exchange(&bundle);
    let imported = rigor_bridges::import_exchange(&text, false).expect("exchange import");
    let rebundled = encode_kernel(&imported.kernel, &imported.roots, &[], &[], None);
    let r = verify(&encode_bundle(&rebundled), &Policy::constructive());
    assert_eq!(r.verdict, VerifyVerdict::VerifiedSelfStated);
}
