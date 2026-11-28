use rigor_front::protocol::{Command, Machine};
use rigor_front::{compile, compile_with};
use rigor_runtime::{verify_bundle, VerifyOptions};
use rigor_spec::{Policy, VerifyVerdict};

fn verify_ok(src: &str) -> rigor_front::CompiledModule {
    let m = compile(src).unwrap_or_else(|e| panic!("compile failed: {e}"));
    let receipt = verify_bundle(&m.bundle_bytes, None, &Policy::constructive(), &VerifyOptions::default(), None);
    assert!(
        receipt.verdict.is_verified(),
        "expected verified, got {:?}: {:?}",
        receipt.verdict,
        receipt.roots.iter().map(|r| &r.diagnostic).collect::<Vec<_>>()
    );
    m
}

#[test]
fn exact_and_solve_poly() {
    verify_ok(
        r#"
module Demo
theorem add_zero_r (given n : Nat) : n + 0 = n := by
  exact Nat.add_zero n
theorem add_comm2 (given a b : Nat) : a + b = b + a := by
  solve poly
theorem square_id (given x : Nat) : (x + 1) * (x + 1) = x * x + (x + x) + 1 := by
  solve poly
"#,
    );
}

#[test]
fn induction_nat() {
    verify_ok(
        r#"
module Demo
theorem zero_add (given n : Nat) : 0 + n = n := by
  induction n
  case zero
    trivial
  case succ
    trivial
"#,
    );
}

#[test]
fn farkas_surface() {
    verify_ok(
        r#"
module Demo
theorem farkas_ex (given x y : Nat) (assuming h1 : 2 <= x) (assuming h2 : 2 <= x + y) : 4 <= x + (x + y) := by
  solve farkas 1 1
"#,
    );
}

#[test]
fn sat_surface() {
    verify_ok(
        r#"
module Demo
theorem sat_ex (given v0 v1 : Bool) : ((v0 && v1) && !v0) = Bool.false := by
  solve sat
"#,
    );
}

#[test]
fn rewrite_surface() {
    verify_ok(
        r#"
module Demo
theorem rw_ex (given a b : Nat) (assuming h : a = b) : a + 0 = b := by
  rewrite h
  exact Nat.add_zero b
"#,
    );
}

#[test]
fn strict_division_obligations() {
    // Literal denominator: no obligation.
    verify_ok(
        r#"
module Demo
theorem div_lit (given n : Nat) : n / 2 = n / 2 := by
  trivial
"#,
    );
    // Non-literal denominator: an obligation goal appears; ignoring it fails.
    let bad = compile(
        r#"
module Demo
theorem div_bad (given n : Nat) : n / n = n / n := by
  trivial
"#,
    );
    assert!(bad.is_err(), "expected unresolved denominator obligation, got Ok");
    let msg = bad.err().unwrap();
    assert!(msg.contains("denominator_nonzero"), "unexpected error: {msg}");
    // Discharging the obligation from a hypothesis works.
    verify_ok(
        r#"
module Demo
theorem div_ok (given n : Nat) (assuming h : n != 0) : n / n = n / n := by
  case denominator_nonzero
    exact h
  case denominator_nonzero
    exact h
  case main
    trivial
"#,
    );
}

#[test]
fn have_and_calc() {
    verify_ok(
        r#"
module Demo
theorem have_ex (given a b : Nat) (assuming h : a = b) : a + 0 = b + 0 := by
  have h2 : a + 0 = a := Nat.add_zero a
  calc
    a + 0 = a := h2
    _ = b := h
    _ = b + 0 := Eq.symm Nat (b + 0) b (Nat.add_zero b)
"#,
    );
}

#[test]
fn defs_and_challenge_match() {
    let src = r#"
module Demo2
def double (given n : Nat) : Nat := n + n
theorem double_zero : double 0 = 0 := by
  trivial
challenge main := double_zero
"#;
    let m = compile_with(src, "constructive").expect("compile");
    assert_eq!(m.challenges.len(), 1);
    let receipt = verify_bundle(
        &m.bundle_bytes,
        Some(&m.challenges[0]),
        &Policy::constructive(),
        &VerifyOptions::default(),
        None,
    );
    assert_eq!(receipt.verdict, VerifyVerdict::VerifiedMatched, "roots: {:?}", receipt.roots);
}

#[test]
fn inductive_surface() {
    verify_ok(
        r#"
module Demo
inductive Pair2 : Type :=
  | mk (given a : Nat) (given b : Nat) : Pair2
def getA (given p : Pair2) : Nat := p.a
theorem getA_ex : getA (Pair2.mk 3 4) = 3 := by
  trivial
inductive SVec : Nat -> Type :=
  | nil : SVec 0
  | cons (given n : Nat) (given x : Nat) (given t : SVec n) : SVec (n + 1)
theorem svec_ok (given n : Nat) (given v : SVec n) : True := by
  induction v
  case nil
    trivial
  case cons
    trivial
"#,
    );
}

#[test]
fn protocol_open_apply_seal() {
    let mut machine = Machine::new();
    let r = machine.execute(Command::Open {
        source: r#"
theorem zero_add (given n : Nat) : 0 + n = n := by
  trivial
"#
        .to_string(),
    });
    assert!(r.ok, "open failed: {}", r.message);
    // The dummy tactic in the source is not run by OPEN; the state is fresh.
    let r = machine.execute(Command::Inspect);
    assert!(r.ok);
    assert_eq!(r.goals.len(), 1);
    let id1 = r.state_id.clone();
    let r = machine.execute(Command::Apply { tactic: "induction n".into() });
    assert!(r.ok, "induction failed: {}", r.message);
    assert_ne!(id1, r.state_id, "state ids must be immutable snapshots");
    let r = machine.execute(Command::Apply { tactic: "trivial".into() });
    assert!(r.ok, "trivial zero failed: {}", r.message);
    let r = machine.execute(Command::Apply { tactic: "trivial".into() });
    assert!(r.ok, "trivial succ failed: {}", r.message);
    let r = machine.execute(Command::Seal);
    assert!(r.ok, "seal failed: {}", r.message);
    let sealed = r.sealed.expect("sealed bundle");
    let receipt = verify_bundle(&sealed.bundle_bytes, None, &Policy::constructive(), &VerifyOptions::default(), None);
    assert!(receipt.verdict.is_verified(), "sealed bundle must verify: {:?}", receipt.roots);
}

#[test]
fn protocol_suggest_and_restore() {
    let mut machine = Machine::new();
    let r = machine.execute(Command::Open {
        source: r#"
theorem zero_add (given n : Nat) : 0 + n = n := by
  trivial
"#
        .to_string(),
    });
    assert!(r.ok, "open failed: {}", r.message);
    assert!(r.suggestions.iter().any(|s| s.tactic == "solve poly"), "suggestions: {:?}", r.suggestions);
    assert!(r.suggestions.iter().any(|s| s.tactic == "induction n"), "suggestions: {:?}", r.suggestions);
    let initial = r.state_id.clone();

    let r = machine.execute(Command::Apply { tactic: "induction n".into() });
    assert!(r.ok, "induction failed: {}", r.message);
    assert!(r.goals.len() > 1);

    let r = machine.execute(Command::Restore { state_id: initial.clone() });
    assert!(r.ok, "restore failed: {}", r.message);
    assert_eq!(r.state_id, initial, "restoring an unchanged immutable state reuses its id");
    assert_eq!(r.goals.len(), 1, "branching work must not leak into the restored state");

    let r = machine.execute(Command::Suggest);
    assert!(r.ok);
    assert!(r.suggestions.iter().any(|s| s.tactic == "solve poly"));
    let r = machine.execute(Command::Apply { tactic: "solve poly".into() });
    assert!(r.ok, "suggested solve poly failed: {}", r.message);
    assert!(r.goals.iter().all(|g| g.closed));
}

#[test]
fn protocol_open_supports_inductive_prelude() {
    let mut machine = Machine::new();
    let r = machine.execute(Command::Open {
        source: r#"
inductive Pair2 : Type :=
  | mk (given a : Nat) (given b : Nat) : Pair2

def getA (given p : Pair2) : Nat := p.a

theorem pair_project : getA (Pair2.mk 3 4) = 3 := by
  trivial
"#
        .to_string(),
    });
    assert!(r.ok, "open failed: {}", r.message);
    let r = machine.execute(Command::Apply { tactic: "trivial".into() });
    assert!(r.ok, "trivial projection failed: {}", r.message);
    assert!(r.goals.iter().all(|g| g.closed));
}

#[test]
fn sorry_is_rejected() {
    let res = compile(
        r#"
module Demo
theorem nope (given n : Nat) : n = n := by
  sorry
"#,
    );
    assert!(res.is_err());
}
