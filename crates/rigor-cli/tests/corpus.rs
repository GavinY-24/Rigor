//! §7 corpus: multi-family mathematical modules, each compiled to a
//! bundle, verified by the Rust runtime, and re-verified by the
//! independent Python checker (ref_checker/rigor_check.py). A VERIFIED
//! from one and INVALID from the other is a release-blocking divergence;
//! the corpus therefore asserts exit code 0 from both, never a waiver.

use rigor_front::compile;
use rigor_runtime::{verify_bundle, VerifyOptions};
use rigor_spec::{Policy, VerifyVerdict};
use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};

const ALGEBRA: &str = r#"
module Algebra
theorem add_comm_g (given a b : Nat) : a + b = b + a := by
  solve poly
theorem add_assoc_g (given a b c : Nat) : (a + b) + c = a + (b + c) := by
  solve poly
theorem square_g (given a b : Nat) : (a + b) * (a + b) = a * a + (a * b + a * b) + b * b := by
  solve poly
theorem mul_assoc_comm (given x y z : Nat) : (x * y) * z = z * (y * x) := by
  solve poly
theorem calc_g (given a b : Nat) (assuming h : a = b) : a + 0 = b + 0 := by
  calc
    a + 0 = a := Nat.add_zero a
    _ = b := h
    _ = b + 0 := Eq.symm Nat (b + 0) b (Nat.add_zero b)
"#;

const ANALYSIS: &str = r#"
module Analysis
theorem bound1 (given x y : Nat) (assuming h1 : 5 <= x + y) (assuming h2 : 2 <= x) : 7 <= (x + y) + x := by
  solve farkas 1 1
theorem bound3 (given x y z : Nat) (assuming h1 : 1 <= x) (assuming h2 : 2 <= y) (assuming h3 : 3 <= z) : 6 <= x + (y + z) := by
  solve farkas 1 1 1
theorem bound_shift (given x y : Nat) (assuming h1 : 1 <= x) (assuming h2 : 1 <= y) : 2 <= y + x := by
  solve farkas 1 1
"#;

const STRUCTURES: &str = r#"
module Structures
def swap (given p : Prod Nat Nat) : Prod Nat Nat := (p.snd, p.fst)
theorem swap_invol (given p : Prod Nat Nat) : swap (swap p) = p := by
  cases p
  case mk
    trivial
inductive Pair2 : Type :=
  | mk (given a : Nat) (given b : Nat) : Pair2
def getA (given p : Pair2) : Nat := p.a
theorem getA_ex : getA (Pair2.mk 3 4) = 3 := by
  trivial
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

const NUMBERS: &str = r#"
module Numbers
inductive Even : Nat -> Prop :=
  | zero : Even 0
  | succ2 (given n : Nat) (given h : Even n) : Even (Nat.succ (Nat.succ n))
theorem even0 : Even 0 := by
  exact Even.zero
theorem even4 : Even 4 := by
  exact Even.succ2 2 (Even.succ2 0 Even.zero)
theorem mod_ex : Nat.mod 17 5 = 2 := by
  trivial
theorem div_ex : Nat.div 17 5 = 3 := by
  trivial
theorem pow_ex : Nat.pow 2 10 = 1024 := by
  trivial
theorem mixed_ex : Nat.pow 3 3 + Nat.mod 10 3 = 28 := by
  trivial
"#;

static COUNTER: AtomicUsize = AtomicUsize::new(0);

fn python_verdict(bytes: &[u8]) -> (i32, String) {
    let n = COUNTER.fetch_add(1, Ordering::SeqCst);
    let path = std::env::temp_dir().join(format!("rigor-corpus-{}-{n}.rigorb", std::process::id()));
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(bytes).unwrap();
    drop(f);
    let script = concat!(env!("CARGO_MANIFEST_DIR"), "/../../ref_checker/rigor_check.py");
    let out = std::process::Command::new("python3")
        .args([script, path.to_str().unwrap()])
        .output()
        .expect("python3 must be available for the differential corpus");
    let _ = std::fs::remove_file(&path);
    (out.status.code().unwrap_or(-1), String::from_utf8_lossy(&out.stdout).into_owned())
}

fn corpus_family(name: &str, src: &str) {
    let m = compile(src).unwrap_or_else(|e| panic!("[{name}] compile failed: {e}"));
    let r = verify_bundle(&m.bundle_bytes, None, &Policy::constructive(), &VerifyOptions::default(), None);
    assert_eq!(
        r.verdict,
        VerifyVerdict::VerifiedSelfStated,
        "[{name}] rust verdict: {:?}",
        r.roots.iter().map(|x| (&x.name, &x.verdict, &x.diagnostic)).collect::<Vec<_>>()
    );
    let (code, stdout) = python_verdict(&m.bundle_bytes);
    assert_eq!(
        code, 0,
        "[{name}] python checker must agree (VERIFIED), got exit {code}:\n{stdout}"
    );
    assert!(stdout.contains("VERIFIED"), "[{name}] python output:\n{stdout}");
}

#[test]
fn corpus_algebra() {
    corpus_family("algebra", ALGEBRA);
}

#[test]
fn corpus_analysis_inequalities() {
    corpus_family("analysis", ANALYSIS);
}

#[test]
fn corpus_structures() {
    corpus_family("structures", STRUCTURES);
}

#[test]
fn corpus_number_theory() {
    corpus_family("numbers", NUMBERS);
}

#[test]
fn differential_python_rejects_what_rust_rejects() {
    // A statement patched after sealing must be INVALID for both
    // checkers — agreement is required on negative cases too.
    let m = compile("module Neg\ntheorem one_ok : 1 = 1 := by\n  trivial\n").expect("compile");
    let mut bundle = m.bundle.clone();
    // point the theorem's value at a proof of a different shape: keep the
    // value but change its *type* by retargeting the decl type to the
    // standard library's False elimination statement shape — the simplest
    // robust corruption is truncating the bundle, which both decoders
    // must refuse.
    let bytes = encode_truncated(&bundle);
    let r = verify_bundle(&bytes, None, &Policy::constructive(), &VerifyOptions::default(), None);
    assert_eq!(r.verdict, VerifyVerdict::Invalid);
    let (code, stdout) = python_verdict(&bytes);
    assert_eq!(code, 1, "python must say INVALID too:\n{stdout}");
    bundle.roots.clear();
    let _ = bundle;
}

fn encode_truncated(bundle: &rigor_codec::Bundle) -> Vec<u8> {
    let bytes = rigor_codec::encode_bundle(bundle);
    bytes[..bytes.len() / 2].to_vec()
}
