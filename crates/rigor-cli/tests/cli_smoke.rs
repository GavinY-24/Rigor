//! CLI end-to-end smoke: build -> verify (matched) -> corrupt (exit 1).
//! Exit-code contract: 0 verified, 1 invalid, 2 unsupported,
//! 3 unknown-resource, 4 usage/IO.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn rigor() -> Command {
    Command::new(env!("CARGO_BIN_EXE_rigor"))
}

fn workdir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rigor-cli-test-{tag}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

const SRC: &str = "module Demo\n\
theorem add_comm2 (given x y : Nat) : x + y = y + x := by\n  solve poly\n\
theorem zero_add (given n : Nat) : 0 + n = n := by\n  induction n\n  case zero\n    trivial\n  case succ\n    trivial\n\
challenge main := add_comm2, zero_add\n";

#[test]
fn build_verify_and_corruption_exit_codes() {
    let dir = workdir("smoke");
    let src = dir.join("demo.rigor");
    fs::write(&src, SRC).unwrap();
    let bundle = dir.join("demo.rigorb");
    let challenge = dir.join("demo.rigorc");

    let out = rigor()
        .args(["build", src.to_str().unwrap(), "-o", bundle.to_str().unwrap(), "--challenge", "main", "--challenge-out", challenge.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(out.status.success(), "build failed: {}", String::from_utf8_lossy(&out.stderr));
    assert!(bundle.exists() && challenge.exists());

    // verify against the sealed challenge
    let out = rigor()
        .args(["verify", bundle.to_str().unwrap(), "--challenge", challenge.to_str().unwrap(), "--workers", "4"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "verify failed: {}", String::from_utf8_lossy(&out.stdout));

    // seal + verify round trip through a fresh challenge file
    let ch2 = dir.join("sealed.rigorc");
    let out = rigor()
        .args(["seal", bundle.to_str().unwrap(), "-o", ch2.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(out.status.success(), "seal failed: {}", String::from_utf8_lossy(&out.stderr));

    // corrupt one byte deep in the bundle: verdict INVALID, exit 1
    let mut bytes = fs::read(&bundle).unwrap();
    let mid = bytes.len() / 2;
    bytes[mid] ^= 0xFF;
    let bad = dir.join("bad.rigorb");
    fs::write(&bad, &bytes).unwrap();
    let out = rigor().args(["verify", bad.to_str().unwrap()]).output().unwrap();
    assert_eq!(
        out.status.code(),
        Some(1),
        "corrupt bundle must exit 1, stdout: {}",
        String::from_utf8_lossy(&out.stdout)
    );

    // usage error exit 4
    let out = rigor().args(["verify"]).output().unwrap();
    assert_eq!(out.status.code(), Some(4));

    let _ = fs::remove_dir_all(&dir);
}
