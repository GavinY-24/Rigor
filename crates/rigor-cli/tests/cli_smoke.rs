//! CLI end-to-end smoke: build -> verify (matched) -> corrupt (exit 1).
//! Exit-code contract: 0 verified, 1 invalid, 2 unsupported,
//! 3 unknown-resource, 4 usage/IO.

use std::fs;
use std::path::PathBuf;
use std::io::Write as _;
use std::process::{Command, Stdio};

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

#[test]
fn check_compiles_and_verifies_in_one_command() {
    let dir = workdir("check");
    let src = dir.join("demo.rigor");
    fs::write(&src, SRC).unwrap();
    let out = rigor()
        .args(["check", src.to_str().unwrap(), "--workers", "2", "--challenge", "main"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "check failed: {}", String::from_utf8_lossy(&out.stdout));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("VERIFIED_MATCHED"), "unexpected receipt: {stdout}");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn check_includes_multiple_unnamed_input_files() {
    let dir = workdir("unnamed-inputs");
    let a = dir.join("a.rigor");
    let b = dir.join("b.rigor");
    fs::write(&a, "theorem alpha_root : 1 = 1 := by\n  trivial\n").unwrap();
    fs::write(&b, "theorem beta_root : 2 = 2 := by\n  trivial\n").unwrap();
    let out = rigor()
        .args(["check", a.to_str().unwrap(), b.to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "check failed: {}", String::from_utf8_lossy(&out.stdout));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("alpha_root"), "first unnamed input missing: {stdout}");
    assert!(stdout.contains("beta_root"), "second unnamed input missing: {stdout}");
    let _ = fs::remove_dir_all(&dir);
}

fn json_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[test]
fn machine_seal_retry_after_output_error() {
    let dir = workdir("seal-retry");
    let bad = dir.join("missing").join("out.rigorb");
    let good = dir.join("out.rigorb");
    let source = "theorem retry_goal : 1 = 1 := by\n  trivial\n";
    let input = format!(
        "{{\"op\":\"open\",\"source\":{}}}\n{{\"op\":\"apply\",\"tactic\":\"trivial\"}}\n{{\"op\":\"seal\",\"verify\":true,\"path\":{},\"include_bundle\":false}}\n{{\"op\":\"seal\",\"verify\":true,\"path\":{},\"include_bundle\":false}}\n{{\"op\":\"quit\"}}\n",
        json_string(source),
        json_string(bad.to_str().unwrap()),
        json_string(good.to_str().unwrap())
    );
    let mut child = rigor()
        .arg("machine")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.as_mut().unwrap().write_all(input.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success(), "machine failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines.len(), 4, "unexpected responses: {stdout}");
    assert!(lines[2].contains("\"ok\":false"), "first output path must fail: {}", lines[2]);
    assert!(lines[2].contains("cannot write bundle"), "first seal response: {}", lines[2]);
    assert!(lines[3].contains("\"ok\":true"), "corrected retry must reuse the admitted proof: {}", lines[3]);
    assert!(good.exists(), "corrected retry did not write the bundle");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn machine_jsonl_opens_suggests_proves_and_seals() {
    let source = "theorem add_comm2 (given x y : Nat) : x + y = y + x := by\n  trivial\n";
    let input = format!(
        "{{\"op\":\"open\",\"source\":{}}}\n{{\"op\":\"suggest\"}}\n{{\"op\":\"apply\",\"tactic\":\"solve poly\"}}\n{{\"op\":\"seal\",\"verify\":true,\"include_bundle\":false}}\n{{\"op\":\"quit\"}}\n",
        json_string(source)
    );
    let mut child = rigor()
        .arg("machine")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.as_mut().unwrap().write_all(input.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success(), "machine failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines.len(), 4, "one response per non-quit command: {stdout}");
    assert!(lines[0].contains("\"ok\":true"), "open response: {}", lines[0]);
    assert!(lines[0].contains("solve poly"), "open should include ranked suggestions: {}", lines[0]);
    assert!(lines[2].contains("\"closed\":true"), "apply response: {}", lines[2]);
    assert!(lines[3].contains("\"verdict\":\"VERIFIED_SELF_STATED\""), "seal response: {}", lines[3]);
    assert!(lines[3].contains("\"verification_key\""), "seal response: {}", lines[3]);
}
