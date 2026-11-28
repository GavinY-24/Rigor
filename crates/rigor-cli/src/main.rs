//! The `rigor` command line: build / seal / verify / explain / import /
//! export / diff / bench.
//!
//! Exit codes: 0 = success (for verify: a VERIFIED_* verdict), 1 = INVALID,
//! 2 = UNSUPPORTED, 3 = UNKNOWN_RESOURCE, 4 = usage/IO error, 5 = other
//! verdicts / internal errors.

mod json;
mod machine;

use rigor_bridges::{diff_bundles, explain, export_bundle_exchange, import_exchange, render_diff, ExplainOpts};
use rigor_codec::{decode_bundle, decode_challenge, encode_bundle, encode_challenge, Challenge};
use rigor_spec::DecoderLimits;
use rigor_runtime::{verify_bundle, Receipt, VerifyCache, VerifyOptions};
use rigor_spec::{Policy, VerifyVerdict};
use std::io::Read as _;
use std::path::PathBuf;
use std::process::ExitCode;

fn err_exit(msg: impl std::fmt::Display) -> ExitCode {
    eprintln!("error: {msg}");
    ExitCode::from(4)
}

fn read_file(path: &str) -> Result<Vec<u8>, String> {
    if path == "-" {
        let mut buf = Vec::new();
        std::io::stdin().read_to_end(&mut buf).map_err(|e| e.to_string())?;
        Ok(buf)
    } else {
        std::fs::read(path).map_err(|e| format!("cannot read {path}: {e}"))
    }
}

fn read_text(path: &str) -> Result<String, String> {
    let b = read_file(path)?;
    String::from_utf8(b).map_err(|_| format!("{path}: not valid UTF-8"))
}

fn write_out(path: Option<&str>, bytes: &[u8]) -> Result<(), String> {
    match path {
        Some(p) if p != "-" => std::fs::write(p, bytes).map_err(|e| format!("cannot write {p}: {e}")),
        _ => {
            use std::io::Write as _;
            std::io::stdout().write_all(bytes).map_err(|e| e.to_string())
        }
    }
}

struct Args {
    positional: Vec<String>,
    flags: std::collections::HashMap<String, String>,
    switches: std::collections::HashSet<String>,
}

fn parse_args(rest: &[String]) -> Args {
    let mut a = Args { positional: Vec::new(), flags: Default::default(), switches: Default::default() };
    let mut i = 0;
    while i < rest.len() {
        let s = &rest[i];
        if let Some(f) = s.strip_prefix("--") {
            if i + 1 < rest.len() && !rest[i + 1].starts_with("--") {
                a.flags.insert(f.to_string(), rest[i + 1].clone());
                i += 2;
            } else {
                a.switches.insert(f.to_string());
                i += 1;
            }
        } else if let Some(f) = s.strip_prefix('-').filter(|x| x.len() == 1) {
            // short flags: -o PATH
            if i + 1 < rest.len() {
                a.flags.insert(f.to_string(), rest[i + 1].clone());
                i += 2;
            } else {
                a.switches.insert(f.to_string());
                i += 1;
            }
        } else {
            a.positional.push(s.clone());
            i += 1;
        }
    }
    a
}

fn policy_of(args: &Args) -> Result<Policy, String> {
    match args.flags.get("policy").map(|s| s.as_str()) {
        None | Some("constructive") => Ok(Policy::constructive()),
        Some("classical") => Ok(Policy::classical()),
        Some(other) => Err(format!("unknown policy '{other}' (constructive|classical)")),
    }
}

/// Order module sources so that imports come before importers, then
/// concatenate into one compilation unit (declaration names are global).
/// Files are visited in CLI order; the sort is stable.
fn order_sources(sources: &[(String, String)]) -> Result<String, String> {
    fn module_of(src: &str) -> String {
        src.lines()
            .map(|l| l.trim())
            .find_map(|l| l.strip_prefix("module "))
            .map(|m| m.trim().to_string())
            .unwrap_or_default()
    }
    fn imports_of(src: &str) -> Vec<String> {
        let mut out = Vec::new();
        for line in src.lines() {
            if let Some(rest) = line.trim().strip_prefix("import ") {
                for dep in rest.split(',') {
                    let dep = dep.trim();
                    if !dep.is_empty() {
                        out.push(dep.to_string());
                    }
                }
            }
        }
        out
    }
    let mut by_module: std::collections::HashMap<String, &str> = Default::default();
    for (_, src) in sources {
        by_module.insert(module_of(src), src.as_str());
    }
    let mut ordered: Vec<&str> = Vec::new();
    let mut done: std::collections::HashSet<String> = Default::default();
    fn visit<'a>(
        name: &str,
        by_module: &std::collections::HashMap<String, &'a str>,
        done: &mut std::collections::HashSet<String>,
        stack: &mut Vec<String>,
        ordered: &mut Vec<&'a str>,
    ) -> Result<(), String> {
        if done.contains(name) {
            return Ok(());
        }
        if stack.iter().any(|s| s == name) {
            return Err(format!("import cycle involving module '{name}'"));
        }
        let Some(src) = by_module.get(name).copied() else {
            return Ok(()); // import of a module not among the inputs: ignore
        };
        stack.push(name.to_string());
        for dep in imports_of(src) {
            visit(&dep, by_module, done, stack, ordered)?;
        }
        stack.pop();
        done.insert(name.to_string());
        ordered.push(src);
        Ok(())
    }
    for (_, src) in sources {
        visit(&module_of(src), &by_module, &mut done, &mut Vec::new(), &mut ordered)?;
    }
    Ok(ordered.join("\n"))
}

fn compile_inputs(files: &[String], policy_name: &str) -> Result<rigor_front::CompiledModule, String> {
    let mut sources = Vec::new();
    for f in files {
        sources.push((f.clone(), read_text(f)?));
    }
    let combined = order_sources(&sources)?;
    rigor_front::compile_with(&combined, policy_name)
}

fn cmd_build(args: &Args) -> ExitCode {
    if args.positional.is_empty() {
        return err_exit("usage: rigor build <file.rigor...> [-o out.rigorb] [--challenge NAME] [--policy P]");
    }
    let policy_name = args.flags.get("policy").cloned().unwrap_or_else(|| "constructive".into());
    match compile_inputs(&args.positional, &policy_name) {
        Ok(m) => {
            if let Some(out) = args.flags.get("o") {
                if let Err(e) = write_out(Some(out), &m.bundle_bytes) {
                    return err_exit(e);
                }
                eprintln!(
                    "built {} ({} declarations, {} roots, {} tickets) -> {out}",
                    m.name,
                    m.bundle.declarations.len(),
                    m.roots.len(),
                    m.ticket_count
                );
            } else {
                println!("{}", rigor_spec::sha256::to_hex(&rigor_spec::sha256::sha256(&m.bundle_bytes)));
                for (name, sid) in &m.statement_ids {
                    if m.roots.contains(name) {
                        println!("{name} {sid}");
                    }
                }
            }
            if let Some(ch_name) = args.flags.get("challenge") {
                let ch = Challenge::from_bundle(ch_name, &m.bundle, &m.roots, &policy_name);
                let out = args.flags.get("challenge-out").cloned().unwrap_or_else(|| format!("{ch_name}.rigorc"));
                match write_out(Some(&out), &encode_challenge(&ch)) {
                    Ok(()) => eprintln!("challenge {ch_name} -> {out}"),
                    Err(e) => return err_exit(e),
                }
            }
            ExitCode::SUCCESS
        }
        Err(e) => err_exit(e),
    }
}

fn receipt_exit(receipt: &Receipt) -> ExitCode {
    match receipt.verdict {
        v if v.is_verified() => ExitCode::SUCCESS,
        VerifyVerdict::Invalid => ExitCode::from(1),
        VerifyVerdict::Unsupported => ExitCode::from(2),
        VerifyVerdict::UnknownResource => ExitCode::from(3),
        _ => ExitCode::from(5),
    }
}

/// Fast agent/development loop: compile sources and verify the resulting
/// bundle in one command, without requiring callers to manage intermediate
/// artifact paths. Any authored `challenge` declaration is used; an explicit
/// `--challenge NAME` instead seals all theorem roots under that name.
fn cmd_check(args: &Args) -> ExitCode {
    if args.positional.is_empty() {
        return err_exit("usage: rigor check <file.rigor...> [--challenge NAME] [--policy P] [--workers N] [--cache DIR] [-o out.rigorb] [--receipt out.rigorr]");
    }
    let policy = match policy_of(args) {
        Ok(p) => p,
        Err(e) => return err_exit(e),
    };
    let policy_name = args.flags.get("policy").cloned().unwrap_or_else(|| "constructive".into());
    let m = match compile_inputs(&args.positional, &policy_name) {
        Ok(m) => m,
        Err(e) => return err_exit(e),
    };
    if let Some(out) = args.flags.get("o") {
        if let Err(e) = write_out(Some(out), &m.bundle_bytes) {
            return err_exit(e);
        }
    }
    let challenge = match args.flags.get("challenge") {
        Some(name) => Some(Challenge::from_bundle(name, &m.bundle, &m.roots, &policy_name)),
        None => m.challenges.first().cloned(),
    };
    let mut opts = VerifyOptions::default();
    if let Some(w) = args.flags.get("workers") {
        opts.workers = w.parse().unwrap_or(1).max(1);
    }
    opts.independent = args.switches.contains("independent");
    let mut cache = match args.flags.get("cache") {
        Some(dir) => VerifyCache::with_disk(PathBuf::from(dir)),
        None => VerifyCache::new(),
    };
    let receipt = verify_bundle(&m.bundle_bytes, challenge.as_ref(), &policy, &opts, Some(&mut cache));
    println!("{}", receipt.to_json());
    if let Some(out) = args.flags.get("receipt") {
        if let Err(e) = write_out(Some(out), receipt.to_json().as_bytes()) {
            return err_exit(e);
        }
    }
    receipt_exit(&receipt)
}

fn cmd_seal(args: &Args) -> ExitCode {
    if args.positional.len() != 1 {
        return err_exit("usage: rigor seal <in.rigorb> [--name NAME] [--policy P] [-o out.rigorc]");
    }
    let bytes = match read_file(&args.positional[0]) {
        Ok(b) => b,
        Err(e) => return err_exit(e),
    };
    let bundle = match decode_bundle(&bytes, &DecoderLimits::default()) {
        Ok(b) => b,
        Err(e) => return err_exit(format!("cannot decode bundle: {e}")),
    };
    let roots: Vec<String> = bundle.roots.iter().map(|r| bundle.name_string(*r)).collect();
    if roots.is_empty() {
        return err_exit("bundle has no roots to seal");
    }
    let name = args.flags.get("name").cloned().unwrap_or_else(|| "main".into());
    let policy = args.flags.get("policy").cloned().unwrap_or_else(|| "constructive".into());
    let ch = Challenge::from_bundle(&name, &bundle, &roots, &policy);
    match write_out(args.flags.get("o").map(|s| s.as_str()), &encode_challenge(&ch)) {
        Ok(()) => {
            eprintln!("sealed challenge '{name}' covering {} root(s)", roots.len());
            ExitCode::SUCCESS
        }
        Err(e) => err_exit(e),
    }
}

fn cmd_verify(args: &Args) -> ExitCode {
    if args.positional.len() != 1 {
        return err_exit("usage: rigor verify <bundle.rigorb> [--challenge c.rigorc] [--policy P] [--workers N] [--independent] [--cache DIR] [--receipt out.rigorr]");
    }
    let bytes = match read_file(&args.positional[0]) {
        Ok(b) => b,
        Err(e) => return err_exit(e),
    };
    let challenge = match args.flags.get("challenge") {
        Some(path) => {
            let cb = match read_file(path) {
                Ok(b) => b,
                Err(e) => return err_exit(e),
            };
            match decode_challenge(&cb) {
                Ok(c) => Some(c),
                Err(e) => return err_exit(format!("cannot decode challenge: {e}")),
            }
        }
        None => None,
    };
    let policy = match policy_of(args) {
        Ok(p) => p,
        Err(e) => return err_exit(e),
    };
    let mut opts = VerifyOptions::default();
    if let Some(w) = args.flags.get("workers") {
        opts.workers = w.parse().unwrap_or(1).max(1);
    }
    opts.independent = args.switches.contains("independent");
    let mut cache = match args.flags.get("cache") {
        Some(dir) => VerifyCache::with_disk(PathBuf::from(dir)),
        None => VerifyCache::new(),
    };
    let receipt = verify_bundle(&bytes, challenge.as_ref(), &policy, &opts, Some(&mut cache));
    println!("{}", receipt.to_json());
    if let Some(out) = args.flags.get("receipt") {
        if let Err(e) = write_out(Some(out), receipt.to_json().as_bytes()) {
            return err_exit(e);
        }
    }
    receipt_exit(&receipt)
}

fn cmd_explain(args: &Args) -> ExitCode {
    if args.positional.len() != 1 {
        return err_exit("usage: rigor explain <bundle.rigorb> [--receipt r.rigorr] [--assumptions] [--coercions]");
    }
    let bytes = match read_file(&args.positional[0]) {
        Ok(b) => b,
        Err(e) => return err_exit(e),
    };
    let bundle = match decode_bundle(&bytes, &DecoderLimits::default()) {
        Ok(b) => b,
        Err(e) => return err_exit(format!("cannot decode bundle: {e}")),
    };
    let receipt: Option<Receipt> = match args.flags.get("receipt") {
        Some(path) => match read_text(path) {
            Ok(t) => Receipt::from_json(&t),
            Err(e) => return err_exit(e),
        },
        None => None,
    };
    let text = explain(
        &bundle,
        receipt.as_ref(),
        ExplainOpts {
            assumptions: args.switches.contains("assumptions"),
            coercions: args.switches.contains("coercions"),
            statements: true,
        },
    );
    print!("{text}");
    ExitCode::SUCCESS
}

fn cmd_import(args: &Args) -> ExitCode {
    if args.positional.len() != 1 {
        return err_exit("usage: rigor import <file.rigx> [-o out.rigorb] [--pin-override]");
    }
    let src = match read_text(&args.positional[0]) {
        Ok(s) => s,
        Err(e) => return err_exit(e),
    };
    match import_exchange(&src, args.switches.contains("pin-override")) {
        Ok(imported) => {
            let bundle = rigor_codec::encode_kernel(&imported.kernel, &imported.roots, &[], &[], None);
            let bytes = encode_bundle(&bundle);
            if let Some(out) = args.flags.get("o") {
                if let Err(e) = write_out(Some(out), &bytes) {
                    return err_exit(e);
                }
            }
            eprintln!(
                "imported {} declarations ({} inductives, {} axioms), {} terms checked, pin_override={}",
                imported.matrix.declarations,
                imported.matrix.inductives,
                imported.matrix.axioms,
                imported.matrix.terms,
                imported.matrix.pin_override
            );
            ExitCode::SUCCESS
        }
        Err(e) => err_exit(e),
    }
}

fn cmd_export(args: &Args) -> ExitCode {
    if args.positional.len() != 1 {
        return err_exit("usage: rigor export <bundle.rigorb> [-o out.rigx] [--challenge c.rigorc]");
    }
    let bytes = match read_file(&args.positional[0]) {
        Ok(b) => b,
        Err(e) => return err_exit(e),
    };
    let bundle = match decode_bundle(&bytes, &DecoderLimits::default()) {
        Ok(b) => b,
        Err(e) => return err_exit(format!("cannot decode bundle: {e}")),
    };
    let text = export_bundle_exchange(&bundle);
    if let Err(e) = write_out(args.flags.get("o").map(|s| s.as_str()), text.as_bytes()) {
        return err_exit(e);
    }
    if let Some(ch_path) = args.flags.get("challenge") {
        let cb = match read_file(ch_path) {
            Ok(b) => b,
            Err(e) => return err_exit(e),
        };
        match decode_challenge(&cb) {
            Ok(ch) => {
                eprintln!("challenge '{}' (id {}) covers: {}", ch.name, ch.challenge_id().to_hex(), ch.roots.iter().map(|r| r.name.clone()).collect::<Vec<_>>().join(", "));
            }
            Err(e) => return err_exit(format!("cannot decode challenge: {e}")),
        }
    }
    ExitCode::SUCCESS
}

fn cmd_diff(args: &Args) -> ExitCode {
    if args.positional.len() != 2 {
        return err_exit("usage: rigor diff <old.rigorb> <new.rigorb>");
    }
    let mut bundles = Vec::new();
    for p in &args.positional {
        let bytes = match read_file(p) {
            Ok(b) => b,
            Err(e) => return err_exit(e),
        };
        match decode_bundle(&bytes, &DecoderLimits::default()) {
            Ok(b) => bundles.push(b),
            Err(e) => return err_exit(format!("cannot decode {p}: {e}")),
        }
    }
    let report = diff_bundles(&bundles[0], &bundles[1]);
    print!("{}", render_diff(&report));
    ExitCode::SUCCESS
}

fn cmd_bench(args: &Args) -> ExitCode {
    let manifest = rigor_bench::run_all();
    if args.switches.contains("json") {
        println!("{}", rigor_bench::manifest_json(&manifest));
    } else {
        print!("{}", rigor_bench::render_manifest(&manifest));
    }
    ExitCode::SUCCESS
}

const USAGE: &str = "rigor — the Rigor proof language (L36 profile)\n\nusage:\n  rigor check <file.rigor...> [--challenge NAME] [--policy P] [--workers N] [--cache DIR] [-o out.rigorb]\n  rigor machine            # agent-native JSONL proof session (alias: rigor ai)\n  rigor build <file.rigor...> [-o out.rigorb] [--challenge NAME] [--policy P]\n  rigor seal <in.rigorb> [--name NAME] [--policy P] [-o out.rigorc]\n  rigor verify <bundle.rigorb> [--challenge c.rigorc] [--policy P] [--workers N] [--independent] [--cache DIR] [--receipt out.rigorr]\n  rigor explain <bundle.rigorb> [--receipt r.rigorr] [--assumptions] [--coercions]\n  rigor import <file.rigx> [-o out.rigorb] [--pin-override]\n  rigor export <bundle.rigorb> [-o out.rigx]\n  rigor diff <old.rigorb> <new.rigorb>\n  rigor bench [--json]\n";

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().collect();
    if argv.len() < 2 {
        eprintln!("{USAGE}");
        return ExitCode::from(4);
    }
    let args = parse_args(&argv[2..]);
    match argv[1].as_str() {
        "build" => cmd_build(&args),
        "check" => cmd_check(&args),
        "seal" => cmd_seal(&args),
        "verify" => cmd_verify(&args),
        "explain" => cmd_explain(&args),
        "import" => cmd_import(&args),
        "export" => cmd_export(&args),
        "diff" => cmd_diff(&args),
        "bench" => cmd_bench(&args),
        "machine" | "ai" => machine::run(),
        "-h" | "--help" | "help" => {
            println!("{USAGE}");
            ExitCode::SUCCESS
        }
        other => {
            eprintln!("unknown command '{other}'\n\n{USAGE}");
            ExitCode::from(4)
        }
    }
}
