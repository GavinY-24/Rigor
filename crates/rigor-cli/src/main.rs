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
    fn uncommented(src: &str) -> String {
        let chars: Vec<char> = src.chars().collect();
        let mut out = String::new();
        let mut i = 0usize;
        while i < chars.len() {
            if chars[i] == '"' {
                out.push(chars[i]);
                i += 1;
                while i < chars.len() {
                    let c = chars[i];
                    out.push(c);
                    i += 1;
                    if c == '\\' && i < chars.len() {
                        out.push(chars[i]);
                        i += 1;
                    } else if c == '"' {
                        break;
                    }
                }
                continue;
            }
            if chars[i] == '-' && chars.get(i + 1) == Some(&'-') {
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
                continue;
            }
            if chars[i] == '/' && chars.get(i + 1) == Some(&'*') {
                let mut depth = 1usize;
                i += 2;
                while i < chars.len() && depth > 0 {
                    if chars[i] == '/' && chars.get(i + 1) == Some(&'*') {
                        depth += 1;
                        i += 2;
                    } else if chars[i] == '*' && chars.get(i + 1) == Some(&'/') {
                        depth -= 1;
                        i += 2;
                    } else {
                        // Newlines inside a block comment are invisible to the
                        // language lexer, so they must not split header lines here.
                        i += 1;
                    }
                }
                continue;
            }
            out.push(chars[i]);
            i += 1;
        }
        out
    }
    fn module_of(src: &str) -> String {
        uncommented(src)
            .lines()
            .map(|l| l.trim())
            .find_map(|l| l.strip_prefix("module "))
            .map(|m| m.trim().to_string())
            .unwrap_or_default()
    }
    fn imports_of(src: &str) -> Vec<String> {
        let mut out = Vec::new();
        for line in uncommented(src).lines() {
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

    #[derive(Clone, PartialEq, Eq, Hash)]
    enum SourceKey {
        Named(String),
        Unnamed(usize),
    }
    fn key_name(key: &SourceKey) -> String {
        match key {
            SourceKey::Named(name) => name.clone(),
            SourceKey::Unnamed(index) => format!("<unnamed input {index}>"),
        }
    }

    let mut keys = Vec::new();
    let mut by_key: std::collections::HashMap<SourceKey, &str> = Default::default();
    let mut named: std::collections::HashMap<String, SourceKey> = Default::default();
    for (index, (_, src)) in sources.iter().enumerate() {
        let module = module_of(src);
        let key = if module.is_empty() {
            SourceKey::Unnamed(index)
        } else {
            SourceKey::Named(module.clone())
        };
        if let SourceKey::Named(name) = &key {
            if named.insert(name.clone(), key.clone()).is_some() {
                return Err(format!("duplicate module '{name}' among input files"));
            }
        }
        by_key.insert(key.clone(), src.as_str());
        keys.push(key);
    }

    let mut ordered: Vec<&str> = Vec::new();
    let mut done: std::collections::HashSet<SourceKey> = Default::default();
    fn visit<'a>(
        key: &SourceKey,
        by_key: &std::collections::HashMap<SourceKey, &'a str>,
        named: &std::collections::HashMap<String, SourceKey>,
        done: &mut std::collections::HashSet<SourceKey>,
        stack: &mut Vec<SourceKey>,
        ordered: &mut Vec<&'a str>,
    ) -> Result<(), String> {
        if done.contains(key) {
            return Ok(());
        }
        if stack.iter().any(|k| k == key) {
            return Err(format!("import cycle involving module '{}'", key_name(key)));
        }
        let Some(src) = by_key.get(key).copied() else {
            return Ok(()); // import of a module not among the inputs: ignore
        };
        stack.push(key.clone());
        for dep in imports_of(src) {
            if let Some(dep_key) = named.get(&dep) {
                visit(dep_key, by_key, named, done, stack, ordered)?;
            }
        }
        stack.pop();
        done.insert(key.clone());
        ordered.push(src);
        Ok(())
    }
    for key in &keys {
        visit(key, &by_key, &named, &mut done, &mut Vec::new(), &mut ordered)?;
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

fn receipts_exit(receipts: &[Receipt]) -> ExitCode {
    if receipts.iter().any(|r| r.verdict == VerifyVerdict::Invalid) {
        return ExitCode::from(1);
    }
    if receipts.iter().any(|r| r.verdict == VerifyVerdict::Unsupported) {
        return ExitCode::from(2);
    }
    if receipts.iter().any(|r| r.verdict == VerifyVerdict::UnknownResource) {
        return ExitCode::from(3);
    }
    if receipts.iter().all(|r| r.verdict.is_verified()) {
        return ExitCode::SUCCESS;
    }
    ExitCode::from(5)
}

/// Fast agent/development loop: compile sources and verify the resulting
/// bundle in one command, without requiring callers to manage intermediate
/// artifact paths. Every authored `challenge` declaration is checked; an
/// explicit `--challenge NAME` instead seals all theorem roots under that name.
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
    let challenges: Vec<Option<Challenge>> = match args.flags.get("challenge") {
        Some(name) => vec![Some(Challenge::from_bundle(name, &m.bundle, &m.roots, &policy_name))],
        None if m.challenges.is_empty() => vec![None],
        None => m.challenges.iter().cloned().map(Some).collect(),
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
    let mut receipts = Vec::new();
    for challenge in &challenges {
        receipts.push(verify_bundle(
            &m.bundle_bytes,
            challenge.as_ref(),
            &policy,
            &opts,
            Some(&mut cache),
        ));
    }
    let output = if receipts.len() == 1 {
        receipts[0].to_json()
    } else {
        format!("[\n{}\n]", receipts.iter().map(|r| r.to_json()).collect::<Vec<_>>().join(",\n"))
    };
    println!("{output}");
    if let Some(out) = args.flags.get("receipt") {
        if let Err(e) = write_out(Some(out), output.as_bytes()) {
            return err_exit(e);
        }
    }
    receipts_exit(&receipts)
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

fn verdict_from_str(s: &str) -> VerifyVerdict {
    match s {
        "VERIFIED_MATCHED" => VerifyVerdict::VerifiedMatched,
        "VERIFIED_SELF_STATED" => VerifyVerdict::VerifiedSelfStated,
        "INVALID" => VerifyVerdict::Invalid,
        "UNSUPPORTED" => VerifyVerdict::Unsupported,
        "UNKNOWN_RESOURCE" => VerifyVerdict::UnknownResource,
        _ => VerifyVerdict::InternalError,
    }
}

fn receipt_from_json_value(value: &json::Json) -> Option<Receipt> {
    let verdict = verdict_from_str(value.get("verdict")?.as_str()?);
    let string_field = |key: &str| value.get(key).and_then(|v| v.as_str()).unwrap_or_default().to_string();
    let u64_field = |key: &str| match value.get(key) {
        Some(json::Json::Number(n)) => n.parse().unwrap_or(0),
        _ => 0,
    };
    Some(Receipt {
        verdict,
        roots: Vec::new(),
        profile: string_field("profile"),
        checker_build: string_field("checker_build"),
        policy: string_field("policy"),
        verification_key: string_field("verification_key"),
        challenge_id: value.get("challenge_id").and_then(|v| v.as_str()).map(str::to_string),
        covered_dependencies: Vec::new(),
        kernel_steps: u64_field("kernel_steps"),
        wall_ms: u64_field("wall_ms"),
        workers: u64_field("workers") as usize,
        bundle_bytes: u64_field("bundle_bytes") as usize,
    })
}

/// Read either one receipt object or the array emitted by `rigor check` for
/// multiple authored challenges. For explanation, surface the worst verdict
/// rather than accidentally reporting only the first challenge.
fn receipt_report_from_json(text: &str) -> Option<Receipt> {
    let parsed = json::parse(text).ok()?;
    let receipts: Vec<Receipt> = match &parsed {
        json::Json::Object(_) => vec![receipt_from_json_value(&parsed)?],
        json::Json::Array(items) => {
            if items.is_empty() {
                return None;
            }
            items.iter().map(receipt_from_json_value).collect::<Option<Vec<_>>>()?
        }
        _ => return None,
    };
    for verdict in [
        VerifyVerdict::Invalid,
        VerifyVerdict::Unsupported,
        VerifyVerdict::UnknownResource,
        VerifyVerdict::InternalError,
    ] {
        if let Some(r) = receipts.iter().find(|r| r.verdict == verdict) {
            return Some(r.clone());
        }
    }
    receipts.into_iter().next()
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
            Ok(t) => receipt_report_from_json(&t),
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
