//! Newline-delimited JSON interface to the stateful machine protocol.
//!
//! One JSON object is read per input line and exactly one JSON object is
//! written per output line. This keeps the interface trivially composable for
//! agents without adding serialization dependencies to the workspace.

use crate::json::{parse, Json};
use rigor_front::protocol::{Command, Machine, Response};
use rigor_runtime::receipt::json_str;
use rigor_runtime::{verify_bundle, VerifyOptions};
use rigor_spec::sha256::to_hex;
use rigor_spec::Policy;
use std::io::{BufRead, Write as _};
use std::process::ExitCode;

fn field<'a>(obj: &'a Json, names: &[&str]) -> Option<&'a Json> {
    names.iter().find_map(|n| obj.get(n))
}

fn string_field(obj: &Json, names: &[&str], required: &str) -> Result<String, String> {
    field(obj, names)
        .and_then(|v| v.as_str())
        .map(str::to_string)
        .ok_or_else(|| format!("missing or non-string field '{required}'"))
}

fn command_from_json(obj: &Json) -> Result<Option<Command>, String> {
    let op = string_field(obj, &["op", "command"], "op")?.to_ascii_lowercase();
    Ok(match op.as_str() {
        "open" => Some(Command::Open { source: string_field(obj, &["source", "src"], "source")? }),
        "inspect" => Some(Command::Inspect),
        "suggest" | "hints" => Some(Command::Suggest),
        "restore" | "checkout" | "jump" => Some(Command::Restore {
            state_id: string_field(obj, &["state", "state_id"], "state")?,
        }),
        "fork" | "focus" => Some(Command::Fork { goal_tag: string_field(obj, &["goal", "goal_tag", "tag"], "goal")? }),
        "apply" | "refine" => Some(Command::Apply { tactic: string_field(obj, &["tactic", "text"], "tactic")? }),
        "cert" | "submit_cert" | "certificate" => {
            let plugin = string_field(obj, &["plugin"], "plugin")?;
            let args = match obj.get("args").and_then(|v| v.as_array()) {
                Some(items) => items
                    .iter()
                    .map(|v| match v {
                        Json::String(s) => Ok(s.clone()),
                        Json::Number(n) => Ok(n.clone()),
                        _ => Err("args must contain only strings or numbers".to_string()),
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                None => Vec::new(),
            };
            Some(Command::SubmitCert { plugin, args })
        }
        "seal" => Some(Command::Seal),
        "quit" | "exit" | "close" => None,
        other => return Err(format!("unknown op '{other}'")),
    })
}

fn goal_json(goals: &[rigor_front::protocol::GoalView]) -> String {
    let mut out = String::from("[");
    for (i, g) in goals.iter().enumerate() {
        if i != 0 {
            out.push(',');
        }
        let ctx = g.context.iter().map(|c| json_str(c)).collect::<Vec<_>>().join(",");
        out.push_str(&format!(
            "{{\"tag\":{},\"context\":[{}],\"target\":{},\"focused\":{},\"closed\":{}}}",
            json_str(&g.tag),
            ctx,
            json_str(&g.target),
            g.focused,
            g.closed
        ));
    }
    out.push(']');
    out
}

fn suggestions_json(resp: &Response) -> String {
    let mut out = String::from("[");
    for (i, s) in resp.suggestions.iter().enumerate() {
        if i != 0 {
            out.push(',');
        }
        out.push_str(&format!(
            "{{\"tactic\":{},\"reason\":{},\"score\":{}}}",
            json_str(&s.tactic),
            json_str(&s.reason),
            s.score
        ));
    }
    out.push(']');
    out
}

fn response_json(resp: &Response, verification_json: Option<String>, output_error: Option<&str>, include_bundle: bool) -> String {
    let mut fields = vec![
        format!("\"ok\":{}", resp.ok && output_error.is_none()),
        format!("\"state_id\":{}", json_str(&resp.state_id)),
        format!("\"message\":{}", json_str(&resp.message)),
        format!(
            "\"theorem\":{}",
            resp.theorem.as_deref().map(json_str).unwrap_or_else(|| "null".into())
        ),
        format!("\"goals\":{}", goal_json(&resp.goals)),
        format!("\"suggestions\":{}", suggestions_json(resp)),
    ];
    if let Some(error) = output_error {
        fields.push(format!("\"error\":{}", json_str(error)));
    }
    if let Some(sealed) = &resp.sealed {
        let mut sf = vec![
            format!("\"bytes\":{}", sealed.bundle_bytes.len()),
            format!(
                "\"statement_id\":{}",
                sealed.statement_id.as_deref().map(json_str).unwrap_or_else(|| "null".into())
            ),
        ];
        if include_bundle {
            sf.push(format!("\"bundle_hex\":{}", json_str(&to_hex(&sealed.bundle_bytes))));
        }
        if let Some(v) = verification_json {
            sf.push(format!("\"verification\":{v}"));
        }
        fields.push(format!("\"sealed\":{{{}}}", sf.join(",")));
    }
    format!("{{{}}}", fields.join(","))
}

fn error_json(message: &str) -> String {
    format!(
        "{{\"ok\":false,\"state_id\":\"\",\"message\":{},\"theorem\":null,\"goals\":[],\"suggestions\":[]}}",
        json_str(message)
    )
}

fn help_json() -> String {
    let ops = [
        "open: {op,source}",
        "inspect: {op}",
        "suggest: {op}",
        "apply: {op,tactic}",
        "cert: {op,plugin,args[]}",
        "fork: {op,goal}",
        "restore: {op,state}",
        "seal: {op,verify?,policy?,path?,include_bundle?}",
        "quit: {op}",
    ];
    format!(
        "{{\"ok\":true,\"protocol\":\"rigor-machine-jsonl-v1\",\"ops\":[{}],\"note\":{}}}",
        ops.iter().map(|s| json_str(s)).collect::<Vec<_>>().join(","),
        json_str("input is one JSON object per line; output is one JSON object per line; suggestions are untrusted producer hints and every seal is kernel-checked")
    )
}

/// Run the JSONL protocol until EOF or a quit command.
pub fn run() -> ExitCode {
    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout();
    let mut machine = Machine::new();
    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(e) => {
                eprintln!("error reading stdin: {e}");
                return ExitCode::from(4);
            }
        };
        if line.trim().is_empty() {
            continue;
        }
        let parsed = match parse(&line) {
            Ok(v) => v,
            Err(e) => {
                let _ = writeln!(stdout, "{}", error_json(&format!("bad JSON: {e}")));
                let _ = stdout.flush();
                continue;
            }
        };
        if parsed.get("op").and_then(|v| v.as_str()).map(|s| s.eq_ignore_ascii_case("help")) == Some(true) {
            let _ = writeln!(stdout, "{}", help_json());
            let _ = stdout.flush();
            continue;
        }
        let cmd = match command_from_json(&parsed) {
            Ok(Some(c)) => c,
            Ok(None) => break,
            Err(e) => {
                let _ = writeln!(stdout, "{}", error_json(&e));
                let _ = stdout.flush();
                continue;
            }
        };
        let is_seal = matches!(cmd, Command::Seal);
        let policy = if is_seal {
            match parsed.get("policy").and_then(|v| v.as_str()).unwrap_or("constructive") {
                "constructive" => Policy::constructive(),
                "classical" => Policy::classical(),
                other => {
                    let _ = writeln!(stdout, "{}", error_json(&format!("unknown policy '{other}' (constructive|classical)")));
                    let _ = stdout.flush();
                    continue;
                }
            }
        } else {
            Policy::constructive()
        };
        let resp = machine.execute(cmd);
        let mut verification_json = None;
        let mut output_error = None;
        if is_seal && resp.ok {
            if let Some(sealed) = &resp.sealed {
                let verify = parsed.get("verify").and_then(|v| v.as_bool()).unwrap_or(true);
                if verify {
                    let receipt = verify_bundle(
                        &sealed.bundle_bytes,
                        None,
                        &policy,
                        &VerifyOptions::default(),
                        None,
                    );
                    if !receipt.verdict.is_verified() {
                        output_error = Some(format!("independent verification failed with {}", receipt.verdict.as_str()));
                    }
                    verification_json = Some(format!(
                        "{{\"verdict\":{},\"verification_key\":{},\"kernel_steps\":{},\"wall_ms\":{}}}",
                        json_str(receipt.verdict.as_str()),
                        json_str(&receipt.verification_key),
                        receipt.kernel_steps,
                        receipt.wall_ms
                    ));
                }
                if output_error.is_none() {
                    if let Some(path) = parsed.get("path").and_then(|v| v.as_str()) {
                        if let Err(e) = std::fs::write(path, &sealed.bundle_bytes) {
                            output_error = Some(format!("cannot write bundle to {path}: {e}"));
                        }
                    }
                }
            }
        }
        let include_bundle = parsed.get("include_bundle").and_then(|v| v.as_bool()).unwrap_or(true);
        let _ = writeln!(stdout, "{}", response_json(&resp, verification_json, output_error.as_deref(), include_bundle));
        let _ = stdout.flush();
    }
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cert_accepts_numeric_multipliers() {
        let value = parse(r#"{"op":"cert","plugin":"farkas","args":[1,2]}"#).unwrap();
        let cmd = command_from_json(&value).unwrap().unwrap();
        match cmd {
            Command::SubmitCert { plugin, args } => {
                assert_eq!(plugin, "farkas");
                assert_eq!(args, vec!["1".to_string(), "2".to_string()]);
            }
            other => panic!("unexpected command: {other:?}"),
        }
    }
}
