//! Pinned core-declaration exchange format (`.rigx`).
//!
//! The exchange format is a line-oriented s-expression encoding of core
//! declarations, structurally mirroring Lean 4's low-level export (names
//! table first, then declarations whose terms use bvar/sort/const/app/lam/
//! pi/let/proj/lit constructors). It exists so that declarations produced
//! by a pinned Lean 4.36.0 exporter — or by Rigor's own exporter — can be
//! imported and *re-admitted by the kernel* without trusting the producer:
//! imported receipts from third parties are never consulted; the only
//! verdict is the one our kernel/runtime derives from the imported terms.
//!
//! Header: `rigor-exchange 1 profile L36-1.0 upstream <pin>`.
//! A mismatched profile or upstream pin is rejected unless the caller
//! explicitly overrides (the override is reported in the feature matrix).

use rigor_kernel::{DeclKind, Kernel, Level, NExpr, Reducibility};
use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub struct FeatureMatrix {
    pub declarations: usize,
    pub inductives: usize,
    pub axioms: usize,
    pub terms: usize,
    pub literals_nat: usize,
    pub literals_str: usize,
    pub projections: usize,
    pub lets: usize,
    /// Constructs that were understood and admitted.
    pub supported: Vec<String>,
    /// Constructs present but rejected (import fails on the first one).
    pub unsupported: Vec<String>,
    pub pin_override: bool,
}

#[derive(Debug, Clone, PartialEq)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn parse_sexps(src: &str) -> Result<Vec<Sexp>, String> {
    let chars: Vec<char> = src.chars().collect();
    let mut pos = 0usize;
    fn skip_ws(chars: &[char], pos: &mut usize) {
        loop {
            match chars.get(*pos) {
                Some(c) if c.is_whitespace() => *pos += 1,
                Some(';') => {
                    while *pos < chars.len() && chars[*pos] != '\n' {
                        *pos += 1;
                    }
                }
                _ => break,
            }
        }
    }
    fn parse_one(chars: &[char], pos: &mut usize) -> Result<Sexp, String> {
        skip_ws(chars, pos);
        match chars.get(*pos) {
            Some('(') => {
                *pos += 1;
                let mut items = Vec::new();
                loop {
                    skip_ws(chars, pos);
                    match chars.get(*pos) {
                        Some(')') => {
                            *pos += 1;
                            return Ok(Sexp::List(items));
                        }
                        None => return Err("unterminated '(' in exchange file".into()),
                        _ => items.push(parse_one(chars, pos)?),
                    }
                }
            }
            Some('"') => {
                *pos += 1;
                let mut s = String::new();
                loop {
                    match chars.get(*pos) {
                        None => return Err("unterminated string in exchange file".into()),
                        Some('"') => {
                            *pos += 1;
                            return Ok(Sexp::Atom(format!("\"{s}\"")));
                        }
                        Some('\\') => {
                            *pos += 1;
                            match chars.get(*pos) {
                                Some('n') => s.push('\n'),
                                Some('t') => s.push('\t'),
                                Some('"') => s.push('"'),
                                Some('\\') => s.push('\\'),
                                Some(other) => return Err(format!("bad escape \\{other}")),
                                None => return Err("unterminated string".into()),
                            }
                            *pos += 1;
                        }
                        Some(c) => {
                            s.push(*c);
                            *pos += 1;
                        }
                    }
                }
            }
            Some(_) => {
                let start = *pos;
                while let Some(c) = chars.get(*pos) {
                    if c.is_whitespace() || *c == '(' || *c == ')' || *c == ';' {
                        break;
                    }
                    *pos += 1;
                }
                Ok(Sexp::Atom(chars[start..*pos].iter().collect()))
            }
            None => Err("unexpected end of exchange file".into()),
        }
    }
    let mut out = Vec::new();
    loop {
        skip_ws(&chars, &mut pos);
        if pos >= chars.len() {
            break;
        }
        out.push(parse_one(&chars, &mut pos)?);
    }
    Ok(out)
}

fn atom(s: &Sexp) -> Result<&str, String> {
    match s {
        Sexp::Atom(a) => Ok(a),
        _ => Err("expected atom".into()),
    }
}

fn list(s: &Sexp) -> Result<&[Sexp], String> {
    match s {
        Sexp::List(l) => Ok(l),
        _ => Err("expected list".into()),
    }
}

fn head_is(s: &Sexp, h: &str) -> bool {
    matches!(s, Sexp::List(l) if matches!(l.first(), Some(Sexp::Atom(a)) if a == h))
}

fn level_of(s: &Sexp) -> Result<Level, String> {
    let l = list(s)?;
    match atom(&l[0])? {
        "zero" => Ok(Level::Zero),
        "succ" => Ok(Level::Succ(Box::new(level_of(&l[1])?))),
        "max" => Ok(Level::Max(Box::new(level_of(&l[1])?), Box::new(level_of(&l[2])?))),
        "imax" => Ok(Level::IMax(Box::new(level_of(&l[1])?), Box::new(level_of(&l[2])?))),
        "param" => {
            let i: u32 = atom(&l[1])?.parse().map_err(|_| "bad level param index")?;
            Ok(Level::Param(i))
        }
        other => Err(format!("unknown level constructor '{other}'")),
    }
}

fn level_sexp(l: &Level) -> Sexp {
    match l {
        Level::Zero => Sexp::List(vec![Sexp::Atom("zero".into())]),
        Level::Succ(a) => Sexp::List(vec![Sexp::Atom("succ".into()), level_sexp(a)]),
        Level::Max(a, b) => Sexp::List(vec![Sexp::Atom("max".into()), level_sexp(a), level_sexp(b)]),
        Level::IMax(a, b) => Sexp::List(vec![Sexp::Atom("imax".into()), level_sexp(a), level_sexp(b)]),
        Level::Param(i) => Sexp::List(vec![Sexp::Atom("param".into()), Sexp::Atom(i.to_string())]),
    }
}

fn binder_info(s: &Sexp) -> Result<rigor_kernel::BinderInfo, String> {
    use rigor_kernel::BinderInfo::*;
    Ok(match atom(s)? {
        "default" => Default,
        "implicit" => Implicit,
        "strict" => StrictImplicit,
        "instance" => InstImplicit,
        other => return Err(format!("unknown binder info '{other}'")),
    })
}

fn term_of(s: &Sexp, names: &[String], m: &mut FeatureMatrix) -> Result<NExpr, String> {
    let l = list(s)?;
    if l.is_empty() {
        return Err("empty term".into());
    }
    m.terms += 1;
    match atom(&l[0])? {
        "bvar" => {
            // Named-form input is required at the exchange boundary; bvar is
            // only accepted when a `(scope ...)` has named the binders.
            Err("exchange terms must be named (bvar found); re-export with named binders".into())
        }
        "var" => Ok(NExpr::var(atom(&l[1])?)),
        "sort" => Ok(NExpr::Sort(level_of(&l[1])?)),
        "const" => {
            let idx: usize = atom(&l[1])?.parse().map_err(|_| "bad const name index")?;
            let name = names.get(idx).cloned().ok_or_else(|| format!("const name index {idx} out of range"))?;
            let mut levels = Vec::new();
            if let Some(ls) = l.get(2) {
                for x in list(ls)? {
                    levels.push(level_of(x)?);
                }
            }
            Ok(NExpr::Const(name, levels))
        }
        "app" => Ok(NExpr::app(term_of(&l[1], names, m)?, term_of(&l[2], names, m)?)),
        "lam" => Ok(NExpr::Lam(
            atom(&l[1])?.to_string(),
            binder_info(&l[2])?,
            Box::new(term_of(&l[3], names, m)?),
            Box::new(term_of(&l[4], names, m)?),
        )),
        "pi" => Ok(NExpr::Pi(
            atom(&l[1])?.to_string(),
            binder_info(&l[2])?,
            Box::new(term_of(&l[3], names, m)?),
            Box::new(term_of(&l[4], names, m)?),
        )),
        "let" => {
            m.lets += 1;
            Ok(NExpr::Let(
                atom(&l[1])?.to_string(),
                Box::new(term_of(&l[2], names, m)?),
                Box::new(term_of(&l[3], names, m)?),
                Box::new(term_of(&l[4], names, m)?),
            ))
        }
        "proj" => {
            m.projections += 1;
            let idx: u32 = atom(&l[2])?.parse().map_err(|_| "bad projection index")?;
            Ok(NExpr::Proj(atom(&l[1])?.to_string(), idx, Box::new(term_of(&l[3], names, m)?)))
        }
        "litnat" => {
            m.literals_nat += 1;
            let v = rigor_spec::BigUint::from_decimal(atom(&l[1])?).ok_or("bad nat literal")?;
            Ok(NExpr::LitNat(v))
        }
        "litstr" => {
            m.literals_str += 1;
            let a = atom(&l[1])?;
            let inner = a.strip_prefix('"').and_then(|x| x.strip_suffix('"')).ok_or("litstr must be quoted")?;
            Ok(NExpr::LitStr(inner.to_string()))
        }
        other => {
            m.unsupported.push(other.to_string());
            Err(format!("unsupported term constructor '{other}' in exchange import"))
        }
    }
}

fn term_sexp(e: &NExpr, name_idx: &HashMap<String, usize>) -> Sexp {
    match e {
        NExpr::Var(s) => Sexp::List(vec![Sexp::Atom("var".into()), Sexp::Atom(s.clone())]),
        NExpr::Const(n, levels) => {
            let idx = name_idx.get(n).copied().unwrap_or(0);
            let ls: Vec<Sexp> = levels.iter().map(level_sexp).collect();
            Sexp::List(vec![Sexp::Atom("const".into()), Sexp::Atom(idx.to_string()), Sexp::List(ls)])
        }
        NExpr::Sort(l) => Sexp::List(vec![Sexp::Atom("sort".into()), level_sexp(l)]),
        NExpr::App(f, a) => Sexp::List(vec![Sexp::Atom("app".into()), term_sexp(f, name_idx), term_sexp(a, name_idx)]),
        NExpr::Lam(n, info, d, b) => Sexp::List(vec![
            Sexp::Atom("lam".into()),
            Sexp::Atom(n.clone()),
            Sexp::Atom(info_name(*info).to_string()),
            term_sexp(d, name_idx),
            term_sexp(b, name_idx),
        ]),
        NExpr::Pi(n, info, d, b) => Sexp::List(vec![
            Sexp::Atom("pi".into()),
            Sexp::Atom(n.clone()),
            Sexp::Atom(info_name(*info).to_string()),
            term_sexp(d, name_idx),
            term_sexp(b, name_idx),
        ]),
        NExpr::Let(n, t, v, b) => Sexp::List(vec![
            Sexp::Atom("let".into()),
            Sexp::Atom(n.clone()),
            term_sexp(t, name_idx),
            term_sexp(v, name_idx),
            term_sexp(b, name_idx),
        ]),
        NExpr::Proj(s, i, t) => Sexp::List(vec![
            Sexp::Atom("proj".into()),
            Sexp::Atom(s.clone()),
            Sexp::Atom(i.to_string()),
            term_sexp(t, name_idx),
        ]),
        NExpr::LitNat(n) => Sexp::List(vec![Sexp::Atom("litnat".into()), Sexp::Atom(n.decimal())]),
        NExpr::LitStr(s) => Sexp::List(vec![Sexp::Atom("litstr".into()), Sexp::Atom(format!("\"{}\"", escape_str(s)))]),
    }
}

fn info_name(i: rigor_kernel::BinderInfo) -> &'static str {
    use rigor_kernel::BinderInfo::*;
    match i {
        Default => "default",
        Implicit => "implicit",
        StrictImplicit => "strict",
        InstImplicit => "instance",
    }
}

fn escape_str(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n")
}

fn sexp_string(s: &Sexp) -> String {
    match s {
        Sexp::Atom(a) => a.clone(),
        Sexp::List(items) => {
            let inner: Vec<String> = items.iter().map(sexp_string).collect();
            format!("({})", inner.join(" "))
        }
    }
}

pub struct Imported {
    pub kernel: Kernel,
    pub roots: Vec<String>,
    pub matrix: FeatureMatrix,
}

/// Import an exchange file into a fresh kernel (no stdlib is assumed: the
/// file must carry every declaration it references, in order).
pub fn import_exchange(src: &str, allow_pin_override: bool) -> Result<Imported, String> {
    let mut m = FeatureMatrix::default();
    let top = parse_sexps(src)?;
    let mut names: Vec<String> = Vec::new();
    let mut kernel = Kernel::new();
    let mut roots: Vec<String> = Vec::new();
    let mut header_seen = false;
    // Inductive blocks are grouped by their block tag.
    let mut pending_block: Vec<rigor_kernel::InductiveSpec> = Vec::new();
    let mut pending_block_id: Option<String> = None;

    let flush_block = |kernel: &mut Kernel, pending: &mut Vec<rigor_kernel::InductiveSpec>, m: &mut FeatureMatrix| -> Result<(), String> {
        if pending.is_empty() {
            return Ok(());
        }
        let specs = std::mem::take(pending);
        m.inductives += specs.len();
        kernel.add_inductive_block(specs).map_err(|e| format!("imported inductive block rejected: {e}"))?;
        Ok(())
    };

    for item in &top {
        if head_is(item, "rigor-exchange") {
            let l = list(item)?;
            let version = atom(&l[1])?;
            if version != "1" {
                return Err(format!("unsupported exchange version {version}"));
            }
            let profile = atom(&l[3])?;
            if profile != rigor_spec::PROFILE_L36_V1 {
                return Err(format!("exchange profile {profile} does not match {}", rigor_spec::PROFILE_L36_V1));
            }
            let pin = atom(&l[5])?;
            if pin != rigor_spec::UPSTREAM_L36_SPEC_PIN && !allow_pin_override {
                return Err(format!(
                    "upstream pin mismatch: file declares '{pin}', this checker is pinned to '{}'; refusing to import without an explicit override",
                    rigor_spec::UPSTREAM_L36_SPEC_PIN
                ));
            }
            m.pin_override = pin != rigor_spec::UPSTREAM_L36_SPEC_PIN;
            header_seen = true;
            continue;
        }
        if !header_seen {
            return Err("exchange file must start with the rigor-exchange header".into());
        }
        if head_is(item, "name") {
            let l = list(item)?;
            let idx: usize = atom(&l[1])?.parse().map_err(|_| "bad name index")?;
            if idx != names.len() {
                return Err(format!("name table out of order: expected {}, got {idx}", names.len()));
            }
            names.push(atom(&l[2])?.to_string());
            continue;
        }
        if head_is(item, "root") {
            let l = list(item)?;
            let idx: usize = atom(&l[1])?.parse().map_err(|_| "bad root index")?;
            roots.push(names.get(idx).cloned().ok_or("root name index out of range")?);
            continue;
        }
        if head_is(item, "inductive") {
            let l = list(item)?;
            // (inductive nameidx (levels...) numparams blockid type ((ctor ty) ...))
            let name_idx: usize = atom(&l[1])?.parse().map_err(|_| "bad inductive name")?;
            let name = names.get(name_idx).cloned().ok_or("inductive name out of range")?;
            let mut level_params = Vec::new();
            for x in list(&l[2])? {
                level_params.push(atom(x)?.to_string());
            }
            let num_params: u32 = atom(&l[3])?.parse().map_err(|_| "bad numparams")?;
            let block = atom(&l[4])?.to_string();
            let ty = term_of(&l[5], &names, &mut m)?;
            let mut ctors = Vec::new();
            for c in list(&l[6])? {
                let cl = list(c)?;
                ctors.push((atom(&cl[0])?.to_string(), term_of(&cl[1], &names, &mut m)?));
            }
            match &pending_block_id {
                Some(b) if *b == block => pending_block.push(rigor_kernel::InductiveSpec {
                    name,
                    level_params,
                    ty,
                    num_params,
                    constructors: ctors,
                }),
                _ => {
                    flush_block(&mut kernel, &mut pending_block, &mut m)?;
                    pending_block_id = Some(block);
                    pending_block.push(rigor_kernel::InductiveSpec {
                        name,
                        level_params,
                        ty,
                        num_params,
                        constructors: ctors,
                    });
                }
            }
            continue;
        }
        if head_is(item, "decl") {
            flush_block(&mut kernel, &mut pending_block, &mut m)?;
            pending_block_id = None;
            let l = list(item)?;
            // (decl nameidx (levels...) kind type [value])
            let name_idx: usize = atom(&l[1])?.parse().map_err(|_| "bad decl name")?;
            let name = names.get(name_idx).cloned().ok_or("decl name out of range")?;
            let mut level_params: Vec<String> = Vec::new();
            for x in list(&l[2])? {
                level_params.push(atom(x)?.to_string());
            }
            let kind = atom(&l[3])?;
            let ty = term_of(&l[4], &names, &mut m)?;
            let lps: Vec<&str> = level_params.iter().map(|s| s.as_str()).collect();
            m.declarations += 1;
            match kind {
                "axiom" => {
                    m.axioms += 1;
                    kernel.add_axiom(&name, &lps, ty).map_err(|e| format!("imported axiom {name}: {e}"))?;
                }
                "def" | "thm" | "opaque" => {
                    let value = term_of(&l[5], &names, &mut m)?;
                    let (k, hint) = match kind {
                        "def" => (DeclKind::Definition, Reducibility::Regular),
                        "thm" => (DeclKind::Theorem, Reducibility::Opaque),
                        _ => (DeclKind::Opaque, Reducibility::Opaque),
                    };
                    kernel
                        .add_definition(&name, &lps, ty, value, k, hint)
                        .map_err(|e| format!("imported declaration {name}: {e}"))?;
                }
                other => {
                    m.unsupported.push(format!("decl kind {other}"));
                    return Err(format!("unsupported declaration kind '{other}'"));
                }
            }
            continue;
        }
        return Err(format!("unknown exchange directive: {}", sexp_string(item)));
    }
    flush_block(&mut kernel, &mut pending_block, &mut m)?;
    if !header_seen {
        return Err("empty exchange file".into());
    }
    for s in ["app", "lam", "pi", "const", "sort"] {
        m.supported.push(s.to_string());
    }
    Ok(Imported { kernel, roots, matrix: m })
}

/// Export a kernel environment to the exchange format.
pub fn export_exchange(kernel: &Kernel, roots: &[String], commentary: &str) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "(rigor-exchange 1 profile {} upstream {})\n",
        rigor_spec::PROFILE_L36_V1,
        rigor_spec::UPSTREAM_L36_SPEC_PIN
    ));
    if !commentary.is_empty() {
        out.push_str(&format!("; {commentary}\n"));
    }
    let mut name_idx: HashMap<String, usize> = HashMap::new();
    for (i, n) in kernel.names.names.iter().enumerate() {
        let dotted = n.to_dotted();
        name_idx.insert(dotted, i);
        out.push_str(&format!("(name {} {})\n", i, n.to_dotted()));
    }
    // Declarations in admission order; inductives are exported with block ids.
    for decl in &kernel.env.decls {
        let name = kernel.names.display(decl.name);
        let levels: Vec<String> = decl
            .level_params
            .iter()
            .map(|lp| kernel.names.display(*lp))
            .collect();
        let levels_str = levels.join(" ");
        match decl.kind {
            DeclKind::Constructor | DeclKind::Recursor => continue,
            DeclKind::Inductive => {
                if let Some(info) = &decl.inductive {
                    let ty_named = rigor_kernel::to_named(&kernel.arena, &kernel.names, decl.ty, &mut Vec::new());
                    let mut ctor_parts = Vec::new();
                    for c in &info.constructors {
                        let cd = kernel.env.get(*c).expect("ctor");
                        let cname = kernel.names.display(*c);
                        let cty = rigor_kernel::to_named(&kernel.arena, &kernel.names, cd.ty, &mut Vec::new());
                        ctor_parts.push(format!("({} {})", cname, sexp_string(&term_sexp(&cty, &name_idx))));
                    }
                    out.push_str(&format!(
                        "(inductive {} ({}) {} block{} {} ({}))\n",
                        name_idx.get(&name).copied().unwrap_or(0),
                        levels_str,
                        info.num_params,
                        info.block_id,
                        sexp_string(&term_sexp(&ty_named, &name_idx)),
                        ctor_parts.join(" ")
                    ));
                }
            }
            DeclKind::Axiom => {
                let ty_named = rigor_kernel::to_named(&kernel.arena, &kernel.names, decl.ty, &mut Vec::new());
                out.push_str(&format!(
                    "(decl {} ({}) axiom {})\n",
                    name_idx.get(&name).copied().unwrap_or(0),
                    levels_str,
                    sexp_string(&term_sexp(&ty_named, &name_idx))
                ));
            }
            DeclKind::External => continue,
            _ => {
                let kind = match decl.kind {
                    DeclKind::Theorem => "thm",
                    DeclKind::Opaque => "opaque",
                    DeclKind::QuotPrimitive => "def",
                    _ => "def",
                };
                let ty_named = rigor_kernel::to_named(&kernel.arena, &kernel.names, decl.ty, &mut Vec::new());
                let val_named = decl
                    .value
                    .map(|v| rigor_kernel::to_named(&kernel.arena, &kernel.names, v, &mut Vec::new()));
                match val_named {
                    Some(v) => out.push_str(&format!(
                        "(decl {} ({}) {} {} {})\n",
                        name_idx.get(&name).copied().unwrap_or(0),
                        levels_str,
                        kind,
                        sexp_string(&term_sexp(&ty_named, &name_idx)),
                        sexp_string(&term_sexp(&v, &name_idx))
                    )),
                    None => out.push_str(&format!(
                        "(decl {} ({}) axiom {})\n",
                        name_idx.get(&name).copied().unwrap_or(0),
                        levels_str,
                        sexp_string(&term_sexp(&ty_named, &name_idx))
                    )),
                }
            }
        }
    }
    for r in roots {
        if let Some(i) = name_idx.get(r) {
            out.push_str(&format!("(root {i})\n"));
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Bundle-level export (walks the portable term table directly)
// ---------------------------------------------------------------------------

fn level_node_sexp(bundle: &rigor_codec::Bundle, idx: u32) -> Sexp {
    use rigor_codec::LevelNode::*;
    match &bundle.levels[idx as usize] {
        Zero => Sexp::List(vec![Sexp::Atom("zero".into())]),
        Succ(a) => Sexp::List(vec![Sexp::Atom("succ".into()), level_node_sexp(bundle, *a)]),
        Max(a, b) => Sexp::List(vec![Sexp::Atom("max".into()), level_node_sexp(bundle, *a), level_node_sexp(bundle, *b)]),
        IMax(a, b) => Sexp::List(vec![Sexp::Atom("imax".into()), level_node_sexp(bundle, *a), level_node_sexp(bundle, *b)]),
        Param(i) => Sexp::List(vec![Sexp::Atom("param".into()), Sexp::Atom(i.to_string())]),
    }
}

fn bundle_term_sexp(bundle: &rigor_codec::Bundle, term: u32, scope: &mut Vec<String>) -> Sexp {
    use rigor_codec::TermNode::*;
    match &bundle.terms[term as usize] {
        BVar(i) => {
            // Exchange terms are named; de Bruijn indices are resolved
            // against the binder scope tracked during rendering.
            let pos = scope.len().saturating_sub(1 + *i as usize);
            let name = scope.get(pos).cloned().unwrap_or_else(|| format!("x{i}"));
            Sexp::List(vec![Sexp::Atom("var".into()), Sexp::Atom(name)])
        }
        Const(n, levels) => {
            let ls: Vec<Sexp> = levels.iter().map(|li| level_node_sexp(bundle, *li)).collect();
            Sexp::List(vec![Sexp::Atom("const".into()), Sexp::Atom(n.to_string()), Sexp::List(ls)])
        }
        Sort(l) => Sexp::List(vec![Sexp::Atom("sort".into()), level_node_sexp(bundle, *l)]),
        Pi(n, _, d, c) => {
            let dn = bundle_term_sexp(bundle, *d, scope);
            let bname = bundle.name_string(*n).rsplit('.').next().unwrap_or("x").to_string();
            scope.push(bname.clone());
            let cn = bundle_term_sexp(bundle, *c, scope);
            scope.pop();
            Sexp::List(vec![Sexp::Atom("pi".into()), Sexp::Atom(bname), Sexp::Atom("default".into()), dn, cn])
        }
        Lam(n, _, d, b) => {
            let dn = bundle_term_sexp(bundle, *d, scope);
            let bname = bundle.name_string(*n).rsplit('.').next().unwrap_or("x").to_string();
            scope.push(bname.clone());
            let bn = bundle_term_sexp(bundle, *b, scope);
            scope.pop();
            Sexp::List(vec![Sexp::Atom("lam".into()), Sexp::Atom(bname), Sexp::Atom("default".into()), dn, bn])
        }
        App(f, a) => Sexp::List(vec![
            Sexp::Atom("app".into()),
            bundle_term_sexp(bundle, *f, scope),
            bundle_term_sexp(bundle, *a, scope),
        ]),
        Let(n, t, v, b) => {
            let tn = bundle_term_sexp(bundle, *t, scope);
            let vn = bundle_term_sexp(bundle, *v, scope);
            let bname = bundle.name_string(*n).rsplit('.').next().unwrap_or("x").to_string();
            scope.push(bname.clone());
            let bn = bundle_term_sexp(bundle, *b, scope);
            scope.pop();
            Sexp::List(vec![Sexp::Atom("let".into()), Sexp::Atom(bname), tn, vn, bn])
        }
        Proj(s, i, t) => Sexp::List(vec![
            Sexp::Atom("proj".into()),
            Sexp::Atom(bundle.name_string(*s)),
            Sexp::Atom(i.to_string()),
            bundle_term_sexp(bundle, *t, scope),
        ]),
        LitNat(n) => Sexp::List(vec![Sexp::Atom("litnat".into()), Sexp::Atom(n.decimal())]),
        LitStr(s) => Sexp::List(vec![Sexp::Atom("litstr".into()), Sexp::Atom(format!("\"{}\"", escape_str(s)))]),
    }
}

/// Export a decoded bundle to the exchange format.
pub fn export_bundle_exchange(bundle: &rigor_codec::Bundle) -> String {
    use rigor_spec::abi::*;
    let mut out = String::new();
    out.push_str(&format!(
        "(rigor-exchange 1 profile {} upstream {})\n",
        rigor_spec::PROFILE_L36_V1,
        rigor_spec::UPSTREAM_L36_SPEC_PIN
    ));
    for (i, n) in bundle.names.iter().enumerate() {
        out.push_str(&format!("(name {} {})\n", i, n.to_dotted()));
    }
    for decl in &bundle.declarations {
        let levels_str = decl
            .level_params
            .iter()
            .map(|lp| bundle.name_string(*lp))
            .collect::<Vec<_>>()
            .join(" ");
        match decl.kind {
            DECL_INDUCTIVE => {
                let ctors: Vec<String> = decl
                    .constructors
                    .iter()
                    .map(|c| format!("({} {})", bundle.name_string(c.name), sexp_string(&bundle_term_sexp(bundle, c.ty, &mut Vec::new()))))
                    .collect();
                out.push_str(&format!(
                    "(inductive {} ({}) {} block{} {} ({}))\n",
                    decl.name,
                    levels_str,
                    decl.num_params,
                    decl.block.unwrap_or(0),
                    sexp_string(&bundle_term_sexp(bundle, decl.ty, &mut Vec::new())),
                    ctors.join(" ")
                ));
            }
            DECL_AXIOM => {
                out.push_str(&format!(
                    "(decl {} ({}) axiom {})\n",
                    decl.name,
                    levels_str,
                    sexp_string(&bundle_term_sexp(bundle, decl.ty, &mut Vec::new()))
                ));
            }
            _ => {
                let kind = match decl.kind {
                    DECL_THEOREM => "thm",
                    DECL_OPAQUE => "opaque",
                    _ => "def",
                };
                match decl.value {
                    Some(v) => out.push_str(&format!(
                        "(decl {} ({}) {} {} {})\n",
                        decl.name,
                        levels_str,
                        kind,
                        sexp_string(&bundle_term_sexp(bundle, decl.ty, &mut Vec::new())),
                        sexp_string(&bundle_term_sexp(bundle, v, &mut Vec::new()))
                    )),
                    None => out.push_str(&format!(
                        "(decl {} ({}) axiom {})\n",
                        decl.name,
                        levels_str,
                        sexp_string(&bundle_term_sexp(bundle, decl.ty, &mut Vec::new()))
                    )),
                }
            }
        }
    }
    for r in &bundle.roots {
        out.push_str(&format!("(root {r})\n"));
    }
    out
}
