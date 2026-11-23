//! Portable bundle model and RIGB1 encode/decode.

use crate::leb::{write_bytes, write_str, write_u64, write_usize, DecodeError, DResult, Reader};
use rigor_kernel::level::Level;
use rigor_kernel::{BinderInfo, Expr, Name, NamePart};
use rigor_spec::abi::*;
use rigor_spec::BigUint;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum LevelNode {
    Zero,
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
}

impl LevelNode {
    pub fn to_level(&self, levels: &[Level]) -> Level {
        match self {
            LevelNode::Zero => Level::Zero,
            LevelNode::Succ(i) => Level::Succ(Box::new(levels[*i as usize].clone())),
            LevelNode::Max(a, b) => Level::Max(
                Box::new(levels[*a as usize].clone()),
                Box::new(levels[*b as usize].clone()),
            ),
            LevelNode::IMax(a, b) => Level::IMax(
                Box::new(levels[*a as usize].clone()),
                Box::new(levels[*b as usize].clone()),
            ),
            LevelNode::Param(p) => Level::Param(*p),
        }
    }
}

pub fn level_to_nodes(level: &Level, nodes: &mut Vec<LevelNode>, map: &mut HashMap<Level, u32>) -> u32 {
    if let Some(&id) = map.get(level) {
        return id;
    }
    let node = match level {
        Level::Zero => LevelNode::Zero,
        Level::Succ(l) => {
            let i = level_to_nodes(l, nodes, map);
            LevelNode::Succ(i)
        }
        Level::Max(a, b) => {
            let x = level_to_nodes(a, nodes, map);
            let y = level_to_nodes(b, nodes, map);
            LevelNode::Max(x, y)
        }
        Level::IMax(a, b) => {
            let x = level_to_nodes(a, nodes, map);
            let y = level_to_nodes(b, nodes, map);
            LevelNode::IMax(x, y)
        }
        Level::Param(p) => LevelNode::Param(*p),
    };
    let id = nodes.len() as u32;
    nodes.push(node);
    map.insert(level.clone(), id);
    id
}

#[derive(Debug, Clone, PartialEq)]
pub enum TermNode {
    BVar(u32),
    Const(u32, Vec<u32>), // name idx, level idxs
    Sort(u32),            // level idx
    Pi(u32, u8, u32, u32),
    Lam(u32, u8, u32, u32),
    App(u32, u32),
    Let(u32, u32, u32, u32),
    Proj(u32, u32, u32),
    LitNat(BigUint),
    LitStr(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct CtxEntry {
    pub is_let: bool,
    pub name: u32,
    pub ty: u32,
    pub value: Option<u32>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PortableCtor {
    pub name: u32,
    pub ty: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PortableDecl {
    pub kind: u8,
    pub name: u32,
    pub level_params: Vec<u32>,
    pub ty: u32,
    pub value: Option<u32>,
    pub hint: u8,
    /// For inductive declarations: number of parameters.
    pub num_params: u32,
    /// For inductive declarations: constructors (regenerated recursors are not stored).
    pub constructors: Vec<PortableCtor>,
    /// Mutual inductive block identifier (declarations sharing it form one block).
    pub block: Option<u32>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PortableTicket {
    pub op: u8,
    pub ctx: u32,
    pub x: u32,
    pub y: u32,
    pub z: u32,
    pub refs: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Bundle {
    pub profile: String,
    pub names: Vec<Name>,
    pub levels: Vec<LevelNode>,
    pub terms: Vec<TermNode>,
    pub contexts: Vec<Vec<CtxEntry>>,
    pub declarations: Vec<PortableDecl>,
    /// Imported proof references (EvidenceIds of dependency bundles), sorted.
    pub evidence_refs: Vec<[u8; 32]>,
    pub tickets: Vec<PortableTicket>,
    pub roots: Vec<u32>, // declaration name indices
    pub commentary: Option<String>,
}

impl Bundle {
    pub fn name_string(&self, idx: u32) -> String {
        self.names
            .get(idx as usize)
            .map(|n| n.to_dotted())
            .unwrap_or_else(|| format!("<bad name {idx}>"))
    }
}

// ---------------- encode ----------------

pub fn encode_bundle(bundle: &Bundle) -> Vec<u8> {
    let mut chunks: Vec<(u8, Vec<u8>)> = Vec::new();

    // Names
    let mut p = Vec::new();
    write_usize(&mut p, bundle.names.len());
    for name in &bundle.names {
        write_usize(&mut p, name.0.len());
        for part in &name.0 {
            match part {
                NamePart::Anon => p.push(NAME_ANON),
                NamePart::Str(s) => {
                    p.push(NAME_STR);
                    write_str(&mut p, s);
                }
                NamePart::Num(n) => {
                    p.push(NAME_NUM);
                    write_u64(&mut p, *n);
                }
            }
        }
    }
    chunks.push((ChunkTag::Names as u8, p));

    // Levels
    let mut p = Vec::new();
    write_usize(&mut p, bundle.levels.len());
    for l in &bundle.levels {
        match l {
            LevelNode::Zero => p.push(LEVEL_ZERO),
            LevelNode::Succ(i) => {
                p.push(LEVEL_SUCC);
                write_u64(&mut p, *i as u64);
            }
            LevelNode::Max(a, b) => {
                p.push(LEVEL_MAX);
                write_u64(&mut p, *a as u64);
                write_u64(&mut p, *b as u64);
            }
            LevelNode::IMax(a, b) => {
                p.push(LEVEL_IMAX);
                write_u64(&mut p, *a as u64);
                write_u64(&mut p, *b as u64);
            }
            LevelNode::Param(i) => {
                p.push(LEVEL_PARAM);
                write_u64(&mut p, *i as u64);
            }
        }
    }
    chunks.push((ChunkTag::Levels as u8, p));

    // Terms
    let mut p = Vec::new();
    write_usize(&mut p, bundle.terms.len());
    for t in &bundle.terms {
        match t {
            TermNode::BVar(i) => {
                p.push(EXPR_BVAR);
                write_u64(&mut p, *i as u64);
            }
            TermNode::Const(n, ls) => {
                p.push(EXPR_CONST);
                write_u64(&mut p, *n as u64);
                write_usize(&mut p, ls.len());
                for l in ls {
                    write_u64(&mut p, *l as u64);
                }
            }
            TermNode::Sort(l) => {
                p.push(EXPR_SORT);
                write_u64(&mut p, *l as u64);
            }
            TermNode::Pi(n, b, d, c) => {
                p.push(EXPR_PI);
                write_u64(&mut p, *n as u64);
                p.push(*b);
                write_u64(&mut p, *d as u64);
                write_u64(&mut p, *c as u64);
            }
            TermNode::Lam(n, b, d, body) => {
                p.push(EXPR_LAM);
                write_u64(&mut p, *n as u64);
                p.push(*b);
                write_u64(&mut p, *d as u64);
                write_u64(&mut p, *body as u64);
            }
            TermNode::App(f, a) => {
                p.push(EXPR_APP);
                write_u64(&mut p, *f as u64);
                write_u64(&mut p, *a as u64);
            }
            TermNode::Let(n, ty, v, b) => {
                p.push(EXPR_LET);
                write_u64(&mut p, *n as u64);
                write_u64(&mut p, *ty as u64);
                write_u64(&mut p, *v as u64);
                write_u64(&mut p, *b as u64);
            }
            TermNode::Proj(s, i, t) => {
                p.push(EXPR_PROJ);
                write_u64(&mut p, *s as u64);
                write_u64(&mut p, *i as u64);
                write_u64(&mut p, *t as u64);
            }
            TermNode::LitNat(v) => {
                p.push(EXPR_LIT_NAT);
                write_bytes(&mut p, &v.to_leb128());
            }
            TermNode::LitStr(s) => {
                p.push(EXPR_LIT_STR);
                write_str(&mut p, s);
            }
        }
    }
    chunks.push((ChunkTag::Terms as u8, p));

    // Contexts
    let mut p = Vec::new();
    write_usize(&mut p, bundle.contexts.len());
    for ctx in &bundle.contexts {
        write_usize(&mut p, ctx.len());
        for e in ctx {
            p.push(if e.is_let { CTX_LET } else { CTX_BINDER });
            write_u64(&mut p, e.name as u64);
            write_u64(&mut p, e.ty as u64);
            match e.value {
                Some(v) => {
                    p.push(1);
                    write_u64(&mut p, v as u64);
                }
                None => p.push(0),
            }
        }
    }
    chunks.push((ChunkTag::Contexts as u8, p));

    // Declarations
    let mut p = Vec::new();
    write_usize(&mut p, bundle.declarations.len());
    for d in &bundle.declarations {
        p.push(d.kind);
        write_u64(&mut p, d.name as u64);
        write_usize(&mut p, d.level_params.len());
        for lp in &d.level_params {
            write_u64(&mut p, *lp as u64);
        }
        write_u64(&mut p, d.ty as u64);
        match d.value {
            Some(v) => {
                p.push(1);
                write_u64(&mut p, v as u64);
            }
            None => p.push(0),
        }
        p.push(d.hint);
        if d.kind == DECL_INDUCTIVE {
            write_u64(&mut p, d.num_params as u64);
            write_usize(&mut p, d.constructors.len());
            for c in &d.constructors {
                write_u64(&mut p, c.name as u64);
                write_u64(&mut p, c.ty as u64);
            }
            match d.block {
                Some(b) => {
                    p.push(1);
                    write_u64(&mut p, b as u64);
                }
                None => p.push(0),
            }
        }
    }
    chunks.push((ChunkTag::Declarations as u8, p));

    // Evidence refs
    let mut p = Vec::new();
    write_usize(&mut p, bundle.evidence_refs.len());
    for r in &bundle.evidence_refs {
        p.extend_from_slice(r);
    }
    chunks.push((ChunkTag::Evidence as u8, p));

    // Tickets
    let mut p = Vec::new();
    write_usize(&mut p, bundle.tickets.len());
    for t in &bundle.tickets {
        p.push(t.op);
        write_u64(&mut p, t.ctx as u64);
        write_u64(&mut p, t.x as u64);
        write_u64(&mut p, t.y as u64);
        write_u64(&mut p, t.z as u64);
        write_usize(&mut p, t.refs.len());
        for r in &t.refs {
            write_u64(&mut p, *r as u64);
        }
    }
    chunks.push((ChunkTag::Tickets as u8, p));

    // Roots
    let mut p = Vec::new();
    write_usize(&mut p, bundle.roots.len());
    for r in &bundle.roots {
        write_u64(&mut p, *r as u64);
    }
    chunks.push((ChunkTag::Roots as u8, p));

    if let Some(c) = &bundle.commentary {
        let mut p = Vec::new();
        write_str(&mut p, c);
        chunks.push((ChunkTag::Commentary as u8, p));
    }

    // Stream: magic, profile, chunk count, chunks in canonical (tag) order.
    chunks.sort_by_key(|(tag, _)| *tag);
    let mut out = Vec::new();
    out.extend_from_slice(MAGIC_RIGB1);
    write_str(&mut out, &bundle.profile);
    write_usize(&mut out, chunks.len());
    for (tag, payload) in &chunks {
        out.push(*tag);
        write_usize(&mut out, payload.len());
        out.extend_from_slice(payload);
    }
    out
}

// ---------------- decode ----------------

fn check_idx(what: &str, idx: u32, len: usize) -> DResult<()> {
    if (idx as usize) >= len {
        return Err(DecodeError(format!("{what} index {idx} out of bounds (table size {len})")));
    }
    Ok(())
}

fn check_backward(what: &str, idx: u32, current: usize) -> DResult<()> {
    if (idx as usize) >= current {
        return Err(DecodeError(format!(
            "{what} reference {idx} is not a backward reference at position {current} (cycle or forward reference)"
        )));
    }
    Ok(())
}

pub fn decode_bundle(bytes: &[u8], limits: &DecoderLimits) -> DResult<Bundle> {
    if bytes.len() > limits.max_bundle_bytes {
        return Err(DecodeError(format!(
            "bundle of {} bytes exceeds limit {}",
            bytes.len(),
            limits.max_bundle_bytes
        )));
    }
    let mut r = Reader::new(bytes);
    let magic = r.bytes(5)?;
    if magic != MAGIC_RIGB1 {
        return Err(DecodeError("bad magic (expected RIGB1)".into()));
    }
    let profile = r.string()?;
    let num_chunks = r.usize()?;
    if num_chunks > 16 {
        return Err(DecodeError("too many chunks".into()));
    }
    let mut chunks: HashMap<u8, Vec<u8>> = HashMap::new();
    let mut last_mandatory: i32 = -1;
    for _ in 0..num_chunks {
        let tag = r.byte()?;
        let len = r.usize()?;
        if len > limits.max_chunk_bytes {
            return Err(DecodeError("chunk exceeds size limit".into()));
        }
        if ChunkTag::from_byte(tag).is_none() {
            if ChunkTag::is_mandatory_range(tag) {
                return Err(DecodeError(format!("unknown mandatory chunk tag {tag:#x}")));
            } else {
                // unknown optional chunk: skip but record nothing
                let _ = r.bytes(len)?;
                continue;
            }
        }
        if chunks.contains_key(&tag) {
            return Err(DecodeError(format!("duplicate chunk tag {tag:#x}")));
        }
        if ChunkTag::is_mandatory_range(tag) {
            if (tag as i32) < last_mandatory {
                return Err(DecodeError("mandatory chunks out of canonical order".into()));
            }
            last_mandatory = tag as i32;
        }
        let payload = r.bytes(len)?.to_vec();
        chunks.insert(tag, payload);
    }
    if !r.is_done() {
        return Err(DecodeError("trailing payload after last chunk".into()));
    }
    for required in [
        ChunkTag::Names,
        ChunkTag::Levels,
        ChunkTag::Terms,
        ChunkTag::Contexts,
        ChunkTag::Declarations,
        ChunkTag::Evidence,
        ChunkTag::Tickets,
        ChunkTag::Roots,
    ] {
        if !chunks.contains_key(&(required as u8)) {
            return Err(DecodeError(format!("missing mandatory chunk {required:?}")));
        }
    }

    let mut bundle = Bundle { profile, ..Default::default() };

    // Names
    {
        let mut cr = Reader::new(&chunks[&(ChunkTag::Names as u8)]);
        let count = cr.usize()?;
        if count > limits.max_names {
            return Err(DecodeError("name table exceeds limit".into()));
        }
        let mut seen: HashMap<Name, ()> = HashMap::new();
        for _ in 0..count {
            let nparts = cr.usize()?;
            if nparts > 256 {
                return Err(DecodeError("name has too many components".into()));
            }
            let mut parts = Vec::new();
            for _ in 0..nparts {
                match cr.byte()? {
                    NAME_ANON => parts.push(NamePart::Anon),
                    NAME_STR => {
                        let s = cr.string()?;
                        if s.len() > limits.max_name_len {
                            return Err(DecodeError("name component exceeds length limit".into()));
                        }
                        parts.push(NamePart::Str(s));
                    }
                    NAME_NUM => parts.push(NamePart::Num(cr.u64()?)),
                    other => return Err(DecodeError(format!("unknown name tag {other:#x}"))),
                }
            }
            let name = Name(parts);
            if seen.insert(name.clone(), ()).is_some() {
                return Err(DecodeError(format!("duplicate name {}", name.to_dotted())));
            }
            bundle.names.push(name);
        }
        if !cr.is_done() {
            return Err(DecodeError("trailing bytes in names chunk".into()));
        }
    }

    // Levels (backward references only)
    {
        let mut cr = Reader::new(&chunks[&(ChunkTag::Levels as u8)]);
        let count = cr.usize()?;
        if count > limits.max_levels {
            return Err(DecodeError("level table exceeds limit".into()));
        }
        for i in 0..count {
            let node = match cr.byte()? {
                LEVEL_ZERO => LevelNode::Zero,
                LEVEL_SUCC => {
                    let c = cr.u64()? as u32;
                    check_backward("level", c, i)?;
                    LevelNode::Succ(c)
                }
                LEVEL_MAX => {
                    let a = cr.u64()? as u32;
                    check_backward("level", a, i)?;
                    let b = cr.u64()? as u32;
                    check_backward("level", b, i)?;
                    LevelNode::Max(a, b)
                }
                LEVEL_IMAX => {
                    let a = cr.u64()? as u32;
                    check_backward("level", a, i)?;
                    let b = cr.u64()? as u32;
                    check_backward("level", b, i)?;
                    LevelNode::IMax(a, b)
                }
                LEVEL_PARAM => LevelNode::Param(cr.u64()? as u32),
                other => return Err(DecodeError(format!("unknown level tag {other:#x}"))),
            };
            bundle.levels.push(node);
        }
        if !cr.is_done() {
            return Err(DecodeError("trailing bytes in levels chunk".into()));
        }
    }

    // Terms (backward references only)
    {
        let mut cr = Reader::new(&chunks[&(ChunkTag::Terms as u8)]);
        let count = cr.usize()?;
        if count > limits.max_terms {
            return Err(DecodeError("term table exceeds limit".into()));
        }
        for i in 0..count {
            let node = match cr.byte()? {
                EXPR_BVAR => TermNode::BVar(cr.u64()? as u32),
                EXPR_CONST => {
                    let n = cr.u64()? as u32;
                    check_idx("name", n, bundle.names.len())?;
                    let nl = cr.usize()?;
                    if nl > 64 {
                        return Err(DecodeError("too many level arguments".into()));
                    }
                    let mut ls = Vec::new();
                    for _ in 0..nl {
                        let l = cr.u64()? as u32;
                        check_idx("level", l, bundle.levels.len())?;
                        ls.push(l);
                    }
                    TermNode::Const(n, ls)
                }
                EXPR_SORT => {
                    let l = cr.u64()? as u32;
                    check_idx("level", l, bundle.levels.len())?;
                    TermNode::Sort(l)
                }
                EXPR_PI | EXPR_LAM => {
                    let is_pi = chunks[&(ChunkTag::Terms as u8)][cr.pos - 1] == EXPR_PI;
                    let n = cr.u64()? as u32;
                    check_idx("name", n, bundle.names.len())?;
                    let binder = cr.byte()?;
                    if BinderInfo::from_tag(binder).is_none() {
                        return Err(DecodeError(format!("unknown binder tag {binder:#x}")));
                    }
                    let d = cr.u64()? as u32;
                    check_backward("term", d, i)?;
                    let c = cr.u64()? as u32;
                    check_backward("term", c, i)?;
                    if is_pi {
                        TermNode::Pi(n, binder, d, c)
                    } else {
                        TermNode::Lam(n, binder, d, c)
                    }
                }
                EXPR_APP => {
                    let f = cr.u64()? as u32;
                    check_backward("term", f, i)?;
                    let a = cr.u64()? as u32;
                    check_backward("term", a, i)?;
                    TermNode::App(f, a)
                }
                EXPR_LET => {
                    let n = cr.u64()? as u32;
                    check_idx("name", n, bundle.names.len())?;
                    let t = cr.u64()? as u32;
                    check_backward("term", t, i)?;
                    let v = cr.u64()? as u32;
                    check_backward("term", v, i)?;
                    let b = cr.u64()? as u32;
                    check_backward("term", b, i)?;
                    TermNode::Let(n, t, v, b)
                }
                EXPR_PROJ => {
                    let s = cr.u64()? as u32;
                    check_idx("name", s, bundle.names.len())?;
                    let idx = cr.u64()? as u32;
                    let t = cr.u64()? as u32;
                    check_backward("term", t, i)?;
                    TermNode::Proj(s, idx, t)
                }
                EXPR_LIT_NAT => {
                    let raw = cr.take_bytes()?;
                    if raw.len() > limits.max_literal_bytes {
                        return Err(DecodeError("Nat literal exceeds size limit".into()));
                    }
                    let (v, used) = BigUint::from_leb128(&raw)
                        .ok_or_else(|| DecodeError("non-canonical Nat literal encoding".into()))?;
                    if used != raw.len() {
                        return Err(DecodeError("Nat literal has trailing bytes".into()));
                    }
                    TermNode::LitNat(v)
                }
                EXPR_LIT_STR => {
                    let s = cr.string()?;
                    if s.len() > limits.max_literal_bytes {
                        return Err(DecodeError("String literal exceeds size limit".into()));
                    }
                    TermNode::LitStr(s)
                }
                other => return Err(DecodeError(format!("unknown term tag {other:#x}"))),
            };
            bundle.terms.push(node);
        }
        if !cr.is_done() {
            return Err(DecodeError("trailing bytes in terms chunk".into()));
        }
    }

    // Contexts
    {
        let mut cr = Reader::new(&chunks[&(ChunkTag::Contexts as u8)]);
        let count = cr.usize()?;
        if count > limits.max_contexts {
            return Err(DecodeError("context table exceeds limit".into()));
        }
        for _ in 0..count {
            let n = cr.usize()?;
            if n > limits.max_context_len {
                return Err(DecodeError("context exceeds length limit".into()));
            }
            let mut ctx = Vec::new();
            for _ in 0..n {
                let tag = cr.byte()?;
                let is_let = match tag {
                    CTX_BINDER => false,
                    CTX_LET => true,
                    other => return Err(DecodeError(format!("unknown context tag {other:#x}"))),
                };
                let name = cr.u64()? as u32;
                check_idx("name", name, bundle.names.len())?;
                let ty = cr.u64()? as u32;
                check_idx("term", ty, bundle.terms.len())?;
                let value = match cr.byte()? {
                    0 => None,
                    1 => {
                        let v = cr.u64()? as u32;
                        check_idx("term", v, bundle.terms.len())?;
                        Some(v)
                    }
                    other => return Err(DecodeError(format!("bad option tag {other:#x}"))),
                };
                if is_let && value.is_none() {
                    return Err(DecodeError("let context entry without value".into()));
                }
                ctx.push(CtxEntry { is_let, name, ty, value });
            }
            bundle.contexts.push(ctx);
        }
        if !cr.is_done() {
            return Err(DecodeError("trailing bytes in contexts chunk".into()));
        }
    }

    // Declarations
    {
        let mut cr = Reader::new(&chunks[&(ChunkTag::Declarations as u8)]);
        let count = cr.usize()?;
        if count > limits.max_declarations {
            return Err(DecodeError("declaration table exceeds limit".into()));
        }
        let mut seen_names: HashMap<u32, ()> = HashMap::new();
        for _ in 0..count {
            let kind = cr.byte()?;
            if !matches!(
                kind,
                DECL_AXIOM | DECL_DEF | DECL_THEOREM | DECL_OPAQUE | DECL_QUOT | DECL_INDUCTIVE | DECL_EXTERNAL_REF
            ) {
                return Err(DecodeError(format!("unknown declaration kind {kind:#x}")));
            }
            let name = cr.u64()? as u32;
            check_idx("name", name, bundle.names.len())?;
            if seen_names.insert(name, ()).is_some() {
                return Err(DecodeError(format!(
                    "duplicate declaration {}",
                    bundle.name_string(name)
                )));
            }
            let nlp = cr.usize()?;
            if nlp > 64 {
                return Err(DecodeError("too many level parameters".into()));
            }
            let mut lps = Vec::new();
            for _ in 0..nlp {
                let lp = cr.u64()? as u32;
                check_idx("name", lp, bundle.names.len())?;
                lps.push(lp);
            }
            let ty = cr.u64()? as u32;
            check_idx("term", ty, bundle.terms.len())?;
            let value = match cr.byte()? {
                0 => None,
                1 => {
                    let v = cr.u64()? as u32;
                    check_idx("term", v, bundle.terms.len())?;
                    Some(v)
                }
                other => return Err(DecodeError(format!("bad option tag {other:#x}"))),
            };
            let hint = cr.byte()?;
            if rigor_kernel::Reducibility::from_tag(hint).is_none() {
                return Err(DecodeError(format!("unknown reducibility hint {hint:#x}")));
            }
            let (num_params, constructors, block) = if kind == DECL_INDUCTIVE {
                let np = cr.u64()? as u32;
                let nc = cr.usize()?;
                if nc > 4096 {
                    return Err(DecodeError("too many constructors".into()));
                }
                let mut ctors = Vec::new();
                for _ in 0..nc {
                    let cn = cr.u64()? as u32;
                    check_idx("name", cn, bundle.names.len())?;
                    let ct = cr.u64()? as u32;
                    check_idx("term", ct, bundle.terms.len())?;
                    ctors.push(PortableCtor { name: cn, ty: ct });
                }
                let block = match cr.byte()? {
                    0 => None,
                    1 => Some(cr.u64()? as u32),
                    other => return Err(DecodeError(format!("bad option tag {other:#x}"))),
                };
                (np, ctors, block)
            } else {
                (0, Vec::new(), None)
            };
            bundle.declarations.push(PortableDecl {
                kind,
                name,
                level_params: lps,
                ty,
                value,
                hint,
                num_params,
                constructors,
                block,
            });
        }
        if !cr.is_done() {
            return Err(DecodeError("trailing bytes in declarations chunk".into()));
        }
    }

    // Evidence refs
    {
        let mut cr = Reader::new(&chunks[&(ChunkTag::Evidence as u8)]);
        let count = cr.usize()?;
        if count > 100_000 {
            return Err(DecodeError("too many evidence references".into()));
        }
        for _ in 0..count {
            let raw = cr.bytes(32)?;
            let mut arr = [0u8; 32];
            arr.copy_from_slice(raw);
            bundle.evidence_refs.push(arr);
        }
        if !cr.is_done() {
            return Err(DecodeError("trailing bytes in evidence chunk".into()));
        }
    }

    // Tickets
    {
        let mut cr = Reader::new(&chunks[&(ChunkTag::Tickets as u8)]);
        let count = cr.usize()?;
        if count > limits.max_tickets {
            return Err(DecodeError("ticket table exceeds limit".into()));
        }
        for i in 0..count {
            let op = cr.byte()?;
            if TicketOpcode::from_byte(op).is_none() {
                return Err(DecodeError(format!("unknown ticket opcode {op:#x}")));
            }
            let ctx = cr.u64()? as u32;
            check_idx("context", ctx, bundle.contexts.len())?;
            let x = cr.u64()? as u32;
            check_idx("term", x, bundle.terms.len())?;
            let y = cr.u64()? as u32;
            check_idx("term", y, bundle.terms.len())?;
            let z = cr.u64()? as u32;
            if z != 0 {
                check_idx("term", z, bundle.terms.len())?;
            }
            let nrefs = cr.usize()?;
            if nrefs > 1024 {
                return Err(DecodeError("ticket has too many fact references".into()));
            }
            let mut refs = Vec::new();
            for _ in 0..nrefs {
                let r = cr.u64()? as u32;
                if (r as usize) >= i {
                    return Err(DecodeError("ticket references a future fact".into()));
                }
                refs.push(r);
            }
            if count > limits.max_ticket_steps && i >= limits.max_ticket_steps {
                return Err(DecodeError("ticket step limit exceeded".into()));
            }
            bundle.tickets.push(PortableTicket { op, ctx, x, y, z, refs });
        }
        if !cr.is_done() {
            return Err(DecodeError("trailing bytes in tickets chunk".into()));
        }
    }

    // Roots
    {
        let mut cr = Reader::new(&chunks[&(ChunkTag::Roots as u8)]);
        let count = cr.usize()?;
        if count > limits.max_roots {
            return Err(DecodeError("root table exceeds limit".into()));
        }
        for _ in 0..count {
            let n = cr.u64()? as u32;
            check_idx("name", n, bundle.names.len())?;
            bundle.roots.push(n);
        }
        if !cr.is_done() {
            return Err(DecodeError("trailing bytes in roots chunk".into()));
        }
    }

    if let Some(raw) = chunks.get(&(ChunkTag::Commentary as u8)) {
        let mut cr = Reader::new(raw);
        let s = cr.string()?;
        if !cr.is_done() {
            return Err(DecodeError("trailing bytes in commentary chunk".into()));
        }
        bundle.commentary = Some(s);
    }

    Ok(bundle)
}

// ---------------- kernel <-> bundle materialization ----------------

/// Build kernel expressions from the bundle tables (in table order).
pub fn materialize_levels(bundle: &Bundle) -> Vec<Level> {
    let mut out: Vec<Level> = Vec::with_capacity(bundle.levels.len());
    for n in &bundle.levels {
        out.push(n.to_level(&out));
    }
    out
}

pub fn materialize_terms(
    bundle: &Bundle,
    kernel_names: &mut rigor_kernel::NameArena,
    arena: &mut rigor_kernel::ExprArena,
) -> Vec<rigor_kernel::ExprId> {
    let levels = materialize_levels(bundle);
    let mut name_ids: Vec<rigor_kernel::NameId> = Vec::with_capacity(bundle.names.len());
    for n in &bundle.names {
        name_ids.push(kernel_names.intern(n.clone()));
    }
    let mut out: Vec<rigor_kernel::ExprId> = Vec::with_capacity(bundle.terms.len());
    for t in &bundle.terms {
        let e = match t {
            TermNode::BVar(i) => arena.bvar(*i),
            TermNode::Const(n, ls) => {
                let lv: Vec<Level> = ls.iter().map(|l| levels[*l as usize].clone()).collect();
                arena.const_(name_ids[*n as usize], lv)
            }
            TermNode::Sort(l) => arena.sort(levels[*l as usize].clone()),
            TermNode::Pi(n, b, d, c) => arena.pi(
                name_ids[*n as usize],
                BinderInfo::from_tag(*b).unwrap(),
                out[*d as usize],
                out[*c as usize],
            ),
            TermNode::Lam(n, b, d, body) => arena.lam(
                name_ids[*n as usize],
                BinderInfo::from_tag(*b).unwrap(),
                out[*d as usize],
                out[*body as usize],
            ),
            TermNode::App(f, a) => arena.app(out[*f as usize], out[*a as usize]),
            TermNode::Let(n, ty, v, b) => arena.intern(Expr::Let(
                name_ids[*n as usize],
                out[*ty as usize],
                out[*v as usize],
                out[*b as usize],
            )),
            TermNode::Proj(s, i, t) => {
                arena.intern(Expr::Proj(name_ids[*s as usize], *i, out[*t as usize]))
            }
            TermNode::LitNat(v) => arena.intern(Expr::LitNat(v.clone())),
            TermNode::LitStr(s) => arena.intern(Expr::LitStr(s.clone())),
        };
        out.push(e);
    }
    out
}

/// Encode a live kernel environment (plus roots/tickets/contexts) into a bundle.
/// Constructors and recursors are regenerated on admission and are not stored;
/// inductive declarations carry their validated constructor telescopes.
pub fn encode_kernel(
    kernel: &rigor_kernel::Kernel,
    roots: &[String],
    tickets: &[PortableTicket],
    contexts: &[Vec<CtxEntry>],
    commentary: Option<String>,
) -> Bundle {
    let mut bundle = Bundle {
        profile: rigor_spec::PROFILE_L36_V1.to_string(),
        ..Default::default()
    };
    // names: kernel name arena order is stable
    bundle.names = kernel.names.names.clone();
    let name_index = |bundle: &Bundle, id: rigor_kernel::NameId| -> u32 {
        // kernel NameId == position in names vec
        let _ = bundle;
        id
    };
    let mut level_nodes: Vec<LevelNode> = Vec::new();
    let mut level_map: HashMap<Level, u32> = HashMap::new();
    let mut term_ids: Vec<u32> = Vec::with_capacity(kernel.arena.len());
    for node in kernel.arena.nodes.iter() {
        let tn = match node {
            Expr::BVar(i) => TermNode::BVar(*i),
            Expr::Const(n, ls) => {
                let lidx: Vec<u32> = ls
                    .iter()
                    .map(|l| level_to_nodes(l, &mut level_nodes, &mut level_map))
                    .collect();
                TermNode::Const(name_index(&bundle, *n), lidx)
            }
            Expr::Sort(l) => {
                TermNode::Sort(level_to_nodes(l, &mut level_nodes, &mut level_map))
            }
            Expr::Pi(n, info, d, c) => TermNode::Pi(
                name_index(&bundle, *n),
                info.to_tag(),
                term_ids[*d as usize],
                term_ids[*c as usize],
            ),
            Expr::Lam(n, info, d, body) => TermNode::Lam(
                name_index(&bundle, *n),
                info.to_tag(),
                term_ids[*d as usize],
                term_ids[*body as usize],
            ),
            Expr::App(f, a) => TermNode::App(term_ids[*f as usize], term_ids[*a as usize]),
            Expr::Let(n, t, v, b) => TermNode::Let(
                name_index(&bundle, *n),
                term_ids[*t as usize],
                term_ids[*v as usize],
                term_ids[*b as usize],
            ),
            Expr::Proj(s, i, t) => {
                TermNode::Proj(name_index(&bundle, *s), *i, term_ids[*t as usize])
            }
            Expr::LitNat(v) => TermNode::LitNat(v.clone()),
            Expr::LitStr(s) => TermNode::LitStr(s.clone()),
        };
        let id = bundle.terms.len() as u32;
        bundle.terms.push(tn);
        term_ids.push(id);
    }
    bundle.levels = level_nodes;
    bundle.contexts = contexts.to_vec();
    bundle.tickets = tickets.to_vec();
    bundle.commentary = commentary;

    // declarations: skip generated constructors/recursors
    let mut block_counter: HashMap<u32, u32> = HashMap::new();
    let mut next_block = 0u32;
    for decl in &kernel.env.decls {
        match decl.kind {
            rigor_kernel::DeclKind::Constructor | rigor_kernel::DeclKind::Recursor => continue,
            _ => {}
        }
        let kind = match decl.kind {
            rigor_kernel::DeclKind::Axiom => DECL_AXIOM,
            rigor_kernel::DeclKind::Definition => DECL_DEF,
            rigor_kernel::DeclKind::Theorem => DECL_THEOREM,
            rigor_kernel::DeclKind::Opaque => DECL_OPAQUE,
            rigor_kernel::DeclKind::QuotPrimitive => DECL_QUOT,
            rigor_kernel::DeclKind::Inductive => DECL_INDUCTIVE,
            rigor_kernel::DeclKind::External => DECL_EXTERNAL_REF,
            rigor_kernel::DeclKind::Constructor | rigor_kernel::DeclKind::Recursor => unreachable!(),
        };
        let (num_params, constructors, block) = if let Some(info) = &decl.inductive {
            let b = *block_counter.entry(info.block_id).or_insert_with(|| {
                let v = next_block;
                next_block += 1;
                v
            });
            let ctors = info
                .constructors
                .iter()
                .map(|c| {
                    let cd = kernel.env.get(*c).unwrap();
                    PortableCtor { name: *c, ty: term_ids[cd.ty as usize] }
                })
                .collect();
            (info.num_params, ctors, Some(b))
        } else {
            (0, Vec::new(), None)
        };
        bundle.declarations.push(PortableDecl {
            kind,
            name: decl.name,
            level_params: decl.level_params.clone(),
            ty: term_ids[decl.ty as usize],
            value: decl.value.map(|v| term_ids[v as usize]),
            hint: decl.hint.to_tag(),
            num_params,
            constructors,
            block,
        });
    }
    for r in roots {
        if let Some(id) = kernel.names.lookup(r) {
            bundle.roots.push(id);
        }
    }
    bundle
}
