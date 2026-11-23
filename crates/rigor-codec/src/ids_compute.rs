//! Canonical statement/evidence identifier computation over decoded bundles.
//!
//! Statement bytes are a standalone canonical encoding of one declaration's
//! statement subgraph (name, level parameters, type term; plus the value for
//! transparent definitions, whose body is part of semantic identity). Mutual
//! inductives are addressed by block hash + local ordinal, avoiding circular
//! hashes. Commentary never enters any identifier.

use crate::bundle::{Bundle, LevelNode, TermNode};
use crate::leb::{write_bytes, write_str, write_u64, write_usize};
use rigor_spec::ids;
use rigor_spec::sha256::domain_hash;
use rigor_spec::{StatementId, DOMAIN_IND_BLOCK_ID, DOMAIN_IND_MEMBER_ID};
use std::collections::HashMap;

/// Collect the subgraph of terms reachable from `roots` and re-encode it in a
/// canonical standalone byte string (fresh local indices in DFS postorder,
/// names by dotted string, levels expanded structurally).
pub fn canonical_term_subgraph(bundle: &Bundle, roots: &[u32]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut term_map: HashMap<u32, u32> = HashMap::new();
    let mut level_map: HashMap<u32, u32> = HashMap::new();
    let mut level_out: Vec<u8> = Vec::new();
    let mut term_out: Vec<u8> = Vec::new();

    fn emit_level(
        bundle: &Bundle,
        idx: u32,
        level_map: &mut HashMap<u32, u32>,
        out: &mut Vec<u8>,
        count: &mut u32,
    ) -> u32 {
        if let Some(&id) = level_map.get(&idx) {
            return id;
        }
        let node = bundle.levels[idx as usize].clone();
        let (tag, children): (u8, Vec<u32>) = match node {
            LevelNode::Zero => (0, vec![]),
            LevelNode::Succ(c) => (1, vec![c]),
            LevelNode::Max(a, b) => (2, vec![a, b]),
            LevelNode::IMax(a, b) => (3, vec![a, b]),
            LevelNode::Param(p) => {
                out.push(4);
                write_u64(out, p as u64);
                let id = *count;
                *count += 1;
                level_map.insert(idx, id);
                return id;
            }
        };
        let mut child_ids = Vec::new();
        for c in children {
            child_ids.push(emit_level(bundle, c, level_map, out, count));
        }
        out.push(tag);
        for c in child_ids {
            write_u64(out, c as u64);
        }
        let id = *count;
        *count += 1;
        level_map.insert(idx, id);
        id
    }

    fn emit_term(
        bundle: &Bundle,
        idx: u32,
        term_map: &mut HashMap<u32, u32>,
        level_map: &mut HashMap<u32, u32>,
        level_out: &mut Vec<u8>,
        level_count: &mut u32,
        out: &mut Vec<u8>,
        count: &mut u32,
    ) -> u32 {
        if let Some(&id) = term_map.get(&idx) {
            return id;
        }
        let node = bundle.terms[idx as usize].clone();
        let mut write_children = |children: &[u32],
                                  term_map: &mut HashMap<u32, u32>,
                                  out: &mut Vec<u8>,
                                  count: &mut u32|
         -> Vec<u32> {
            let mut ids = Vec::new();
            for &c in children {
                ids.push(emit_term(bundle, c, term_map, level_map, level_out, level_count, out, count));
            }
            ids
        };
        match node {
            TermNode::BVar(i) => {
                out.push(0x01);
                write_u64(out, i as u64);
            }
            TermNode::Const(n, ls) => {
                out.push(0x02);
                write_str(out, &bundle.name_string(n));
                write_usize(out, ls.len());
                for l in ls {
                    let lid = emit_level(bundle, l, level_map, level_out, level_count);
                    write_u64(out, lid as u64);
                }
            }
            TermNode::Sort(l) => {
                out.push(0x03);
                let lid = emit_level(bundle, l, level_map, level_out, level_count);
                write_u64(out, lid as u64);
            }
            TermNode::Pi(n, b, d, c) | TermNode::Lam(n, b, d, c) => {
                let tag = if matches!(bundle.terms[idx as usize], TermNode::Pi(..)) { 0x04 } else { 0x05 };
                let ids2 = write_children(&[d, c], term_map, out, count);
                out.push(tag);
                write_str(out, &bundle.name_string(n));
                out.push(b);
                write_u64(out, ids2[0] as u64);
                write_u64(out, ids2[1] as u64);
            }
            TermNode::App(f, a) => {
                let ids2 = write_children(&[f, a], term_map, out, count);
                out.push(0x06);
                write_u64(out, ids2[0] as u64);
                write_u64(out, ids2[1] as u64);
            }
            TermNode::Let(n, t, v, b) => {
                let ids2 = write_children(&[t, v, b], term_map, out, count);
                out.push(0x07);
                write_str(out, &bundle.name_string(n));
                write_u64(out, ids2[0] as u64);
                write_u64(out, ids2[1] as u64);
                write_u64(out, ids2[2] as u64);
            }
            TermNode::Proj(s, i, t) => {
                let ids2 = write_children(&[t], term_map, out, count);
                out.push(0x08);
                write_str(out, &bundle.name_string(s));
                write_u64(out, i as u64);
                write_u64(out, ids2[0] as u64);
            }
            TermNode::LitNat(v) => {
                out.push(0x09);
                write_bytes(out, &v.to_leb128());
            }
            TermNode::LitStr(s) => {
                out.push(0x0A);
                write_str(out, &s);
            }
        }
        let id = *count;
        *count += 1;
        term_map.insert(idx, id);
        id
    }

    let mut level_count = 0u32;
    let mut term_count = 0u32;
    let mut root_ids = Vec::new();
    for &r in roots {
        root_ids.push(emit_term(
            bundle,
            r,
            &mut term_map,
            &mut level_map,
            &mut level_out,
            &mut level_count,
            &mut term_out,
            &mut term_count,
        ));
    }
    out.extend_from_slice(b"STMTGRAPH1");
    write_usize(&mut out, level_out.len());
    out.extend_from_slice(&level_out);
    out.extend_from_slice(&term_out);
    write_usize(&mut out, root_ids.len());
    for id in root_ids {
        write_u64(&mut out, id as u64);
    }
    out
}

/// Global constants referenced by a term (bundle name indices).
pub fn term_consts(bundle: &Bundle, term: u32) -> Vec<u32> {
    let mut out = Vec::new();
    fn go(bundle: &Bundle, t: u32, out: &mut Vec<u32>) {
        match &bundle.terms[t as usize] {
            TermNode::Const(n, _) => {
                if !out.contains(n) {
                    out.push(*n);
                }
            }
            TermNode::Pi(_, _, d, c) | TermNode::Lam(_, _, d, c) => {
                go(bundle, *d, out);
                go(bundle, *c, out);
            }
            TermNode::App(f, a) => {
                go(bundle, *f, out);
                go(bundle, *a, out);
            }
            TermNode::Let(_, t2, v, b) => {
                go(bundle, *t2, out);
                go(bundle, *v, out);
                go(bundle, *b, out);
            }
            TermNode::Proj(s, _, t2) => {
                if !out.contains(s) {
                    out.push(*s);
                }
                go(bundle, *t2, out);
            }
            _ => {}
        }
    }
    go(bundle, term, &mut out);
    out
}

/// StatementId for every declaration in the bundle, computed in declaration
/// order (dependencies are earlier declarations; inductive blocks use the
/// block-hash + ordinal scheme).
pub fn statement_ids(bundle: &Bundle) -> HashMap<String, StatementId> {
    let mut by_name_idx: HashMap<u32, StatementId> = HashMap::new();
    let mut result: HashMap<String, StatementId> = HashMap::new();
    // block hashes for inductive blocks
    let mut block_ids: HashMap<u32, [u8; 32]> = HashMap::new();
    for decl in &bundle.declarations {
        let name_str = bundle.name_string(decl.name);
        if decl.kind == rigor_spec::abi::DECL_INDUCTIVE {
            let block_key = decl.block.unwrap_or(decl.name);
            let block_hash = *block_ids.entry(block_key).or_insert_with(|| {
                // block hash over member names + their type subgraphs in order
                let mut fields: Vec<Vec<u8>> = Vec::new();
                for member in bundle
                    .declarations
                    .iter()
                    .filter(|d| d.kind == rigor_spec::abi::DECL_INDUCTIVE && d.block.unwrap_or(d.name) == block_key)
                {
                    let mut f = Vec::new();
                    write_str(&mut f, &bundle.name_string(member.name));
                    f.extend_from_slice(&canonical_term_subgraph(bundle, &[member.ty]));
                    for c in &member.constructors {
                        write_str(&mut f, &bundle.name_string(c.name));
                        f.extend_from_slice(&canonical_term_subgraph(bundle, &[c.ty]));
                    }
                    fields.push(f);
                }
                let refs: Vec<&[u8]> = fields.iter().map(|f| f.as_slice()).collect();
                domain_hash(DOMAIN_IND_BLOCK_ID, &refs)
            });
            let ordinal = bundle
                .declarations
                .iter()
                .filter(|d| {
                    d.kind == rigor_spec::abi::DECL_INDUCTIVE
                        && d.block.unwrap_or(d.name) == block_key
                        && d.name <= decl.name
                })
                .count()
                - 1;
            let mut ord_bytes = Vec::new();
            write_u64(&mut ord_bytes, ordinal as u64);
            let id = StatementId(domain_hash(
                DOMAIN_IND_MEMBER_ID,
                &[&block_hash, &ord_bytes],
            ));
            by_name_idx.insert(decl.name, id);
            result.insert(name_str, id);
            continue;
        }
        let mut stmt_roots = vec![decl.ty];
        let transparent = decl.kind == rigor_spec::abi::DECL_DEF;
        if transparent {
            if let Some(v) = decl.value {
                stmt_roots.push(v);
            }
        }
        let mut bytes = Vec::new();
        write_str(&mut bytes, &name_str);
        bytes.push(decl.kind);
        write_usize(&mut bytes, decl.level_params.len());
        for lp in &decl.level_params {
            write_str(&mut bytes, &bundle.name_string(*lp));
        }
        bytes.extend_from_slice(&canonical_term_subgraph(bundle, &stmt_roots));
        // semantic dependencies: statement ids of referenced earlier declarations
        let mut deps: Vec<[u8; 32]> = Vec::new();
        let mut all_terms = vec![decl.ty];
        if let Some(v) = decl.value {
            all_terms.push(v);
        }
        for t in all_terms {
            for c in term_consts(bundle, t) {
                if let Some(sid) = by_name_idx.get(&c) {
                    deps.push(sid.0);
                }
            }
        }
        deps.sort();
        deps.dedup();
        let id = ids::statement_id(&bytes, &deps);
        by_name_idx.insert(decl.name, id);
        result.insert(name_str, id);
    }
    result
}

/// EvidenceId for a root: statement + canonical proof subgraph + imported proof refs.
pub fn evidence_id_for(bundle: &Bundle, root_decl_name: &str, stmt: &StatementId) -> rigor_spec::EvidenceId {
    let decl = bundle
        .declarations
        .iter()
        .find(|d| bundle.name_string(d.name) == root_decl_name);
    let proof_bytes = match decl.and_then(|d| d.value) {
        Some(v) => canonical_term_subgraph(bundle, &[v]),
        None => Vec::new(),
    };
    ids::evidence_id(stmt, &proof_bytes, &bundle.evidence_refs)
}
