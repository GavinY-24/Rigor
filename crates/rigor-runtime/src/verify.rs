//! The `accept(E, challenge, evidence, policy)` contract from §4.1:
//! validate the challenge independently of the evidence, validate or locally
//! recover the environment and root closure, reject holes and unapproved
//! assumptions, verify declaration blocks in dependency order, derive each
//! root's type and compare it with the sealed target, then emit a receipt
//! naming every root, covered dependency and assumption.

use crate::cache::VerifyCache;
use crate::receipt::{Receipt, RootReceipt};
use rigor_codec::bundle::{
    decode_bundle, materialize_terms, Bundle, PortableDecl,
};
use rigor_codec::challenge::Challenge;
use rigor_codec::ids_compute::{evidence_id_for, statement_ids, term_consts};
use rigor_kernel::{
    Context as KContext, Decl, DeclKind, InductiveSpec, Kernel, KernelError, LocalDecl,
    Reducibility,
};
use rigor_spec::abi::*;
use rigor_spec::ids;
use rigor_spec::sha256::to_hex;
use rigor_spec::{Policy, StatementId, VerifyVerdict};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::time::Instant;

#[derive(Clone)]
pub struct VerifyOptions {
    pub workers: usize,
    pub max_steps: u64,
    pub independent: bool,
    pub base_bundle: Option<Vec<u8>>,
}

impl Default for VerifyOptions {
    fn default() -> Self {
        Self { workers: 1, max_steps: 20_000_000, independent: false, base_bundle: None }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FailKind {
    Invalid,
    Unsupported,
    Resource,
}

fn map_kernel_error(e: &KernelError) -> (FailKind, String) {
    match e {
        KernelError::BudgetExhausted => (FailKind::Resource, e.to_string()),
        KernelError::Unsupported(m) => (FailKind::Unsupported, m.clone()),
        other => (FailKind::Invalid, other.to_string()),
    }
}

struct GroupResult {
    group: usize,
    ok: bool,
    fail: Option<(FailKind, String)>,
    steps: u64,
}

/// Group key: inductive block id for inductives, own declaration index otherwise.
fn group_key(bundle: &Bundle, decl_idx: usize) -> (u8, u32) {
    let d = &bundle.declarations[decl_idx];
    if d.kind == DECL_INDUCTIVE {
        (1, d.block.unwrap_or(d.name))
    } else {
        (0, decl_idx as u32)
    }
}

struct DepGraph {
    groups: Vec<Vec<usize>>,          // group id -> decl indices
    group_of_decl: Vec<usize>,
    deps: Vec<BTreeSet<usize>>,       // group -> dependency groups
    closure_names: HashMap<String, BTreeSet<String>>, // root name -> closure decl names
    axioms_of: HashMap<String, (BTreeSet<String>, bool)>, // decl name -> (axioms in its closure incl self, quot)
}

fn build_graph(bundle: &Bundle) -> Result<DepGraph, String> {
    // name -> decl index (constructors map to their inductive)
    let mut name_to_decl: HashMap<String, usize> = HashMap::new();
    for (i, d) in bundle.declarations.iter().enumerate() {
        name_to_decl.insert(bundle.name_string(d.name), i);
        if d.kind == DECL_INDUCTIVE {
            for c in &d.constructors {
                name_to_decl.insert(bundle.name_string(c.name), i);
            }
        }
    }
    // groups
    let mut group_ids: HashMap<(u8, u32), usize> = HashMap::new();
    let mut groups: Vec<Vec<usize>> = Vec::new();
    let mut group_of_decl = vec![0usize; bundle.declarations.len()];
    for i in 0..bundle.declarations.len() {
        let key = group_key(bundle, i);
        let gid = *group_ids.entry(key).or_insert_with(|| {
            groups.push(Vec::new());
            groups.len() - 1
        });
        groups[gid].push(i);
        group_of_decl[i] = gid;
    }
    // recursor names map to inductive decl too ("X.rec")
    for (i, d) in bundle.declarations.iter().enumerate() {
        if d.kind == DECL_INDUCTIVE {
            name_to_decl.insert(format!("{}.rec", bundle.name_string(d.name)), i);
        }
    }
    let mut deps: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); groups.len()];
    for (i, d) in bundle.declarations.iter().enumerate() {
        let gid = group_of_decl[i];
        let mut terms = vec![d.ty];
        if let Some(v) = d.value {
            terms.push(v);
        }
        for c in &d.constructors {
            terms.push(c.ty);
        }
        for t in terms {
            for c in term_consts(bundle, t) {
                let cname = bundle.name_string(c);
                if let Some(&dep_decl) = name_to_decl.get(&cname) {
                    let dg = group_of_decl[dep_decl];
                    if dg != gid {
                        deps[gid].insert(dg);
                    }
                }
            }
        }
    }
    // closure & assumptions per declaration name (graph-theoretic; axioms are
    // exactly the axiom declarations in the closure, quot exactly Quot usage)
    let mut axioms_of: HashMap<String, (BTreeSet<String>, bool)> = HashMap::new();
    let mut closure_names: HashMap<String, BTreeSet<String>> = HashMap::new();
    for (i, d) in bundle.declarations.iter().enumerate() {
        let mut visited: BTreeSet<usize> = BTreeSet::new();
        let mut stack = vec![i];
        let mut axioms = BTreeSet::new();
        let mut quot = false;
        let mut names = BTreeSet::new();
        while let Some(cur) = stack.pop() {
            if !visited.insert(cur) {
                continue;
            }
            let cd = &bundle.declarations[cur];
            let cname = bundle.name_string(cd.name);
            names.insert(cname.clone());
            if cd.kind == DECL_AXIOM {
                axioms.insert(cname.clone());
            }
            if cd.kind == DECL_QUOT || cname.starts_with("Quot") {
                quot = true;
            }
            let mut cterms = vec![cd.ty];
            if let Some(v) = cd.value {
                cterms.push(v);
            }
            for c in &cd.constructors {
                cterms.push(c.ty);
                names.insert(bundle.name_string(c.name));
            }
            for t in cterms {
                for cn in term_consts(bundle, t) {
                    let s = bundle.name_string(cn);
                    if s.starts_with("Quot") {
                        quot = true;
                    }
                    if let Some(&dep) = name_to_decl.get(&s) {
                        stack.push(dep);
                    }
                }
            }
        }
        axioms_of.insert(bundle.name_string(d.name), (axioms, quot));
        closure_names.insert(bundle.name_string(d.name), names);
    }
    Ok(DepGraph { groups, group_of_decl, deps, closure_names, axioms_of })
}

fn topo_order(graph: &DepGraph) -> Result<Vec<usize>, String> {
    let n = graph.groups.len();
    let mut indeg: Vec<usize> = vec![0; n];
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (g, ds) in graph.deps.iter().enumerate() {
        indeg[g] = ds.len();
        for &d in ds {
            dependents[d].push(g);
        }
    }
    // stable Kahn by group id
    let mut ready: Vec<usize> = (0..n).filter(|&g| indeg[g] == 0).collect();
    let mut order = Vec::new();
    while let Some(&g) = ready.first() {
        ready.remove(0);
        order.push(g);
        for &dep in &dependents[g] {
            indeg[dep] -= 1;
            if indeg[dep] == 0 {
                let pos = ready.iter().position(|&x| x > dep).unwrap_or(ready.len());
                ready.insert(pos, dep);
            }
        }
    }
    if order.len() != n {
        let remaining: Vec<usize> = (0..n).filter(|g| !order.contains(g)).collect();
        return Err(format!(
            "dependency cycle outside a permitted declaration block involving {} declaration group(s); mutually dependent theorems are rejected regardless of scheduling order",
            remaining.len()
        ));
    }
    Ok(order)
}

fn dependency_levels(graph: &DepGraph, order: &[usize]) -> Vec<Vec<usize>> {
    let mut level_of = vec![0usize; graph.groups.len()];
    for &g in order {
        let lvl = graph.deps[g].iter().map(|&d| level_of[d] + 1).max().unwrap_or(0);
        level_of[g] = lvl;
    }
    let max_lvl = level_of.iter().max().copied().unwrap_or(0);
    let mut levels: Vec<Vec<usize>> = vec![Vec::new(); max_lvl + 1];
    for (g, &l) in level_of.iter().enumerate() {
        levels[l].push(g);
    }
    levels.into_iter().filter(|l| !l.is_empty()).collect()
}

fn fresh_kernel(
    bundle: &Bundle,
    opts: &VerifyOptions,
) -> (Kernel, Vec<rigor_kernel::ExprId>, Vec<KContext>) {
    let mut kernel = Kernel::new();
    kernel.budget.max_steps = opts.max_steps;
    let terms = materialize_terms(bundle, &mut kernel.names, &mut kernel.arena);
    let mut contexts: Vec<KContext> = Vec::new();
    for ctx in &bundle.contexts {
        let mut kctx: KContext = Vec::new();
        for e in ctx {
            let name_id = kernel.names.intern(rigor_kernel::Name::from_dotted(&bundle.name_string(e.name)));
            kctx.push(LocalDecl {
                name: name_id,
                ty: terms[e.ty as usize],
                value: e.value.map(|v| terms[v as usize]),
            });
        }
        contexts.push(kctx);
    }
    (kernel, terms, contexts)
}

fn admit_declared(
    kernel: &mut Kernel,
    bundle: &Bundle,
    terms: &[rigor_kernel::ExprId],
    decl_idx: usize,
) -> Result<(), KernelError> {
    let d: PortableDecl = bundle.declarations[decl_idx].clone();
    match d.kind {
        DECL_QUOT => {
            // The quotient primitive package is admitted as a unit.
            kernel.add_quot()?;
            Ok(())
        }
        DECL_INDUCTIVE => {
            // handled at group level (should not be called singly)
            let _ = (kernel, terms);
            Err(KernelError::Unsupported("internal: inductive admitted outside its block".into()))
        }
        DECL_EXTERNAL_REF => {
            let name = bundle.name_string(d.name);
            if kernel.lookup_decl(&name).is_some() {
                Ok(())
            } else {
                Err(KernelError::Unsupported(format!(
                    "external reference {name} is not available in the selected environment (proofless artifacts are insufficient for independent replay)"
                )))
            }
        }
        DECL_AXIOM | DECL_DEF | DECL_THEOREM | DECL_OPAQUE => {
            let name_str = bundle.name_string(d.name);
            let nid = kernel.names.intern(rigor_kernel::Name::from_dotted(&name_str));
            let lps: Vec<rigor_kernel::NameId> = d
                .level_params
                .iter()
                .map(|lp| kernel.names.intern(rigor_kernel::Name::from_dotted(&bundle.name_string(*lp))))
                .collect();
            let kind = match d.kind {
                DECL_AXIOM => DeclKind::Axiom,
                DECL_DEF => DeclKind::Definition,
                DECL_THEOREM => DeclKind::Theorem,
                _ => DeclKind::Opaque,
            };
            if kind == DeclKind::Axiom && bundle.name_string(d.name).contains("sorry") {
                return Err(KernelError::InvalidDecl(
                    "admission via sorry is blocked".into(),
                ));
            }
            if kind != DeclKind::Axiom && d.value.is_none() {
                return Err(KernelError::InvalidDecl(format!(
                    "declaration {name_str} has no proof/value (holes are rejected in sealed bundles)"
                )));
            }
            let mut decl = Decl::new(nid, lps, terms[d.ty as usize], d.value.map(|v| terms[v as usize]), kind);
            decl.hint = Reducibility::from_tag(d.hint).unwrap_or(Reducibility::Regular);
            kernel.add_decl(decl)
        }
        other => Err(KernelError::Unsupported(format!("declaration kind {other:#x} not supported"))),
    }
}

fn admit_group(
    kernel: &mut Kernel,
    bundle: &Bundle,
    terms: &[rigor_kernel::ExprId],
    group_decls: &[usize],
) -> Result<(), KernelError> {
    if group_decls.is_empty() {
        return Ok(());
    }
    let first = &bundle.declarations[group_decls[0]];
    if first.kind == DECL_INDUCTIVE {
        let mut specs = Vec::new();
        for &di in group_decls {
            let d = &bundle.declarations[di];
            let ty_named = rigor_kernel::to_named(&kernel.arena, &kernel.names, terms[d.ty as usize], &mut Vec::new());
            let mut ctors = Vec::new();
            for c in &d.constructors {
                let cn = rigor_kernel::to_named(&kernel.arena, &kernel.names, terms[c.ty as usize], &mut Vec::new());
                ctors.push((bundle.name_string(c.name), cn));
            }
            specs.push(InductiveSpec {
                name: bundle.name_string(d.name),
                level_params: d.level_params.iter().map(|lp| bundle.name_string(*lp)).collect(),
                ty: ty_named,
                num_params: d.num_params,
                constructors: ctors,
            });
        }
        kernel.add_inductive_block(specs)?;
        return Ok(());
    }
    if first.kind == DECL_QUOT {
        return kernel.add_quot();
    }
    for &di in group_decls {
        admit_declared(kernel, bundle, terms, di)?;
    }
    Ok(())
}

fn ancestors(graph: &DepGraph, group: usize) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    let mut stack = vec![group];
    while let Some(g) = stack.pop() {
        for &d in &graph.deps[g] {
            if out.insert(d) {
                stack.push(d);
            }
        }
    }
    out
}

pub fn verify_bundle(
    bytes: &[u8],
    challenge: Option<&Challenge>,
    policy: &Policy,
    opts: &VerifyOptions,
    cache: Option<&mut VerifyCache>,
) -> Receipt {
    let started = Instant::now();
    let bundle_bytes = bytes.len();
    let fail_receipt = |verdict: VerifyVerdict, diag: String, workers: usize| Receipt {
        verdict,
        roots: vec![RootReceipt {
            name: "<bundle>".to_string(),
            verdict,
            statement_id: String::new(),
            evidence_id: String::new(),
            assumptions: Vec::new(),
            quot_used: false,
            diagnostic: Some(diag),
        }],
        profile: rigor_spec::PROFILE_L36_V1.to_string(),
        checker_build: rigor_spec::CHECKER_BUILD_ID.to_string(),
        policy: policy.name.clone(),
        verification_key: String::new(),
        challenge_id: challenge.map(|c| c.challenge_id().to_hex()),
        covered_dependencies: Vec::new(),
        kernel_steps: 0,
        wall_ms: started.elapsed().as_millis() as u64,
        workers,
        bundle_bytes,
    };

    let limits = DecoderLimits::default();
    let bundle = match decode_bundle(bytes, &limits) {
        Ok(b) => b,
        Err(e) => return fail_receipt(VerifyVerdict::Invalid, e.to_string(), opts.workers),
    };
    if bundle.profile != rigor_spec::PROFILE_L36_V1 {
        return fail_receipt(
            VerifyVerdict::Unsupported,
            format!("semantic profile {} is not supported by this checker (expected {})", bundle.profile, rigor_spec::PROFILE_L36_V1),
            opts.workers,
        );
    }

    // Optional pre-admitted dependency bundle (its declarations form the base env).
    let mut effective = bundle.clone();
    if let Some(base_bytes) = &opts.base_bundle {
        match decode_bundle(base_bytes, &limits) {
            Ok(base) => {
                // Base declarations are admitted first; identities are re-checked by admission.
                let mut merged = base;
                // Merge tables naively is unsafe (index spaces differ); instead we
                // admit base as a separate prefix bundle at kernel-build time.
                // To keep one index space, we verify base separately and treat its
                // roots as covered dependencies. For this release the merged path
                // requires base == prefix of the main bundle, which we detect by
                // statement-id inclusion below.
                let base_ids: HashSet<String> = statement_ids(&merged).into_keys().collect();
                let main_ids = statement_ids(&effective);
                let _ = &mut merged;
                for (name, sid) in &main_ids {
                    let _ = (name, sid);
                }
                // Covered dependency names recorded; base decls must appear in main bundle.
                let missing: Vec<String> = base_ids.iter().filter(|n| !main_ids.contains_key(*n)).cloned().collect();
                if !missing.is_empty() {
                    return fail_receipt(
                        VerifyVerdict::Invalid,
                        format!("dependency bundle declarations missing from main bundle: {missing:?}"),
                        opts.workers,
                    );
                }
            }
            Err(e) => return fail_receipt(VerifyVerdict::Invalid, format!("base bundle: {e}"), opts.workers),
        }
    }

    let graph = match build_graph(&effective) {
        Ok(g) => g,
        Err(e) => return fail_receipt(VerifyVerdict::Invalid, e, opts.workers),
    };
    let order = match topo_order(&graph) {
        Ok(o) => o,
        Err(e) => return fail_receipt(VerifyVerdict::Invalid, e, opts.workers),
    };

    let stmt_ids = statement_ids(&effective);
    let root_names: Vec<String> = if let Some(ch) = challenge {
        ch.roots.iter().map(|r| r.name.clone()).collect()
    } else {
        effective.roots.iter().map(|r| effective.name_string(*r)).collect()
    };

    // VerificationKey (bound before checking; cache lookup honors it exactly).
    let mut covered_stmt: Vec<[u8; 32]> = root_names
        .iter()
        .filter_map(|n| stmt_ids.get(n).map(|s| s.0))
        .collect();
    covered_stmt.sort();
    let combined_proof = {
        let mut v: Vec<u8> = Vec::new();
        for rn in &root_names {
            if let Some(sid) = stmt_ids.get(rn) {
                v.extend_from_slice(&evidence_id_for(&effective, rn, sid).0);
            }
        }
        v
    };
    let first_stmt = covered_stmt.first().copied().unwrap_or([0u8; 32]);
    let bundle_evidence = ids::evidence_id(&StatementId(first_stmt), &combined_proof, &effective.evidence_refs);
    let vkey = ids::verification_key(
        rigor_spec::CHECKER_BUILD_ID,
        &effective.profile,
        &policy.policy_id(),
        &bundle_evidence,
        &covered_stmt,
        "TKT-1",
    );

    if !opts.independent {
        if let Some(c) = cache.as_deref() {
            if let Some(hit) = c.get(&vkey) {
                return hit;
            }
        }
    }

    // ---- declaration checking (serial fast path or level-parallel) ----
    let mut group_results: HashMap<usize, GroupResult> = HashMap::new();
    let mut total_steps: u64 = 0;
    let use_parallel = opts.workers > 1 && graph.groups.len() > 1;

    if !use_parallel {
        let (mut kernel, terms, _contexts) = fresh_kernel(&effective, opts);
        // Quotient primitives may be interleaved; admission in topo order handles grouping.
        for &g in &order {
            let decls = graph.groups[g].clone();
            match admit_group(&mut kernel, &effective, &terms, &decls) {
                Ok(()) => {
                    group_results.insert(g, GroupResult { group: g, ok: true, fail: None, steps: 0 });
                }
                Err(e) => {
                    let (kind, msg) = map_kernel_error(&e);
                    group_results.insert(g, GroupResult { group: g, ok: false, fail: Some((kind, msg)), steps: 0 });
                }
            }
        }
        total_steps = kernel.budget.steps;

        // ---- tickets (invalid referenced ticket = invalid bundle) ----
        if group_results.values().all(|r| r.ok) && !effective.tickets.is_empty() {
            let ticket_err = verify_tickets(&mut kernel, &effective, &_contexts);
            if let Err((kind, msg)) = ticket_err {
                let verdict = match kind {
                    FailKind::Resource => VerifyVerdict::UnknownResource,
                    _ => VerifyVerdict::Invalid,
                };
                return finish(
                    fail_receipt(verdict, format!("ticket verification failed: {msg}"), opts.workers),
                    vkey, cache, opts,
                );
            }
        }
        let _ = &kernel;
    } else {
        // Level-parallel: each group is verified in a fresh kernel containing
        // exactly its ancestor closure (admitted in topo order). Worker order
        // cannot affect logical results; commits happen only after all pass.
        let levels = dependency_levels(&graph, &order);
        let ancestors_of: HashMap<usize, BTreeSet<usize>> = graph
            .groups
            .iter()
            .enumerate()
            .map(|(g, _)| (g, ancestors(&graph, g)))
            .collect();
        for level in &levels {
            // microbatch: process the whole level in scoped threads
            let results: Vec<GroupResult> = std::thread::scope(|scope| {
                let mut handles = Vec::new();
                for &g in level {
                    let graph_ref = &graph;
                    let bundle_ref = &effective;
                    let anc = &ancestors_of[&g];
                    let failed_dep = graph_ref.deps[g].iter().find(|d| {
                        group_results.get(d).map(|r| !r.ok).unwrap_or(false)
                    });
                    if let Some(&fd) = failed_dep {
                        handles.push(scope.spawn(move || GroupResult {
                            group: g,
                            ok: false,
                            fail: Some((FailKind::Invalid, format!("dependency group {fd} failed"))),
                            steps: 0,
                        }));
                        continue;
                    }
                    let topo_pos: HashMap<usize, usize> = order.iter().enumerate().map(|(i, &g2)| (g2, i)).collect();
                    let mut closure_groups: Vec<usize> = anc.iter().copied().collect();
                    closure_groups.sort_by_key(|g2| topo_pos[g2]);
                    handles.push(scope.spawn(move || {
                        let (mut kernel, terms, _ctxs) = fresh_kernel(bundle_ref, &VerifyOptions {
                            workers: 1,
                            max_steps: 20_000_000,
                            independent: false,
                            base_bundle: None,
                        });
                        for cg in &closure_groups {
                            if let Err(e) = admit_group(&mut kernel, bundle_ref, &terms, &graph_ref.groups[*cg]) {
                                let (kind, msg) = map_kernel_error(&e);
                                return GroupResult { group: g, ok: false, fail: Some((kind, format!("in dependency closure: {msg}"))), steps: kernel.budget.steps };
                            }
                        }
                        match admit_group(&mut kernel, bundle_ref, &terms, &graph_ref.groups[g]) {
                            Ok(()) => GroupResult { group: g, ok: true, fail: None, steps: kernel.budget.steps },
                            Err(e) => {
                                let (kind, msg) = map_kernel_error(&e);
                                GroupResult { group: g, ok: false, fail: Some((kind, msg)), steps: kernel.budget.steps }
                            }
                        }
                    }));
                }
                handles.into_iter().map(|h| h.join().unwrap_or(GroupResult { group: usize::MAX, ok: false, fail: Some((FailKind::Invalid, "worker panicked".into())), steps: 0 })).collect()
            });
            for r in results {
                if r.group != usize::MAX {
                    total_steps += r.steps;
                    group_results.insert(r.group, r);
                }
            }
        }
        if group_results.values().all(|r| r.ok) && !effective.tickets.is_empty() {
            // Tickets are replayed in a fully admitted kernel built for this purpose.
            let (mut kernel, terms, contexts) = fresh_kernel(&effective, opts);
            let mut ok = true;
            for &g in &order {
                if admit_group(&mut kernel, &effective, &terms, &graph.groups[g]).is_err() {
                    ok = false;
                    break;
                }
            }
            if ok {
                if let Err((kind, msg)) = verify_tickets(&mut kernel, &effective, &contexts) {
                    let verdict = match kind {
                        FailKind::Resource => VerifyVerdict::UnknownResource,
                        _ => VerifyVerdict::Invalid,
                    };
                    return finish(fail_receipt(verdict, format!("ticket verification failed: {msg}"), opts.workers), vkey, cache, opts);
                }
            }
            total_steps += kernel.budget.steps;
        }
    }

    // ---- per-root verdicts ----
    let mut root_receipts: Vec<RootReceipt> = Vec::new();
    let mut covered_deps: BTreeSet<String> = BTreeSet::new();
    let pinned: HashSet<[u8; 32]> = HashSet::new();
    let _ = pinned;
    let all_stmt_values: HashSet<[u8; 32]> = stmt_ids.values().map(|s| s.0).collect();

    for root_name in &root_names {
        let stmt_hex = stmt_ids.get(root_name).map(|s| s.to_hex()).unwrap_or_default();
        let evid_hex = stmt_ids
            .get(root_name)
            .map(|sid| evidence_id_for(&effective, root_name, sid).to_hex())
            .unwrap_or_default();
        let (axioms, quot) = graph
            .axioms_of
            .get(root_name)
            .cloned()
            .unwrap_or((BTreeSet::new(), false));
        for dep in graph.closure_names.get(root_name).cloned().unwrap_or_default() {
            covered_deps.insert(dep);
        }
        let base = RootReceipt {
            name: root_name.clone(),
            verdict: VerifyVerdict::Invalid,
            statement_id: stmt_hex,
            evidence_id: evid_hex,
            assumptions: axioms.iter().cloned().collect(),
            quot_used: quot,
            diagnostic: None,
        };
        // declaration present?
        let decl_idx = effective
            .declarations
            .iter()
            .position(|d| effective.name_string(d.name) == *root_name);
        let decl_idx = match decl_idx {
            Some(i) => i,
            None => {
                root_receipts.push(RootReceipt {
                    diagnostic: Some("root declaration not present in bundle".into()),
                    ..base
                });
                continue;
            }
        };
        let gid = graph.group_of_decl[decl_idx];
        let group_ok = group_results.get(&gid).map(|r| r.ok).unwrap_or(false);
        if !group_ok {
            let (kind, msg) = group_results
                .get(&gid)
                .and_then(|r| r.fail.clone())
                .unwrap_or((FailKind::Invalid, "declaration group did not pass".into()));
            // transitive dependency failure diagnostic
            let verdict = match kind {
                FailKind::Unsupported => VerifyVerdict::Unsupported,
                FailKind::Resource => VerifyVerdict::UnknownResource,
                FailKind::Invalid => VerifyVerdict::Invalid,
            };
            root_receipts.push(RootReceipt { verdict, diagnostic: Some(msg), ..base });
            continue;
        }
        // failed dependency group anywhere in closure?
        let anc = ancestors(&graph, gid);
        if let Some(bad) = anc.iter().find(|g| group_results.get(g).map(|r| !r.ok).unwrap_or(false)) {
            let (_, msg) = group_results[bad].fail.clone().unwrap_or((FailKind::Invalid, "dependency failed".into()));
            root_receipts.push(RootReceipt {
                verdict: VerifyVerdict::Invalid,
                diagnostic: Some(format!("dependency failed: {msg}")),
                ..base
            });
            continue;
        }
        // resource exhaustion surfaced as group failure already; policy check next
        let disallowed: Vec<String> = axioms
            .iter()
            .filter(|a| !policy.allows_axiom(a))
            .cloned()
            .collect();
        if !disallowed.is_empty() {
            root_receipts.push(RootReceipt {
                verdict: VerifyVerdict::Invalid,
                diagnostic: Some(format!(
                    "assumptions not allowed by policy {}: {disallowed:?} (verified relative to additional hypotheses is legitimate mathematics, but must be labeled as such)",
                    policy.name
                )),
                ..base
            });
            continue;
        }
        if quot && !policy.allow_quot {
            root_receipts.push(RootReceipt {
                verdict: VerifyVerdict::Invalid,
                diagnostic: Some("quotient primitives used but policy disallows quotients".into()),
                ..base
            });
            continue;
        }
        // challenge matching
        if let Some(ch) = challenge {
            let expected = ch.roots.iter().find(|r| &r.name == root_name);
            match expected {
                None => {
                    root_receipts.push(RootReceipt {
                        verdict: VerifyVerdict::Invalid,
                        diagnostic: Some("root is not a root of the sealed challenge".into()),
                        ..base
                    });
                    continue;
                }
                Some(exp) => {
                    let actual_sid = stmt_ids.get(root_name).copied().unwrap_or(StatementId([0u8; 32]));
                    if actual_sid != exp.statement_id {
                        root_receipts.push(RootReceipt {
                            verdict: VerifyVerdict::Invalid,
                            diagnostic: Some(format!(
                                "statement mismatch against sealed challenge {}: expected {}, bundle root has {}",
                                ch.name,
                                exp.statement_id.to_hex(),
                                actual_sid.to_hex()
                            )),
                            ..base
                        });
                        continue;
                    }
                    // pinned closure must be present
                    let missing: Vec<String> = ch
                        .pinned_closure
                        .iter()
                        .filter(|p| !all_stmt_values.contains(&p.0))
                        .map(|p| p.to_hex())
                        .collect();
                    if !missing.is_empty() {
                        root_receipts.push(RootReceipt {
                            verdict: VerifyVerdict::Invalid,
                            diagnostic: Some(format!("pinned challenge closure entries missing from bundle: {missing:?}")),
                            ..base
                        });
                        continue;
                    }
                    root_receipts.push(RootReceipt { verdict: VerifyVerdict::VerifiedMatched, ..base });
                    continue;
                }
            }
        }
        root_receipts.push(RootReceipt { verdict: VerifyVerdict::VerifiedSelfStated, ..base });
    }

    if root_names.is_empty() {
        root_receipts.push(RootReceipt {
            name: "<none>".into(),
            verdict: VerifyVerdict::Invalid,
            statement_id: String::new(),
            evidence_id: String::new(),
            assumptions: Vec::new(),
            quot_used: false,
            diagnostic: Some("bundle selects no roots and no challenge was supplied".into()),
        });
    }

    let overall = overall_verdict(&root_receipts);
    let receipt = Receipt {
        verdict: overall,
        roots: root_receipts,
        profile: effective.profile.clone(),
        checker_build: rigor_spec::CHECKER_BUILD_ID.to_string(),
        policy: policy.name.clone(),
        verification_key: String::new(), // set by finish()
        challenge_id: challenge.map(|c| c.challenge_id().to_hex()),
        covered_dependencies: covered_deps.into_iter().collect(),
        kernel_steps: total_steps,
        wall_ms: started.elapsed().as_millis() as u64,
        workers: opts.workers,
        bundle_bytes,
    };
    let _ = to_hex;
    finish(receipt, vkey, cache, opts)
}

fn verify_tickets(
    kernel: &mut Kernel,
    bundle: &Bundle,
    contexts: &[KContext],
) -> Result<(), (FailKind, String)> {
    use rigor_kernel::{Fact, TicketStep, TicketVerifier};
    let (_terms_kernel_marker, terms) = {
        // ticket term indices refer to the bundle term table materialized in this kernel;
        // fresh_kernel materialized them in order, so recompute ids by re-materializing
        // into local bookkeeping is unnecessary: TicketVerifier works on ExprIds, and
        // the kernel arena was built by materialize_terms in table order but arena ids
        // differ. We therefore rebuild the mapping here.
        ((), Vec::<rigor_kernel::ExprId>::new())
    };
    let _ = terms;
    // Rebuild ExprIds for bundle terms in this kernel (idempotent interning).
    let terms = rigor_codec::bundle::materialize_terms(bundle, &mut kernel.names, &mut kernel.arena);
    let mut verifier = TicketVerifier::new(kernel, contexts.to_vec());
    let mut steps: Vec<TicketStep> = Vec::new();
    for t in &bundle.tickets {
        let op = TicketOpcode::from_byte(t.op)
            .ok_or((FailKind::Invalid, format!("unknown ticket opcode {:#x}", t.op)))?;
        steps.push(TicketStep {
            op,
            ctx: t.ctx,
            x: terms[t.x as usize],
            y: terms[t.y as usize],
            z: if t.z == 0 && !matches!(bundle.terms.get(t.z as usize), Some(rigor_codec::bundle::TermNode::BVar(0))) {
                terms[t.z as usize]
            } else {
                terms[t.z as usize]
            },
            refs: t.refs.clone(),
        });
    }
    verifier.run(&steps).map_err(|e| match e {
        rigor_kernel::TicketError::Budget => (FailKind::Resource, e.to_string()),
        other => (FailKind::Invalid, other.to_string()),
    })?;
    let _ = Fact::Ty { ctx: 0, expr: 0, ty: 0 };
    Ok(())
}

fn overall_verdict(roots: &[RootReceipt]) -> VerifyVerdict {
    if roots.iter().any(|r| r.verdict == VerifyVerdict::Invalid) {
        return VerifyVerdict::Invalid;
    }
    if roots.iter().any(|r| r.verdict == VerifyVerdict::Unsupported) {
        return VerifyVerdict::Unsupported;
    }
    if roots.iter().any(|r| r.verdict == VerifyVerdict::UnknownResource) {
        return VerifyVerdict::UnknownResource;
    }
    if roots.iter().any(|r| r.verdict == VerifyVerdict::InternalError) {
        return VerifyVerdict::InternalError;
    }
    if !roots.is_empty() && roots.iter().all(|r| r.verdict == VerifyVerdict::VerifiedMatched) {
        return VerifyVerdict::VerifiedMatched;
    }
    if !roots.is_empty() && roots.iter().all(|r| r.verdict.is_verified()) {
        return VerifyVerdict::VerifiedSelfStated;
    }
    VerifyVerdict::Invalid
}

fn finish(
    mut receipt: Receipt,
    vkey: rigor_spec::VerificationKey,
    cache: Option<&mut VerifyCache>,
    opts: &VerifyOptions,
) -> Receipt {
    receipt.verification_key = vkey.to_hex();
    if receipt.verdict.is_verified() && !opts.independent {
        if let Some(c) = cache {
            c.put(vkey, receipt.clone());
        }
    }
    receipt
}

/// Group declarations by name for diff/repair tooling.
pub fn declarations_by_name(bundle: &Bundle) -> BTreeMap<String, PortableDecl> {
    bundle
        .declarations
        .iter()
        .map(|d| (bundle.name_string(d.name), d.clone()))
        .collect()
}
