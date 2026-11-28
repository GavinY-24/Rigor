//! Rigor surface front end: `.rigor` parser, strict-profile elaborator,
//! conversion-ticket recording, and the stateful machine protocol.
//!
//! The front end is an untrusted producer: everything it emits is a core
//! proof bundle (`.rigorb`) rechecked by `rigor-kernel` at admission time
//! and independently by `rigor-runtime` at verification time.

pub mod ast;
pub mod elab;
pub mod lexer;
pub mod parser;
pub mod protocol;
pub mod suggest;

pub use ast::*;
pub use elab::{Elab, ProofState};
pub use parser::{parse_source, parse_tactics_text};

use rigor_certificates::bootstrap_kernel;
use rigor_codec::{encode_bundle, encode_kernel, statement_ids, Bundle, Challenge};
use rigor_kernel::{DeclKind, Kernel, NExpr, Reducibility};
use std::collections::BTreeMap;

pub struct CompiledModule {
    pub name: String,
    pub bundle: Bundle,
    pub bundle_bytes: Vec<u8>,
    /// Declaration name -> StatementId (hex).
    pub statement_ids: BTreeMap<String, String>,
    pub roots: Vec<String>,
    pub challenges: Vec<Challenge>,
    pub ticket_count: usize,
}

pub fn elaborate_telescope(elab: &mut Elab, telescope: &[Tele]) -> Result<Vec<elab::CtxLocal>, String> {
    let mut ctx: Vec<elab::CtxLocal> = Vec::new();
    for tele in telescope {
        let mut obs = Vec::new();
        let ty = elab.elaborate(&ctx, &tele.ty, &mut obs)?;
        if !obs.is_empty() {
            return Err("division in a telescope type creates an obligation that cannot be discharged there".into());
        }
        for name in &tele.names {
            let local = elab.make_local(&ctx, name, ty.clone(), None, tele.assuming)?;
            ctx.push(local);
        }
    }
    Ok(ctx)
}

pub fn wrap(ctx: &[elab::CtxLocal], body: NExpr, is_type: bool) -> NExpr {
    let mut out = body;
    for local in ctx.iter().rev() {
        out = if is_type {
            NExpr::pi(&local.name, local.ty.clone(), out)
        } else {
            NExpr::lam(&local.name, local.ty.clone(), out)
        };
    }
    out
}

/// Prove a theorem-like declaration: elaborate the statement, run the proof
/// (term or tactics), and admit it to the kernel. Returns the open proof.
fn prove_decl(
    elab: &mut Elab,
    name: &str,
    telescope: &[Tele],
    target_st: &STerm,
    proof: &TheoremProof,
) -> Result<(Vec<elab::CtxLocal>, NExpr, NExpr), String> {
    let ctx = elaborate_telescope(elab, telescope)?;
    let mut obs = Vec::new();
    let target = elab.elaborate(&ctx, target_st, &mut obs)?;
    let mut state = ProofState::new(ctx.clone(), target.clone());
    for (octx, oty) in obs {
        state.add_goal(octx, oty, "denominator_nonzero".to_string());
    }
    match proof {
        TheoremProof::Term(t) => {
            elab.run_tactic(&mut state, &Tactic::Exact(t.clone()))?;
        }
        TheoremProof::Tactics(tactics) => {
            elab.run_tactics(&mut state, tactics)?;
        }
    }
    let open = state.open_goals();
    if !open.is_empty() {
        let desc: Vec<String> = open
            .iter()
            .map(|g| format!("goal '{}': {}", g.tag, rigor_kernel::pretty_named(&g.target)))
            .collect();
        return Err(format!("'{name}' has {} open goal(s): {}", open.len(), desc.join("; ")));
    }
    let root = state.goals[0].clone();
    let proof_open = state.assemble(&root)?;
    Ok((ctx, target, proof_open))
}

/// Emit the per-theorem TY_CHECK_CORE conversion ticket (proof term checks
/// against the statement in the telescope context).
pub fn emit_theorem_ticket(elab: &mut Elab, ctx: &[elab::CtxLocal], proof_open: &NExpr, target: &NExpr) -> Result<(), String> {
    let ctx_idx = elab.register_ctx(ctx);
    let x = elab.lower_in(ctx, proof_open)?;
    let y = elab.lower_in(ctx, target)?;
    elab.tickets.push(rigor_codec::PortableTicket {
        op: rigor_spec::TicketOpcode::TyCheckCore as u8,
        ctx: ctx_idx,
        x,
        y,
        z: 0,
        refs: Vec::new(),
    });
    Ok(())
}

/// Compile a `.rigor` source file into a proof bundle.
pub fn compile(source: &str) -> Result<CompiledModule, String> {
    compile_with(source, "constructive")
}

pub fn compile_with(source: &str, challenge_policy: &str) -> Result<CompiledModule, String> {
    let decls = parse_source(source)?;
    let kernel: Kernel = bootstrap_kernel()?;
    let mut elab = Elab::new(kernel);
    let mut module_name = String::new();
    let mut roots: Vec<String> = Vec::new();
    let mut challenge_decls: Vec<(String, Vec<String>)> = Vec::new();

    for decl in &decls {
        match decl {
            SDecl::Module { name } => module_name = name.clone(),
            SDecl::Profile { strict } => elab.strict = *strict,
            SDecl::Import { .. } => {
                // Imports are resolved by the CLI driver (it concatenates
                // dependency modules before calling compile); the kernel
                // environment is append-only so earlier text is already in.
            }
            SDecl::Axiom { name, levels, ty } => {
                elab.level_scope = levels.clone();
                let mut obs = Vec::new();
                let ty_e = elab.elaborate(&[], ty, &mut obs)?;
                if !obs.is_empty() {
                    return Err(format!("axiom '{name}': obligations are not allowed in axioms"));
                }
                let lps: Vec<&str> = levels.iter().map(|s| s.as_str()).collect();
                elab.kernel.add_axiom(name, &lps, ty_e).map_err(|e| format!("axiom '{name}': {e}"))?;
            }
            SDecl::Def { name, levels, telescope, ty, value } => {
                elab.level_scope = levels.clone();
                let lps: Vec<&str> = levels.iter().map(|s| s.as_str()).collect();
                match value {
                    TheoremProof::Term(t) => {
                        let ctx = elaborate_telescope(&mut elab, telescope)?;
                        let mut obs = Vec::new();
                        let val_open = elab.elaborate(&ctx, t, &mut obs)?;
                        if !obs.is_empty() {
                            return Err(format!(
                                "def '{name}': division creates a nonzero obligation that a definition cannot discharge; prove it in a theorem instead"
                            ));
                        }
                        let ty_open = match ty {
                            Some(t) => {
                                let mut obs2 = Vec::new();
                                elab.elaborate(&ctx, t, &mut obs2)?
                            }
                            None => elab.infer_nexpr(&ctx, &val_open)?,
                        };
                        let ty_closed = wrap(&ctx, ty_open, true);
                        let val_closed = wrap(&ctx, val_open, false);
                        elab.kernel
                            .add_definition(name, &lps, ty_closed, val_closed, DeclKind::Definition, Reducibility::Regular)
                            .map_err(|e| format!("def '{name}': {e}"))?;
                    }
                    TheoremProof::Tactics(tactics) => {
                        let ty_st = ty.clone().ok_or_else(|| format!("def '{name}' with a tactic proof needs a result type"))?;
                        let (ctx, target, proof_open) = prove_decl(
                            &mut elab,
                            name,
                            telescope,
                            &ty_st,
                            &TheoremProof::Tactics(tactics.clone()),
                        )?;
                        emit_theorem_ticket(&mut elab, &ctx, &proof_open, &target)?;
                        let ty_closed = wrap(&ctx, target, true);
                        let val_closed = wrap(&ctx, proof_open, false);
                        elab.kernel
                            .add_definition(name, &lps, ty_closed, val_closed, DeclKind::Definition, Reducibility::Regular)
                            .map_err(|e| format!("def '{name}': {e}"))?;
                    }
                }
            }
            SDecl::Theorem { name, levels, telescope, target, proof } => {
                elab.level_scope = levels.clone();
                let lps: Vec<&str> = levels.iter().map(|s| s.as_str()).collect();
                let (ctx, target_e, proof_open) = prove_decl(&mut elab, name, telescope, target, proof)?;
                emit_theorem_ticket(&mut elab, &ctx, &proof_open, &target_e)?;
                let ty_closed = wrap(&ctx, target_e, true);
                let val_closed = wrap(&ctx, proof_open, false);
                elab.kernel
                    .add_definition(name, &lps, ty_closed, val_closed, DeclKind::Theorem, Reducibility::Opaque)
                    .map_err(|e| format!("theorem '{name}': {e}"))?;
                roots.push(name.clone());
            }
            SDecl::Inductive { name, levels, params, ty, ctors } => {
                elab.level_scope = levels.clone();
                let pctx = elaborate_telescope(&mut elab, params)?;
                let mut obs = Vec::new();
                let result_ty = elab.elaborate(&pctx, ty, &mut obs)?;
                if !obs.is_empty() {
                    return Err(format!("inductive '{name}': obligations not allowed in the result type"));
                }
                let full_ty = wrap(&pctx, result_ty, true);
                let num_params: u32 = params.iter().map(|t| t.names.len() as u32).sum();
                let mut ctor_specs = Vec::new();
                for ctor in ctors {
                    // Constructor telescope lives under the parameters.
                    let mut cctx = pctx.clone();
                    for tele in &ctor.binders {
                        let mut obs2 = Vec::new();
                        let cty = elab.elaborate(&cctx, &tele.ty, &mut obs2)?;
                        if !obs2.is_empty() {
                            return Err(format!("constructor '{}': obligations not allowed", ctor.name));
                        }
                        for n in &tele.names {
                            let local = elab.make_local(&cctx, n, cty.clone(), None, false)?;
                            cctx.push(local);
                        }
                    }
                    let result = match &ctor.result {
                        Some(r) => {
                            let mut obs3 = Vec::new();
                            elab.elaborate(&cctx, r, &mut obs3)?
                        }
                        None => {
                            let mut app = NExpr::Const(name.clone(), elab.default_levels(name));
                            for local in &pctx {
                                app = NExpr::app(app, NExpr::var(&local.name));
                            }
                            app
                        }
                    };
                    let full = wrap(&cctx, result, true);
                    // Kernel constructor names are scoped: Vec.cons etc.
                    let cname = if ctor.name.contains('.') {
                        ctor.name.clone()
                    } else {
                        format!("{name}.{}", ctor.name)
                    };
                    ctor_specs.push((cname, full));
                }
                let spec = rigor_kernel::InductiveSpec {
                    name: name.clone(),
                    level_params: levels.clone(),
                    ty: full_ty,
                    num_params,
                    constructors: ctor_specs,
                };
                elab.kernel
                    .add_inductive_block(vec![spec])
                    .map_err(|e| format!("inductive '{name}': {e}"))?;
            }
            SDecl::Challenge { name, roots } => {
                challenge_decls.push((name.clone(), roots.clone()));
            }
        }
    }

    let bundle = encode_kernel(
        &elab.kernel,
        &roots,
        &elab.tickets,
        &elab.contexts,
        Some(format!("compiled from module {module_name}")),
    );
    let bundle_bytes = encode_bundle(&bundle);
    let sids = statement_ids(&bundle);
    let statement_id_map: BTreeMap<String, String> = sids
        .iter()
        .map(|(k, v)| (k.clone(), v.to_hex()))
        .collect();
    let mut challenges = Vec::new();
    for (cname, croots) in &challenge_decls {
        challenges.push(Challenge::from_bundle(cname, &bundle, croots, challenge_policy));
    }
    Ok(CompiledModule {
        name: module_name,
        ticket_count: elab.tickets.len(),
        bundle,
        bundle_bytes,
        statement_ids: statement_id_map,
        roots,
        challenges,
    })
}
