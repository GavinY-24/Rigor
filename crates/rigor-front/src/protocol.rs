//! Stateful machine protocol over the surface elaborator.
//!
//! Commands: OPEN, INSPECT, FORK, APPLY, REFINE, SUBMIT_CERT, SEAL.
//! Every successful mutating command produces a new *immutable state id*
//! (a hash of the serialized proof state plus a session nonce); earlier
//! states remain addressable and unchanged. A state is only ever a
//! producer-side artifact: SEAL re-checks the finished proof with the
//! kernel and emits a bundle whose verdict is decided by the runtime
//! verifier, never by this session.

use crate::ast::{SolveKind, Tactic};
use crate::elab::{Elab, ProofState};
use crate::parser::{parse_source, parse_tactics_text};
use crate::suggest::{suggest_goal, Suggestion};
use crate::{CompiledModule, SDecl, TheoremProof};
use rigor_certificates::bootstrap_kernel;
use rigor_codec::{encode_bundle, encode_kernel, Challenge};
use rigor_kernel::{DeclKind, NExpr, Reducibility};
use rigor_spec::sha256::domain_hash;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum Command {
    Open { source: String },
    Inspect,
    /// Move the current state pointer back to a previously returned immutable
    /// state id. Stored states themselves never change.
    Restore { state_id: String },
    /// Return deterministic tactic hints for the focused goal without
    /// changing the proof state.
    Suggest,
    Fork { goal_tag: String },
    Apply { tactic: String },
    Refine { tactic: String },
    SubmitCert { plugin: String, args: Vec<String> },
    Seal,
}

#[derive(Debug, Clone)]
pub struct GoalView {
    pub tag: String,
    pub context: Vec<String>,
    pub target: String,
    pub focused: bool,
    pub closed: bool,
}

#[derive(Debug, Clone)]
pub struct Response {
    pub state_id: String,
    pub ok: bool,
    pub message: String,
    pub goals: Vec<GoalView>,
    pub theorem: Option<String>,
    pub suggestions: Vec<Suggestion>,
    pub sealed: Option<SealedBundle>,
}

#[derive(Debug, Clone)]
pub struct SealedBundle {
    pub bundle_bytes: Vec<u8>,
    pub challenge: Option<Challenge>,
    pub statement_id: Option<String>,
}

struct Session {
    elab: Elab,
    /// The theorem currently being proved interactively (name, telescope
    /// context, target), if any.
    current: Option<(String, Vec<crate::elab::CtxLocal>, NExpr, Vec<String>)>,
    states: HashMap<String, ProofState>,
    current_state: Option<String>,
    nonce: u64,
    sealed: Vec<(String, SealedBundle)>,
    pending_roots: Vec<String>,
}

impl Session {
    fn snapshot(&mut self, state: &ProofState) -> String {
        self.nonce += 1;
        let mut data = format!("nonce:{};", self.nonce);
        for g in &state.goals {
            data.push_str(&format!(
                "goal[{}|{}|{}|{:?}];",
                g.tag,
                rigor_kernel::pretty_named(&g.target),
                g.assign.is_some(),
                g.ctx.iter().map(|l| l.name.clone()).collect::<Vec<_>>()
            ));
        }
        let id = rigor_spec::sha256::to_hex(&domain_hash("RIGOR_PROTO_STATE_V1\0".as_bytes(), &[data.as_bytes()]));
        self.states.insert(id.clone(), state.clone());
        self.current_state = Some(id.clone());
        id
    }

    fn goals_view(&self, state: &ProofState) -> Vec<GoalView> {
        state
            .goals
            .iter()
            .map(|g| GoalView {
                tag: g.tag.clone(),
                context: g.ctx.iter().map(|l| format!("{} : {}", l.name, rigor_kernel::pretty_named(&l.ty))).collect(),
                target: rigor_kernel::pretty_named(&g.target),
                focused: state.focus == Some(g.id),
                closed: g.assign.is_some(),
            })
            .collect()
    }
}

pub struct Machine {
    session: Session,
}

impl Default for Machine {
    fn default() -> Self {
        Self::new()
    }
}

impl Machine {
    pub fn new() -> Self {
        let kernel = bootstrap_kernel().expect("stdlib bootstrap");
        Machine {
            session: Session {
                elab: Elab::new(kernel),
                current: None,
                states: HashMap::new(),
                current_state: None,
                nonce: 0,
                sealed: Vec::new(),
                pending_roots: Vec::new(),
            },
        }
    }

    fn err(&self, msg: impl Into<String>) -> Response {
        let state = self.current_state().ok();
        Response {
            state_id: self.session.current_state.clone().unwrap_or_default(),
            ok: false,
            message: msg.into(),
            goals: state.as_ref().map(|st| self.session.goals_view(st)).unwrap_or_default(),
            theorem: self.session.current.as_ref().map(|c| c.0.clone()),
            suggestions: state
                .as_ref()
                .and_then(|st| st.focused())
                .map(|g| suggest_goal(&self.session.elab, g))
                .unwrap_or_default(),
            sealed: None,
        }
    }

    fn ok(&mut self, state: &ProofState, msg: impl Into<String>) -> Response {
        let suggestions = state.focused().map(|g| suggest_goal(&self.session.elab, g)).unwrap_or_default();
        let id = self.session.snapshot(state);
        Response {
            state_id: id,
            ok: true,
            message: msg.into(),
            goals: self.session.goals_view(state),
            theorem: self.session.current.as_ref().map(|c| c.0.clone()),
            suggestions,
            sealed: None,
        }
    }

    fn current_state(&self) -> Result<ProofState, String> {
        let id = self.session.current_state.clone().ok_or("no open proof state; OPEN a theorem first")?;
        self.session.states.get(&id).cloned().ok_or_else(|| "state vanished".to_string())
    }

    pub fn execute(&mut self, cmd: Command) -> Response {
        match cmd {
            Command::Open { source } => self.cmd_open(&source),
            Command::Inspect => match self.current_state() {
                Ok(st) => {
                    let id = self.session.current_state.clone().unwrap_or_default();
                    Response {
                        state_id: id,
                        ok: true,
                        message: "goals".into(),
                        goals: self.session.goals_view(&st),
                        theorem: self.session.current.as_ref().map(|c| c.0.clone()),
                        suggestions: st.focused().map(|g| suggest_goal(&self.session.elab, g)).unwrap_or_default(),
                        sealed: None,
                    }
                }
                Err(e) => self.err(e),
            },
            Command::Restore { state_id } => {
                if !self.session.states.contains_key(&state_id) {
                    return self.err(format!("unknown state id '{state_id}'"));
                }
                self.session.current_state = Some(state_id.clone());
                let st = self.session.states[&state_id].clone();
                Response {
                    state_id,
                    ok: true,
                    message: "restored immutable proof state".into(),
                    goals: self.session.goals_view(&st),
                    theorem: self.session.current.as_ref().map(|c| c.0.clone()),
                    suggestions: st.focused().map(|g| suggest_goal(&self.session.elab, g)).unwrap_or_default(),
                    sealed: None,
                }
            }
            Command::Suggest => match self.current_state() {
                Ok(st) => {
                    let id = self.session.current_state.clone().unwrap_or_default();
                    Response {
                        state_id: id,
                        ok: true,
                        message: "suggestions".into(),
                        goals: self.session.goals_view(&st),
                        theorem: self.session.current.as_ref().map(|c| c.0.clone()),
                        suggestions: st.focused().map(|g| suggest_goal(&self.session.elab, g)).unwrap_or_default(),
                        sealed: None,
                    }
                }
                Err(e) => self.err(e),
            },
            Command::Fork { goal_tag } => {
                let mut st = match self.current_state() {
                    Ok(s) => s,
                    Err(e) => return self.err(e),
                };
                match st.goals.iter().find(|g| g.assign.is_none() && g.tag == goal_tag) {
                    Some(g) => {
                        st.focus = Some(g.id);
                        self.ok(&st, format!("forked focus to goal '{goal_tag}'"))
                    }
                    None => self.err(format!("no open goal tagged '{goal_tag}'")),
                }
            }
            Command::Apply { tactic } | Command::Refine { tactic } => {
                let mut st = match self.current_state() {
                    Ok(s) => s,
                    Err(e) => return self.err(e),
                };
                let tactics = match parse_tactics_text(&tactic) {
                    Ok(t) => t,
                    Err(e) => return self.err(e),
                };
                if tactics.len() != 1 {
                    return self.err("APPLY takes exactly one tactic");
                }
                match self.session.elab.run_tactics(&mut st, &tactics) {
                    Ok(()) => self.ok(&st, "applied"),
                    Err(e) => self.err(e),
                }
            }
            Command::SubmitCert { plugin, args } => {
                let mut st = match self.current_state() {
                    Ok(s) => s,
                    Err(e) => return self.err(e),
                };
                let tac = match plugin.as_str() {
                    "poly" => Tactic::Solve(SolveKind::Poly),
                    "sat" => Tactic::Solve(SolveKind::Sat),
                    "farkas" => {
                        let mut mults = Vec::new();
                        for a in &args {
                            match a.parse::<u64>() {
                                Ok(n) => mults.push(rigor_spec::BigUint::from_u64(n)),
                                Err(_) => return self.err(format!("bad farkas multiplier '{a}'")),
                            }
                        }
                        Tactic::Solve(SolveKind::Farkas(mults))
                    }
                    other => return self.err(format!("unknown certificate plugin '{other}'")),
                };
                match self.session.elab.run_tactic(&mut st, &tac) {
                    Ok(()) => self.ok(&st, format!("certificate {plugin} accepted (reduced to a core proof)")),
                    Err(e) => self.err(e),
                }
            }
            Command::Seal => self.cmd_seal(),
        }
    }

    fn cmd_open(&mut self, source: &str) -> Response {
        let decls = match parse_source(source) {
            Ok(d) => d,
            Err(e) => return self.err(e),
        };
        // OPEN runs declarations until the first theorem (inclusive), which
        // becomes the interactive proof. Definitions before it are admitted.
        for decl in &decls {
            match decl {
                SDecl::Theorem { name, telescope, target, proof, .. } => {
                    if let TheoremProof::Term(_) = proof {
                        // closed-form proof: admit immediately via compile path pieces
                    }
                    let ctx = match crate::elaborate_telescope(&mut self.session.elab, telescope) {
                        Ok(c) => c,
                        Err(e) => return self.err(e),
                    };
                    let mut obs = Vec::new();
                    let target_e = match self.session.elab.elaborate(&ctx, target, &mut obs) {
                        Ok(t) => t,
                        Err(e) => return self.err(e),
                    };
                    let mut state = ProofState::new(ctx.clone(), target_e.clone());
                    for (octx, oty) in obs {
                        state.add_goal(octx, oty, "denominator_nonzero".to_string());
                    }
                    if let TheoremProof::Term(t) = proof {
                        if let Err(e) = self.session.elab.run_tactic(&mut state, &Tactic::Exact(t.clone())) {
                            return self.err(e);
                        }
                    }
                    let levels = match decl {
                        SDecl::Theorem { levels, .. } => levels.clone(),
                        _ => Vec::new(),
                    };
                    self.session.current = Some((name.clone(), ctx, target_e, levels));
                    let resp = self.ok(&state, format!("opened theorem '{name}'"));
                    return resp;
                }
                SDecl::Module { .. } | SDecl::Profile { .. } | SDecl::Import { .. } | SDecl::Challenge { .. } => {
                    if let SDecl::Profile { strict } = decl {
                        self.session.elab.strict = *strict;
                    }
                }
                other => {
                    // Admit non-theorem declarations by compiling them alone:
                    // reuse the module compiler over a synthetic source is not
                    // possible here, so admit defs/axioms/inductives directly
                    // through the shared helpers by re-dispatch: simplest is
                    // to require theorems last. We support def/axiom/inductive
                    // via a one-decl compile in a fresh bootstrap? No: they
                    // must land in *this* session kernel. Handle the common
                    // cases explicitly:
                    if let Err(e) = self.admit_non_theorem(other) {
                        return self.err(e);
                    }
                }
            }
        }
        self.err("OPEN source contains no theorem")
    }

    fn admit_non_theorem(&mut self, decl: &SDecl) -> Result<(), String> {
        // Delegate to the batch compiler machinery by compiling a module
        // consisting of just this declaration in the *same* kernel: replicate
        // the Def/Axiom/Inductive arms of compile_with on this session.
        match decl {
            SDecl::Def { name, levels, telescope, ty, value } => {
                self.session.elab.level_scope = levels.clone();
                let lps: Vec<&str> = levels.iter().map(|s| s.as_str()).collect();
                let ctx = crate::elaborate_telescope(&mut self.session.elab, telescope)?;
                match value {
                    TheoremProof::Term(t) => {
                        let mut obs = Vec::new();
                        let val_open = self.session.elab.elaborate(&ctx, t, &mut obs)?;
                        if !obs.is_empty() {
                            return Err("definition with unresolved division obligation".into());
                        }
                        let ty_open = match ty {
                            Some(t) => {
                                let mut o2 = Vec::new();
                                self.session.elab.elaborate(&ctx, t, &mut o2)?
                            }
                            None => self.session.elab.infer_nexpr(&ctx, &val_open)?,
                        };
                        let ty_closed = crate::wrap(&ctx, ty_open, true);
                        let val_closed = crate::wrap(&ctx, val_open, false);
                        self.session
                            .elab
                            .kernel
                            .add_definition(name, &lps, ty_closed, val_closed, DeclKind::Definition, Reducibility::Regular)
                            .map_err(|e| e.to_string())?;
                        Ok(())
                    }
                    TheoremProof::Tactics(_) => Err("interactive OPEN does not support tactic-defined defs".into()),
                }
            }
            SDecl::Axiom { name, levels, ty } => {
                self.session.elab.level_scope = levels.clone();
                let lps: Vec<&str> = levels.iter().map(|s| s.as_str()).collect();
                let mut obs = Vec::new();
                let ty_e = self.session.elab.elaborate(&[], ty, &mut obs)?;
                self.session.elab.kernel.add_axiom(name, &lps, ty_e).map_err(|e| e.to_string())?;
                Ok(())
            }
            SDecl::Inductive { name, levels, params, ty, ctors } => {
                self.session.elab.level_scope = levels.clone();
                let pctx = crate::elaborate_telescope(&mut self.session.elab, params)?;
                let mut obs = Vec::new();
                let result_ty = self.session.elab.elaborate(&pctx, ty, &mut obs)?;
                if !obs.is_empty() {
                    return Err(format!("inductive '{name}': obligations not allowed in the result type"));
                }
                let full_ty = crate::wrap(&pctx, result_ty, true);
                let num_params: u32 = params.iter().map(|t| t.names.len() as u32).sum();
                let mut ctor_specs = Vec::new();
                for ctor in ctors {
                    let mut cctx = pctx.clone();
                    for tele in &ctor.binders {
                        let mut obs2 = Vec::new();
                        let cty = self.session.elab.elaborate(&cctx, &tele.ty, &mut obs2)?;
                        if !obs2.is_empty() {
                            return Err(format!("constructor '{}': obligations not allowed", ctor.name));
                        }
                        for n in &tele.names {
                            let local = self.session.elab.make_local(&cctx, n, cty.clone(), None, false)?;
                            cctx.push(local);
                        }
                    }
                    let result = match &ctor.result {
                        Some(r) => {
                            let mut obs3 = Vec::new();
                            self.session.elab.elaborate(&cctx, r, &mut obs3)?
                        }
                        None => {
                            let mut app = NExpr::Const(name.clone(), self.session.elab.default_levels(name));
                            for local in &pctx {
                                app = NExpr::app(app, NExpr::var(&local.name));
                            }
                            app
                        }
                    };
                    let full = crate::wrap(&cctx, result, true);
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
                self.session
                    .elab
                    .kernel
                    .add_inductive_block(vec![spec])
                    .map_err(|e| format!("inductive '{name}': {e}"))?;
                Ok(())
            }
            _ => Err("OPEN supports def/axiom/inductive declarations before the theorem".into()),
        }
    }

    fn cmd_seal(&mut self) -> Response {
        let st = match self.current_state() {
            Ok(s) => s,
            Err(e) => return self.err(e),
        };
        let (name, ctx, target, levels) = match &self.session.current {
            Some(c) => c.clone(),
            None => return self.err("nothing to seal"),
        };
        let open = st.open_goals();
        if !open.is_empty() {
            return self.err(format!("cannot seal: {} open goal(s) remain", open.len()));
        }
        let root = st.goals[0].clone();
        let proof_open = match st.assemble(&root) {
            Ok(p) => p,
            Err(e) => return self.err(e),
        };
        // Record the checking ticket and admit to the kernel.
        if let Err(e) = crate::emit_theorem_ticket(&mut self.session.elab, &ctx, &proof_open, &target) {
            return self.err(e);
        }
        let ty_closed = crate::wrap(&ctx, target.clone(), true);
        let val_closed = crate::wrap(&ctx, proof_open, false);
        let lps: Vec<&str> = levels.iter().map(|s| s.as_str()).collect();
        if let Err(e) = self
            .session
            .elab
            .kernel
            .add_definition(&name, &lps, ty_closed, val_closed, DeclKind::Theorem, Reducibility::Opaque)
        {
            return self.err(format!("kernel rejected the sealed proof: {e}"));
        }
        self.session.pending_roots.push(name.clone());
        let roots = self.session.pending_roots.clone();
        let bundle = encode_kernel(
            &self.session.elab.kernel,
            &roots,
            &self.session.elab.tickets,
            &self.session.elab.contexts,
            Some("sealed via machine protocol".into()),
        );
        let bytes = encode_bundle(&bundle);
        let sids = rigor_codec::statement_ids(&bundle);
        let sealed = SealedBundle {
            bundle_bytes: bytes,
            challenge: None,
            statement_id: sids.get(&name).map(|s| s.to_hex()),
        };
        self.session.sealed.push((name.clone(), sealed.clone()));
        let mut resp = self.ok(&st, format!("sealed theorem '{name}'"));
        resp.sealed = Some(sealed);
        resp
    }
}

/// Compile a finished interactive session's module (batch equivalent of
/// sealing every pending root into one bundle).
pub fn compile_session_module(machine: &Machine) -> Result<CompiledModule, String> {
    let s = &machine.session;
    let roots = s.pending_roots.clone();
    let bundle = encode_kernel(&s.elab.kernel, &roots, &s.elab.tickets, &s.elab.contexts, None);
    let bytes = encode_bundle(&bundle);
    let sids = rigor_codec::statement_ids(&bundle);
    Ok(CompiledModule {
        name: String::new(),
        bundle,
        bundle_bytes: bytes,
        statement_ids: sids.iter().map(|(k, v)| (k.clone(), v.to_hex())).collect(),
        roots,
        challenges: Vec::new(),
        ticket_count: s.elab.tickets.len(),
    })
}
