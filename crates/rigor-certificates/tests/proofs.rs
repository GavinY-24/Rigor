use rigor_certificates::linarith::{nat_farkas_proof, NatIneq};
use rigor_certificates::poly::{poly_identity_proof, PolyExpr};
use rigor_certificates::sat::{unsat_case_proof, unsat_statement, Formula};
use rigor_certificates::*;
use rigor_kernel::*;
use rigor_spec::BigUint;

fn check_proof(k: &mut Kernel, ty: &NExpr, proof: &NExpr, scope: &[&str]) {
    let mut sc: Vec<String> = scope.iter().map(|s| s.to_string()).collect();
    let ty_id = lower(&mut k.arena, &mut k.names, &mut sc.clone(), ty).expect("lower ty");
    let mut sc2: Vec<String> = scope.iter().map(|s| s.to_string()).collect();
    let _ = &mut sc;
    let proof_id = lower(&mut k.arena, &mut k.names, &mut sc2, proof).expect("lower proof");
    let ctx: Vec<LocalDecl> = Vec::new();
    // Build context from scope: all Nat unless specified by caller through ty structure.
    let _ = ctx;
    // Use a Nat context for all scope variables (tests use Nat/Bool by name prefix).
    let mut kctx: Vec<LocalDecl> = Vec::new();
    for name in scope {
        let nid = k.names.intern(Name::root(name));
        let tid = {
            let cn = if name.starts_with('v') && !name.starts_with("x") { "Bool" } else { "Nat" };
            let id = k.name(cn);
            k.arena.const_(id, vec![])
        };
        kctx.push(LocalDecl { name: nid, ty: tid, value: None });
    }
    k.check(&kctx, proof_id, ty_id)
        .unwrap_or_else(|e| panic!("proof does not check: {e}"));
}

#[test]
fn poly_identity_core_proof() {
    let mut k = bootstrap_kernel().expect("bootstrap");
    let x = PolyExpr::var(0);
    let lhs = PolyExpr::mul(
        PolyExpr::add(x.clone(), PolyExpr::konst(1)),
        PolyExpr::add(x.clone(), PolyExpr::konst(1)),
    );
    let rhs = PolyExpr::add(
        PolyExpr::add(
            PolyExpr::mul(x.clone(), x.clone()),
            PolyExpr::mul(PolyExpr::konst(2), x.clone()),
        ),
        PolyExpr::konst(1),
    );
    let vars = vec!["x".to_string()];
    let proof = poly_identity_proof(&lhs, &rhs, &vars).expect("build poly proof");
    let ty = stdlib::eq(
        stdlib::nat(),
        rigor_certificates::poly::poly_to_nexpr(&lhs, &vars),
        rigor_certificates::poly::poly_to_nexpr(&rhs, &vars),
    );
    check_proof(&mut k, &ty, &proof, &["x"]);
}

#[test]
fn poly_identity_three_factor_comm() {
    // Regression: multiplying three monomials reassociates and sorts.
    // The coefficient-1 wrapper used to claim the scaled product was
    // already sorted, so the proof's equality endpoints did not match.
    let mut k = bootstrap_kernel().expect("bootstrap");
    let lhs = PolyExpr::mul(
        PolyExpr::mul(PolyExpr::var(0), PolyExpr::var(1)),
        PolyExpr::var(2),
    );
    let rhs = PolyExpr::mul(
        PolyExpr::var(2),
        PolyExpr::mul(PolyExpr::var(1), PolyExpr::var(0)),
    );
    let vars = vec!["x".to_string(), "y".to_string(), "z".to_string()];
    let proof = poly_identity_proof(&lhs, &rhs, &vars).expect("build");
    let ty = stdlib::eq(
        stdlib::nat(),
        rigor_certificates::poly::poly_to_nexpr(&lhs, &vars),
        rigor_certificates::poly::poly_to_nexpr(&rhs, &vars),
    );
    check_proof(&mut k, &ty, &proof, &["x", "y", "z"]);
}

#[test]
fn poly_identity_simple_comm() {
    let mut k = bootstrap_kernel().expect("bootstrap");
    let lhs = PolyExpr::add(PolyExpr::var(0), PolyExpr::var(1));
    let rhs = PolyExpr::add(PolyExpr::var(1), PolyExpr::var(0));
    let vars = vec!["x".to_string(), "y".to_string()];
    let proof = poly_identity_proof(&lhs, &rhs, &vars).expect("build");
    let ty = stdlib::eq(
        stdlib::nat(),
        rigor_certificates::poly::poly_to_nexpr(&lhs, &vars),
        rigor_certificates::poly::poly_to_nexpr(&rhs, &vars),
    );
    // manual Nat context (both Nat)
    let mut sc: Vec<String> = vec!["x".into(), "y".into()];
    let ty_id = lower(&mut k.arena, &mut k.names, &mut sc.clone(), &ty).unwrap();
    let proof_id = lower(&mut k.arena, &mut k.names, &mut sc, &proof).unwrap();
    let nat_id = k.name("Nat");
    let nat_ty = k.arena.const_(nat_id, vec![]);
    let ctx = vec![
        LocalDecl { name: k.name("x"), ty: nat_ty, value: None },
        LocalDecl { name: k.name("y"), ty: nat_ty, value: None },
    ];
    k.check(&ctx, proof_id, ty_id).expect("comm proof checks");
}

#[test]
fn farkas_nat_core_proof() {
    let mut k = bootstrap_kernel().expect("bootstrap");
    // Hypotheses (as Nat.le rhs lhs, i.e. lhs >= rhs in Nat.le orientation):
    // h1: 5 <= 2x + y   (2x + y >= 5)
    // h2: 1 + x <= y + ... represent -x + y >= 1 over Nat as: x + 1 <= y  is wrong
    // sign-wise for integers; for the Nat core test use a Nat-valid example:
    // h1: x + y >= 3 (3 <= x + y), h2: x >= 1 (1 <= x) prove x + y + x >= 4 with (1,1)? 
    // Use goal: 4 <= 2x + y given h1: 2 <= x, h2: 2 <= x + y with multipliers (1,1):
    // combined le: 2 + 2 = 4 <= x + (x + y) = 2x + y (ge side must match exactly).
    let h1 = NatIneq {
        le_side: vec![],
        le_const: BigUint::from_u64(2),
        ge_side: vec![(0, BigUint::from_u64(1))],
        ge_const: BigUint::zero(),
        proof_name: "h1".to_string(),
    };
    let h2 = NatIneq {
        le_side: vec![],
        le_const: BigUint::from_u64(2),
        ge_side: vec![(0, BigUint::from_u64(1)), (1, BigUint::from_u64(1))],
        ge_const: BigUint::zero(),
        proof_name: "h2".to_string(),
    };
    let goal = NatIneq {
        le_side: vec![],
        le_const: BigUint::from_u64(4),
        ge_side: vec![(0, BigUint::from_u64(2)), (1, BigUint::from_u64(1))],
        ge_const: BigUint::zero(),
        proof_name: String::new(),
    };
    let vars = vec!["x".to_string(), "y".to_string()];
    let proof = nat_farkas_proof(&[h1, h2], &goal, &[BigUint::one(), BigUint::one()], &vars)
        .expect("build farkas proof");
    // goal type: Nat.le 4 (2*x + y) with expression shapes as built by the plugin:
    // ge form poly: 0 + 2*x + 1*y in the plugin's form_to_nexpr shape. Build the
    // expected type via the same linear form machinery is internal; instead state
    // the goal as Nat.le (4) (x + (x + y))... kernel defeq via polynomial
    // normalization is NOT definitional, so we check the proof against the
    // plugin's own form expression:
    let ge = {
        // replicate form_to_nexpr: ((0 + 2*x) + 1*y)
        let two_x = stdlib::apps(
            stdlib::c("Nat.mul"),
            &[NExpr::LitNat(BigUint::from_u64(2)), NExpr::var("x")],
        );
        let one_y = NExpr::var("y");
        stdlib::apps(
            stdlib::c("Nat.add"),
            &[
                stdlib::apps(stdlib::c("Nat.add"), &[NExpr::LitNat(BigUint::zero()), two_x]),
                one_y,
            ],
        )
    };
    let ty = stdlib::apps(stdlib::c("Nat.le"), &[NExpr::LitNat(BigUint::from_u64(4)), ge]);
    let sc: Vec<String> = vec!["x".into(), "y".into()];
    // hypotheses context: h1 : Nat.le 2 x, h2 : Nat.le 2 (x + y) with plugin shapes
    let h1_ty = {
        let mut s: Vec<String> = vec!["x".into(), "y".into()];
        let e = stdlib::apps(stdlib::c("Nat.le"), &[NExpr::LitNat(BigUint::from_u64(2)), NExpr::var("x")]);
        lower(&mut k.arena, &mut k.names, &mut s, &e).unwrap()
    };
    let h2_ty = {
        let mut s: Vec<String> = vec!["x".into(), "y".into(), "h1".into()];
        let ge2 = stdlib::apps(
            stdlib::c("Nat.add"),
            &[
                stdlib::apps(stdlib::c("Nat.add"), &[NExpr::LitNat(BigUint::zero()), NExpr::var("x")]),
                NExpr::var("y"),
            ],
        );
        let e = stdlib::apps(stdlib::c("Nat.le"), &[NExpr::LitNat(BigUint::from_u64(2)), ge2]);
        lower(&mut k.arena, &mut k.names, &mut s, &e).unwrap()
    };
    let ty_id = {
        let mut s: Vec<String> = vec!["x".into(), "y".into(), "h1".into(), "h2".into()];
        lower(&mut k.arena, &mut k.names, &mut s, &ty).unwrap()
    };
    let nat_id = k.name("Nat");
    let nat_ty = k.arena.const_(nat_id, vec![]);
    let ctx = vec![
        LocalDecl { name: k.name("x"), ty: nat_ty, value: None },
        LocalDecl { name: k.name("y"), ty: nat_ty, value: None },
        LocalDecl { name: k.name("h1"), ty: h1_ty, value: None },
        LocalDecl { name: k.name("h2"), ty: h2_ty, value: None },
    ];
    let mut sc3: Vec<String> = vec!["x".into(), "y".into(), "h1".into(), "h2".into()];
    let proof_id2 = lower(&mut k.arena, &mut k.names, &mut sc3.clone(), &proof).unwrap();
    let _ = &mut sc3;
    k.check(&ctx, proof_id2, ty_id).expect("farkas proof checks");
}

#[test]
fn sat_core_proof() {
    let mut k = bootstrap_kernel().expect("bootstrap");
    // (v0 /\ not v0) is unsat
    let f = Formula::And(
        Box::new(Formula::Var(0)),
        Box::new(Formula::Not(Box::new(Formula::Var(0)))),
    );
    let proof = unsat_case_proof(&f, 1).expect("build sat proof");
    let ty = unsat_statement(&f, 1);
    let mut sc: Vec<String> = Vec::new();
    let ty_id = lower(&mut k.arena, &mut k.names, &mut sc.clone(), &ty).unwrap();
    let proof_id = lower(&mut k.arena, &mut k.names, &mut sc, &proof).unwrap();
    k.check(&vec![], proof_id, ty_id).expect("sat proof checks");
}
