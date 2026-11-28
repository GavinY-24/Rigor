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
fn poly_identity_cube_and_scale() {
    // Like-term collection in a cube, and scaling a sum by a coefficient
    // above 1. Both are routine for a ring tactic; the merge walk used to
    // stop after one adjacent pair and treat the rest as reflexivity.
    let mut k = bootstrap_kernel().expect("bootstrap");
    let x = PolyExpr::var(0);
    let xp1 = PolyExpr::add(x.clone(), PolyExpr::konst(1));
    let cube = PolyExpr::mul(PolyExpr::mul(xp1.clone(), xp1.clone()), xp1);
    let expanded = PolyExpr::add(
        PolyExpr::konst(1),
        PolyExpr::add(
            PolyExpr::mul(PolyExpr::konst(3), x.clone()),
            PolyExpr::add(
                PolyExpr::mul(PolyExpr::konst(3), PolyExpr::mul(x.clone(), x.clone())),
                PolyExpr::mul(x.clone(), PolyExpr::mul(x.clone(), x.clone())),
            ),
        ),
    );
    let vars = vec!["x".to_string()];
    let proof = poly_identity_proof(&cube, &expanded, &vars).expect("cube");
    let ty = stdlib::eq(
        stdlib::nat(),
        rigor_certificates::poly::poly_to_nexpr(&cube, &vars),
        rigor_certificates::poly::poly_to_nexpr(&expanded, &vars),
    );
    check_proof(&mut k, &ty, &proof, &["x"]);

    let scaled = PolyExpr::mul(PolyExpr::konst(2), PolyExpr::add(PolyExpr::konst(0), x.clone()));
    let distributed = PolyExpr::add(PolyExpr::konst(0), PolyExpr::mul(PolyExpr::konst(2), x));
    let proof = poly_identity_proof(&scaled, &distributed, &vars).expect("scale");
    let ty = stdlib::eq(
        stdlib::nat(),
        rigor_certificates::poly::poly_to_nexpr(&scaled, &vars),
        rigor_certificates::poly::poly_to_nexpr(&distributed, &vars),
    );
    check_proof(&mut k, &ty, &proof, &["x"]);

    // (a+b)^2 with the cross term collected, the step a ring tactic takes
    // after distributing.
    let a = PolyExpr::var(0);
    let b = PolyExpr::var(1);
    let sq = PolyExpr::mul(
        PolyExpr::add(a.clone(), b.clone()),
        PolyExpr::add(a.clone(), b.clone()),
    );
    let collected = PolyExpr::add(
        PolyExpr::mul(a.clone(), a.clone()),
        PolyExpr::add(
            PolyExpr::mul(PolyExpr::konst(2), PolyExpr::mul(a.clone(), b.clone())),
            PolyExpr::mul(b.clone(), b),
        ),
    );
    let vars2 = vec!["a".into(), "b".into()];
    let proof = poly_identity_proof(&sq, &collected, &vars2).expect("square collect");
    let ty = stdlib::eq(
        stdlib::nat(),
        rigor_certificates::poly::poly_to_nexpr(&sq, &vars2),
        rigor_certificates::poly::poly_to_nexpr(&collected, &vars2),
    );
    check_proof(&mut k, &ty, &proof, &["a", "b"]);
}

#[test]
fn poly_identity_four_factor_comm() {
    // Variable `w` sorts before `x` by name and after it by index. The
    // factor sort has to follow the index order the normal form uses.
    let mut k = bootstrap_kernel().expect("bootstrap");
    let lhs = PolyExpr::mul(
        PolyExpr::mul(PolyExpr::var(0), PolyExpr::var(1)),
        PolyExpr::mul(PolyExpr::var(2), PolyExpr::var(3)),
    );
    let rhs = PolyExpr::mul(
        PolyExpr::var(3),
        PolyExpr::mul(
            PolyExpr::var(2),
            PolyExpr::mul(PolyExpr::var(1), PolyExpr::var(0)),
        ),
    );
    let vars = vec!["x".into(), "y".into(), "z".into(), "w".into()];
    let proof = poly_identity_proof(&lhs, &rhs, &vars).expect("build");
    let ty = stdlib::eq(
        stdlib::nat(),
        rigor_certificates::poly::poly_to_nexpr(&lhs, &vars),
        rigor_certificates::poly::poly_to_nexpr(&rhs, &vars),
    );
    check_proof(&mut k, &ty, &proof, &["x", "y", "z", "w"]);
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
fn farkas_scale_by_two() {
    let mut k = bootstrap_kernel().expect("bootstrap");
    let h = NatIneq {
        le_side: vec![(0, BigUint::one())],
        le_const: BigUint::zero(),
        ge_side: vec![],
        ge_const: BigUint::from_u64(4),
        proof_name: "h".into(),
    };
    let goal = NatIneq {
        le_side: vec![(0, BigUint::from_u64(2))],
        le_const: BigUint::zero(),
        ge_side: vec![],
        ge_const: BigUint::from_u64(8),
        proof_name: String::new(),
    };
    let vars = vec!["x".into()];
    let proof = nat_farkas_proof(&[h], &goal, &[BigUint::from_u64(2)], &vars).expect("build");
    let le = stdlib::apps(
        stdlib::c("Nat.add"),
        &[NExpr::LitNat(BigUint::zero()), stdlib::apps(stdlib::c("Nat.mul"), &[NExpr::LitNat(BigUint::from_u64(2)), NExpr::var("x")])],
    );
    let ty = stdlib::apps(stdlib::c("Nat.le"), &[le, NExpr::LitNat(BigUint::from_u64(8))]);
    let h_ty = stdlib::apps(stdlib::c("Nat.le"), &[NExpr::var("x"), NExpr::LitNat(BigUint::from_u64(4))]);
    let mut sc_h = vec!["x".into()];
    let h_id = lower(&mut k.arena, &mut k.names, &mut sc_h, &h_ty).unwrap();
    let mut sc = vec!["x".into(), "h".into()];
    let ty_id = lower(&mut k.arena, &mut k.names, &mut sc.clone(), &ty).unwrap();
    let proof_id = lower(&mut k.arena, &mut k.names, &mut sc, &proof).unwrap();
    let nat_name = k.name("Nat");
    let x_name = k.name("x");
    let h_name = k.name("h");
    let nat_ty = k.arena.const_(nat_name, vec![]);
    let ctx = vec![
        LocalDecl { name: x_name, ty: nat_ty, value: None },
        LocalDecl { name: h_name, ty: h_id, value: None },
    ];
    k.check(&ctx, proof_id, ty_id).unwrap_or_else(|e| {
        let m = e.to_string();
        panic!("{}", &m[..m.len().min(600)]);
    });
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
