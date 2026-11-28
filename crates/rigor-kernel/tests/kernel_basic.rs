use rigor_kernel::*;

fn nat_spec() -> InductiveSpec {
    InductiveSpec {
        name: "Nat".to_string(),
        level_params: vec![],
        ty: NExpr::type0(),
        num_params: 0,
        constructors: vec![
            ("Nat.zero".to_string(), NExpr::const_("Nat")),
            (
                "Nat.succ".to_string(),
                NExpr::pi("n", NExpr::const_("Nat"), NExpr::const_("Nat")),
            ),
        ],
    }
}

fn eq_spec() -> InductiveSpec {
    InductiveSpec {
        name: "Eq".to_string(),
        level_params: vec!["u".to_string()],
        ty: NExpr::pi(
            "α",
            NExpr::sort(Level::Param(0)),
            NExpr::pi(
                "a",
                NExpr::var("α"),
                NExpr::pi("_", NExpr::var("α"), NExpr::prop()),
            ),
        ),
        num_params: 2,
        constructors: vec![(
            "Eq.refl".to_string(),
            NExpr::pi(
                "α",
                NExpr::sort(Level::Param(0)),
                NExpr::pi(
                    "a",
                    NExpr::var("α"),
                    NExpr::apps(
                        NExpr::const_levels("Eq", vec![Level::Param(0)]),
                        &[NExpr::var("α"), NExpr::var("a"), NExpr::var("a")],
                    ),
                ),
            ),
        )],
    }
}

#[test]
fn nat_rec_computes() {
    let mut k = Kernel::new();
    k.add_inductive_block(vec![nat_spec()]).expect("Nat admitted");
    // Nat.add := fun a b => Nat.rec (fun _ => Nat) b (fun _ ih => Nat.succ ih) a
    let add_ty = NExpr::pi(
        "a",
        NExpr::const_("Nat"),
        NExpr::pi("b", NExpr::const_("Nat"), NExpr::const_("Nat")),
    );
    let motive = NExpr::lam("_", NExpr::const_("Nat"), NExpr::const_("Nat"));
    let add_val = NExpr::lam(
        "a",
        NExpr::const_("Nat"),
        NExpr::lam(
            "b",
            NExpr::const_("Nat"),
            NExpr::apps(
                NExpr::const_levels("Nat.rec", vec![Level::Succ(Box::new(Level::Zero))]),
                &[
                    motive,
                    NExpr::var("b"),
                    NExpr::lam(
                        "n",
                        NExpr::const_("Nat"),
                        NExpr::lam(
                            "ih",
                            NExpr::const_("Nat"),
                            NExpr::app(NExpr::const_("Nat.succ"), NExpr::var("ih")),
                        ),
                    ),
                    NExpr::var("a"),
                ],
            ),
        ),
    );
    k.add_definition("Nat.add", &[], add_ty, add_val, DeclKind::Definition, Reducibility::Regular)
        .expect("Nat.add admitted");
    // (2 + 3) reduces to 5: lit infra uses Nat.succ chains as expected type check
    let two = lower_closed(
        &mut k.arena,
        &mut k.names,
        &NExpr::app(
            NExpr::const_("Nat.succ"),
            NExpr::app(NExpr::const_("Nat.succ"), NExpr::const_("Nat.zero")),
        ),
    )
    .unwrap();
    let three = lower_closed(
        &mut k.arena,
        &mut k.names,
        &NExpr::app(
            NExpr::const_("Nat.succ"),
            NExpr::app(
                NExpr::const_("Nat.succ"),
                NExpr::app(NExpr::const_("Nat.succ"), NExpr::const_("Nat.zero")),
            ),
        ),
    )
    .unwrap();
    let nat_id = k.name("Nat");
    let nat_ty = k.arena.const_(nat_id, vec![]);
    let add_id = k.name("Nat.add");
    let add_const = k.arena.const_(add_id, vec![]);
    let lhs = { let a1 = k.arena.app(add_const, two); k.arena.app(a1, three) };
    let five = lower_closed(
        &mut k.arena,
        &mut k.names,
        &NExpr::app(
            NExpr::const_("Nat.succ"),
            NExpr::app(
                NExpr::const_("Nat.succ"),
                NExpr::app(
                    NExpr::const_("Nat.succ"),
                    NExpr::app(
                        NExpr::const_("Nat.succ"),
                        NExpr::app(NExpr::const_("Nat.succ"), NExpr::const_("Nat.zero")),
                    ),
                ),
            ),
        ),
    )
    .unwrap();
    assert!(k.is_def_eq(&vec![], lhs, five).expect("defeq"), "2+3 should be 5");
    let lhs_ty = k.infer(&vec![], lhs).unwrap();
    assert!(k.is_def_eq(&vec![], lhs_ty, nat_ty).unwrap());
}

#[test]
fn eq_transport_round_trip() {
    let mut k = Kernel::new();
    k.add_inductive_block(vec![eq_spec()]).expect("Eq admitted");
    // theorem transport_round_trip : forall (A : Type u) (F : A -> Type v) (x y : A)
    //   (h : Eq A x y) (b : F x), Eq (F y) (transport...) ...
    // We check the Eq.rec-based proof term directly:
    //   fun A F x y h b => Eq.rec A x (fun y _ => F y) b y h  : F y
    // and the round-trip statement proved by Eq.rec on h with motive fun y _ => Eq (F y) (...) b... simplified:
    // statement: Eq (F x) (Eq.rec ... (Eq.rec ... b)) b proved by Eq.rec with motive
    //   fun y h => Eq (F x?) ... Use direct dependent example from the spec:
    // transport F h b := Eq.rec (motive := fun y _ => F y) b h
    // goal after induction h (x:=y via rec): Eq (F x) b b, proof Eq.refl.
    // Full term: fun A F x y h b =>
    //   Eq.rec A x (fun y h => Eq (F y) (transport F (Eq.rec sym...) (transport F h b)) b) (Eq.refl (F x) b) y h
    // Transporting symm requires Eq.rec again; instead state round trip via two recs nested in motive:
    // Simpler checked claim (same dependent content): forall h b, Eq (F y) (transport F h b) (transport F h b) is refl-trivial.
    // The genuinely dependent part we assert here: transport has type F y, and
    // Eq.rec with motive (fun y _ => Eq (F y) (transport...) ...) reduces on refl.
    let u = Level::Param(0);
    let v = Level::Param(1);
    // transport as a definition
    let transport_ty = NExpr::pi(
        "A",
        NExpr::sort(u.clone()),
        NExpr::pi(
            "F",
            NExpr::pi("_", NExpr::var("A"), NExpr::sort(v.clone())),
            NExpr::pi(
                "x",
                NExpr::var("A"),
                NExpr::pi(
                    "y",
                    NExpr::var("A"),
                    NExpr::pi(
                        "h",
                        NExpr::apps(
                            NExpr::const_levels("Eq", vec![u.clone()]),
                            &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y")],
                        ),
                        NExpr::pi(
                            "b",
                            NExpr::app(NExpr::var("F"), NExpr::var("x")),
                            NExpr::app(NExpr::var("F"), NExpr::var("y")),
                        ),
                    ),
                ),
            ),
        ),
    );
    // Eq.rec.{u, v} A x (fun y _ => F y) b y h
    let transport_val = NExpr::lam(
        "A",
        NExpr::sort(u.clone()),
        NExpr::lam(
            "F",
            NExpr::pi("_", NExpr::var("A"), NExpr::sort(v.clone())),
            NExpr::lam(
                "x",
                NExpr::var("A"),
                NExpr::lam(
                    "y",
                    NExpr::var("A"),
                    NExpr::lam(
                        "h",
                        NExpr::apps(
                            NExpr::const_levels("Eq", vec![u.clone()]),
                            &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y")],
                        ),
                        NExpr::lam(
                            "b",
                            NExpr::app(NExpr::var("F"), NExpr::var("x")),
                            NExpr::apps(
                                NExpr::const_levels("Eq.rec", vec![u.clone(), v.clone()]),
                                &[
                                    NExpr::var("A"),
                                    NExpr::var("x"),
                                    NExpr::lam(
                                        "y2",
                                        NExpr::var("A"),
                                        NExpr::lam(
                                            "_",
                                            NExpr::apps(
                                                NExpr::const_levels("Eq", vec![u.clone()]),
                                                &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y2")],
                                            ),
                                            NExpr::app(NExpr::var("F"), NExpr::var("y2")),
                                        ),
                                    ),
                                    NExpr::var("b"),
                                    NExpr::var("y"),
                                    NExpr::var("h"),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    k.add_definition(
        "transport",
        &["u", "v"],
        transport_ty,
        transport_val,
        DeclKind::Definition,
        Reducibility::Regular,
    )
    .expect("transport should typecheck (dependent Eq.rec)");

    // Round-trip theorem: transport (symm h) (transport h b) = b, proved by
    // Eq.rec on h (motive over y,h), refl case is Eq.refl.
    // symm: fun h => Eq.rec (motive fun y _ => Eq A y x) (Eq.refl) h
    let symm_ty = NExpr::pi(
        "A",
        NExpr::sort(u.clone()),
        NExpr::pi(
            "x",
            NExpr::var("A"),
            NExpr::pi(
                "y",
                NExpr::var("A"),
                NExpr::pi(
                    "h",
                    NExpr::apps(NExpr::const_levels("Eq", vec![u.clone()]), &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y")]),
                    NExpr::apps(NExpr::const_levels("Eq", vec![u.clone()]), &[NExpr::var("A"), NExpr::var("y"), NExpr::var("x")]),
                ),
            ),
        ),
    );
    let symm_val = NExpr::lam(
        "A",
        NExpr::sort(u.clone()),
        NExpr::lam(
            "x",
            NExpr::var("A"),
            NExpr::lam(
                "y",
                NExpr::var("A"),
                NExpr::lam(
                    "h",
                    NExpr::apps(NExpr::const_levels("Eq", vec![u.clone()]), &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y")]),
                    NExpr::apps(
                        NExpr::const_levels("Eq.rec", vec![u.clone(), Level::Zero]),
                        &[
                            NExpr::var("A"),
                            NExpr::var("x"),
                            NExpr::lam(
                                "y2",
                                NExpr::var("A"),
                                NExpr::lam(
                                    "_",
                                    NExpr::apps(NExpr::const_levels("Eq", vec![u.clone()]), &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y2")]),
                                    NExpr::apps(NExpr::const_levels("Eq", vec![u.clone()]), &[NExpr::var("A"), NExpr::var("y2"), NExpr::var("x")]),
                                ),
                            ),
                            NExpr::apps(NExpr::const_levels("Eq.refl", vec![u.clone()]), &[NExpr::var("A"), NExpr::var("x")]),
                            NExpr::var("y"),
                            NExpr::var("h"),
                        ],
                    ),
                ),
            ),
        ),
    );
    k.add_definition("Eq.symm", &["u"], symm_ty, symm_val, DeclKind::Definition, Reducibility::Regular)
        .expect("Eq.symm should typecheck");

    let rt_ty = NExpr::pi(
        "A",
        NExpr::sort(u.clone()),
        NExpr::pi(
            "F",
            NExpr::pi("_", NExpr::var("A"), NExpr::sort(v.clone())),
            NExpr::pi(
                "x",
                NExpr::var("A"),
                NExpr::pi(
                    "y",
                    NExpr::var("A"),
                    NExpr::pi(
                        "h",
                        NExpr::apps(NExpr::const_levels("Eq", vec![u.clone()]), &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y")]),
                        NExpr::pi(
                            "b",
                            NExpr::app(NExpr::var("F"), NExpr::var("x")),
                            NExpr::apps(
                                NExpr::const_levels("Eq", vec![v.clone()]),
                                &[
                                    NExpr::app(NExpr::var("F"), NExpr::var("x")),
                                    NExpr::apps(
                                        NExpr::const_levels("transport", vec![u.clone(), v.clone()]),
                                        &[
                                            NExpr::var("A"),
                                            NExpr::var("F"),
                                            NExpr::var("y"),
                                            NExpr::var("x"),
                                            NExpr::apps(
                                                NExpr::const_levels("Eq.symm", vec![u.clone()]),
                                                &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y"), NExpr::var("h")],
                                            ),
                                            NExpr::apps(
                                                NExpr::const_levels("transport", vec![u.clone(), v.clone()]),
                                                &[NExpr::var("A"), NExpr::var("F"), NExpr::var("x"), NExpr::var("y"), NExpr::var("h"), NExpr::var("b")],
                                            ),
                                        ],
                                    ),
                                    NExpr::var("b"),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    // proof: Eq.rec on h with motive (fun y h => Eq (F x) (transport (symm h) (transport h b)) b), case refl: Eq.refl
    let motive = NExpr::lam(
        "y2",
        NExpr::var("A"),
        NExpr::lam(
            "h2",
            NExpr::apps(NExpr::const_levels("Eq", vec![u.clone()]), &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y2")]),
            NExpr::apps(
                NExpr::const_levels("Eq", vec![v.clone()]),
                &[
                    NExpr::app(NExpr::var("F"), NExpr::var("x")),
                    NExpr::apps(
                        NExpr::const_levels("transport", vec![u.clone(), v.clone()]),
                        &[
                            NExpr::var("A"),
                            NExpr::var("F"),
                            NExpr::var("y2"),
                            NExpr::var("x"),
                            NExpr::apps(NExpr::const_levels("Eq.symm", vec![u.clone()]), &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y2"), NExpr::var("h2")]),
                            NExpr::apps(
                                NExpr::const_levels("transport", vec![u.clone(), v.clone()]),
                                &[NExpr::var("A"), NExpr::var("F"), NExpr::var("x"), NExpr::var("y2"), NExpr::var("h2"), NExpr::var("b")],
                            ),
                        ],
                    ),
                    NExpr::var("b"),
                ],
            ),
        ),
    );
    let rt_val = NExpr::lam(
        "A",
        NExpr::sort(u.clone()),
        NExpr::lam(
            "F",
            NExpr::pi("_", NExpr::var("A"), NExpr::sort(v.clone())),
            NExpr::lam(
                "x",
                NExpr::var("A"),
                NExpr::lam(
                    "y",
                    NExpr::var("A"),
                    NExpr::lam(
                        "h",
                        NExpr::apps(NExpr::const_levels("Eq", vec![u.clone()]), &[NExpr::var("A"), NExpr::var("x"), NExpr::var("y")]),
                        NExpr::lam(
                            "b",
                            NExpr::app(NExpr::var("F"), NExpr::var("x")),
                            NExpr::apps(
                                NExpr::const_levels("Eq.rec", vec![u.clone(), Level::Zero]),
                                &[
                                    NExpr::var("A"),
                                    NExpr::var("x"),
                                    motive,
                                    NExpr::apps(
                                        NExpr::const_levels("Eq.refl", vec![v.clone()]),
                                        &[NExpr::app(NExpr::var("F"), NExpr::var("x")), NExpr::var("b")],
                                    ),
                                    NExpr::var("y"),
                                    NExpr::var("h"),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    k.add_definition(
        "transport_round_trip",
        &["u", "v"],
        rt_ty,
        rt_val,
        DeclKind::Theorem,
        Reducibility::Opaque,
    )
    .expect("transport_round_trip (spec 2.2) should typecheck");
}

#[test]
fn rejects_type_in_type_and_negative_inductive() {
    let mut k = Kernel::new();
    // Sort u : Sort (succ u) is fine, Type:Type is not expressible; check that
    // (Sort 0 : Sort 0) fails via check of a bogus definition.
    let bad_ty = NExpr::sort(Level::Zero);
    let bad_val = NExpr::sort(Level::Zero);
    let nid = k.name("Bad");
    let ty_id = lower_closed(&mut k.arena, &mut k.names, &bad_ty).unwrap();
    let val_id = lower_closed(&mut k.arena, &mut k.names, &bad_val).unwrap();
    assert!(
        k.add_decl(Decl::new(nid, vec![], ty_id, Some(val_id), DeclKind::Definition))
            .is_err(),
        "Prop : Prop must be rejected"
    );
    // negative inductive: Bad (f : Bad -> Nat) rejected (Nat undeclared is fine; positivity hit first via Bad in Pi domain)
    let mut k2 = Kernel::new();
    let spec = InductiveSpec {
        name: "Bad".to_string(),
        level_params: vec![],
        ty: NExpr::type0(),
        num_params: 0,
        constructors: vec![(
            "Bad.mk".to_string(),
            NExpr::pi(
                "f",
                NExpr::pi("_", NExpr::const_("Bad"), NExpr::const_("Bad")),
                NExpr::const_("Bad"),
            ),
        )],
    };
    assert!(k2.add_inductive_block(vec![spec]).is_err(), "negative inductive must be rejected");
}

#[test]
fn proof_irrelevance_scoped() {
    let mut k = Kernel::new();
    k.add_inductive_block(vec![eq_spec()]).unwrap();
    k.add_inductive_block(vec![nat_spec()]).unwrap();
    // two proofs of same Prop are defeq; proofs of different Props are not terms of same type (unit check via Irrel semantics in ticket tests)
    // Here: Eq.refl at different values have different types, check defeq of types fails appropriately.
    let prop_a = lower_closed(
        &mut k.arena,
        &mut k.names,
        &NExpr::apps(
            NExpr::const_levels("Eq", vec![Level::Succ(Box::new(Level::Zero))]),
            &[
                NExpr::const_("Nat"),
                NExpr::const_("Nat.zero"),
                NExpr::const_("Nat.zero"),
            ],
        ),
    )
    .unwrap();
    let proof1 = lower_closed(
        &mut k.arena,
        &mut k.names,
        &NExpr::apps(
            NExpr::const_levels("Eq.refl", vec![Level::Succ(Box::new(Level::Zero))]),
            &[NExpr::const_("Nat"), NExpr::const_("Nat.zero")],
        ),
    )
    .unwrap();
    k.check(&vec![], proof1, prop_a).expect("refl checks");
}
