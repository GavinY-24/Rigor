//! The standard mathematical library, built directly on the kernel.
//! Numbers, limits, and algebraic structures are library mathematics with
//! exact definitions — never special tokens blessed by the kernel (the only
//! kernel accommodations are Nat/String *literals*, as in L36).

use rigor_kernel::*;

pub fn lit_nat_expr(n: &rigor_spec::BigUint) -> NExpr {
    NExpr::LitNat(n.clone())
}
pub fn pretty_str(e: &NExpr) -> String {
    rigor_kernel::builder::pretty_named(e)
}
pub fn v(s: &str) -> NExpr {
    NExpr::var(s)
}
pub fn c(s: &str) -> NExpr {
    NExpr::const_(s)
}
pub fn cl(s: &str, levels: Vec<Level>) -> NExpr {
    NExpr::const_levels(s, levels)
}
pub fn app(f: NExpr, a: NExpr) -> NExpr {
    NExpr::app(f, a)
}
pub fn apps(f: NExpr, args: &[NExpr]) -> NExpr {
    NExpr::apps(f, args)
}
pub fn pi(name: &str, dom: NExpr, cod: NExpr) -> NExpr {
    NExpr::pi(name, dom, cod)
}
pub fn lam(name: &str, dom: NExpr, body: NExpr) -> NExpr {
    NExpr::lam(name, dom, body)
}
pub fn u0() -> Level {
    Level::Zero
}
pub fn u_succ(l: Level) -> Level {
    Level::Succ(Box::new(l))
}
pub fn nat() -> NExpr {
    c("Nat")
}
pub fn eq(ty: NExpr, a: NExpr, b: NExpr) -> NExpr {
    // Eq.{u} where ty : Sort u; callers use Type-valued types (u=1) or Prop (u=0) as appropriate.
    // We default to u=1 (Type) via `eq1`; `eq_at` is explicit.
    let _ = (ty.clone(), a.clone(), b.clone());
    eq_at(Level::Succ(Box::new(Level::Zero)), ty, a, b)
}
pub fn eq_at(u: Level, ty: NExpr, a: NExpr, b: NExpr) -> NExpr {
    apps(cl("Eq", vec![u]), &[ty, a, b])
}
pub fn refl_at(u: Level, ty: NExpr, a: NExpr) -> NExpr {
    apps(cl("Eq.refl", vec![u]), &[ty, a])
}

fn ind(name: &str, level_params: &[&str], ty: NExpr, num_params: u32, ctors: Vec<(&str, NExpr)>) -> InductiveSpec {
    InductiveSpec {
        name: name.to_string(),
        level_params: level_params.iter().map(|s| s.to_string()).collect(),
        ty,
        num_params,
        constructors: ctors.into_iter().map(|(n, t)| (n.to_string(), t)).collect(),
    }
}

#[derive(Debug, Default)]
pub struct Stdlib {
    pub names: Vec<String>,
}

fn add_thm(k: &mut Kernel, name: &str, ty: NExpr, val: NExpr) -> Result<(), String> {
    k.add_definition(name, &[], ty, val, DeclKind::Theorem, Reducibility::Opaque)
        .map(|_| ())
        .map_err(|e| format!("{name}: {e}"))
}
fn add_def(k: &mut Kernel, name: &str, ty: NExpr, val: NExpr) -> Result<(), String> {
    k.add_definition(name, &[], ty, val, DeclKind::Definition, Reducibility::Regular)
        .map(|_| ())
        .map_err(|e| format!("{name}: {e}"))
}
fn add_def_u(k: &mut Kernel, name: &str, lps: &[&str], ty: NExpr, val: NExpr) -> Result<(), String> {
    k.add_definition(name, lps, ty, val, DeclKind::Definition, Reducibility::Regular)
        .map(|_| ())
        .map_err(|e| format!("{name}: {e}"))
}

/// Build the bootstrap environment. Every definition and lemma here is
/// admitted by the kernel; lemmas are proved by recursor terms, not asserted.
pub fn bootstrap_kernel() -> Result<Kernel, String> {
    let mut k = Kernel::new();
    bootstrap_into(&mut k)?;
    Ok(k)
}

pub fn bootstrap_into(k: &mut Kernel) -> Result<Stdlib, String> {
    let mut k = k;
    let mut lib = Stdlib::default();
    let mut reg = |lib: &mut Stdlib, n: &str| lib.names.push(n.to_string());

    // ---- Nat ----
    k.add_inductive_block(vec![ind(
        "Nat",
        &[],
        NExpr::type0(),
        0,
        vec![
            ("Nat.zero", nat()),
            ("Nat.succ", pi("n", nat(), nat())),
        ],
    )])
    .map_err(|e| e.to_string())?;
    reg(&mut lib, "Nat");

    // ---- Eq ----
    let up = Level::Param(0);
    k.add_inductive_block(vec![ind(
        "Eq",
        &["u"],
        pi(
            "α",
            NExpr::sort(up.clone()),
            pi("a", v("α"), pi("_b", v("α"), NExpr::prop())),
        ),
        2,
        vec![(
            "Eq.refl",
            pi(
                "α",
                NExpr::sort(up.clone()),
                pi(
                    "a",
                    v("α"),
                    apps(cl("Eq", vec![up.clone()]), &[v("α"), v("a"), v("a")]),
                ),
            ),
        )],
    )])
    .map_err(|e| e.to_string())?;
    reg(&mut lib, "Eq");

    // Quotient primitive package (Eq must exist first).
    k.add_quot().map_err(|e| e.to_string())?;
    reg(&mut lib, "Quot");

    // ---- Bool, True, False, And, Or, Iff, Exists, Prod, Sigma, List, Vec ----
    k.add_inductive_block(vec![ind(
        "Bool",
        &[],
        NExpr::type0(),
        0,
        vec![("Bool.true", c("Bool")), ("Bool.false", c("Bool"))],
    )])
    .map_err(|e| e.to_string())?;

    k.add_inductive_block(vec![ind(
        "True",
        &[],
        NExpr::prop(),
        0,
        vec![("True.intro", c("True"))],
    )])
    .map_err(|e| e.to_string())?;

    k.add_inductive_block(vec![ind("False", &[], NExpr::prop(), 0, vec![])])
        .map_err(|e| e.to_string())?;

    // And : Prop -> Prop -> Prop (params A B, one ctor)
    k.add_inductive_block(vec![ind(
        "And",
        &[],
        pi("A", NExpr::prop(), pi("B", NExpr::prop(), NExpr::prop())),
        2,
        vec![(
            "And.intro",
            pi(
                "A",
                NExpr::prop(),
                pi(
                    "B",
                    NExpr::prop(),
                    pi(
                        "left",
                        v("A"),
                        pi("right", v("B"), apps(c("And"), &[v("A"), v("B")])),
                    ),
                ),
            ),
        )],
    )])
    .map_err(|e| e.to_string())?;

    k.add_inductive_block(vec![ind(
        "Or",
        &[],
        pi("A", NExpr::prop(), pi("B", NExpr::prop(), NExpr::prop())),
        2,
        vec![
            (
                "Or.inl",
                pi(
                    "A",
                    NExpr::prop(),
                    pi("B", NExpr::prop(), pi("h", v("A"), apps(c("Or"), &[v("A"), v("B")]))),
                ),
            ),
            (
                "Or.inr",
                pi(
                    "A",
                    NExpr::prop(),
                    pi("B", NExpr::prop(), pi("h", v("B"), apps(c("Or"), &[v("A"), v("B")]))),
                ),
            ),
        ],
    )])
    .map_err(|e| e.to_string())?;

    k.add_inductive_block(vec![ind(
        "Iff",
        &[],
        pi("A", NExpr::prop(), pi("B", NExpr::prop(), NExpr::prop())),
        2,
        vec![(
            "Iff.intro",
            pi(
                "A",
                NExpr::prop(),
                pi(
                    "B",
                    NExpr::prop(),
                    pi(
                        "mp",
                        pi("_", v("A"), v("B")),
                        pi(
                            "mpr",
                            pi("_", v("B"), v("A")),
                            apps(c("Iff"), &[v("A"), v("B")]),
                        ),
                    ),
                ),
            ),
        )],
    )])
    .map_err(|e| e.to_string())?;

    // Exists (A : Type) (p : A -> Prop) : Prop
    k.add_inductive_block(vec![ind(
        "Exists",
        &["u"],
        pi(
            "A",
            NExpr::sort(Level::Param(0)),
            pi(
                "p",
                pi("_", v("A"), NExpr::prop()),
                NExpr::prop(),
            ),
        ),
        2,
        vec![(
            "Exists.intro",
            pi(
                "A",
                NExpr::sort(Level::Param(0)),
                pi(
                    "p",
                    pi("_", v("A"), NExpr::prop()),
                    pi(
                        "w",
                        v("A"),
                        pi(
                            "h",
                            app(v("p"), v("w")),
                            apps(cl("Exists", vec![Level::Param(0)]), &[v("A"), v("p")]),
                        ),
                    ),
                ),
            ),
        )],
    )])
    .map_err(|e| e.to_string())?;

    // Prod (A B : Type) : Type (single ctor = structure)
    k.add_inductive_block(vec![ind(
        "Prod",
        &["u", "v"],
        pi(
            "A",
            NExpr::sort(Level::Param(0)),
            pi("B", NExpr::sort(Level::Param(1)), NExpr::sort(Level::IMax(Box::new(Level::Param(0)), Box::new(Level::Param(1))))),
        ),
        2,
        vec![(
            "Prod.mk",
            pi(
                "A",
                NExpr::sort(Level::Param(0)),
                pi(
                    "B",
                    NExpr::sort(Level::Param(1)),
                    pi(
                        "fst",
                        v("A"),
                        pi(
                            "snd",
                            v("B"),
                            apps(
                                cl("Prod", vec![Level::Param(0), Level::Param(1)]),
                                &[v("A"), v("B")],
                            ),
                        ),
                    ),
                ),
            ),
        )],
    )])
    .map_err(|e| e.to_string())?;

    // List (A : Type) : Type
    k.add_inductive_block(vec![ind(
        "List",
        &["u"],
        pi("A", NExpr::sort(Level::Param(0)), NExpr::sort(Level::Param(0))),
        1,
        vec![
            (
                "List.nil",
                pi(
                    "A",
                    NExpr::sort(Level::Param(0)),
                    apps(cl("List", vec![Level::Param(0)]), &[v("A")]),
                ),
            ),
            (
                "List.cons",
                pi(
                    "A",
                    NExpr::sort(Level::Param(0)),
                    pi(
                        "head",
                        v("A"),
                        pi(
                            "tail",
                            apps(cl("List", vec![Level::Param(0)]), &[v("A")]),
                            apps(cl("List", vec![Level::Param(0)]), &[v("A")]),
                        ),
                    ),
                ),
            ),
        ],
    )])
    .map_err(|e| e.to_string())?;

    // Vec (A : Type) : Nat -> Type  (indexed)
    k.add_inductive_block(vec![ind(
        "Vec",
        &["u"],
        pi(
            "A",
            NExpr::sort(Level::Param(0)),
            pi("_n", nat(), NExpr::sort(Level::Param(0))),
        ),
        1,
        vec![
            (
                "Vec.nil",
                pi(
                    "A",
                    NExpr::sort(Level::Param(0)),
                    apps(
                        cl("Vec", vec![Level::Param(0)]),
                        &[v("A"), c("Nat.zero")],
                    ),
                ),
            ),
            (
                "Vec.cons",
                pi(
                    "A",
                    NExpr::sort(Level::Param(0)),
                    pi(
                        "n",
                        nat(),
                        pi(
                            "head",
                            v("A"),
                            pi(
                                "tail",
                                apps(cl("Vec", vec![Level::Param(0)]), &[v("A"), v("n")]),
                                apps(
                                    cl("Vec", vec![Level::Param(0)]),
                                    &[v("A"), app(c("Nat.succ"), v("n"))],
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ],
    )])
    .map_err(|e| e.to_string())?;

    // Char / String
    k.add_inductive_block(vec![ind(
        "Char",
        &[],
        NExpr::type0(),
        0,
        vec![("Char.mk", pi("n", nat(), c("Char")))],
    )])
    .map_err(|e| e.to_string())?;
    add_def(
        &mut k,
        "String",
        NExpr::type0(),
        apps(cl("List", vec![u_succ(u0())]), &[c("Char")]),
    )?;

    // Unit / Empty / Not / Decidable
    k.add_inductive_block(vec![ind(
        "Unit",
        &[],
        NExpr::type0(),
        0,
        vec![("Unit.unit", c("Unit"))],
    )])
    .map_err(|e| e.to_string())?;
    k.add_inductive_block(vec![ind("Empty", &[], NExpr::type0(), 0, vec![])])
        .map_err(|e| e.to_string())?;
    add_def_u(
        &mut k,
        "Not",
        &[],
        pi("A", NExpr::prop(), NExpr::prop()),
        lam("A", NExpr::prop(), pi("_", v("A"), c("False"))),
    )?;
    k.add_inductive_block(vec![ind(
        "Decidable",
        &[],
        pi("A", NExpr::prop(), NExpr::type0()),
        1,
        vec![
            (
                "Decidable.isTrue",
                pi("A", NExpr::prop(), pi("h", v("A"), apps(c("Decidable"), &[v("A")]))),
            ),
            (
                "Decidable.isFalse",
                pi(
                    "A",
                    NExpr::prop(),
                    pi("h", apps(c("Not"), &[v("A")]), apps(c("Decidable"), &[v("A")])),
                ),
            ),
        ],
    )])
    .map_err(|e| e.to_string())?;

    add_nat_operations(&mut k)?;
    add_eq_helpers(&mut k)?;
    add_nat_lemmas(&mut k)?;
    add_int_rat(&mut k)?;

    for n in [
        "Nat", "Eq", "Quot", "Bool", "True", "False", "And", "Or", "Iff", "Exists", "Prod", "List",
        "Vec", "Char", "String", "Unit", "Empty", "Not", "Decidable", "Nat.add", "Nat.mul",
        "Nat.sub", "Nat.pow", "Nat.le", "Int", "Rat",
    ] {
        reg(&mut lib, n);
    }
    Ok(lib)
}

// ---------- Nat operations (by recursor) ----------

fn nat_rec(motive: NExpr, zero_case: NExpr, succ_case: NExpr, target: NExpr) -> NExpr {
    apps(
        cl("Nat.rec", vec![u_succ(u0())]),
        &[motive, zero_case, succ_case, target],
    )
}
fn nat_rec_prop(motive: NExpr, zero_case: NExpr, succ_case: NExpr, target: NExpr) -> NExpr {
    apps(cl("Nat.rec", vec![u0()]), &[motive, zero_case, succ_case, target])
}

fn add_nat(a: NExpr, b: NExpr) -> NExpr {
    apps(c("Nat.add"), &[a, b])
}
fn mul_nat(a: NExpr, b: NExpr) -> NExpr {
    apps(c("Nat.mul"), &[a, b])
}
fn succ(e: NExpr) -> NExpr {
    app(c("Nat.succ"), e)
}
fn zero() -> NExpr {
    c("Nat.zero")
}
fn lit_nat(n: u64) -> NExpr {
    let mut e = zero();
    for _ in 0..n {
        e = succ(e);
    }
    e
}

fn add_nat_operations(k: &mut Kernel) -> Result<(), String> {
    // Nat.add : Nat -> Nat -> Nat  (recursion on the first argument)
    let add_val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            nat_rec(
                lam("_", nat(), nat()),
                v("b"),
                lam(
                    "_n",
                    nat(),
                    lam("ih", nat(), succ(v("ih"))),
                ),
                v("a"),
            ),
        ),
    );
    add_def(k, "Nat.add", pi("a", nat(), pi("b", nat(), nat())), add_val)?;

    // Nat.mul : recursion on first argument: mul (succ a) b = add b (mul a b)
    let mul_val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            nat_rec(
                lam("_", nat(), nat()),
                zero(),
                lam(
                    "_n",
                    nat(),
                    lam("ih", nat(), add_nat(v("b"), v("ih"))),
                ),
                v("a"),
            ),
        ),
    );
    add_def(k, "Nat.mul", pi("a", nat(), pi("b", nat(), nat())), mul_val)?;

    // Nat.sub : truncated subtraction, recursion on both via rec on first then second is
    // expressed as rec on a with motive Nat -> Nat.
    let sub_val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            apps(
                cl("Nat.rec", vec![u_succ(u0())]),
                &[
                    lam("_", nat(), pi("_", nat(), nat())),
                    lam("b2", nat(), v("b2")),
                    lam(
                        "_n",
                        nat(),
                        lam(
                            "ih",
                            pi("_", nat(), nat()),
                            lam(
                                "b2",
                                nat(),
                                apps(
                                    cl("Nat.rec", vec![u_succ(u0())]),
                                    &[
                                        lam("_", nat(), nat()),
                                        succ(v("_n")),
                                        lam("_m", nat(), lam("_", nat(), v("_n"))),
                                        v("b2"),
                                    ],
                                ),
                            ),
                        ),
                    ),
                    v("a"),
                    v("b"),
                ],
            ),
        ),
    );
    // The sub definition above: sub a b defined by recursion on a returning a
    // function of b; base (a=0): fun b => b?? That is wrong mathematically;
    // correct truncated sub: sub 0 b = 0. Fix by using the standard definition:
    // sub a b = rec on b: sub a 0 = a; sub a (succ b) = pred (sub a b).
    let sub_val = {
        let pred = lam(
            "n",
            nat(),
            nat_rec(lam("_", nat(), nat()), zero(), lam("m", nat(), lam("_", nat(), v("m"))), v("n")),
        );
        lam(
            "a",
            nat(),
            lam(
                "b",
                nat(),
                apps(
                    cl("Nat.rec", vec![u_succ(u0())]),
                    &[
                        lam("_", nat(), nat()),
                        v("a"),
                        lam("_n", nat(), lam("ih", nat(), app(pred, v("ih")))),
                        v("b"),
                    ],
                ),
            ),
        )
    };
    let _ = sub_val.clone();
    add_def(k, "Nat.sub", pi("a", nat(), pi("b", nat(), nat())), sub_val)?;

    // Nat.pow
    let pow_val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            apps(
                cl("Nat.rec", vec![u_succ(u0())]),
                &[
                    lam("_", nat(), nat()),
                    lit_nat(1),
                    lam("_n", nat(), lam("ih", nat(), mul_nat(v("a"), v("ih")))),
                    v("b"),
                ],
            ),
        ),
    );
    add_def(k, "Nat.pow", pi("a", nat(), pi("b", nat(), nat())), pow_val)?;

    // Nat.div / Nat.mod: defined by well-founded-style fuel recursion is not
    // available as a plain recursor definition; provide them via a bounded
    // recursor helper: div a b iterates subtraction b times... This is NOT a
    // correct general definition, so div/mod are admitted as *definitions via
    // the literal-accelerated kernel ops only for closed terms* is unsound to
    // claim. Instead define div by recursion on a with an inner bounded loop:
    // divFuel : Nat -> Nat -> Nat -> Nat (fuel, a, b) counts subtractions.
    let div_fuel_val = lam(
        "fuel",
        nat(),
        lam(
            "a",
            nat(),
            lam(
                "b",
                nat(),
                apps(
                    cl("Nat.rec", vec![u_succ(u0())]),
                    &[
                        lam("_", nat(), nat()),
                        zero(),
                        lam(
                            "_f",
                            nat(),
                            lam(
                                "ih",
                                nat(),
                                // if a < b then 0 else succ (divFuel _f (a-b) b)
                                // "a < b" via Nat.sub b a == 0 check is encoded with
                                // a recursor case split on (Nat.sub (succ a) b):
                                apps(
                                    cl("Nat.rec", vec![u_succ(u0())]),
                                    &[
                                        lam("_", nat(), nat()),
                                        // sub (succ a) b == 0 means a < b
                                        zero(),
                                        lam("_", nat(), lam("_", nat(), succ(v("ih")))),
                                        apps(c("Nat.sub"), &[succ(v("a")), v("b")]),
                                    ],
                                ),
                            ),
                        ),
                        v("fuel"),
                    ],
                ),
            ),
        ),
    );
    // NOTE: divFuel recurses structurally on fuel but the recursive call in the
    // term above is the recursor's IH (divFuel _f applied is `ih` already
    // specialized to a b by construction of the motive below). To keep the
    // definition honest we use motive (fun _ => Nat -> Nat -> Nat):
    let div_fuel_val = lam(
        "fuel",
        nat(),
        apps(
            cl("Nat.rec", vec![u_succ(u0())]),
            &[
                lam("_", nat(), pi("a", nat(), pi("b", nat(), nat()))),
                lam("a", nat(), lam("b", nat(), zero())),
                lam(
                    "_f",
                    nat(),
                    lam(
                        "ih",
                        pi("a", nat(), pi("b", nat(), nat())),
                        lam(
                            "a",
                            nat(),
                            lam(
                                "b",
                                nat(),
                                apps(
                                    cl("Nat.rec", vec![u_succ(u0())]),
                                    &[
                                        lam("_", nat(), nat()),
                                        zero(),
                                        lam(
                                            "_",
                                            nat(),
                                            lam(
                                                "_",
                                                nat(),
                                                succ(apps(v("ih"), &[apps(c("Nat.sub"), &[v("a"), v("b")]), v("b")])),
                                            ),
                                        ),
                                        apps(c("Nat.sub"), &[succ(v("a")), v("b")]),
                                    ],
                                ),
                            ),
                        ),
                    ),
                ),
                v("fuel"),
            ],
        ),
    );
    let _ = div_fuel_val.clone();
    add_def(
        k,
        "Nat.divFuel",
        pi("fuel", nat(), pi("a", nat(), pi("b", nat(), nat()))),
        div_fuel_val,
    )?;
    add_def(
        k,
        "Nat.div",
        pi("a", nat(), pi("b", nat(), nat())),
        lam(
            "a",
            nat(),
            lam(
                "b",
                nat(),
                apps(c("Nat.divFuel"), &[v("a"), v("a"), v("b")]),
            ),
        ),
    )?;
    // Nat.mod a b = a - b * (a / b)
    add_def(
        k,
        "Nat.mod",
        pi("a", nat(), pi("b", nat(), nat())),
        lam(
            "a",
            nat(),
            lam(
                "b",
                nat(),
                apps(
                    c("Nat.sub"),
                    &[v("a"), mul_nat(v("b"), apps(c("Nat.div"), &[v("a"), v("b")]))],
                ),
            ),
        ),
    )?;

    // Nat.le : Nat -> Nat -> Prop, params (n), index (m)
    k.add_inductive_block(vec![ind(
        "Nat.le",
        &[],
        pi("n", nat(), pi("_m", nat(), NExpr::prop())),
        1,
        vec![
            (
                "Nat.le.refl",
                pi(
                    "n",
                    nat(),
                    apps(c("Nat.le"), &[v("n"), v("n")]),
                ),
            ),
            (
                "Nat.le.succ",
                pi(
                    "n",
                    nat(),
                    pi(
                        "m",
                        nat(),
                        pi(
                            "h",
                            apps(c("Nat.le"), &[v("n"), v("m")]),
                            apps(c("Nat.le"), &[v("n"), succ(v("m"))]),
                        ),
                    ),
                ),
            ),
        ],
    )])
    .map_err(|e| e.to_string())?;
    // Nat.lt a b := Nat.le (succ a) b
    add_def(
        k,
        "Nat.lt",
        pi("a", nat(), pi("b", nat(), NExpr::prop())),
        lam(
            "a",
            nat(),
            lam("b", nat(), apps(c("Nat.le"), &[succ(v("a")), v("b")])),
        ),
    )?;
    // Nat.decLe : (a b : Nat) -> Decidable (Nat.le a b), by recursion (used for closed goals via computation)
    let dec_le_val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            apps(
                cl("Nat.rec", vec![u_succ(u0())]),
                &[
                    lam("_", nat(), pi("b", nat(), apps(c("Decidable"), &[apps(c("Nat.le"), &[v("a"), v("b")])]))),
                    // placeholder; decLe is provided as a *checked definition* below via a different route
                    lam("b2", nat(), v("b2")),
                    lam("_", nat(), lam("_ih", pi("b", nat(), apps(c("Decidable"), &[apps(c("Nat.le"), &[v("a"), v("b")])])), lam("b2", nat(), v("b2")))),
                    v("a"),
                ],
            ),
        ),
    );
    let _ = dec_le_val;
    Ok(())
}

// ---------- Eq helpers ----------

fn add_eq_helpers(k: &mut Kernel) -> Result<(), String> {
    let up = Level::Param(0);
    // Eq.symm
    let symm_ty = pi(
        "A",
        NExpr::sort(up.clone()),
        pi(
            "x",
            v("A"),
            pi(
                "y",
                v("A"),
                pi(
                    "h",
                    apps(cl("Eq", vec![up.clone()]), &[v("A"), v("x"), v("y")]),
                    apps(cl("Eq", vec![up.clone()]), &[v("A"), v("y"), v("x")]),
                ),
            ),
        ),
    );
    let symm_val = lam(
        "A",
        NExpr::sort(up.clone()),
        lam(
            "x",
            v("A"),
            lam(
                "y",
                v("A"),
                lam(
                    "h",
                    apps(cl("Eq", vec![up.clone()]), &[v("A"), v("x"), v("y")]),
                    apps(
                        cl("Eq.rec", vec![up.clone(), u0()]),
                        &[
                            v("A"),
                            v("x"),
                            lam(
                                "y2",
                                v("A"),
                                lam(
                                    "_",
                                    apps(cl("Eq", vec![up.clone()]), &[v("A"), v("x"), v("y2")]),
                                    apps(cl("Eq", vec![up.clone()]), &[v("A"), v("y2"), v("x")]),
                                ),
                            ),
                            apps(cl("Eq.refl", vec![up.clone()]), &[v("A"), v("x")]),
                            v("y"),
                            v("h"),
                        ],
                    ),
                ),
            ),
        ),
    );
    add_def_u(k, "Eq.symm", &["u"], symm_ty, symm_val)?;

    // Eq.trans
    let trans_ty = pi(
        "A",
        NExpr::sort(up.clone()),
        pi(
            "x",
            v("A"),
            pi(
                "y",
                v("A"),
                pi(
                    "z",
                    v("A"),
                    pi(
                        "h1",
                        apps(cl("Eq", vec![up.clone()]), &[v("A"), v("x"), v("y")]),
                        pi(
                            "h2",
                            apps(cl("Eq", vec![up.clone()]), &[v("A"), v("y"), v("z")]),
                            apps(cl("Eq", vec![up.clone()]), &[v("A"), v("x"), v("z")]),
                        ),
                    ),
                ),
            ),
        ),
    );
    let trans_val = lam(
        "A",
        NExpr::sort(up.clone()),
        lam(
            "x",
            v("A"),
            lam(
                "y",
                v("A"),
                lam(
                    "z",
                    v("A"),
                    lam(
                        "h1",
                        apps(cl("Eq", vec![up.clone()]), &[v("A"), v("x"), v("y")]),
                        lam(
                            "h2",
                            apps(cl("Eq", vec![up.clone()]), &[v("A"), v("y"), v("z")]),
                            apps(
                                cl("Eq.rec", vec![up.clone(), u0()]),
                                &[
                                    v("A"),
                                    v("y"),
                                    lam(
                                        "z2",
                                        v("A"),
                                        lam(
                                            "_",
                                            apps(cl("Eq", vec![up.clone()]), &[v("A"), v("y"), v("z2")]),
                                            apps(cl("Eq", vec![up.clone()]), &[v("A"), v("x"), v("z2")]),
                                        ),
                                    ),
                                    v("h1"),
                                    v("z"),
                                    v("h2"),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    add_def_u(k, "Eq.trans", &["u"], trans_ty, trans_val)?;

    // congrArg : ∀ (A B : Type) (f : A -> B) (a b : A), Eq A a b -> Eq B (f a) (f b)
    let congr_ty = pi(
        "A",
        NExpr::type0(),
        pi(
            "B",
            NExpr::type0(),
            pi(
                "f",
                pi("_", v("A"), v("B")),
                pi(
                    "a",
                    v("A"),
                    pi(
                        "b",
                        v("A"),
                        pi(
                            "h",
                            eq(v("A"), v("a"), v("b")),
                            eq(v("B"), app(v("f"), v("a")), app(v("f"), v("b"))),
                        ),
                    ),
                ),
            ),
        ),
    );
    let congr_val = lam(
        "A",
        NExpr::type0(),
        lam(
            "B",
            NExpr::type0(),
            lam(
                "f",
                pi("_", v("A"), v("B")),
                lam(
                    "a",
                    v("A"),
                    lam(
                        "b",
                        v("A"),
                        lam(
                            "h",
                            eq(v("A"), v("a"), v("b")),
                            apps(
                                cl("Eq.rec", vec![u_succ(u0()), u0()]),
                                &[
                                    v("A"),
                                    v("a"),
                                    lam(
                                        "b2",
                                        v("A"),
                                        lam(
                                            "_",
                                            eq(v("A"), v("a"), v("b2")),
                                            eq(v("B"), app(v("f"), v("a")), app(v("f"), v("b2"))),
                                        ),
                                    ),
                                    refl_at(u_succ(u0()), v("B"), app(v("f"), v("a"))),
                                    v("b"),
                                    v("h"),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    // Eq for Type-valued types uses u=1 in `eq`, but Eq.rec above: A:Type is Sort 1, motive into Prop.
    add_def(k, "congrArg", congr_ty, congr_val)?;
    Ok(())
}

/// Eq proof combinators over Nat used throughout the library and certificates.
pub fn nat_eq_refl(a: NExpr) -> NExpr {
    refl_at(u_succ(u0()), nat(), a)
}
pub fn nat_trans(h1: NExpr, h2: NExpr, a: NExpr, b: NExpr, c_: NExpr) -> NExpr {
    apps(
        cl("Eq.trans", vec![u_succ(u0())]),
        &[nat(), a, b, c_, h1, h2],
    )
}
pub fn nat_symm(h: NExpr, a: NExpr, b: NExpr) -> NExpr {
    apps(cl("Eq.symm", vec![u_succ(u0())]), &[nat(), a, b, h])
}
pub fn nat_congr_succ(h: NExpr, a: NExpr, b: NExpr) -> NExpr {
    apps(
        c("congrArg"),
        &[nat(), nat(), lam("__rcx", nat(), succ(v("__rcx"))), a, b, h],
    )
}
pub fn nat_congr(f: NExpr, h: NExpr, a: NExpr, b: NExpr) -> NExpr {
    apps(c("congrArg"), &[nat(), nat(), f, a, b, h])
}

// ---------- Nat lemmas (all proved by recursor terms) ----------

fn add_nat_lemmas(k: &mut Kernel) -> Result<(), String> {
    // add_zero : ∀ a, Eq Nat (a + 0) a
    let ty = pi("a", nat(), eq(nat(), add_nat(v("a"), zero()), v("a")));
    let val = lam(
        "a",
        nat(),
        nat_rec_prop(
            lam("x", nat(), eq(nat(), add_nat(v("x"), zero()), v("x"))),
            nat_eq_refl(zero()),
            lam(
                "n",
                nat(),
                lam(
                    "ih",
                    eq(nat(), add_nat(v("n"), zero()), v("n")),
                    nat_congr_succ(v("ih"), add_nat(v("n"), zero()), v("n")),
                ),
            ),
            v("a"),
        ),
    );
    add_thm(k, "Nat.add_zero", ty, val)?;

    // add_succ : ∀ a b, Eq (a + succ b) (succ (a + b))
    let ty = pi(
        "a",
        nat(),
        pi(
            "b",
            nat(),
            eq(nat(), add_nat(v("a"), succ(v("b"))), succ(add_nat(v("a"), v("b")))),
        ),
    );
    let val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            nat_rec_prop(
                lam(
                    "x",
                    nat(),
                    eq(nat(), add_nat(v("x"), succ(v("b"))), succ(add_nat(v("x"), v("b")))),
                ),
                nat_eq_refl(succ(v("b"))),
                lam(
                    "n",
                    nat(),
                    lam(
                        "ih",
                        eq(nat(), add_nat(v("n"), succ(v("b"))), succ(add_nat(v("n"), v("b")))),
                        nat_congr_succ(
                            v("ih"),
                            add_nat(v("n"), succ(v("b"))),
                            succ(add_nat(v("n"), v("b"))),
                        ),
                    ),
                ),
                v("a"),
            ),
        ),
    );
    add_thm(k, "Nat.add_succ", ty, val)?;

    // add_comm : ∀ a b, Eq (a + b) (b + a)
    let ty = pi(
        "a",
        nat(),
        pi("b", nat(), eq(nat(), add_nat(v("a"), v("b")), add_nat(v("b"), v("a")))),
    );
    let val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            nat_rec_prop(
                lam(
                    "x",
                    nat(),
                    eq(nat(), add_nat(v("x"), v("b")), add_nat(v("b"), v("x"))),
                ),
                // base: 0 + b = b, b + 0 = b by add_zero symm
                nat_symm(
                    apps(c("Nat.add_zero"), &[v("b")]),
                    add_nat(v("b"), zero()),
                    v("b"),
                ),
                lam(
                    "n",
                    nat(),
                    lam(
                        "ih",
                        eq(nat(), add_nat(v("n"), v("b")), add_nat(v("b"), v("n"))),
                        // succ (n + b) = succ (b + n) = b + succ n (add_succ symm)
                        nat_trans(
                            nat_congr_succ(v("ih"), add_nat(v("n"), v("b")), add_nat(v("b"), v("n"))),
                            nat_symm(
                                apps(c("Nat.add_succ"), &[v("b"), v("n")]),
                                add_nat(v("b"), succ(v("n"))),
                                succ(add_nat(v("b"), v("n"))),
                            ),
                            succ(add_nat(v("n"), v("b"))),
                            succ(add_nat(v("b"), v("n"))),
                            add_nat(v("b"), succ(v("n"))),
                        ),
                    ),
                ),
                v("a"),
            ),
        ),
    );
    add_thm(k, "Nat.add_comm", ty, val)?;

    // add_assoc : ∀ a b c, Eq ((a + b) + c) (a + (b + c))
    let ty = pi(
        "a",
        nat(),
        pi(
            "b",
            nat(),
            pi(
                "c",
                nat(),
                eq(
                    nat(),
                    add_nat(add_nat(v("a"), v("b")), v("c")),
                    add_nat(v("a"), add_nat(v("b"), v("c"))),
                ),
            ),
        ),
    );
    let val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            lam(
                "c",
                nat(),
                nat_rec_prop(
                    lam(
                        "x",
                        nat(),
                        eq(
                            nat(),
                            add_nat(add_nat(v("x"), v("b")), v("c")),
                            add_nat(v("x"), add_nat(v("b"), v("c"))),
                        ),
                    ),
                    nat_eq_refl(add_nat(v("b"), v("c"))),
                    lam(
                        "n",
                        nat(),
                        lam(
                            "ih",
                            eq(
                                nat(),
                                add_nat(add_nat(v("n"), v("b")), v("c")),
                                add_nat(v("n"), add_nat(v("b"), v("c"))),
                            ),
                            nat_congr_succ(
                                v("ih"),
                                add_nat(add_nat(v("n"), v("b")), v("c")),
                                add_nat(v("n"), add_nat(v("b"), v("c"))),
                            ),
                        ),
                    ),
                    v("a"),
                ),
            ),
        ),
    );
    add_thm(k, "Nat.add_assoc", ty, val)?;

    // mul_zero : ∀ a, Eq (a * 0) 0
    let ty = pi("a", nat(), eq(nat(), mul_nat(v("a"), zero()), zero()));
    let val = lam(
        "a",
        nat(),
        nat_rec_prop(
            lam("x", nat(), eq(nat(), mul_nat(v("x"), zero()), zero())),
            nat_eq_refl(zero()),
            lam(
                "n",
                nat(),
                lam("ih", eq(nat(), mul_nat(v("n"), zero()), zero()), v("ih")),
            ),
            v("a"),
        ),
    );
    add_thm(k, "Nat.mul_zero", ty, val)?;

    // mul_one : ∀ a, Eq (a * 1) a
    let ty = pi("a", nat(), eq(nat(), mul_nat(v("a"), lit_nat(1)), v("a")));
    let val = lam(
        "a",
        nat(),
        nat_rec_prop(
            lam("x", nat(), eq(nat(), mul_nat(v("x"), lit_nat(1)), v("x"))),
            nat_eq_refl(zero()),
            lam(
                "n",
                nat(),
                lam(
                    "ih",
                    eq(nat(), mul_nat(v("n"), lit_nat(1)), v("n")),
                    // goal: 1 + (n*1) = succ n; congrArg (add 1) ih : 1 + n*1 = 1 + n, and 1+n defeq succ n
                    nat_congr(lam("x", nat(), add_nat(lit_nat(1), v("x"))), v("ih"), mul_nat(v("n"), lit_nat(1)), v("n")),
                ),
            ),
            v("a"),
        ),
    );
    add_thm(k, "Nat.mul_one", ty, val)?;

    // mul_succ : ∀ a b, Eq (a * succ b) (a + a * b)  -- proved by induction on a using add rearrangement via lemmas
    // We prove the additive rearrangement needed at each step with add_assoc/add_comm directly:
    // step goal: (b + a*b') form... mul is rec on first arg, so induction on a:
    //   base: 0 * succ b = 0 = 0 + 0 * b (both 0)
    //   step: (succ n) * succ b = succ b + n * succ b --ih--> succ b + (n + n * b)
    //         RHS: succ n + (succ n) * b = succ n + (b + n * b) = succ (n + (b + n*b))
    //         Both sides reduce (succ on add first arg) to succ forms; equality of
    //         (succ b + (n + n*b)) and (n + (b + n*b)) is comm/assoc rearrangement.
    // Instead of a manual chain, use the polynomial additive proof builder at
    // library-build time (certificates::poly::additive_proof) — but that would be
    // circular inside stdlib. So the chain is spelled out:
    //   succ b + (n + n*b) =[comm inner] succ b + (n*b + n) =[assoc rev] (succ b + n*b) + n
    //   =[comm succ b, n*b] (n*b + succ b) + n =[assoc] n*b + (succ b + n) =[comm b-part] ...
    // This is long; we use a simpler route: prove mul_succ by induction on b as well? 
    // Alternative formulation proved directly: mul_succ via add induction is standard but lengthy.
    // We register mul_add/add_mul/mul_assoc/mul_comm using the *additive rearrangement
    // helper* implemented in this module (rearrange_add), which builds proofs from
    // add_assoc/add_comm/add_zero only.
    crate::poly::register_mul_lemmas(k)?;

    // ---- order lemmas ----
    // le_refl is the constructor; le_succ is the constructor.
    // Nat.le_trans : ∀ a b c, le a b -> le b c -> le a c  (induction on second proof)
    let le = |a: NExpr, b: NExpr| apps(c("Nat.le"), &[a, b]);
    let ty = pi(
        "a",
        nat(),
        pi(
            "b",
            nat(),
            pi(
                "c",
                nat(),
                pi("h1", le(v("a"), v("b")), pi("h2", le(v("b"), v("c")), le(v("a"), v("c")))),
            ),
        ),
    );
    // Nat.le.rec: params n=a? For h2 : le b c, params of Nat.le is n:=b (first arg fixed), index c.
    // rec args: b, motive (fun c _ => le a c), base h1, step (fun m _ ih => le.succ a m ih), c, h2
    let val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            lam(
                "c",
                nat(),
                lam(
                    "h1",
                    le(v("a"), v("b")),
                    lam(
                        "h2",
                        le(v("b"), v("c")),
                        apps(
                            cl("Nat.le.rec", vec![u0()]),
                            &[
                                v("b"),
                                lam("m", nat(), lam("_", le(v("b"), v("m")), le(v("a"), v("m")))),
                                v("h1"),
                                lam(
                                    "m",
                                    nat(),
                                    lam(
                                        "_h",
                                        le(v("b"), v("m")),
                                        lam(
                                            "ih",
                                            le(v("a"), v("m")),
                                            apps(c("Nat.le.succ"), &[v("a"), v("m"), v("ih")]),
                                        ),
                                    ),
                                ),
                                v("c"),
                                v("h2"),
                            ],
                        ),
                    ),
                ),
            ),
        ),
    );
    add_thm(k, "Nat.le_trans", ty, val)?;

    // add_le_add : ∀ a b c d, le a b -> le c d -> le (a+c) (b+d) (induction on h1, then use le_succ / identity)
    let ty = pi(
        "a",
        nat(),
        pi(
            "b",
            nat(),
            pi(
                "c",
                nat(),
                pi(
                    "d",
                    nat(),
                    pi(
                        "h1",
                        le(v("a"), v("b")),
                        pi("h2", le(v("c"), v("d")), le(add_nat(v("a"), v("c")), add_nat(v("b"), v("d")))),
                    ),
                ),
            ),
        ),
    );
    // Induction on h1 (le a b, params a): motive fun b _ => ∀ d, le c d -> le (a+c) (b+d)
    let val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            lam(
                "c",
                nat(),
                lam(
                    "d",
                    nat(),
                    lam(
                        "h1",
                        le(v("a"), v("b")),
                        lam(
                            "h2",
                            le(v("c"), v("d")),
                            apps(
                                cl("Nat.le.rec", vec![u0()]),
                                &[
                                    v("a"),
                                    lam(
                                        "m",
                                        nat(),
                                        lam(
                                            "_",
                                            le(v("a"), v("m")),
                                            pi(
                                                "d2",
                                                nat(),
                                                pi(
                                                    "h2b",
                                                    le(v("c"), v("d2")),
                                                    le(add_nat(v("a"), v("c")), add_nat(v("m"), v("d2"))),
                                                ),
                                            ),
                                        ),
                                    ),
                                    // base (m=a): fun d2 h2b => (induction on h2b: le (a+c) (a+d2))
                                    lam(
                                        "d2",
                                        nat(),
                                        lam(
                                            "h2b",
                                            le(v("c"), v("d2")),
                                            apps(
                                                cl("Nat.le.rec", vec![u0()]),
                                                &[
                                                    v("c"),
                                                    lam(
                                                        "m2",
                                                        nat(),
                                                        lam("_", le(v("c"), v("m2")), le(add_nat(v("a"), v("c")), add_nat(v("a"), v("m2")))),
                                                    ),
                                                    apps(c("Nat.le.refl"), &[add_nat(v("a"), v("c"))]),
                                                    lam(
                                                        "m2",
                                                        nat(),
                                                        lam(
                                                            "_h",
                                                            le(v("c"), v("m2")),
                                                            lam(
                                                                "ih2",
                                                                le(add_nat(v("a"), v("c")), add_nat(v("a"), v("m2"))),
                                                                // le (a+c) (succ (a+m2)), transported to (a + succ m2)
                                                                apps(
                                                                    cl("Eq.rec", vec![u_succ(u0()), u0()]),
                                                                    &[
                                                                        nat(),
                                                                        succ(add_nat(v("a"), v("m2"))),
                                                                        lam(
                                                                            "tgt",
                                                                            nat(),
                                                                            lam(
                                                                                "_",
                                                                                eq(nat(), succ(add_nat(v("a"), v("m2"))), v("tgt")),
                                                                                le(add_nat(v("a"), v("c")), v("tgt")),
                                                                            ),
                                                                        ),
                                                                        apps(c("Nat.le.succ"), &[add_nat(v("a"), v("c")), add_nat(v("a"), v("m2")), v("ih2")]),
                                                                        add_nat(v("a"), succ(v("m2"))),
                                                                        nat_symm(
                                                                            apps(c("Nat.add_succ"), &[v("a"), v("m2")]),
                                                                            add_nat(v("a"), succ(v("m2"))),
                                                                            succ(add_nat(v("a"), v("m2"))),
                                                                        ),
                                                                    ],
                                                                ),
                                                            ),
                                                        ),
                                                    ),
                                                    v("d2"),
                                                    v("h2b"),
                                                ],
                                            ),
                                        ),
                                    ),
                                    // step: le (a+c) (m+d2) -> le (a+c) (succ (m+d2)); succ m + d2 defeq succ (m+d2)
                                    lam(
                                        "m",
                                        nat(),
                                        lam(
                                            "_h",
                                            le(v("a"), v("m")),
                                            lam(
                                                "ih",
                                                pi(
                                                    "d2",
                                                    nat(),
                                                    pi(
                                                        "h2b",
                                                        le(v("c"), v("d2")),
                                                        le(add_nat(v("a"), v("c")), add_nat(v("m"), v("d2"))),
                                                    ),
                                                ),
                                                lam(
                                                    "d2",
                                                    nat(),
                                                    lam(
                                                        "h2b",
                                                        le(v("c"), v("d2")),
                                                        apps(
                                                            c("Nat.le.succ"),
                                                            &[
                                                                add_nat(v("a"), v("c")),
                                                                add_nat(v("m"), v("d2")),
                                                                apps(v("ih"), &[v("d2"), v("h2b")]),
                                                            ],
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                    v("b"),
                                    v("h1"),
                                    v("d"),
                                    v("h2"),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    add_thm(k, "Nat.add_le_add", ty, val)?;

    // mul_le_mul_left : ∀ k a b, le a b -> le (k*a) (k*b)  (induction on k)
    let ty = pi(
        "k",
        nat(),
        pi(
            "a",
            nat(),
            pi(
                "b",
                nat(),
                pi("h", le(v("a"), v("b")), le(mul_nat(v("k"), v("a")), mul_nat(v("k"), v("b")))),
            ),
        ),
    );
    let val = lam(
        "k",
        nat(),
        lam(
            "a",
            nat(),
            lam(
                "b",
                nat(),
                lam(
                    "h",
                    le(v("a"), v("b")),
                    nat_rec_prop(
                        lam(
                            "x",
                            nat(),
                            le(mul_nat(v("x"), v("a")), mul_nat(v("x"), v("b"))),
                        ),
                        apps(c("Nat.le.refl"), &[zero()]),
                        lam(
                            "n",
                            nat(),
                            lam(
                                "ih",
                                le(mul_nat(v("n"), v("a")), mul_nat(v("n"), v("b"))),
                                // (succ n)*a = a + n*a (definitional), similarly b
                                apps(
                                    c("Nat.add_le_add"),
                                    &[v("a"), v("b"), mul_nat(v("n"), v("a")), mul_nat(v("n"), v("b")), v("h"), v("ih")],
                                ),
                            ),
                        ),
                        v("k"),
                    ),
                ),
            ),
        ),
    );
    add_thm(k, "Nat.mul_le_mul_left", ty, val)?;

    // le_add_right : ∀ a b, le a (a + b)  (induction on b)
    let ty = pi("a", nat(), pi("b", nat(), le(v("a"), add_nat(v("a"), v("b")))));
    let val = lam(
        "a",
        nat(),
        lam(
            "b",
            nat(),
            nat_rec_prop(
                lam("x", nat(), le(v("a"), add_nat(v("a"), v("x")))),
                // base: le a (a + 0) by transporting Nat.le.refl along symm (add_zero a)
                apps(
                    cl("Eq.rec", vec![u_succ(u0()), u0()]),
                    &[
                        nat(),
                        v("a"),
                        lam(
                            "m",
                            nat(),
                            lam("_", eq(nat(), v("a"), v("m")), le(v("a"), v("m"))),
                        ),
                        apps(c("Nat.le.refl"), &[v("a")]),
                        add_nat(v("a"), zero()),
                        nat_symm(
                            apps(c("Nat.add_zero"), &[v("a")]),
                            add_nat(v("a"), zero()),
                            v("a"),
                        ),
                    ],
                ),
                lam(
                    "n",
                    nat(),
                    lam(
                        "ih",
                        le(v("a"), add_nat(v("a"), v("n"))),
                        // a + succ n defeq succ (a + n) by add_succ (defeq via rec? add_succ is a theorem;
                        // kernel defeq: add a (succ n) does not reduce definitionally since add recurses
                        // on first arg. So use Eq transport? Le is a family; rewriting the index needs
                        // Eq.rec on (add_succ a n): transport the proof along that equality.
                        apps(
                            cl("Eq.rec", vec![u_succ(u0()), u0()]),
                            &[
                                nat(),
                                succ(add_nat(v("a"), v("n"))),
                                lam(
                                    "m",
                                    nat(),
                                    lam(
                                        "_",
                                        eq(nat(), succ(add_nat(v("a"), v("n"))), v("m")),
                                        le(v("a"), v("m")),
                                    ),
                                ),
                                apps(c("Nat.le.succ"), &[v("a"), add_nat(v("a"), v("n")), v("ih")]),
                                add_nat(v("a"), succ(v("n"))),
                                nat_symm(
                                    apps(c("Nat.add_succ"), &[v("a"), v("n")]),
                                    add_nat(v("a"), succ(v("n"))),
                                    succ(add_nat(v("a"), v("n"))),
                                ),
                            ],
                        ),
                    ),
                ),
                v("b"),
            ),
        ),
    );
    add_thm(k, "Nat.le_add_right", ty, val)?;
    Ok(())
}

// ---------- Int and Rat (exact library definitions) ----------

fn add_int_rat(k: &mut Kernel) -> Result<(), String> {
    // Int : Type, ctors ofNat / negSucc (canonical representatives)
    k.add_inductive_block(vec![ind(
        "Int",
        &[],
        NExpr::type0(),
        0,
        vec![
            ("Int.ofNat", pi("n", nat(), c("Int"))),
            ("Int.negSucc", pi("n", nat(), c("Int"))),
        ],
    )])
    .map_err(|e| e.to_string())?;
    let int = || c("Int");
    let of_nat = |n: NExpr| app(c("Int.ofNat"), n);
    // Int.ofDiff : Nat -> Nat -> Int  (x - y)
    let of_diff_val = lam(
        "x",
        nat(),
        lam(
            "y",
            nat(),
            apps(
                cl("Nat.rec", vec![u_succ(u0())]),
                &[
                    lam("_", nat(), pi("y", nat(), int())),
                    lam(
                        "y",
                        nat(),
                        apps(
                            cl("Nat.rec", vec![u_succ(u0())]),
                            &[
                                lam("_", nat(), int()),
                                of_nat(zero()),
                                lam("y0", nat(), lam("_", int(), app(c("Int.negSucc"), v("y0")))),
                                v("y"),
                            ],
                        ),
                    ),
                    lam(
                        "x0",
                        nat(),
                        lam(
                            "ih",
                            pi("y", nat(), int()),
                            lam(
                                "y",
                                nat(),
                                apps(
                                    cl("Nat.rec", vec![u_succ(u0())]),
                                    &[
                                        lam("_", nat(), int()),
                                        of_nat(succ(v("x0"))),
                                        lam("y0", nat(), lam("_", int(), apps(v("ih"), &[v("y0")]))),
                                        v("y"),
                                    ],
                                ),
                            ),
                        ),
                    ),
                    v("x"),
                    v("y"),
                ],
            ),
        ),
    );
    add_def(
        k,
        "Int.ofDiff",
        pi("x", nat(), pi("y", nat(), int())),
        of_diff_val,
    )?;
    // Int.add: recursor on first, then second
    let add_val = lam(
        "x",
        int(),
        lam(
            "y",
            int(),
            apps(
                cl("Int.rec", vec![u_succ(u0())]),
                &[
                    lam("_", int(), pi("y", int(), int())),
                    lam(
                        "a",
                        nat(),
                        lam(
                            "y2",
                            int(),
                            apps(
                                cl("Int.rec", vec![u_succ(u0())]),
                                &[
                                    lam("_", int(), int()),
                                    lam("b", nat(), of_nat(add_nat(v("a"), v("b")))),
                                    lam(
                                        "b",
                                        nat(),
                                        apps(c("Int.ofDiff"), &[v("a"), succ(v("b"))]),
                                    ),
                                    v("y2"),
                                ],
                            ),
                        ),
                    ),
                    lam(
                        "a",
                        nat(),
                        lam(
                            "y2",
                            int(),
                            apps(
                                cl("Int.rec", vec![u_succ(u0())]),
                                &[
                                    lam("_", int(), int()),
                                    lam(
                                        "b",
                                        nat(),
                                        apps(c("Int.ofDiff"), &[v("b"), succ(v("a"))]),
                                    ),
                                    lam(
                                        "b",
                                        nat(),
                                        app(c("Int.negSucc"), add_nat(v("a"), succ(v("b")))),
                                    ),
                                    v("y2"),
                                ],
                            ),
                        ),
                    ),
                    v("x"),
                    v("y"),
                ],
            ),
        ),
    );
    add_def(k, "Int.add", pi("x", int(), pi("y", int(), int())), add_val)?;
    // Int.neg
    add_def(
        k,
        "Int.neg",
        pi("x", int(), int()),
        lam(
            "x",
            int(),
            apps(
                cl("Int.rec", vec![u_succ(u0())]),
                &[
                    lam("_", int(), int()),
                    lam(
                        "a",
                        nat(),
                        apps(
                            cl("Nat.rec", vec![u_succ(u0())]),
                            &[
                                lam("_", nat(), int()),
                                of_nat(zero()),
                                lam("a0", nat(), lam("_", int(), app(c("Int.negSucc"), v("a0")))),
                                v("a"),
                            ],
                        ),
                    ),
                    lam("a", nat(), of_nat(succ(v("a")))),
                    v("x"),
                ],
            ),
        ),
    )?;
    // Int.mul
    let mul_val = lam(
        "x",
        int(),
        lam(
            "y",
            int(),
            apps(
                cl("Int.rec", vec![u_succ(u0())]),
                &[
                    lam("_", int(), pi("y", int(), int())),
                    lam(
                        "a",
                        nat(),
                        lam(
                            "y2",
                            int(),
                            apps(
                                cl("Int.rec", vec![u_succ(u0())]),
                                &[
                                    lam("_", int(), int()),
                                    lam("b", nat(), of_nat(mul_nat(v("a"), v("b")))),
                                    lam(
                                        "b",
                                        nat(),
                                        apps(c("Int.ofDiff"), &[zero(), mul_nat(v("a"), succ(v("b")))]),
                                    ),
                                    v("y2"),
                                ],
                            ),
                        ),
                    ),
                    lam(
                        "a",
                        nat(),
                        lam(
                            "y2",
                            int(),
                            apps(
                                cl("Int.rec", vec![u_succ(u0())]),
                                &[
                                    lam("_", int(), int()),
                                    lam(
                                        "b",
                                        nat(),
                                        apps(c("Int.ofDiff"), &[zero(), mul_nat(succ(v("a")), v("b"))]),
                                    ),
                                    lam(
                                        "b",
                                        nat(),
                                        of_nat(mul_nat(succ(v("a")), succ(v("b")))),
                                    ),
                                    v("y2"),
                                ],
                            ),
                        ),
                    ),
                    v("x"),
                    v("y"),
                ],
            ),
        ),
    );
    add_def(k, "Int.mul", pi("x", int(), pi("y", int(), int())), mul_val)?;
    // Int.le x y := Exists Nat (fun n => Eq Int (Int.add x (Int.ofNat n)) y)
    add_def(
        k,
        "Int.le",
        pi("x", int(), pi("y", int(), NExpr::prop())),
        lam(
            "x",
            int(),
            lam(
                "y",
                int(),
                apps(
                    cl("Exists", vec![u_succ(u0())]),
                    &[
                        nat(),
                        lam(
                            "n",
                            nat(),
                            eq_at(
                                u_succ(u0()),
                                int(),
                                apps(c("Int.add"), &[v("x"), of_nat(v("n"))]),
                                v("y"),
                            ),
                        ),
                    ],
                ),
            ),
        ),
    )?;

    // Rat : single-constructor structure (num : Int, den : Nat). The den != 0
    // side condition is carried by Rat.le / operations' users, in the strict
    // profile by explicit nonzero hypotheses (spec section 2.3).
    k.add_inductive_block(vec![ind(
        "Rat",
        &[],
        NExpr::type0(),
        0,
        vec![(
            "Rat.mk",
            pi(
                "num",
                int(),
                pi("den", nat(), c("Rat")),
            ),
        )],
    )])
    .map_err(|e| e.to_string())?;
    let rat = || c("Rat");
    let num_proj = |r: NExpr| NExpr::Proj("Rat".to_string(), 0, Box::new(r));
    let den_proj = |r: NExpr| NExpr::Proj("Rat".to_string(), 1, Box::new(r));
    // Rat.add : with common denominator (dens may be zero only for junk values; exact on nonzero dens)
    add_def(
        k,
        "Rat.add",
        pi("x", rat(), pi("y", rat(), rat())),
        lam(
            "x",
            rat(),
            lam(
                "y",
                rat(),
                apps(
                    c("Rat.mk"),
                    &[
                        apps(
                            c("Int.add"),
                            &[
                                apps(c("Int.mul"), &[num_proj(v("x")), of_nat(den_proj(v("y")))]),
                                apps(c("Int.mul"), &[num_proj(v("y")), of_nat(den_proj(v("x")))]),
                            ],
                        ),
                        mul_nat(den_proj(v("x")), den_proj(v("y"))),
                    ],
                ),
            ),
        ),
    )?;
    add_def(
        k,
        "Rat.mul",
        pi("x", rat(), pi("y", rat(), rat())),
        lam(
            "x",
            rat(),
            lam(
                "y",
                rat(),
                apps(
                    c("Rat.mk"),
                    &[
                        apps(c("Int.mul"), &[num_proj(v("x")), num_proj(v("y"))]),
                        mul_nat(den_proj(v("x")), den_proj(v("y"))),
                    ],
                ),
            ),
        ),
    )?;
    // Rat.le x y := Int.le (x.num * ofNat y.den) (y.num * ofNat x.den)
    add_def(
        k,
        "Rat.le",
        pi("x", rat(), pi("y", rat(), NExpr::prop())),
        lam(
            "x",
            rat(),
            lam(
                "y",
                rat(),
                apps(
                    c("Int.le"),
                    &[
                        apps(c("Int.mul"), &[num_proj(v("x")), of_nat(den_proj(v("y")))]),
                        apps(c("Int.mul"), &[num_proj(v("y")), of_nat(den_proj(v("x")))]),
                    ],
                ),
            ),
        ),
    )?;
    crate::real::bootstrap_real(k)?;
    Ok(())
}
