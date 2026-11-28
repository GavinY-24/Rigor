//! Initial constructive real/complex analysis foundation.
//!
//! `Real` is a bundled Cauchy sequence of rationals. Equality of reals is the
//! standard eventual-closeness relation (`Real.eq`), not raw equality of the
//! chosen Cauchy representatives. This is intentionally small and fully
//! kernel-checked; it is the substrate later ring, order, and completeness
//! developments build on, not an axiomatization.

use rigor_kernel::*;
use rigor_spec::BigUint;

fn v(s: &str) -> NExpr {
    NExpr::var(s)
}
fn c(s: &str) -> NExpr {
    NExpr::const_(s)
}
fn cl(s: &str, levels: Vec<Level>) -> NExpr {
    NExpr::const_levels(s, levels)
}
fn app(f: NExpr, a: NExpr) -> NExpr {
    NExpr::app(f, a)
}
fn apps(f: NExpr, args: &[NExpr]) -> NExpr {
    NExpr::apps(f, args)
}
fn pi(name: &str, dom: NExpr, cod: NExpr) -> NExpr {
    NExpr::pi(name, dom, cod)
}
fn lam(name: &str, dom: NExpr, body: NExpr) -> NExpr {
    NExpr::lam(name, dom, body)
}
fn lit(n: u64) -> NExpr {
    NExpr::LitNat(BigUint::from_u64(n))
}
fn type1() -> Level {
    Level::Succ(Box::new(Level::Zero))
}
fn nat() -> NExpr {
    c("Nat")
}
fn int() -> NExpr {
    c("Int")
}
fn rat() -> NExpr {
    c("Rat")
}
fn int_of_nat(n: NExpr) -> NExpr {
    app(c("Int.ofNat"), n)
}
fn rat_seq_ty() -> NExpr {
    pi("_", nat(), rat())
}
fn num(r: NExpr) -> NExpr {
    NExpr::Proj("Rat".to_string(), 0, Box::new(r))
}
fn den(r: NExpr) -> NExpr {
    NExpr::Proj("Rat".to_string(), 1, Box::new(r))
}
fn rat_mk(n: NExpr, d: NExpr) -> NExpr {
    apps(c("Rat.mk"), &[n, d])
}
fn rat_zero() -> NExpr {
    c("Rat.zero")
}
fn rat_add(x: NExpr, y: NExpr) -> NExpr {
    apps(c("Rat.add"), &[x, y])
}
fn rat_neg(x: NExpr) -> NExpr {
    app(c("Rat.neg"), x)
}
fn rat_sub(x: NExpr, y: NExpr) -> NExpr {
    apps(c("Rat.sub"), &[x, y])
}
fn rat_abs(x: NExpr) -> NExpr {
    app(c("Rat.abs"), x)
}
fn rat_lt(x: NExpr, y: NExpr) -> NExpr {
    apps(c("Rat.lt"), &[x, y])
}
fn nat_le(x: NExpr, y: NExpr) -> NExpr {
    apps(c("Nat.le"), &[x, y])
}
fn rat_valid(x: NExpr) -> NExpr {
    app(c("Rat.valid"), x)
}
fn real_seq(x: NExpr) -> NExpr {
    NExpr::Proj("Real".to_string(), 0, Box::new(x))
}
fn complex_proj(x: NExpr, idx: u32) -> NExpr {
    NExpr::Proj("Complex".to_string(), idx, Box::new(x))
}
fn eq1(ty: NExpr, a: NExpr, b: NExpr) -> NExpr {
    apps(cl("Eq", vec![type1()]), &[ty, a, b])
}
fn refl1(ty: NExpr, a: NExpr) -> NExpr {
    apps(cl("Eq.refl", vec![type1()]), &[ty, a])
}
fn exists_nat(p: NExpr) -> NExpr {
    apps(cl("Exists", vec![type1()]), &[nat(), p])
}

fn pi_positive_eps(body: NExpr) -> NExpr {
    pi(
        "eps",
        rat(),
        pi(
            "hvalid",
            rat_valid(v("eps")),
            pi("hpos", rat_lt(rat_zero(), v("eps")), body),
        ),
    )
}
fn lam_positive_eps(body: NExpr) -> NExpr {
    lam(
        "eps",
        rat(),
        lam(
            "hvalid",
            rat_valid(v("eps")),
            lam("hpos", rat_lt(rat_zero(), v("eps")), body),
        ),
    )
}

fn const_seq_cauchy_proof(seq_const: &str) -> NExpr {
    let witness_pred = lam(
        "n0",
        nat(),
        pi(
            "m",
            nat(),
            pi(
                "n",
                nat(),
                pi(
                    "hm",
                    nat_le(v("n0"), v("m")),
                    pi(
                        "hn",
                        nat_le(v("n0"), v("n")),
                        rat_lt(
                            rat_abs(rat_sub(
                                app(c(seq_const), v("m")),
                                app(c(seq_const), v("n")),
                            )),
                            v("eps"),
                        ),
                    ),
                ),
            ),
        ),
    );
    lam_positive_eps(apps(
        cl("Exists.intro", vec![type1()]),
        &[
            nat(),
            witness_pred,
            lit(0),
            lam(
                "m",
                nat(),
                lam(
                    "n",
                    nat(),
                    lam(
                        "hm",
                        nat_le(lit(0), v("m")),
                        lam("hn", nat_le(lit(0), v("n")), v("hpos")),
                    ),
                ),
            ),
        ],
    ))
}

fn const_seq_close_proof(seq_const: &str) -> NExpr {
    let witness_pred = lam(
        "n0",
        nat(),
        pi(
            "n",
            nat(),
            pi(
                "hn",
                nat_le(v("n0"), v("n")),
                rat_lt(
                    rat_abs(rat_sub(
                        app(c(seq_const), v("n")),
                        app(c(seq_const), v("n")),
                    )),
                    v("eps"),
                ),
            ),
        ),
    );
    lam_positive_eps(apps(
        cl("Exists.intro", vec![type1()]),
        &[
            nat(),
            witness_pred,
            lit(0),
            lam("n", nat(), lam("hn", nat_le(lit(0), v("n")), v("hpos"))),
        ],
    ))
}

fn const_seq_valid_proof() -> NExpr {
    lam("n", nat(), app(c("Nat.le.refl"), lit(1)))
}

fn add_def(k: &mut Kernel, name: &str, ty: NExpr, val: NExpr) -> Result<(), String> {
    k.add_definition(
        name,
        &[],
        ty,
        val,
        DeclKind::Definition,
        Reducibility::Regular,
    )
    .map(|_| ())
    .map_err(|e| format!("{name}: {e}"))
}
fn add_thm(k: &mut Kernel, name: &str, ty: NExpr, val: NExpr) -> Result<(), String> {
    k.add_definition(name, &[], ty, val, DeclKind::Theorem, Reducibility::Opaque)
        .map(|_| ())
        .map_err(|e| format!("{name}: {e}"))
}

/// Add the first checked layer of analysis. Everything here is a definition or
/// a theorem with a kernel proof term; no Real/Complex operation is an axiom.
pub fn bootstrap_real(k: &mut Kernel) -> Result<(), String> {
    // Int.abs by constructor case split.
    add_def(
        k,
        "Int.abs",
        pi("x", int(), int()),
        lam(
            "x",
            int(),
            apps(
                cl("Int.rec", vec![type1()]),
                &[
                    lam("_", int(), int()),
                    lam("n", nat(), int_of_nat(v("n"))),
                    lam("n", nat(), int_of_nat(app(c("Nat.succ"), v("n")))),
                    v("x"),
                ],
            ),
        ),
    )?;

    // Basic rational constants and operations. `Rat` is represented as a raw
    // numerator/denominator pair, so comparisons must use `Rat.lt`/`Rat.le`;
    // raw definitional equality is intentionally not rational equality.
    add_def(k, "Rat.zero", rat(), rat_mk(int_of_nat(lit(0)), lit(1)))?;
    add_def(k, "Rat.one", rat(), rat_mk(int_of_nat(lit(1)), lit(1)))?;
    add_def(
        k,
        "Rat.neg",
        pi("x", rat(), rat()),
        lam(
            "x",
            rat(),
            rat_mk(app(c("Int.neg"), num(v("x"))), den(v("x"))),
        ),
    )?;
    add_def(
        k,
        "Rat.sub",
        pi("x", rat(), pi("y", rat(), rat())),
        lam(
            "x",
            rat(),
            lam("y", rat(), rat_add(v("x"), rat_neg(v("y")))),
        ),
    )?;
    add_def(
        k,
        "Rat.abs",
        pi("x", rat(), rat()),
        lam(
            "x",
            rat(),
            rat_mk(app(c("Int.abs"), num(v("x"))), den(v("x"))),
        ),
    )?;

    // A valid rational representative has a positive denominator. Keeping
    // this as data in Cauchy reals prevents zero-denominator junk values from
    // entering the analysis development.
    add_def(
        k,
        "Rat.valid",
        pi("x", rat(), NExpr::prop()),
        lam("x", rat(), nat_le(lit(1), den(v("x")))),
    )?;

    // Strict integer and rational order in common-denominator form.
    add_def(
        k,
        "Int.lt",
        pi("x", int(), pi("y", int(), NExpr::prop())),
        lam(
            "x",
            int(),
            lam(
                "y",
                int(),
                apps(
                    c("Int.le"),
                    &[apps(c("Int.add"), &[v("x"), int_of_nat(lit(1))]), v("y")],
                ),
            ),
        ),
    )?;
    add_def(
        k,
        "Rat.lt",
        pi("x", rat(), pi("y", rat(), NExpr::prop())),
        lam(
            "x",
            rat(),
            lam(
                "y",
                rat(),
                apps(
                    c("Int.lt"),
                    &[
                        apps(c("Int.mul"), &[num(v("x")), int_of_nat(den(v("y")))]),
                        apps(c("Int.mul"), &[num(v("y")), int_of_nat(den(v("x")))]),
                    ],
                ),
            ),
        ),
    )?;

    // Cauchy sequences of rationals:
    // forall valid eps > 0, exists N, forall m n >= N, |seq m - seq n| < eps.
    let cauchy_pred = lam(
        "seq",
        rat_seq_ty(),
        pi_positive_eps(exists_nat(lam(
            "n0",
            nat(),
            pi(
                "m",
                nat(),
                pi(
                    "n",
                    nat(),
                    pi(
                        "hm",
                        nat_le(v("n0"), v("m")),
                        pi(
                            "hn",
                            nat_le(v("n0"), v("n")),
                            rat_lt(
                                rat_abs(rat_sub(app(v("seq"), v("m")), app(v("seq"), v("n")))),
                                v("eps"),
                            ),
                        ),
                    ),
                ),
            ),
        ))),
    );
    add_def(
        k,
        "Real.isCauchy",
        pi("seq", rat_seq_ty(), NExpr::prop()),
        cauchy_pred,
    )?;

    // A real number is a Cauchy sequence bundled with its correctness proof.
    let real_ctor_ty = pi(
        "seq",
        rat_seq_ty(),
        pi(
            "valid",
            pi("n", nat(), rat_valid(app(v("seq"), v("n")))),
            pi("cauchy", app(c("Real.isCauchy"), v("seq")), c("Real")),
        ),
    );
    k.add_inductive_block(vec![InductiveSpec {
        name: "Real".to_string(),
        level_params: Vec::new(),
        ty: NExpr::type0(),
        num_params: 0,
        constructors: vec![("Real.mk".to_string(), real_ctor_ty)],
    }])
    .map_err(|e| e.to_string())?;

    // Eventual-closeness equality of two reals. This is the mathematical
    // equality relation for the setoid of Cauchy sequences.
    let close = |sx: NExpr, sy: NExpr| {
        pi_positive_eps(exists_nat(lam(
            "n0",
            nat(),
            pi(
                "n",
                nat(),
                pi(
                    "hn",
                    nat_le(v("n0"), v("n")),
                    rat_lt(
                        rat_abs(rat_sub(app(sx.clone(), v("n")), app(sy.clone(), v("n")))),
                        v("eps"),
                    ),
                ),
            ),
        )))
    };
    add_def(
        k,
        "Real.eq",
        pi("x", c("Real"), pi("y", c("Real"), NExpr::prop())),
        lam(
            "x",
            c("Real"),
            lam("y", c("Real"), close(real_seq(v("x")), real_seq(v("y")))),
        ),
    )?;

    // The zero sequence and its Cauchy proof. After the sequence/recursion
    // definitions unfold, the remaining obligation is exactly `0 < eps`, so
    // the positivity hypothesis itself closes every arithmetic branch.
    add_def(k, "Real.zeroSeq", rat_seq_ty(), lam("_", nat(), rat_zero()))?;

    let zero_proof = const_seq_cauchy_proof("Real.zeroSeq");
    add_thm(
        k,
        "Real.zeroSeq_valid",
        pi("n", nat(), rat_valid(app(c("Real.zeroSeq"), v("n")))),
        const_seq_valid_proof(),
    )?;
    add_thm(
        k,
        "Real.zeroSeq_cauchy",
        app(c("Real.isCauchy"), c("Real.zeroSeq")),
        zero_proof,
    )?;
    add_def(
        k,
        "Real.zero",
        c("Real"),
        apps(
            c("Real.mk"),
            &[
                c("Real.zeroSeq"),
                c("Real.zeroSeq_valid"),
                c("Real.zeroSeq_cauchy"),
            ],
        ),
    )?;

    add_thm(
        k,
        "Real.eq_zero_zero",
        apps(c("Real.eq"), &[c("Real.zero"), c("Real.zero")]),
        const_seq_close_proof("Real.zeroSeq"),
    )?;

    add_def(
        k,
        "Real.oneSeq",
        rat_seq_ty(),
        lam("_", nat(), c("Rat.one")),
    )?;
    add_thm(
        k,
        "Real.oneSeq_valid",
        pi("n", nat(), rat_valid(app(c("Real.oneSeq"), v("n")))),
        const_seq_valid_proof(),
    )?;
    add_thm(
        k,
        "Real.oneSeq_cauchy",
        app(c("Real.isCauchy"), c("Real.oneSeq")),
        const_seq_cauchy_proof("Real.oneSeq"),
    )?;
    add_def(
        k,
        "Real.one",
        c("Real"),
        apps(
            c("Real.mk"),
            &[
                c("Real.oneSeq"),
                c("Real.oneSeq_valid"),
                c("Real.oneSeq_cauchy"),
            ],
        ),
    )?;

    // Complex numbers are ordered pairs of real parts. Arithmetic operations
    // arrive after the corresponding Cauchy-sequence operations are proved.
    let complex_ctor_ty = pi("re", c("Real"), pi("im", c("Real"), c("Complex")));
    k.add_inductive_block(vec![InductiveSpec {
        name: "Complex".to_string(),
        level_params: Vec::new(),
        ty: NExpr::type0(),
        num_params: 0,
        constructors: vec![("Complex.mk".to_string(), complex_ctor_ty)],
    }])
    .map_err(|e| e.to_string())?;
    add_def(
        k,
        "Complex.re",
        pi("z", c("Complex"), c("Real")),
        lam("z", c("Complex"), complex_proj(v("z"), 0)),
    )?;
    add_def(
        k,
        "Complex.im",
        pi("z", c("Complex"), c("Real")),
        lam("z", c("Complex"), complex_proj(v("z"), 1)),
    )?;
    add_def(
        k,
        "Complex.zero",
        c("Complex"),
        apps(c("Complex.mk"), &[c("Real.zero"), c("Real.zero")]),
    )?;
    add_def(
        k,
        "Complex.i",
        c("Complex"),
        apps(c("Complex.mk"), &[c("Real.zero"), c("Real.one")]),
    )?;

    add_thm(
        k,
        "Complex.zero_re",
        eq1(
            c("Real"),
            app(c("Complex.re"), c("Complex.zero")),
            c("Real.zero"),
        ),
        refl1(c("Real"), c("Real.zero")),
    )?;
    add_thm(
        k,
        "Complex.zero_im",
        eq1(
            c("Real"),
            app(c("Complex.im"), c("Complex.zero")),
            c("Real.zero"),
        ),
        refl1(c("Real"), c("Real.zero")),
    )?;
    add_thm(
        k,
        "Complex.i_re",
        eq1(
            c("Real"),
            app(c("Complex.re"), c("Complex.i")),
            c("Real.zero"),
        ),
        refl1(c("Real"), c("Real.zero")),
    )?;
    add_thm(
        k,
        "Complex.i_im",
        eq1(
            c("Real"),
            app(c("Complex.im"), c("Complex.i")),
            c("Real.one"),
        ),
        refl1(c("Real"), c("Real.one")),
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::bootstrap_kernel;

    #[test]
    fn bootstrap_includes_checked_real_zero() {
        let k = bootstrap_kernel().expect("stdlib bootstrap");
        for name in [
            "Real.isCauchy",
            "Real",
            "Real.zeroSeq_valid",
            "Real.zeroSeq_cauchy",
            "Real.zero",
            "Real.eq_zero_zero",
            "Real.one",
            "Complex.zero",
            "Complex.i",
            "Complex.zero_re",
            "Complex.i_im",
        ] {
            assert!(k.lookup_decl(name).is_some(), "missing {name}");
        }
    }
}
