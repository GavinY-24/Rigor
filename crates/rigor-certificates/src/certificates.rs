//! Plugin contracts (§4.2). Each plugin publishes its exact supported
//! fragment, its soundness basis, and its reconstruction strategy. No plugin
//! requires a new axiom: acceptance reduces to a kernel-checked core proof
//! (or, for the rational Farkas verifier, to an exact arithmetic check whose
//! Nat-fragment expansion is a core proof).

use rigor_kernel::NExpr;
use rigor_spec::{BigInt, BigRat, BigUint};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct PluginInfo {
    pub name: &'static str,
    pub fragment: &'static str,
    pub soundness: &'static str,
    pub reconstruction: &'static str,
}

pub fn plugin_registry() -> Vec<PluginInfo> {
    vec![
        PluginInfo {
            name: "rewriting",
            fragment: "Equations over any type built from Eq.refl / Eq.symm / Eq.trans and congrArg steps supplied as checked lemmas",
            soundness: "Each step is an application of Eq constructors or library lemmas whose types the kernel checks; composition is Eq.trans",
            reconstruction: "Build the transitivity chain as a core term; kernel rechecks it",
        },
        PluginInfo {
            name: "polynomial",
            fragment: "Polynomial identities over Nat in variables x0..xn with literal coefficients (Add/Mul/Pow)",
            soundness: "Normalization is a decision procedure over the free commutative semiring; the proof term is built only from Nat.add/mul assoc, comm, distrib, zero/one lemmas, all proved by recursor terms in the library",
            reconstruction: "Proof-producing normalization (see poly::normalize_proof); kernel rechecks the resulting Eq proof",
        },
        PluginInfo {
            name: "linarith",
            fragment: "Linear arithmetic over Nat (core expansion) and over Q (exact Farkas verifier). Hypotheses/goals are linear forms with literal coefficients",
            soundness: "Farkas: for hypotheses Ax>=b (resp. <=), multipliers lambda>=0 with lambda*A and lambda*b matching the goal up to nonnegative slack polynomials give the conclusion; sign and denominator conditions are checked exactly",
            reconstruction: "Nat fragment: scale hypotheses by literal multipliers (Nat.mul_le_mul_left), add them (Nat.add_le_add), transport along polynomial identities (poly plugin) and Nat.le_trans. Q fragment: exact BigRat verifier; scaling by the common positive denominator reduces to the Nat/Int certificate shape",
        },
        PluginInfo {
            name: "enumeration",
            fragment: "Goals over finitely many Bool/Nat-below-bound variables with a decidable kernel-computable predicate",
            soundness: "Case analysis on each variable (Bool.rec / Nat.rec bounds); every leaf is checked by kernel computation (Eq.refl at the leaf goal)",
            reconstruction: "Nested recursor case terms; kernel rechecks and computes each leaf",
        },
        PluginInfo {
            name: "sat",
            fragment: " propositional formulas over Bool variables (And/Or/Not/Var/Lit) with at most 16 variables for core expansion; Rust DPLL + brute-force refutation for the verifier",
            soundness: "Unsatisfiability is proved by exhaustive case analysis in the core term (each leaf computes the formula to false); the Rust checker is only a proposal mechanism",
            reconstruction: "Nested Bool.rec case term over the formula evaluation function; kernel recomputes every leaf",
        },
        PluginInfo {
            name: "interval",
            fragment: "Linear/polynomial expressions over Q with rational interval inputs; bounds are rational enclosures with exact endpoints",
            soundness: "Interval evaluation with exact BigRat endpoints is outward-rounded by construction (endpoint arithmetic is exact rational arithmetic, no floating point); the final endpoint inequality reduces to a linarith certificate",
            reconstruction: "Exact interval evaluation in Rust; endpoint inequalities expand through the linarith Nat-scaled certificate route or are closed literal inequalities",
        },
    ]
}

/// Equality rewriting: build `Eq ty a b` from a chain of checked steps.
/// Each step is a proof term of `Eq ty (current) (next)`; the endpoints are
/// tracked symbolically so the chain is only built when it truly connects.
pub fn rewrite_chain(steps: &[(NExpr, NExpr, NExpr)], ty: &NExpr) -> Result<NExpr, String> {
    // steps: (from, to, proof)
    if steps.is_empty() {
        return Err("empty rewrite chain".into());
    }
    for w in steps.windows(2) {
        if w[0].1 != w[1].0 {
            return Err("rewrite chain is disconnected".into());
        }
    }
    let mut acc = steps[0].2.clone();
    for (i, step) in steps.iter().enumerate().skip(1) {
        acc = rigor_kernel::NExpr::apps(
            rigor_kernel::NExpr::const_levels("Eq.trans", vec![rigor_kernel::Level::Succ(Box::new(rigor_kernel::Level::Zero))]),
            &[
                ty.clone(),
                steps[0].0.clone(),
                steps[i - 1].1.clone(),
                step.1.clone(),
                acc,
                step.2.clone(),
            ],
        );
    }
    Ok(acc)
}

/// Linear form over variables x0..xn with rational (or integer) coefficients:
/// `coeffs[i] * xi`, plus a constant. Used by linarith and interval plugins.
#[derive(Debug, Clone, PartialEq)]
pub struct LinearForm {
    pub coeffs: BTreeMap<usize, BigRat>,
    pub constant: BigRat,
}

impl LinearForm {
    pub fn zero() -> Self {
        Self { coeffs: BTreeMap::new(), constant: BigRat::zero() }
    }
    pub fn var(i: usize) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(i, BigRat::one());
        Self { coeffs, constant: BigRat::zero() }
    }
    pub fn konst(c: BigRat) -> Self {
        Self { coeffs: BTreeMap::new(), constant: c }
    }
    pub fn add(&self, o: &Self) -> Self {
        let mut coeffs = self.coeffs.clone();
        for (k, v) in &o.coeffs {
            let e = coeffs.entry(*k).or_insert_with(BigRat::zero);
            *e = e.add(v);
        }
        coeffs.retain(|_, v| !v.is_zero());
        Self { coeffs, constant: self.constant.add(&o.constant) }
    }
    pub fn scale(&self, s: &BigRat) -> Self {
        if s.is_zero() {
            return Self::zero();
        }
        Self {
            coeffs: self.coeffs.iter().map(|(k, v)| (*k, v.mul(s))).collect(),
            constant: self.constant.mul(s),
        }
    }
    pub fn neg(&self) -> Self {
        self.scale(&BigRat::from_i64(-1))
    }
    pub fn sub(&self, o: &Self) -> Self {
        self.add(&o.neg())
    }
    pub fn is_zero(&self) -> bool {
        self.coeffs.values().all(|v| v.is_zero()) && self.constant.is_zero()
    }
    pub fn eval(&self, assignment: &BTreeMap<usize, BigRat>) -> BigRat {
        let mut result = self.constant.clone();
        for (k, v) in &self.coeffs {
            if let Some(x) = assignment.get(k) {
                result = result.add(&v.mul(x));
            }
        }
        result
    }
}

/// A linear inequality `form >= bound` (normalized: `form - bound >= 0`),
/// or `form <= bound` when `le` is set. Keep one orientation internally:
/// we store `lhs >= rhs` forms only (see `LinearConstraint`).
#[derive(Debug, Clone, PartialEq)]
pub struct LinearConstraint {
    /// lhs - rhs >= 0
    pub form: LinearForm,
}

impl LinearConstraint {
    /// `lhs >= rhs`
    pub fn ge(lhs: LinearForm, rhs: LinearForm) -> Self {
        Self { form: lhs.sub(&rhs) }
    }
    /// `lhs <= rhs`
    pub fn le(lhs: LinearForm, rhs: LinearForm) -> Self {
        Self { form: rhs.sub(&lhs) }
    }
}

pub fn biguint_to_nat_expr(v: &BigUint) -> NExpr {
    NExpr::LitNat(v.clone())
}

pub fn bigrat_to_pair(v: &BigRat) -> (BigInt, BigUint) {
    (v.num.clone(), v.den.clone())
}
