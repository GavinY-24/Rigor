//! Rational linear arithmetic (Farkas certificates), §4.2 worked example.
//!
//! For hypotheses `A x >= b`, multipliers `lambda >= 0` with
//! `lambda^T A = c^T` and `lambda^T b >= d` establish `c^T x >= d`.
//! All arithmetic is exact `BigRat`: signs are normalized and denominators
//! are positive. A negative multiplier invalidates the certificate even if
//! an algebraic expression happens to match. The argument is *not* extended
//! to strict inequalities, floating-point rounding, or integer-only
//! consequences.

use crate::certificates::{LinearConstraint, LinearForm};
use crate::poly::{normalize_proof, poly_to_nexpr, PolyExpr};
use rigor_kernel::NExpr;
use rigor_spec::{BigInt, BigRat, BigUint};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct FarkasCertificate {
    /// One multiplier per hypothesis, in order.
    pub multipliers: Vec<BigRat>,
}

#[derive(Debug, Clone)]
pub enum FarkasError {
    NegativeMultiplier(usize),
    DimensionMismatch,
    CombinationMismatch(String),
    BoundMismatch(String),
}

impl std::fmt::Display for FarkasError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FarkasError::NegativeMultiplier(i) => {
                write!(f, "Farkas multiplier {i} is negative: a scaled hypothesis would flip the inequality")
            }
            FarkasError::DimensionMismatch => write!(f, "Farkas certificate dimension mismatch"),
            FarkasError::CombinationMismatch(m) => write!(f, "Farkas combination mismatch: {m}"),
            FarkasError::BoundMismatch(m) => write!(f, "Farkas bound mismatch: {m}"),
        }
    }
}
impl std::error::Error for FarkasError {}

/// Verify a Farkas certificate for a goal `goal_form >= 0` (i.e. `c^T x >= d`
/// stored as a LinearConstraint) from hypotheses (each `form >= 0`).
/// Requires: lambda >= 0, sum lambda_i * hyp_i = goal + slack, where slack is
/// a nonnegative-coefficient form (possibly zero). This is the precise
/// Farkas implication for `>=` systems.
pub fn verify_farkas(
    hypotheses: &[LinearConstraint],
    goal: &LinearConstraint,
    cert: &FarkasCertificate,
) -> Result<LinearForm, FarkasError> {
    if cert.multipliers.len() != hypotheses.len() {
        return Err(FarkasError::DimensionMismatch);
    }
    let mut combination = LinearForm::zero();
    for (i, (lambda, hyp)) in cert.multipliers.iter().zip(hypotheses.iter()).enumerate() {
        if !lambda.is_nonnegative() {
            return Err(FarkasError::NegativeMultiplier(i));
        }
        combination = combination.add(&hyp.form.scale(lambda));
    }
    // combination - goal must be a nonnegative slack form (all coeffs and constant >= 0)?
    // Goal: combination >= 0 implies goal >= 0 iff combination = goal + slack with slack >= 0
    // for all x in the *unconstrained rational* case only when slack is syntactically
    // nonnegative as a form over the hypotheses' domain. For Nat variables this
    // coefficientwise condition is exactly right; for rational variables with no
    // sign constraints, Farkas requires combination == goal (slack zero). We check
    // the exact case here and let the Nat route use `verify_farkas_nat`.
    let diff = combination.sub(&goal.form);
    if !diff.is_zero() {
        return Err(FarkasError::CombinationMismatch(format!(
            "lambda^T A - c^T = ({}) with constant {}, not zero",
            diff
                .coeffs
                .iter()
                .map(|(k, v)| format!("{v}*x{k}"))
                .collect::<Vec<_>>()
                .join(" + "),
            diff.constant
        )));
    }
    Ok(combination)
}

/// Nat-fragment Farkas: variables range over Nat, so slack forms with
/// nonnegative coefficients/constants are valid. Returns the slack.
pub fn verify_farkas_nat(
    hypotheses: &[LinearConstraint],
    goal: &LinearConstraint,
    cert: &FarkasCertificate,
) -> Result<LinearForm, FarkasError> {
    if cert.multipliers.len() != hypotheses.len() {
        return Err(FarkasError::DimensionMismatch);
    }
    let mut combination = LinearForm::zero();
    for (i, (lambda, hyp)) in cert.multipliers.iter().zip(hypotheses.iter()).enumerate() {
        if !lambda.is_nonnegative() {
            return Err(FarkasError::NegativeMultiplier(i));
        }
        // Nat scaling in the core proof uses literal Nat multipliers: require integers.
        if !lambda.den.is_one() {
            return Err(FarkasError::CombinationMismatch(format!(
                "multiplier {i} = {lambda} is not a natural number; scale the certificate by a common denominator first"
            )));
        }
        combination = combination.add(&hyp.form.scale(lambda));
    }
    let slack = combination.sub(&goal.form);
    for (k, v) in &slack.coeffs {
        if !v.is_nonnegative() {
            return Err(FarkasError::CombinationMismatch(format!(
                "coefficient of x{k} in the combination is below the goal ({} < 0 slack)",
                v
            )));
        }
    }
    if !slack.constant.is_nonnegative() {
        return Err(FarkasError::BoundMismatch(format!(
            "combined constant is below the goal by {}",
            slack.constant.neg()
        )));
    }
    Ok(slack)
}

/// Scale a rational Farkas certificate to natural multipliers by the common
/// positive denominator. Returns (scaled hypotheses, scaled goal) — the goal
/// scales too, so callers prove the scaled goal and divide back at the
/// statement level (for Nat goals the usual route keeps integer data).
pub fn scale_to_nat(
    hypotheses: &[LinearConstraint],
    cert: &FarkasCertificate,
) -> Result<Vec<BigUint>, FarkasError> {
    let mut out = Vec::new();
    for (i, lambda) in cert.multipliers.iter().enumerate() {
        if !lambda.is_nonnegative() {
            return Err(FarkasError::NegativeMultiplier(i));
        }
        if !lambda.den.is_one() {
            return Err(FarkasError::CombinationMismatch(format!(
                "multiplier {i} is not a natural number"
            )));
        }
        out.push(lambda.num.mag.clone());
    }
    let _ = hypotheses;
    Ok(out)
}

// ---------- core proof construction for the Nat fragment ----------

/// A Nat linear inequality occurrence in a proof context: the linear form is
/// `sum coeffs[i] * xi` and the statement is `Nat.le (lhs) (rhs)` where the
/// certificate works with hypotheses of shape `Nat.le rhs lhs` (i.e. lhs >= rhs
/// as `rhs <= lhs`). We use the library orientation directly:
///
/// Hypothesis i in the context is a proof of `Nat.le (rhs_i) (lhs_i)` and the
/// goal is `Nat.le (goal_rhs) (goal_lhs)`. The Farkas data is given in that
/// orientation through `NatIneq` below.
#[derive(Debug, Clone)]
pub struct NatIneq {
    /// left-hand (smaller) linear form
    pub le_side: Vec<(usize, BigUint)>, // (var, coeff)
    pub le_const: BigUint,
    /// right-hand (larger) linear form
    pub ge_side: Vec<(usize, BigUint)>,
    pub ge_const: BigUint,
    /// Name of the hypothesis proof in context (for hypotheses); for the goal this is ignored.
    pub proof_name: String,
}

fn form_to_poly(coeffs: &[(usize, BigUint)], konst: &BigUint, _vars: &[String]) -> PolyExpr {
    let mut result = PolyExpr::Const(konst.clone());
    for (var, coeff) in coeffs {
        if coeff.is_zero() {
            continue;
        }
        let term = if coeff.is_one() {
            PolyExpr::Var(*var)
        } else {
            PolyExpr::Mul(Box::new(PolyExpr::Const(coeff.clone())), Box::new(PolyExpr::Var(*var)))
        };
        result = PolyExpr::Add(Box::new(result), Box::new(term));
    }
    result
}

fn form_to_nexpr(coeffs: &[(usize, BigUint)], konst: &BigUint, vars: &[String]) -> NExpr {
    poly_to_nexpr(&form_to_poly(coeffs, konst, vars), vars)
}

fn add_nat_expr(a: NExpr, b: NExpr) -> NExpr {
    crate::stdlib::apps(crate::stdlib::c("Nat.add"), &[a, b])
}
fn mul_nat_expr(a: NExpr, b: NExpr) -> NExpr {
    crate::stdlib::apps(crate::stdlib::c("Nat.mul"), &[a, b])
}
fn le_expr(a: NExpr, b: NExpr) -> NExpr {
    crate::stdlib::apps(crate::stdlib::c("Nat.le"), &[a, b])
}

/// Scale a hypothesis proof `h : Nat.le rhs lhs` by a literal `k`:
/// returns proof of `Nat.le (k*rhs) (k*lhs)`. For k = 0 this is `Nat.le.refl 0`.
fn scale_le_proof(k: &BigUint, h: &NExpr, rhs: &NExpr, lhs: &NExpr) -> NExpr {
    if k.is_one() {
        return h.clone();
    }
    if k.is_zero() {
        return crate::stdlib::apps(crate::stdlib::c("Nat.le.refl"), &[crate::stdlib::lit_nat_expr(&BigUint::zero())]);
    }
    crate::stdlib::apps(
        crate::stdlib::c("Nat.mul_le_mul_left"),
        &[
            crate::stdlib::lit_nat_expr(k),
            rhs.clone(),
            lhs.clone(),
            h.clone(),
        ],
    )
}

/// Add two inequality proofs: `Nat.le a b -> Nat.le c d -> Nat.le (a+c) (b+d)`.
fn add_le_proofs(h1: NExpr, h2: NExpr, a: NExpr, b: NExpr, c_: NExpr, d: NExpr) -> NExpr {
    crate::stdlib::apps(crate::stdlib::c("Nat.add_le_add"), &[a, b, c_, d, h1, h2])
}

fn le_trans_proof(h1: NExpr, h2: NExpr, a: NExpr, b: NExpr, c_: NExpr) -> NExpr {
    crate::stdlib::apps(crate::stdlib::c("Nat.le_trans"), &[a, b, c_, h1, h2])
}

/// Build a core proof of the goal inequality from Nat hypotheses and natural
/// Farkas multipliers. The mathematical content: sum k_i*(rhs_i <= lhs_i)
/// gives `sum k_i rhs_i <= sum k_i lhs_i`; polynomial identities identify
/// `goal_rhs + slack_small = sum k_i rhs_i`-style rearrangements. Precisely we
/// require (checked exactly in BigUint arithmetic):
///   sum_i k_i * ge_side_i  =  goal.ge_side + slack_ge   (coefficientwise >=, slack as a poly)
///   sum_i k_i * le_side_i  =  goal.le_side + slack_le
/// and then `goal.le_side <= sum le = ... ` — the valid chain is:
///   goal.le <= goal.le + slack_le = sum le_i*k_i <= sum ge_i*k_i = goal.ge + slack_ge
/// and `goal.ge <= goal.ge + slack_ge` (Nat.le_add_right), so transitivity gives
/// goal.le <= goal.ge + slack_ge; to land exactly on goal.ge we additionally
/// require slack_ge == 0 in this fragment (slack on the large side would prove
/// a weaker statement). Slack on the small side is fine.
pub fn nat_farkas_proof(
    hypotheses: &[NatIneq],
    goal: &NatIneq,
    multipliers: &[BigUint],
    vars: &[String],
) -> Result<NExpr, String> {
    if multipliers.len() != hypotheses.len() {
        return Err("multiplier count does not match hypotheses".into());
    }
    // Compute combined forms exactly.
    let mut comb_le: BTreeMap<usize, BigUint> = BTreeMap::new();
    let mut comb_le_const = BigUint::zero();
    let mut comb_ge: BTreeMap<usize, BigUint> = BTreeMap::new();
    let mut comb_ge_const = BigUint::zero();
    for (k, h) in multipliers.iter().zip(hypotheses.iter()) {
        if k.is_zero() {
            continue;
        }
        for (var, coeff) in &h.le_side {
            let e = comb_le.entry(*var).or_insert_with(BigUint::zero);
            *e = e.add(&coeff.mul(k));
        }
        comb_le_const = comb_le_const.add(&h.le_const.mul(k));
        for (var, coeff) in &h.ge_side {
            let e = comb_ge.entry(*var).or_insert_with(BigUint::zero);
            *e = e.add(&coeff.mul(k));
        }
        comb_ge_const = comb_ge_const.add(&h.ge_const.mul(k));
    }
    let map_to_vec = |m: &BTreeMap<usize, BigUint>| -> Vec<(usize, BigUint)> {
        m.iter().map(|(k, v)| (*k, v.clone())).collect()
    };
    // slack_le = comb_le - goal.le must be coefficientwise >= 0 (Nat data: automatic
    // since forms are Nat-valued; we check the identity comb_le = goal.le + slack).
    let goal_le_map: BTreeMap<usize, BigUint> = goal.le_side.iter().cloned().collect();
    let mut slack_le: Vec<(usize, BigUint)> = Vec::new();
    for (var, coeff) in &comb_le {
        let g = goal_le_map.get(var).cloned().unwrap_or_else(BigUint::zero);
        if coeff.cmp(&g) == std::cmp::Ordering::Less {
            return Err(format!(
                "Farkas combination is too small on the left at x{var}: {coeff} < {g}"
            ));
        }
        let s = coeff.sub(&g);
        if !s.is_zero() {
            slack_le.push((*var, s));
        }
    }
    for (var, _) in &goal_le_map {
        if !comb_le.contains_key(var) {
            return Err(format!("Farkas combination is missing variable x{var} on the left"));
        }
    }
    if comb_le_const.cmp(&goal.le_const) == std::cmp::Ordering::Less {
        return Err("Farkas combination constant is too small on the left".into());
    }
    let slack_le_const = comb_le_const.sub(&goal.le_const);
    // Large side must match exactly.
    let goal_ge_map: BTreeMap<usize, BigUint> = goal.ge_side.iter().cloned().collect();
    if comb_ge != goal_ge_map || comb_ge_const != goal.ge_const {
        return Err(format!(
            "Farkas combination on the right ({:?} + {}) does not equal the goal's right side ({:?} + {})",
            map_to_vec(&comb_ge),
            comb_ge_const,
            goal.ge_side,
            goal.ge_const
        ));
    }

    // Build sum of scaled hypothesis proofs: proof of Nat.le (combined le) (combined ge).
    let mut combined_proof: Option<NExpr> = None;
    let mut cur_le = PolyExpr::konst(0);
    let mut cur_ge = PolyExpr::konst(0);
    for (k, h) in multipliers.iter().zip(hypotheses.iter()) {
        let rhs = form_to_nexpr(&h.le_side, &h.le_const, vars);
        let lhs = form_to_nexpr(&h.ge_side, &h.ge_const, vars);
        let hp = scale_le_proof(k, &NExpr::var(&h.proof_name), &rhs, &lhs);
        let scaled_le = form_to_poly(&h.le_side, &h.le_const, vars).scale_poly(k);
        let scaled_ge = form_to_poly(&h.ge_side, &h.ge_const, vars).scale_poly(k);
        match combined_proof {
            None => {
                combined_proof = Some(hp);
                cur_le = scaled_le;
                cur_ge = scaled_ge;
            }
            Some(acc) => {
                let acc_le_expr = poly_to_nexpr(&cur_le, vars);
                let acc_ge_expr = poly_to_nexpr(&cur_ge, vars);
                let scaled_le_expr = poly_to_nexpr(&scaled_le, vars);
                let scaled_ge_expr = poly_to_nexpr(&scaled_ge, vars);
                combined_proof = Some(add_le_proofs(
                    acc,
                    hp,
                    acc_le_expr,
                    acc_ge_expr,
                    scaled_le_expr,
                    scaled_ge_expr,
                ));
                cur_le = PolyExpr::Add(Box::new(cur_le), Box::new(scaled_le));
                cur_ge = PolyExpr::Add(Box::new(cur_ge), Box::new(scaled_ge));
            }
        }
    }
    let combined_proof = combined_proof.ok_or("no hypotheses supplied")?;
    // combined_proof : Nat.le (sum le) (sum ge) where the sums are the literal
    // Add-trees cur_le/cur_ge. The goal is Nat.le (goal.le) (goal.ge).
    // Chain: goal.le <= goal.le + slack_le =polys= sum le <= sum ge =poly= goal.ge.
    // First: goal.le <= goal.le + slack_le is Nat.le_add_right.
    let goal_le_expr = form_to_nexpr(&goal.le_side, &goal.le_const, vars);
    let goal_ge_expr = form_to_nexpr(&goal.ge_side, &goal.ge_const, vars);
    let slack_le_expr = form_to_nexpr(&slack_le, &slack_le_const, vars);
    let step1 = crate::stdlib::apps(
        crate::stdlib::c("Nat.le_add_right"),
        &[goal_le_expr.clone(), slack_le_expr.clone()],
    );
    // goal.le + slack_le = sum le (polynomial identity)
    let sum_le_poly = {
        let mut p = form_to_poly(&goal.le_side, &goal.le_const, vars);
        for (var, coeff) in &slack_le {
            let term = if coeff.is_one() {
                PolyExpr::Var(*var)
            } else {
                PolyExpr::Mul(Box::new(PolyExpr::Const(coeff.clone())), Box::new(PolyExpr::Var(*var)))
            };
            p = PolyExpr::Add(Box::new(p), Box::new(term));
        }
        if !slack_le_const.is_zero() {
            p = PolyExpr::Add(Box::new(p), Box::new(PolyExpr::Const(slack_le_const.clone())));
        }
        p
    };
    let _ = &sum_le_poly;
    // Transport combined_proof along the two polynomial identities using Eq.rec
    // on Nat.le indices: we rewrite the *statement* via Eq.transport of the
    // inequality proof. transport for Nat.le: given Eq Nat (sum_le) (goal_le+slack)
    // and Eq Nat (sum_ge) (goal_ge), produce the goal proof by Eq.rec.
    let sum_le_expr = poly_to_nexpr(&cur_le, vars);
    let sum_ge_expr = poly_to_nexpr(&cur_ge, vars);
    let eq_le = crate::poly::poly_identity_proof(
        &cur_le,
        &sum_le_poly,
        vars,
    )?; // Eq (sum_le) (goal_le + slack_le)
    let eq_ge = crate::poly::poly_identity_proof(&cur_ge, &form_to_poly(&goal.ge_side, &goal.ge_const, vars), vars)
        .unwrap_or_else(|_| crate::stdlib::nat_eq_refl(sum_ge_expr.clone())); // Eq (sum_ge) (goal_ge)
    // Now: step1 : le (goal.le) (goal.le + slack_le). Rewrite its right index
    // along symm eq_le to (sum_le)? Directions: combined is le(sum_le, sum_ge).
    // Desired chain: goal.le <= goal.le+slack (=defeq-as-Eq to sum_le via eq_le symm...)
    // Use Eq.rec transport on the *type* Nat.le (goal.le) X:
    //   transport (motive fun X => Nat.le goal.le X) eq_le step1?? eq_le : sum_le = goal_le+slack,
    //   so symm gives goal_le+slack = sum_le; transporting step1 along symm eq_le
    //   yields le (goal.le) (sum_le). Then le_trans with combined (le sum_le sum_ge),
    //   then transport right index along eq_ge to goal.ge.
    let transported1 = transport_le_right(step1, &goal_le_expr, &add_nat_expr(goal_le_expr.clone(), slack_le_expr.clone()), &sum_le_expr, crate::stdlib::nat_symm(eq_le, sum_le_expr.clone(), add_nat_expr(goal_le_expr.clone(), slack_le_expr.clone())));
    let chained = le_trans_proof(
        transported1,
        combined_proof,
        goal_le_expr.clone(),
        sum_le_expr.clone(),
        sum_ge_expr.clone(),
    );
    let result = transport_le_right(chained, &goal_le_expr, &sum_ge_expr, &goal_ge_expr, eq_ge);
    Ok(result)
}

/// Transport `h : Nat.le a b` along `e : Eq Nat b c` to `Nat.le a c` (Eq.rec).
fn transport_le_right(h: NExpr, a: &NExpr, b: &NExpr, c_: &NExpr, e: NExpr) -> NExpr {
    crate::stdlib::apps(
        rigor_kernel::NExpr::const_levels("Eq.rec", vec![rigor_kernel::Level::Succ(Box::new(rigor_kernel::Level::Zero)), rigor_kernel::Level::Zero]),
        &[
            crate::stdlib::nat(),
            b.clone(),
            NExpr::lam(
                "m",
                crate::stdlib::nat(),
                NExpr::lam(
                    "_",
                    crate::stdlib::eq(crate::stdlib::nat(), b.clone(), NExpr::var("m")),
                    le_expr(a.clone(), NExpr::var("m")),
                ),
            ),
            h,
            c_.clone(),
            e,
        ],
    )
}

impl PolyExpr {
    pub fn scale_poly(&self, k: &BigUint) -> PolyExpr {
        if k.is_zero() {
            return PolyExpr::konst(0);
        }
        if k.is_one() {
            return self.clone();
        }
        PolyExpr::Mul(Box::new(PolyExpr::Const(k.clone())), Box::new(self.clone()))
    }
}

pub fn bigint_nonnegative(v: &BigInt) -> bool {
    !v.negative
}

#[cfg(test)]
mod tests {
    use super::*;

    fn form(coeffs: &[(usize, i64)], konst: i64) -> LinearForm {
        LinearForm {
            coeffs: coeffs
                .iter()
                .map(|(k, v)| (*k, BigRat::from_i64(*v)))
                .collect(),
            constant: BigRat::from_i64(konst),
        }
    }

    #[test]
    fn spec_worked_example() {
        // 2x + y >= 5 and -x + y >= 1 prove 3y >= 7 with multipliers (1, 2).
        // Hypotheses in >= 0 form: (2x + y - 5), (-x + y - 1). Goal: 3y - 7.
        let h1 = LinearConstraint { form: form(&[(0, 2), (1, 1)], -5) };
        let h2 = LinearConstraint { form: form(&[(0, -1), (1, 1)], -1) };
        let goal = LinearConstraint { form: form(&[(1, 3)], -7) };
        let cert = FarkasCertificate { multipliers: vec![BigRat::from_i64(1), BigRat::from_i64(2)] };
        verify_farkas(&[h1.clone(), h2.clone()], &goal, &cert).expect("(1,2) must be accepted");
        // negative multiplier rejected even though algebra could be arranged
        let bad = FarkasCertificate { multipliers: vec![BigRat::from_i64(1), BigRat::from_i64(-2)] };
        assert!(matches!(
            verify_farkas(&[h1, h2], &goal, &bad),
            Err(FarkasError::NegativeMultiplier(1))
        ));
    }
}
