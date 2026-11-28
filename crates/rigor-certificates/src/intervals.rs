//! Interval bounds with exact rational enclosures (§4.2).
//! Endpoint arithmetic is exact `BigRat` arithmetic — no floating point,
//! so enclosures are outward-valid by construction.

use crate::certificates::LinearForm;
use crate::linarith::{verify_farkas, FarkasCertificate, FarkasError};
use crate::certificates::LinearConstraint;
use rigor_spec::BigRat;
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq)]
pub struct Interval {
    pub lo: BigRat,
    pub hi: BigRat,
}

impl Interval {
    pub fn new(lo: BigRat, hi: BigRat) -> Option<Self> {
        if lo.cmp(&hi) == std::cmp::Ordering::Greater {
            None
        } else {
            Some(Self { lo, hi })
        }
    }
    pub fn point(v: BigRat) -> Self {
        Self { lo: v.clone(), hi: v }
    }
    pub fn add(&self, o: &Self) -> Self {
        Self { lo: self.lo.add(&o.lo), hi: self.hi.add(&o.hi) }
    }
    pub fn neg(&self) -> Self {
        Self { lo: self.hi.neg(), hi: self.lo.neg() }
    }
    pub fn sub(&self, o: &Self) -> Self {
        self.add(&o.neg())
    }
    pub fn mul(&self, o: &Self) -> Self {
        let products = [
            self.lo.mul(&o.lo),
            self.lo.mul(&o.hi),
            self.hi.mul(&o.lo),
            self.hi.mul(&o.hi),
        ];
        let mut lo = products[0].clone();
        let mut hi = products[0].clone();
        for p in &products[1..] {
            if p.cmp(&lo) == std::cmp::Ordering::Less {
                lo = p.clone();
            }
            if p.cmp(&hi) == std::cmp::Ordering::Greater {
                hi = p.clone();
            }
        }
        Self { lo, hi }
    }
    pub fn contains(&self, v: &BigRat) -> bool {
        self.lo.cmp(v) != std::cmp::Ordering::Greater && v.cmp(&self.hi) != std::cmp::Ordering::Greater
    }
}

#[derive(Debug, Clone)]
pub enum IntervalExpr {
    Var(usize),
    Const(BigRat),
    Add(Box<IntervalExpr>, Box<IntervalExpr>),
    Sub(Box<IntervalExpr>, Box<IntervalExpr>),
    Mul(Box<IntervalExpr>, Box<IntervalExpr>),
}

pub fn eval_interval(e: &IntervalExpr, env: &BTreeMap<usize, Interval>) -> Option<Interval> {
    match e {
        IntervalExpr::Var(i) => env.get(i).cloned(),
        IntervalExpr::Const(c) => Some(Interval::point(c.clone())),
        IntervalExpr::Add(a, b) => Some(eval_interval(a, env)?.add(&eval_interval(b, env)?)),
        IntervalExpr::Sub(a, b) => Some(eval_interval(a, env)?.sub(&eval_interval(b, env)?)),
        IntervalExpr::Mul(a, b) => Some(eval_interval(a, env)?.mul(&eval_interval(b, env)?)),
    }
}

/// Prove `expr <= bound` for all inputs in the given intervals: evaluates the
/// enclosure and checks its upper endpoint against the bound exactly.
pub fn prove_bound(
    e: &IntervalExpr,
    env: &BTreeMap<usize, Interval>,
    bound: &BigRat,
) -> Result<Interval, String> {
    let enclosure = eval_interval(e, env).ok_or("unbound variable in interval expression")?;
    if enclosure.hi.cmp(bound) == std::cmp::Ordering::Greater {
        return Err(format!(
            "interval bound not established: enclosure upper endpoint {} exceeds bound {}",
            enclosure.hi, bound
        ));
    }
    Ok(enclosure)
}

/// A linear bound proved by intervals reduces to a Farkas certificate once
/// endpoints are substituted: for a linear form and interval inputs, the
/// worst-case endpoint combination is a rational linear inequality in the
/// endpoints. This function checks the resulting scalar inequality exactly.
pub fn linear_interval_bound(
    form: &LinearForm,
    env: &BTreeMap<usize, Interval>,
    bound: &BigRat,
) -> Result<BigRat, String> {
    let mut worst = form.constant.clone();
    for (var, coeff) in &form.coeffs {
        let iv = env.get(var).ok_or("unbound variable")?;
        let endpoint = if coeff.is_nonnegative() { &iv.hi } else { &iv.lo };
        worst = worst.add(&coeff.mul(endpoint));
    }
    if worst.cmp(bound) == std::cmp::Ordering::Greater {
        return Err(format!("linear interval bound fails: worst case {worst} > {bound}"));
    }
    Ok(worst)
}

/// Verify an interval-derived bound through the Farkas route (the reduction
/// used when the endpoint inequality is presented as a certificate).
pub fn bound_via_farkas(
    hypotheses: &[LinearConstraint],
    goal: &LinearConstraint,
    cert: &FarkasCertificate,
) -> Result<(), FarkasError> {
    verify_farkas(hypotheses, goal, cert).map(|_| ())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interval_arithmetic_exact() {
        let x = Interval::new(BigRat::parse("1/3").unwrap(), BigRat::parse("1/2").unwrap()).unwrap();
        let y = Interval::new(BigRat::from_i64(1), BigRat::from_i64(2)).unwrap();
        let p = x.mul(&y);
        assert_eq!(p.lo.to_string(), "1/3");
        assert_eq!(p.hi.to_string(), "1");
        // (x + y) <= 5/2 exactly at the top endpoint
        let s = x.add(&y);
        assert_eq!(s.hi.to_string(), "5/2");
    }
}
