//! Arbitrary-precision signed integers and normalized rationals.
//! Little-endian base-2^32 magnitudes. No floating point anywhere.

use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct BigUint {
    limbs: Vec<u32>, // little-endian, no trailing zeros
}

impl BigUint {
    pub fn zero() -> Self {
        Self { limbs: Vec::new() }
    }
    pub fn one() -> Self {
        Self { limbs: vec![1] }
    }
    pub fn from_u64(mut v: u64) -> Self {
        let mut limbs = Vec::new();
        while v > 0 {
            limbs.push((v & 0xffff_ffff) as u32);
            v >>= 32;
        }
        Self { limbs }
    }
    pub fn from_bytes_be(bytes: &[u8]) -> Self {
        let mut out = Self::zero();
        for &b in bytes {
            out = out.mul_small(256).add_small(b as u32);
        }
        out
    }
    pub fn to_bytes_be(&self) -> Vec<u8> {
        if self.is_zero() {
            return vec![0];
        }
        let mut bytes = Vec::new();
        let mut cur = self.clone();
        while !cur.is_zero() {
            let (q, r) = cur.div_rem_small(256);
            bytes.push(r as u8);
            cur = q;
        }
        bytes.reverse();
        bytes
    }
    /// Minimal LEB128 unsigned encoding (canonical bytes for Nat literals).
    pub fn to_leb128(&self) -> Vec<u8> {
        if self.is_zero() {
            return vec![0];
        }
        let mut out = Vec::new();
        let mut cur = self.clone();
        while !cur.is_zero() {
            let (q, r) = cur.div_rem_small(128);
            let mut byte = r as u8;
            cur = q;
            if !cur.is_zero() {
                byte |= 0x80;
            }
            out.push(byte);
        }
        out
    }
    pub fn from_leb128(bytes: &[u8]) -> Option<(Self, usize)> {
        let mut result = Self::zero();
        let mut shift_bytes: Vec<u8> = Vec::new();
        for (i, &b) in bytes.iter().enumerate() {
            shift_bytes.push(b & 0x7f);
            if b & 0x80 == 0 {
                // minimal encoding: last byte nonzero unless single zero
                if i > 0 && (b & 0x7f) == 0 {
                    // still canonical if higher bits were set; trailing zero group is not minimal
                    // LEB128 minimality: the final group must be non-zero when length > 1
                    return None;
                }
                for (j, part) in shift_bytes.iter().enumerate() {
                    // result += part * 128^j
                    let mut term = Self::from_u64(*part as u64);
                    for _ in 0..j {
                        term = term.mul_small(128);
                    }
                    result = result.add(&term);
                }
                return Some((result, i + 1));
            }
            if i >= 512 {
                return None;
            }
        }
        None
    }
    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }
    pub fn is_one(&self) -> bool {
        self.limbs.len() == 1 && self.limbs[0] == 1
    }
    fn trim(mut self) -> Self {
        while self.limbs.last() == Some(&0) {
            self.limbs.pop();
        }
        self
    }
    pub fn add(&self, other: &Self) -> Self {
        let mut out = Vec::with_capacity(self.limbs.len().max(other.limbs.len()) + 1);
        let mut carry: u64 = 0;
        for i in 0..self.limbs.len().max(other.limbs.len()) {
            let a = *self.limbs.get(i).unwrap_or(&0) as u64;
            let b = *other.limbs.get(i).unwrap_or(&0) as u64;
            let s = a + b + carry;
            out.push((s & 0xffff_ffff) as u32);
            carry = s >> 32;
        }
        if carry > 0 {
            out.push(carry as u32);
        }
        Self { limbs: out }.trim()
    }
    /// Requires self >= other.
    pub fn sub(&self, other: &Self) -> Self {
        debug_assert!(self.cmp(other) != Ordering::Less);
        let mut out = Vec::with_capacity(self.limbs.len());
        let mut borrow: i64 = 0;
        for i in 0..self.limbs.len() {
            let a = self.limbs[i] as i64;
            let b = *other.limbs.get(i).unwrap_or(&0) as i64;
            let mut d = a - b - borrow;
            if d < 0 {
                d += 1 << 32;
                borrow = 1;
            } else {
                borrow = 0;
            }
            out.push(d as u32);
        }
        Self { limbs: out }.trim()
    }
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut out = vec![0u32; self.limbs.len() + other.limbs.len()];
        for (i, &a) in self.limbs.iter().enumerate() {
            let mut carry: u64 = 0;
            for (j, &b) in other.limbs.iter().enumerate() {
                let cur = out[i + j] as u64 + (a as u64) * (b as u64) + carry;
                out[i + j] = (cur & 0xffff_ffff) as u32;
                carry = cur >> 32;
            }
            let mut k = i + other.limbs.len();
            while carry > 0 {
                let cur = out[k] as u64 + carry;
                out[k] = (cur & 0xffff_ffff) as u32;
                carry = cur >> 32;
                k += 1;
            }
        }
        Self { limbs: out }.trim()
    }
    pub fn mul_small(&self, m: u32) -> Self {
        if m == 0 || self.is_zero() {
            return Self::zero();
        }
        let mut out = Vec::with_capacity(self.limbs.len() + 1);
        let mut carry: u64 = 0;
        for &a in &self.limbs {
            let cur = (a as u64) * (m as u64) + carry;
            out.push((cur & 0xffff_ffff) as u32);
            carry = cur >> 32;
        }
        if carry > 0 {
            out.push(carry as u32);
        }
        Self { limbs: out }.trim()
    }
    pub fn add_small(&self, a: u32) -> Self {
        self.add(&Self::from_u64(a as u64))
    }
    pub fn div_rem_small(&self, d: u32) -> (Self, u32) {
        assert!(d != 0);
        let mut out = vec![0u32; self.limbs.len()];
        let mut rem: u64 = 0;
        for i in (0..self.limbs.len()).rev() {
            let cur = (rem << 32) | (self.limbs[i] as u64);
            out[i] = (cur / (d as u64)) as u32;
            rem = cur % (d as u64);
        }
        (Self { limbs: out }.trim(), rem as u32)
    }
    pub fn bit_len(&self) -> usize {
        if self.is_zero() { return 0; }
        let top = self.limbs[self.limbs.len()-1];
        (self.limbs.len()-1)*32 + (32 - top.leading_zeros() as usize)
    }
    pub fn get_bit(&self, i: usize) -> bool {
        let limb = i/32; if limb>=self.limbs.len() { return false; }
        (self.limbs[limb] >> (i%32)) & 1 == 1
    }
    pub fn shl1(&self) -> Self {
        let mut out=vec![0u32; self.limbs.len()+1];
        let mut carry=0u32;
        for i in 0..self.limbs.len() { let c=self.limbs[i]>>31; out[i]=(self.limbs[i]<<1)|carry; carry=c; }
        out[self.limbs.len()]=carry;
        Self{limbs:out}.trim()
    }
    pub fn set_bit(&mut self, i: usize) {
        let limb=i/32; if self.limbs.len()<=limb { self.limbs.resize(limb+1,0); }
        self.limbs[limb] |= 1<<(i%32);
    }
    pub fn div_rem(&self, other: &Self) -> (Self, Self) {
        assert!(!other.is_zero(), "division by zero");
        if self.cmp(other) == Ordering::Less { return (Self::zero(), self.clone()); }
        if other.limbs.len() == 1 { let (q,r)=self.div_rem_small(other.limbs[0]); return (q, Self::from_u64(r as u64)); }
        // Binary long division: simple, correct, adequate for certificate-sized integers.
        let mut q = Self::zero();
        let mut r = Self::zero();
        for i in (0..self.bit_len()).rev() {
            r = r.shl1();
            if self.get_bit(i) { if r.limbs.is_empty() { r.limbs.push(1); } else { r.limbs[0] |= 1; } }
            if r.cmp(other) != Ordering::Less { r = r.sub(other); q.set_bit(i); }
        }
        (q.trim(), r.trim())
    }
    pub fn cmp(&self, other: &Self) -> Ordering {
        if self.limbs.len() != other.limbs.len() {
            return self.limbs.len().cmp(&other.limbs.len());
        }
        for i in (0..self.limbs.len()).rev() {
            match self.limbs[i].cmp(&other.limbs[i]) {
                Ordering::Equal => continue,
                o => return o,
            }
        }
        Ordering::Equal
    }
    pub fn gcd(a: &Self, b: &Self) -> Self {
        let mut x = a.clone();
        let mut y = b.clone();
        while !y.is_zero() {
            let (_, r) = x.div_rem(&y);
            x = y;
            y = r;
        }
        x
    }
    pub fn pow(&self, mut e: u64) -> Self {
        let mut result = Self::one();
        let mut base = self.clone();
        while e > 0 {
            if e & 1 == 1 {
                result = result.mul(&base);
            }
            e >>= 1;
            if e > 0 {
                base = base.mul(&base);
            }
        }
        result
    }
    pub fn to_u64(&self) -> Option<u64> {
        match self.limbs.len() {
            0 => Some(0),
            1 => Some(self.limbs[0] as u64),
            2 => Some((self.limbs[0] as u64) | ((self.limbs[1] as u64) << 32)),
            _ => None,
        }
    }
    pub fn decimal(&self) -> String {
        if self.is_zero() {
            return "0".to_string();
        }
        let mut cur = self.clone();
        let mut digits = Vec::new();
        while !cur.is_zero() {
            let (q, r) = cur.div_rem_small(10);
            digits.push((b'0' + r as u8) as char);
            cur = q;
        }
        digits.iter().rev().collect()
    }
    pub fn from_decimal(s: &str) -> Option<Self> {
        if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let mut out = Self::zero();
        for b in s.bytes() {
            out = out.mul_small(10).add_small((b - b'0') as u32);
        }
        Some(out)
    }
}

impl fmt::Display for BigUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.decimal())
    }
}
impl fmt::Debug for BigUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BigUint({})", self.decimal())
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BigInt {
    pub negative: bool, // false when zero
    pub mag: BigUint,
}

impl BigInt {
    pub fn zero() -> Self {
        Self { negative: false, mag: BigUint::zero() }
    }
    pub fn one() -> Self {
        Self { negative: false, mag: BigUint::one() }
    }
    pub fn from_i64(v: i64) -> Self {
        if v < 0 {
            Self { negative: true, mag: BigUint::from_u64(v.unsigned_abs()) }
        } else {
            Self { negative: false, mag: BigUint::from_u64(v as u64) }
        }
    }
    pub fn from_biguint(mag: BigUint) -> Self {
        let negative = !mag.is_zero();
        Self { negative: false && negative, mag }
    }
    pub fn is_zero(&self) -> bool {
        self.mag.is_zero()
    }
    pub fn signum(&self) -> i64 {
        if self.is_zero() {
            0
        } else if self.negative {
            -1
        } else {
            1
        }
    }
    pub fn neg(&self) -> Self {
        if self.is_zero() {
            self.clone()
        } else {
            Self { negative: !self.negative, mag: self.mag.clone() }
        }
    }
    pub fn abs(&self) -> BigUint {
        self.mag.clone()
    }
    pub fn add(&self, other: &Self) -> Self {
        if self.negative == other.negative {
            let mag = self.mag.add(&other.mag);
            Self { negative: self.negative && !mag.is_zero(), mag }
        } else {
            match self.mag.cmp(&other.mag) {
                Ordering::Equal => Self::zero(),
                Ordering::Greater => Self { negative: self.negative, mag: self.mag.sub(&other.mag) },
                Ordering::Less => Self { negative: other.negative, mag: other.mag.sub(&self.mag) },
            }
        }
    }
    pub fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }
    pub fn mul(&self, other: &Self) -> Self {
        let mag = self.mag.mul(&other.mag);
        Self { negative: self.negative != other.negative && !mag.is_zero(), mag }
    }
    pub fn div_rem_euclid(&self, other: &Self) -> (Self, Self) {
        assert!(!other.is_zero(), "division by zero");
        let (mut q, r) = self.mag.div_rem(&other.mag);
        let mut qq = Self { negative: self.negative != other.negative && !q.is_zero(), mag: q.clone() };
        let mut rr = Self { negative: false, mag: r.clone() };
        if !r.is_zero() && self.negative {
            // euclidean: remainder >= 0
            q = q.add_small(1);
            qq = Self { negative: self.negative != other.negative, mag: q };
            rr = Self { negative: false, mag: other.mag.sub(&r) };
        }
        let _ = &mut qq;
        (qq, rr)
    }
    pub fn cmp(&self, other: &Self) -> Ordering {
        match (self.negative, other.negative) {
            (false, true) => {
                if self.is_zero() && other.is_zero() {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
            (true, false) => {
                if self.is_zero() && other.is_zero() {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            }
            (false, false) => self.mag.cmp(&other.mag),
            (true, true) => other.mag.cmp(&self.mag),
        }
    }
    pub fn gcd(a: &Self, b: &Self) -> BigUint {
        BigUint::gcd(&a.mag, &b.mag)
    }
    pub fn to_i64(&self) -> Option<i64> {
        let v = self.mag.to_u64()?;
        if self.negative {
            if v == (i64::MAX as u64) + 1 {
                Some(i64::MIN)
            } else if v <= i64::MAX as u64 {
                Some(-(v as i64))
            } else {
                None
            }
        } else if v <= i64::MAX as u64 {
            Some(v as i64)
        } else {
            None
        }
    }
    pub fn decimal(&self) -> String {
        if self.negative {
            format!("-{}", self.mag.decimal())
        } else {
            self.mag.decimal()
        }
    }
    pub fn from_decimal(s: &str) -> Option<Self> {
        let (neg, digits) = match s.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, s.strip_prefix('+').unwrap_or(s)),
        };
        let mag = BigUint::from_decimal(digits)?;
        Some(Self { negative: neg && !mag.is_zero(), mag })
    }
}

impl fmt::Display for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.decimal())
    }
}
impl fmt::Debug for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BigInt({})", self.decimal())
    }
}


/// Normalized rational: denominator > 0, gcd(|num|, den) = 1. Signs normalized, denominators positive.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BigRat {
    pub num: BigInt,
    pub den: BigUint, // > 0
}

impl BigRat {
    pub fn new(num: BigInt, den: BigInt) -> Option<Self> {
        if den.is_zero() {
            return None;
        }
        let mut n = num;
        let mut d = den;
        if d.negative {
            d = d.neg();
            n = n.neg();
        }
        let g = BigUint::gcd(&n.mag, &d.mag);
        if !g.is_one() && !g.is_zero() {
            n.mag = n.mag.div_rem(&g).0;
            if n.mag.is_zero() {
                n.negative = false;
            }
            d.mag = d.mag.div_rem(&g).0;
        }
        if n.is_zero() {
            return Some(Self { num: BigInt::zero(), den: BigUint::one() });
        }
        Some(Self { num: n, den: d.mag })
    }
    pub fn from_int(v: BigInt) -> Self {
        Self { num: v, den: BigUint::one() }
    }
    pub fn from_i64(v: i64) -> Self {
        Self::from_int(BigInt::from_i64(v))
    }
    pub fn zero() -> Self { Self::from_i64(0) }
    pub fn one() -> Self { Self::from_i64(1) }
    pub fn is_zero(&self) -> bool { self.num.is_zero() }
    pub fn is_nonnegative(&self) -> bool { !self.num.negative }
    pub fn is_positive(&self) -> bool { !self.num.negative && !self.num.is_zero() }
    pub fn add(&self, o: &Self) -> Self {
        let n = self.num.mul(&BigInt { negative: false, mag: o.den.clone() })
            .add(&o.num.mul(&BigInt { negative: false, mag: self.den.clone() }));
        let d = BigInt { negative: false, mag: self.den.mul(&o.den) };
        Self::new(n, d).expect("denominator nonzero")
    }
    pub fn sub(&self, o: &Self) -> Self { self.add(&o.neg()) }
    pub fn neg(&self) -> Self { Self { num: self.num.clone().neg(), den: self.den.clone() } }
    pub fn mul(&self, o: &Self) -> Self {
        Self::new(
            self.num.mul(&o.num),
            BigInt { negative: false, mag: self.den.mul(&o.den) },
        )
        .expect("denominator nonzero")
    }
    pub fn div(&self, o: &Self) -> Option<Self> {
        if o.is_zero() {
            return None;
        }
        let recip_num = BigInt { negative: o.num.negative, mag: o.den.clone() };
        let recip_den = BigInt { negative: false, mag: o.num.mag.clone() };
        Some(self.mul(&Self::new(recip_num, recip_den)?))
    }
    pub fn cmp(&self, o: &Self) -> Ordering {
        let lhs = self.num.mul(&BigInt { negative: false, mag: o.den.clone() });
        let rhs = o.num.mul(&BigInt { negative: false, mag: self.den.clone() });
        lhs.cmp(&rhs)
    }
    pub fn parse(s: &str) -> Option<Self> {
        if let Some((a, b)) = s.split_once('/') {
            let num = BigInt::from_decimal(a.trim())?;
            let den = BigInt::from_decimal(b.trim())?;
            Self::new(num, den)
        } else if let Some((int_part, frac_part)) = s.split_once('.') {
            let neg = int_part.starts_with('-');
            let int_digits = int_part.trim_start_matches(['-', '+']);
            let scale = BigUint::from_u64(10).pow(frac_part.len() as u64);
            let mut num_mag = BigUint::from_decimal(&format!("{}{}", int_digits, frac_part))?;
            let _ = &mut num_mag;
            let num = BigInt { negative: neg && !num_mag.is_zero(), mag: num_mag };
            Self::new(num, BigInt { negative: false, mag: scale })
        } else {
            Some(Self::from_int(BigInt::from_decimal(s.trim())?))
        }
    }
}

impl fmt::Display for BigRat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den.is_one() {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}
impl fmt::Debug for BigRat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BigRat({})", self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uint_arith() {
        let a = BigUint::from_decimal("123456789012345678901234567890").unwrap();
        let b = BigUint::from_decimal("98765432109876543210").unwrap();
        assert_eq!(a.add(&b).decimal(), "123456789111111111011111111100");
        let (q, r) = a.div_rem(&b);
        assert_eq!(q.mul(&b).add(&r), a);
        assert_eq!(BigUint::gcd(&a, &b).decimal(), "90");
    }

    #[test]
    fn rat_normalization() {
        let r = BigRat::new(BigInt::from_i64(6), BigInt::from_i64(-8)).unwrap();
        assert_eq!(r.to_string(), "-3/4");
        assert!(r.den.cmp(&BigUint::zero()) == Ordering::Greater);
        let s = BigRat::parse("1.25").unwrap();
        assert_eq!(s.to_string(), "5/4");
        assert_eq!(r.add(&s).to_string(), "1/2");
    }

    #[test]
    fn int_euclid_div() {
        let (q, r) = BigInt::from_i64(-7).div_rem_euclid(&BigInt::from_i64(3));
        assert_eq!(q, BigInt::from_i64(-3));
        assert_eq!(r, BigInt::from_i64(2));
    }
}
