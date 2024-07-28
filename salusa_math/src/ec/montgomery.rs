use std::{
    fmt::{Debug, Display},
    marker::PhantomData,
    ops::Neg,
};

use crate::{group::{Field, FieldElement, Group, GroupElement}, mod_sqrt};
use anyhow::{ensure, Context, Result};
use num::BigInt;
use salusa_math_macros::GroupOps;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MontgomeryPoint<FE>
where
    FE: Clone + Debug,
{
    pub u: FE,
    pub v: Option<FE>,
    pub inf: bool,
}

impl<FE> Display for MontgomeryPoint<FE>
where
    FE: Eq + Clone + Display + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.inf {
            write!(f, "\u{1D4DE}")
        } else if let Some(v) = &self.v {
            write!(f, "({}, {})", self.u, v)
        } else {
            write!(f, "({}, _)", self.u)
        }
    }
}

impl<FE> MontgomeryPoint<FE>
where FE: Clone + Debug
{
    pub fn new(x: FE, y: FE) -> Self {
        MontgomeryPoint { u: x, v: Some(y), inf: false }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, GroupOps)]
pub struct EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    point: MontgomeryPoint<FE>,
    curve: EcCurve<F, FE, T, GE, ME>,
}

impl<F, FE, T, GE, ME> Display for EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME> + Display,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.point, f)
    }
}

impl<F, FE, T, GE, ME> GroupElement<MontgomeryPoint<FE>> for EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn consume(self) -> MontgomeryPoint<FE> {
        self.point
    }

    fn raw(&self) -> &MontgomeryPoint<FE> {
        &self.point
    }

    fn gop(&self, rhs: &Self) -> Self {
        if self.curve.strict || rhs.curve.strict {
            assert_eq!(self.curve, rhs.curve);
        }
        if self.is_infinity() {
            return rhs.clone();
        }
        if rhs.is_infinity() {
            return self.clone();
        }

        if self == &rhs.gneg() {
            return self.curve.identity();
        }
        
        
        todo!()
    }

    fn gneg(&self) -> Self {
        if self.is_infinity() {
            return self.clone();
        }
        if let Some(v) = &self.point.v {
            let neg_v = v.gneg();
            let neg_raw = MontgomeryPoint {
                u: self.point.u.clone(),
                v: Some(neg_v),
                inf: false,
            };
            Self {
                point: neg_raw,
                curve: self.curve.clone(),
            }
        } else {
            self.clone()
        }
    }
    
    fn identity(&self) -> Self {
        self.curve.identity()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.point.u.to_bytes()
    }

    fn scalar_mult(&self, k: &BigInt) -> Self {
        let u = self.point.u.clone();
        let field = u.field();
        let a = &self.curve.a;
        let zero = field.identity();
        let one = field.mult_identity();
        let mut u2 = one.clone();
        let mut w2 = zero;
        let mut u3 = u.clone();
        let mut w3 = one;
        let p = field.order().unwrap();

        for i in (0..p.bits()).rev() {
            let b = k.bit(i);
            (u2, u3) = cswap(u2, u3, b);
            (w2, w3) = cswap(w2, w3, b);
            let u2_u3 = u2.mop(&u3);
            let w2_w3 = w2.mop(&w3);
            let tmp1 = u2_u3 - w2_w3;
            let tmp1 = tmp1.mop(&tmp1);
            let u2_w3 = u2.mop(&w3);
            let w2_u3 = w2.mop(&u3);
            let tmp2 = u2_w3 - w2_u3;
            let tmp2 = tmp2.mop(&tmp2);
            (u3, w3) = (tmp1, u.mop(&tmp2));

            let u2_squared = u2.mop(&u2);
            let w2_squared = w2.mop(&w2);
            let tmp1 = u2_squared.gop(&w2_squared.gneg());
            let tmp1 = tmp1.mop(&tmp1);

            let u2_w2 = u2.mop(&w2);
            let four_u2_w2 = u2_w2.gop(&u2_w2).gop(&u2_w2).gop(&u2_w2);
            let a_u2_w2 = a.mop(&u2_w2);
            (u2, w2) = (tmp1,
                four_u2_w2 * (u2_squared + a_u2_w2 + w2_squared));
            (u2, u3) = cswap(u2, u3, b);
            (w2, w3) = cswap(w2, w3, b);
        }
        let new_u = u2 * (w2.scalar_mult(&(p - BigInt::from(2i32))));
        let inf = new_u.is_zero();
        let new_point = MontgomeryPoint { u: new_u, v: None, inf};
        EcPoint { point: new_point, curve: self.curve.clone() }

    }
}

// Not constant time.... I know.....
fn cswap<T>(a: T, b: T, condition: bool) -> (T, T) {
    if condition {
        (b, a)
    } else {
        (a, b)
    }
}

impl<F, FE, T, GE, ME> EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    pub fn is_infinity(&self) -> bool {
        self.point.inf
    }

    pub fn curve(&self) -> &EcCurve<F, FE, T, GE, ME> {
        &self.curve
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EcCurve<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    pub a: FE,
    pub b: FE,
    order: Option<BigInt>,
    pub strict: bool,
    _pf: PhantomData<F>,
    _pt: PhantomData<T>,
    _pge: PhantomData<GE>,
    _pme: PhantomData<ME>,
}

impl<F, FE, T, GE, ME> EcCurve<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    pub fn new(a: FE, b: FE, order: Option<BigInt>) -> Self {
        Self::new_with_strict(a, b, order, true)
    }

    pub fn new_with_strict(a: FE, b: FE, order: Option<BigInt>, strict: bool) -> Self {
        assert_eq!(a.field(), b.field());
        EcCurve { a, b, order, strict, _pf: PhantomData::default(), _pt: PhantomData::default(), _pge: PhantomData::default(), _pme: PhantomData::default() }
    }

    pub fn field(&self) -> &F {
        self.a.field()
    }

    pub fn decompress(&self, u: &FE, v_bit: bool) -> Result<EcPoint<F, FE, T, GE, ME>> {
        let u_sq = u.mop(u);
        let u_cube = u.mop(&u_sq);

        let a_u_sq = self.a.mop(&u_sq);
        let rhs = u_cube.gop(&a_u_sq).gop(u);

        let b_inv = self.b.m_inv()?;
        let v_sq = rhs.mop(&b_inv);
        let mut v = mod_sqrt(&v_sq)?;

        let actual_v_bit = (v.to_bytes().iter().last().unwrap() & 0x01) == 1;

        if actual_v_bit != v_bit {
            v = v.gneg();
        }
        let point = MontgomeryPoint {
            u: u.clone(), v: Some(v), inf: false
        };
        let point = EcPoint{ point, curve: self.clone()};

        Ok(point)
    }
}

impl<F, FE, T, GE, ME> Group<MontgomeryPoint<FE>, EcPoint<F, FE, T, GE, ME>>
    for EcCurve<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn identity(&self) -> EcPoint<F, FE, T, GE, ME> {
        let zero = self.field().identity();
        EcPoint {
            point: MontgomeryPoint {
                u: zero.clone(),
                v: Some(zero),
                inf: true,
            },
            curve: self.clone(),
        }
    }

    fn contains(&self, val: &MontgomeryPoint<FE>) -> bool {
        if val.inf {
            return true;
        }
        let decompressed_v = self.decompress(&val.u, true);
        if decompressed_v.is_err() {
            return false;
        }
        if let Some(v) = val.v.as_ref() {
            let decompressed_v = decompressed_v.unwrap();
            let decompressed_v = decompressed_v.point.v.unwrap();
            if decompressed_v == *v {
                return true;
            }
            let decompressed_v = decompressed_v.gneg();
            if decompressed_v == *v {
                return true;
            }
            false
        } else {
            true
        }
    }

    fn of(&self, val: &MontgomeryPoint<FE>) -> Result<EcPoint<F, FE, T, GE, ME>> {
        ensure!(!self.strict || self.contains(val));

        Ok(EcPoint {
            point: val.clone(),
            curve: self.clone(),
        })
    }

    fn wrap(&self, val: MontgomeryPoint<FE>) -> Result<EcPoint<F, FE, T, GE, ME>> {
        ensure!(!self.strict || self.contains(&val));

        Ok(EcPoint {
            point: val,
            curve: self.clone(),
        })
    }

    fn order(&self) -> Option<&num::BigInt> {
        self.order.as_ref()
    }
}

impl<F, FE, T, GE, ME> Display for EcCurve<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME> + Display,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} v^2 = u^3 + {} * u^2 + u" , self.b, self.a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smoke() -> Result<()> {

        Ok(())
    }

    #[test]
    fn decompression() -> Result<()> {

        Ok(())
    }
}
