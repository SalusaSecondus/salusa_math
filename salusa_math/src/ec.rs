use std::{
    fmt::{Debug, Display},
    marker::PhantomData,
    ops::{Add, Mul, Sub},
};

use crate::group::{Field, FieldElement, Group, GroupElement};
use anyhow::{ensure, Result};
use num::BigInt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AffinePoint<FE>
where
    FE: Clone + Debug,
{
    pub x: FE,
    pub y: FE,
    pub inf: bool,
}

impl<FE> Display for AffinePoint<FE>
where
    FE: Eq + Clone + Display + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.inf {
            write!(f, "\u{1D4DE}")
        } else {
            write!(f, "({}, {})", self.x, self.y)
        }
    }
}

impl<FE> AffinePoint<FE>
where FE: Clone + Debug
{
    pub fn new(x: FE, y: FE) -> Self {
        AffinePoint { x, y, inf: false }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    affine: AffinePoint<FE>,
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
        Display::fmt(&self.affine, f)
    }
}

impl<F, FE, T, GE, ME> GroupElement<AffinePoint<FE>> for EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn consume(self) -> AffinePoint<FE> {
        self.affine
    }

    fn raw(&self) -> &AffinePoint<FE> {
        &self.affine
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

        let (x1, y1) = (self.affine.x.clone(), self.affine.y.clone());
        let (x2, y2) = (rhs.affine.x.clone(), rhs.affine.y.clone());

        let m;
        if self == rhs {
            let x1_sq = x1.mop(&x1);
            let three_x1_sq = x1_sq.gop(&x1_sq).gop(&x1_sq);
            let top = three_x1_sq.gop(&self.curve.a);
            let bottom = y1.gop(&y1);
            let bottom_inv = bottom.m_inv().unwrap();
            m = top.mop(&bottom_inv);
        } else {
            let top = y2.gop(&y1.gneg());
            let bottom = x2.gop(&x1.gneg());
            let bottom_inv = bottom.m_inv().unwrap();
            m = top.mop(&bottom_inv);
        }

        let m_sq = m.mop(&m);

        let x3 = m_sq.gop(&x1.gneg()).gop(&x2.gneg());
        let x1_m_x3 = x1.gop(&x3.gneg());
        let y3 = m.mop(&x1_m_x3).gop(&y1.gneg());

        let affine = AffinePoint {
            x: x3,
            y: y3,
            inf: false,
        };
        EcPoint {
            affine,
            curve: self.curve.clone(),
        }
    }

    fn gneg(&self) -> Self {
        if self.is_infinity() {
            return self.clone();
        }
        let neg_y = self.affine.y.gneg();
        let neg_affine = AffinePoint {
            x: self.affine.x.clone(),
            y: neg_y,
            inf: false,
        };
        Self {
            affine: neg_affine,
            curve: self.curve.clone(),
        }
    }
    
    fn identity(&self) -> Self {
        self.curve.identity()
    }

    
}

impl<F, FE, T, GE, ME> Add for EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn add(self, rhs: Self) -> Self::Output {
        self.gop(&rhs)
    }
}

impl<F, FE, T, GE, ME> Add for &EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn add(self, rhs: Self) -> Self::Output {
        self.gop(&rhs)
    }
}

impl<F, FE, T, GE, ME> Add<&EcPoint<F, FE, T, GE, ME>> for EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn add(self, rhs: &EcPoint<F, FE, T, GE, ME>) -> Self::Output {
        self.gop(&rhs)
    }
}

impl<F, FE, T, GE, ME> Add<EcPoint<F, FE, T, GE, ME>> for &EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn add(self, rhs: EcPoint<F, FE, T, GE, ME>) -> Self::Output {
        self.gop(&rhs)
    }
}

impl<F, FE, T, GE, ME> Sub for EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn sub(self, rhs: Self) -> Self::Output {
        self.gop(&rhs.gneg())
    }
}

impl<F, FE, T, GE, ME> Sub for &EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn sub(self, rhs: Self) -> Self::Output {
        self.gop(&rhs.gneg())
    }
}

impl<F, FE, T, GE, ME> Sub<&EcPoint<F, FE, T, GE, ME>> for EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn sub(self, rhs: &EcPoint<F, FE, T, GE, ME>) -> Self::Output {
        self.gop(&rhs.gneg())
    }
}

impl<F, FE, T, GE, ME> Sub<EcPoint<F, FE, T, GE, ME>> for &EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn sub(self, rhs: EcPoint<F, FE, T, GE, ME>) -> Self::Output {
        self.gop(&rhs.gneg())
    }
}

impl<F, FE, T, GE, ME> Mul<EcPoint<F, FE, T, GE, ME>> for BigInt
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
 {
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn mul(self, rhs: EcPoint<F, FE, T, GE, ME>) -> Self::Output {
        rhs.scalar_mult(&self)
    }
}

impl<F, FE, T, GE, ME> Mul<EcPoint<F, FE, T, GE, ME>> for &BigInt
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
 {
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn mul(self, rhs: EcPoint<F, FE, T, GE, ME>) -> Self::Output {
        rhs.scalar_mult(self)
    }
}

impl<F, FE, T, GE, ME> Mul<&EcPoint<F, FE, T, GE, ME>> for BigInt
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
 {
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn mul(self, rhs: &EcPoint<F, FE, T, GE, ME>) -> Self::Output {
        rhs.scalar_mult(&self)
    }
}

impl<F, FE, T, GE, ME> Mul<&EcPoint<F, FE, T, GE, ME>> for &BigInt
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, F, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
 {
    type Output = EcPoint<F, FE, T, GE, ME>;

    fn mul(self, rhs: &EcPoint<F, FE, T, GE, ME>) -> Self::Output {
        rhs.scalar_mult(self)
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
        self.affine.inf
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
}

impl<F, FE, T, GE, ME> Group<AffinePoint<FE>, EcPoint<F, FE, T, GE, ME>>
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
            affine: AffinePoint {
                x: zero.clone(),
                y: zero,
                inf: true,
            },
            curve: self.clone(),
        }
    }

    fn contains(&self, val: &AffinePoint<FE>) -> bool {
        if val.inf {
            return true;
        }
        let y = &val.y;
        let x = &val.x;
        let a = &self.a;
        let b = &self.b;

        let y_squared = y.mop(&y);
        let x_squared = val.x.mop(&val.x);
        let x_cubed = val.x.mop(&x_squared);

        let a_x = self.a.mop(&val.x);
        let rhs = x_cubed.gop(&a_x).gop(&self.b);

        // println!("{:?} =? {:?}", y_squared, rhs);
        y_squared == rhs
    }

    fn of(&self, val: &AffinePoint<FE>) -> Result<EcPoint<F, FE, T, GE, ME>> {
        ensure!(self.contains(val));

        Ok(EcPoint {
            affine: val.clone(),
            curve: self.clone(),
        })
    }

    fn wrap(&self, val: AffinePoint<FE>) -> Result<EcPoint<F, FE, T, GE, ME>> {
        ensure!(self.contains(&val));

        Ok(EcPoint {
            affine: val,
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
        write!(f, "y^2 = x^3 + {} * x + {}", self.a, self.b)
    }
}

#[cfg(test)]
mod tests {
    use num::{Num, One};

    use crate::group::ZField;

    use super::*;

    #[test]
    fn smoke() -> Result<()> {
        let gf = ZField::modulus(&BigInt::from_str_radix("233970423115425145524320034830162017933", 10)?);
        let a = gf.wrap((-95051i32).into())?;
        let b = gf.wrap(11279326i32.into())?;
        let order = BigInt::from_str_radix("29246302889428143187362802287225875743", 10)?;
        let curve = EcCurve::new(a, b, Some(order));

        println!("{}", curve);

        let inf = curve.identity();
        
        let g = curve.wrap(
            AffinePoint::new(gf.wrap(182u32.into())?, gf.wrap(85518893674295321206118380980485522083u128.into())?)
        )?;

        let result = curve.order().unwrap() * &g;
        println!("{} * {} = {}", curve.order().unwrap(), g, result);
        assert_eq!(result, inf);
        assert!(result.is_infinity());

        let result = (curve.order().unwrap() - BigInt::one()) * &g;
        println!("{}", result);
        println!("{}", &result + &g);
        Ok(())
    }
}
