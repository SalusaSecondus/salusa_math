use std::{
    fmt::{Debug, Display},
    marker::PhantomData,
    ops::Neg,
};

use crate::{
    group::{
        Field, FieldElement, GenericFieldElement, Group, GroupElement, ZAddElement, ZField,
        ZMultElement,
    },
    mod_sqrt,
};
use anyhow::{ensure, Context, Result};
use lazy_static::lazy_static;
use num::{BigInt, Num};
use salusa_math_macros::GroupOps;

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
where
    FE: Clone + Debug,
{
    pub fn new(x: FE, y: FE) -> Self {
        AffinePoint { x, y, inf: false }
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

    fn to_bytes(&self) -> Vec<u8> {
        let mut x = self.affine.x.to_bytes();
        let mut y = self.affine.y.to_bytes();
        let max_length = std::cmp::max(x.len(), y.len());
        x.resize(max_length, 0);
        y.resize(max_length, 0);
        x.extend_from_slice(&y);
        x
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
        EcCurve {
            a,
            b,
            order,
            strict,
            _pf: PhantomData::default(),
            _pt: PhantomData::default(),
            _pge: PhantomData::default(),
            _pme: PhantomData::default(),
        }
    }

    pub fn field(&self) -> &F {
        self.a.field()
    }
}

impl<F, FE, GE, ME> EcCurve<F, FE, BigInt, GE, ME>
where
    F: Field<BigInt, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<BigInt, F, GE, ME>,
    GE: GroupElement<BigInt>,
    ME: GroupElement<BigInt>,
{
    pub fn decompress(&self, x: BigInt, y_bit: bool) -> Result<EcPoint<F, FE, BigInt, GE, ME>> {
        let x = self.field().wrap(x)?;
        let x_cubed = x.mop(&x).mop(&x);
        let a_x = self.a.mop(&x);
        let rhs = x_cubed.gop(&a_x).gop(&self.b);
        let mut y = mod_sqrt(&rhs)?;
        let actual_y_bit = (y.to_bytes().iter().last().unwrap() & 0x01) == 1;

        if actual_y_bit != y_bit {
            y = y.gneg();
        }
        let affine = AffinePoint { x, y, inf: false };
        let point = EcPoint {
            affine,
            curve: self.clone(),
        };

        Ok(point)
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

        let y_squared = y.mop(y);
        let x_squared = x.mop(x);
        let x_cubed = x.mop(&x_squared);

        let a_x = a.mop(x);
        let rhs = x_cubed.gop(&a_x).gop(b);

        // println!("{:?} =? {:?}", y_squared, rhs);
        y_squared == rhs
    }

    fn of(&self, val: &AffinePoint<FE>) -> Result<EcPoint<F, FE, T, GE, ME>> {
        ensure!(!self.strict || self.contains(val));

        Ok(EcPoint {
            affine: val.clone(),
            curve: self.clone(),
        })
    }

    fn wrap(&self, val: AffinePoint<FE>) -> Result<EcPoint<F, FE, T, GE, ME>> {
        ensure!(!self.strict || self.contains(&val));

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

lazy_static! {
    static ref CRYPTO_PALS_WEIERSTRASS: EcCurve<
        ZField,
        GenericFieldElement<BigInt, ZField, ZAddElement, ZMultElement>,
        BigInt,
        ZAddElement,
        ZMultElement,
    > = {
        let gf = ZField::modulus(
            &BigInt::from_str_radix("233970423115425145524320034830162017933", 10).unwrap(),
        );
        let a = gf.wrap((-95051i32).into()).unwrap();
        let b = gf.wrap(11279326i32.into()).unwrap();
        let order = BigInt::from_str_radix("29246302889428143187362802287225875743", 10).unwrap();
        EcCurve::new(a, b, Some(order))
    };
    static ref CRYPTO_PALS_WEIERSTRASS_G: EcPoint<
        ZField,
        GenericFieldElement<BigInt, ZField, ZAddElement, ZMultElement>,
        BigInt,
        ZAddElement,
        ZMultElement,
    > = CRYPTO_PALS_WEIERSTRASS
        .wrap(AffinePoint::new(
            CRYPTO_PALS_WEIERSTRASS.field().wrap(182u32.into()).unwrap(),
            CRYPTO_PALS_WEIERSTRASS
                .field()
                .wrap(85518893674295321206118380980485522083u128.into())
                .unwrap()
        ))
        .unwrap();
}

#[cfg(test)]
mod tests {
    use num::{Num, One};
    use num_bigint::RandBigInt;
    use rand_core::OsRng;

    use crate::group::ZField;

    use super::*;

    #[test]
    fn smoke() -> Result<()> {
        println!("{}", *CRYPTO_PALS_WEIERSTRASS);

        let inf = CRYPTO_PALS_WEIERSTRASS.identity();

        let result =
            CRYPTO_PALS_WEIERSTRASS_G.scalar_mult(&CRYPTO_PALS_WEIERSTRASS.order().unwrap());
        println!(
            "{} * {} = {}",
            CRYPTO_PALS_WEIERSTRASS.order().unwrap(),
            *CRYPTO_PALS_WEIERSTRASS_G,
            result
        );
        assert_eq!(result, inf);
        assert!(result.is_infinity());

        let result = CRYPTO_PALS_WEIERSTRASS_G
            .scalar_mult(&(CRYPTO_PALS_WEIERSTRASS.order().unwrap() - BigInt::one()));
        println!("{}", result);
        println!("{}", result.gop(&CRYPTO_PALS_WEIERSTRASS_G));
        Ok(())
    }

    #[test]
    fn decompression() -> Result<()> {
        let order = CRYPTO_PALS_WEIERSTRASS.order().unwrap();

        let rnd_point =
            CRYPTO_PALS_WEIERSTRASS_G.scalar_mult(&OsRng.gen_bigint_range(&BigInt::ZERO, order));
        let y_bit = rnd_point.raw().y.raw().bit(0);

        let recovered =
            CRYPTO_PALS_WEIERSTRASS.decompress(rnd_point.raw().x.raw().clone(), y_bit)?;

        assert_eq!(recovered, rnd_point);

        Ok(())
    }
}
