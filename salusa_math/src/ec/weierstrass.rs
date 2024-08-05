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
use anyhow::{ensure, Result};
use lazy_static::lazy_static;
use num::{BigInt, Num};
use salusa_math_macros::GroupOps;

pub type StdCurve = EcCurve<ZField, BigInt, ZAddElement, ZMultElement>;
pub type StdPoint = EcPoint<ZField, BigInt, ZAddElement, ZMultElement>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, GroupOps)]
pub struct EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    affine: AffinePoint<GenericFieldElement<T, F, GE, ME>>,
    curve: EcCurve<F, T, GE, ME>,
}

impl<F, T, GE, ME> Display for EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug + Display,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.affine, f)
    }
}

impl<F, T, GE, ME> GroupElement<AffinePoint<GenericFieldElement<T, F, GE, ME>>> for EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn consume(self) -> AffinePoint<GenericFieldElement<T, F, GE, ME>> {
        self.affine
    }

    fn raw(&self) -> &AffinePoint<GenericFieldElement<T, F, GE, ME>> {
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

        let two = BigInt::from(2);
        let three = BigInt::from(3);
        let a = &self.curve.a;
        let m;
        if self == rhs {
            m = (three * x1.pow(&two) + a) / (&two * &y1);
        } else {
            m = (&y2 - &y1) / (&x2 - &x1);
        }

        let x3 = m.pow(&two) - &x1 - &x2;
        let y3 = &m * (x1 - &x3) - y1;

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
    
    fn is_raw_identity(raw: &AffinePoint<GenericFieldElement<T, F, GE, ME>>) -> Option<bool> {
        Some(raw.inf)
    }
}

impl<F, T, GE, ME> EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    pub fn is_infinity(&self) -> bool {
        self.affine.inf
    }

    pub fn curve(&self) -> &EcCurve<F, T, GE, ME> {
        &self.curve
    }

    pub fn x(&self) -> &GenericFieldElement<T, F, GE, ME> {
        &self.affine.x
    }

    pub fn y(&self) -> &GenericFieldElement<T, F, GE, ME> {
        &self.affine.y
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EcCurve<F,  T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    pub a: GenericFieldElement<T, F, GE, ME>,
    pub b: GenericFieldElement<T, F, GE, ME>,
    order: Option<BigInt>,
    pub strict: bool,
    _pf: PhantomData<F>,
    _pt: PhantomData<T>,
    _pge: PhantomData<GE>,
    _pme: PhantomData<ME>,
}

impl<F, T, GE, ME> EcCurve<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    pub fn new(a: GenericFieldElement<T, F, GE, ME>, b: GenericFieldElement<T, F, GE, ME>, order: Option<BigInt>) -> Self {
        Self::new_with_strict(a, b, order, true)
    }

    pub fn new_with_strict(a: GenericFieldElement<T, F, GE, ME>, b: GenericFieldElement<T, F, GE, ME>, order: Option<BigInt>, strict: bool) -> Self {
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

    pub fn decompress(&self, x: GenericFieldElement<T, F, GE, ME>, y_bit: bool) -> Result<EcPoint<F, T, GE, ME>> {
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

impl<F, T, GE, ME> Group<AffinePoint<GenericFieldElement<T, F, GE, ME>>, EcPoint<F, T, GE, ME>>
    for EcCurve<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn identity(&self) -> EcPoint<F, T, GE, ME> {
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

    fn contains(&self, val: &AffinePoint<GenericFieldElement<T, F, GE, ME>>) -> bool {
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

    fn of(&self, val: &AffinePoint<GenericFieldElement<T, F, GE, ME>>) -> Result<EcPoint<F, T, GE, ME>> {
        ensure!(!self.strict || self.contains(val));

        Ok(EcPoint {
            affine: val.clone(),
            curve: self.clone(),
        })
    }

    fn wrap(&self, val: AffinePoint<GenericFieldElement<T, F, GE, ME>>) -> Result<EcPoint<F, T, GE, ME>> {
        ensure!(!self.strict || self.contains(&val));

        Ok(EcPoint {
            affine: val,
            curve: self.clone(),
        })
    }

    fn order(&self) -> Option<&num::BigInt> {
        self.order.as_ref()
    }

    fn from_bytes(&self, val: &[u8]) -> Result<EcPoint<F, T, GE, ME>> {
        let parts = val.split_at(val.len() / 2);
        let x = self.field().from_bytes(parts.0)?;
        let y = self.field().from_bytes(parts.0)?;
        let inf = x.is_zero();
        let point = AffinePoint { x, y, inf};
        ensure!(self.contains(&point));
        self.wrap(point)
    }
}

impl<F, T, GE, ME> Display for EcCurve<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug + Display,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "y^2 = x^3 + {} * x + {}", self.a, self.b)
    }
}

lazy_static! {
    pub static ref CRYPTO_PALS_WEIERSTRASS: StdCurve = {
        let gf = ZField::modulus(
            &BigInt::from_str_radix("233970423115425145524320034830162017933", 10).unwrap(),
        );
        let a = gf.wrap((-95051i32).into()).unwrap();
        let b = gf.wrap(11279326i32.into()).unwrap();
        let order = BigInt::from_str_radix("29246302889428143187362802287225875743", 10).unwrap();
        EcCurve::new(a, b, Some(order))
    };
    pub static ref CRYPTO_PALS_WEIERSTRASS_G: StdPoint = CRYPTO_PALS_WEIERSTRASS
        .wrap(AffinePoint::new(
            CRYPTO_PALS_WEIERSTRASS.field().wrap(182u32.into()).unwrap(),
            CRYPTO_PALS_WEIERSTRASS
                .field()
                .wrap(85518893674295321206118380980485522083u128.into())
                .unwrap()
        ))
        .unwrap();

    pub static ref NIST_P256 : StdCurve = {
        let p = BigInt::from_str_radix("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff", 16).unwrap();
        let gf = ZField::modulus(&p);
        let a = BigInt::from_str_radix("ffffffff00000001000000000000000000000000fffffffffffffffffffffffc", 16).unwrap();
        let b = BigInt::from_str_radix("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b", 16).unwrap();
        let a = gf.wrap(a).unwrap();
        let b = gf.wrap(b).unwrap();
        let order = BigInt::from_str_radix("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551", 16).unwrap();
        EcCurve::new(a, b, Some(order))
    };
    pub static ref NIST_P256_G : StdPoint = {
        let x = BigInt::from_str_radix("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296", 16).unwrap();
        let y = BigInt::from_str_radix("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5", 16).unwrap();
        let x = NIST_P256.field().wrap(x).unwrap();
        let y = NIST_P256.field().wrap(y).unwrap();
        let point = AffinePoint {x, y, inf: false};
        NIST_P256.wrap(point).unwrap()
    };
}

#[cfg(test)]
mod tests {
    use num::{One, Zero};
    use num_bigint::RandBigInt;
    use rand_core::OsRng;

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

        println!("{}", *NIST_P256);
        let result = NIST_P256_G.scalar_mult(NIST_P256.order().unwrap());
        println!("{}", result);
        assert!(result.is_infinity());
        assert!(result.is_identity());

        Ok(())
    }

    #[test]
    fn p256_smoke() -> Result<()> {
        println!("1G = {}", *NIST_P256_G);
        println!("2G = {}", NIST_P256_G.scalar_mult(&BigInt::from(2)));
        println!("3G = {}", NIST_P256_G.scalar_mult(&BigInt::from(3)));
        println!("100000 G = {}", NIST_P256_G.scalar_mult(&BigInt::from(100000)));

        println!("G + G = {}", &*NIST_P256_G + &*NIST_P256_G);

        Ok(())

    }

    #[test]
    fn decompression() -> Result<()> {
        let order = CRYPTO_PALS_WEIERSTRASS.order().unwrap();

        let rnd_point =
            CRYPTO_PALS_WEIERSTRASS_G.scalar_mult(&OsRng.gen_bigint_range(&BigInt::ZERO, order));
        let y_bit = rnd_point.raw().y.raw().bit(0);

        let recovered =
            CRYPTO_PALS_WEIERSTRASS.decompress(rnd_point.raw().x.clone(), y_bit)?;

        assert_eq!(recovered, rnd_point);

        Ok(())
    }
}
