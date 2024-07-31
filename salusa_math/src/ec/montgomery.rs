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
use num::{BigInt, Num as _};
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
where
    FE: Clone + Debug,
{
    pub fn new(x: FE, y: FE) -> Self {
        MontgomeryPoint {
            u: x,
            v: Some(y),
            inf: false,
        }
    }
}

#[derive(Debug, Clone, GroupOps)]
pub struct EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    point: MontgomeryPoint<GenericFieldElement<T, F, GE, ME>>,
    curve: EcCurve<F, T, GE, ME>,
}

impl<F, T, GE, ME> PartialEq for EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn eq(&self, other: &Self) -> bool {
        self.u() == other.u()
    }
}

impl<F, T, GE, ME> Eq for EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
}

impl<F, T, GE, ME> Display for EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug + Display,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.point, f)
    }
}

impl<F, T, GE, ME> GroupElement<MontgomeryPoint<GenericFieldElement<T, F, GE, ME>>> for EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn consume(self) -> MontgomeryPoint<GenericFieldElement<T, F, GE, ME>> {
        self.point
    }

    fn raw(&self) -> &MontgomeryPoint<GenericFieldElement<T, F, GE, ME>> {
        &self.point
    }

    fn gop(&self, rhs: &Self) -> Self {
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
        lazy_static!{
            static ref TWO : BigInt = BigInt::from(2);
            static ref FOUR : BigInt = BigInt::from(4);
        }
        let u = &self.point.u;
        let field = u.field();
        let one = field.mult_identity();
        let zero = field.identity();
        let (mut u2, mut w2) = (one.clone(), zero);
        let (mut u3, mut w3) = (u.clone(), one);
    
        let p = field.order().unwrap();
        for i in (0..p.bits()).rev() {
            let b = k.bit(i);
            (u2, u3) = cswap(u2, u3, b);
            (w2, w3) = cswap(w2, w3, b);

            (u3, w3) = ((&u2*&u3 - &w2*&w3).pow(&TWO),
                       u * (&u2*&w3 - &w2*&u3).pow(&TWO));
            (u2, w2) = ((u2.pow(&TWO) - w2.pow(&TWO)).pow(&TWO),
                       &*FOUR*&u2*&w2 * (u2.pow(&TWO) + &self.curve.a*&u2*&w2 + w2.pow(&TWO)));

            (u2, u3) = cswap(u2, u3, b);
            (w2, w3) = cswap(w2, w3, b);

        }
        let new_u = u2 * w2.pow(&(p - &*TWO));
        let inf = new_u.is_zero();
        Self {
            point: MontgomeryPoint {
                u: new_u,
                v: None,
                inf
            },
            curve: self.curve.clone()
        }
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

impl<F, T, GE, ME> EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    pub fn is_infinity(&self) -> bool {
        self.point.inf
    }

    pub fn curve(&self) -> &EcCurve<F, T, GE, ME> {
        &self.curve
    }

    pub fn u(&self) -> &GenericFieldElement<T, F, GE, ME> {
        &self.point.u
    }

    pub fn v(&self) -> Option<&GenericFieldElement<T, F, GE, ME>> {
        self.point.v.as_ref()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EcCurve<F, T, GE, ME>
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

    pub fn decompress(&self, u: &GenericFieldElement<T, F, GE, ME>, v_bit: bool) -> Result<EcPoint<F, T, GE, ME>> {
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
            u: u.clone(),
            v: Some(v),
            inf: false,
        };
        let point = EcPoint {
            point,
            curve: self.clone(),
        };

        Ok(point)
    }
}

impl<F, T, GE, ME> Group<MontgomeryPoint<GenericFieldElement<T, F, GE, ME>>, EcPoint<F, T, GE, ME>>
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
            point: MontgomeryPoint {
                u: zero.clone(),
                v: Some(zero),
                inf: true,
            },
            curve: self.clone(),
        }
    }

    fn contains(&self, val: &MontgomeryPoint<GenericFieldElement<T, F, GE, ME>>) -> bool {
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

    fn of(&self, val: &MontgomeryPoint<GenericFieldElement<T, F, GE, ME>>) -> Result<EcPoint<F, T, GE, ME>> {
        ensure!(!self.strict || self.contains(val));

        Ok(EcPoint {
            point: val.clone(),
            curve: self.clone(),
        })
    }

    fn wrap(&self, val: MontgomeryPoint<GenericFieldElement<T, F, GE, ME>>) -> Result<EcPoint<F, T, GE, ME>> {
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

impl<F, T, GE, ME> Display for EcCurve<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug + Display,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} v^2 = u^3 + {} * u^2 + u", self.b, self.a)
    }
}

lazy_static! {
    pub static ref CRYPTO_PALS_MONTGOMERY: EcCurve<
        ZField,
        BigInt,
        ZAddElement,
        ZMultElement,
    > = {
        let gf = ZField::modulus(
            &BigInt::from_str_radix("233970423115425145524320034830162017933", 10).unwrap(),
        );
        let a = gf.wrap(534.into()).unwrap();
        let b = gf.mult_identity();
        let order = BigInt::from_str_radix("29246302889428143187362802287225875743", 10).unwrap();

        EcCurve::new(a, b, Some(order))
    };
    pub static ref CRYPTO_PALS_MONTGOMERY_G: EcPoint<
        ZField,
        BigInt,
        ZAddElement,
        ZMultElement,
    > = CRYPTO_PALS_MONTGOMERY
        .wrap(MontgomeryPoint::new(
            CRYPTO_PALS_MONTGOMERY.field().wrap(4u32.into()).unwrap(),
            CRYPTO_PALS_MONTGOMERY
                .field()
                .wrap(85518893674295321206118380980485522083u128.into())
                .unwrap()
        ))
        .unwrap();
}

#[cfg(test)]
mod tests {
    use num::One as _;

    use super::*;

    #[test]
    fn smoke2() {
        let g = CRYPTO_PALS_MONTGOMERY_G.clone();
        let order = &CRYPTO_PALS_MONTGOMERY.order().unwrap();
        println!("{}", g);
        println!("{}", g.scalar_mult(order));

        println!("{}", g.scalar_mult(&BigInt::one()));
        println!("{}", g.scalar_mult( &BigInt::from(2)));

        println!("{:?}", g);

    }

    #[test]
    fn smoke() -> Result<()> {
        println!("{}", *CRYPTO_PALS_MONTGOMERY);

        let result =
        CRYPTO_PALS_MONTGOMERY_G.scalar_mult(&CRYPTO_PALS_MONTGOMERY.order().unwrap());
        println!(
            "{} * {} = {}",
            CRYPTO_PALS_MONTGOMERY.order().unwrap(),
            *CRYPTO_PALS_MONTGOMERY_G,
            result
        );
        println!("{:?}", result);
        assert!(result.is_infinity());
        Ok(())
    }

    #[test]
    fn decompression() -> Result<()> {
        Ok(())
    }
}
