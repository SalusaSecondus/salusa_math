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


#[derive(Debug, Clone, GroupOps)]
pub struct EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    u: GenericFieldElement<T, F, GE, ME>,
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
        write!(f, "({}, _)", self.u)
    }
}

impl<F, T, GE, ME> GroupElement<GenericFieldElement<T, F, GE, ME>> for EcPoint<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn consume(self) -> GenericFieldElement<T, F, GE, ME> {
        self.u
    }

    fn raw(&self) -> &GenericFieldElement<T, F, GE, ME> {
        &self.u
    }

    fn gop(&self, _rhs: &Self) -> Self {
        todo!()
    }

    fn gneg(&self) -> Self {
        self.clone()
    }

    fn identity(&self) -> Self {
        self.curve.identity()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.u.to_bytes()
    }

    fn scalar_mult(&self, k: &BigInt) -> Self {
        lazy_static!{
            static ref TWO : BigInt = BigInt::from(2);
            static ref FOUR : BigInt = BigInt::from(4);
        }
        let u = &self.u;
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
        Self {
            u: new_u,
            curve: self.curve.clone()
        }
    }
    
    fn is_raw_identity(raw: &GenericFieldElement<T, F, GE, ME>) -> Option<bool> {
        Some(raw.is_zero())
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
        self.u.is_zero()
    }

    pub fn curve(&self) -> &EcCurve<F, T, GE, ME> {
        &self.curve
    }

    pub fn u(&self) -> &GenericFieldElement<T, F, GE, ME> {
        &self.u
    }

    pub fn v(&self) -> Result<GenericFieldElement<T, F, GE, ME>> {
        self.curve.recover_v(&self.u, true)
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

    pub fn recover_v(&self, u: &GenericFieldElement<T, F, GE, ME>, v_bit: bool) -> Result<GenericFieldElement<T, F, GE, ME>> {
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

        Ok(v)
    }
}

impl<F, T, GE, ME> Group<GenericFieldElement<T, F, GE, ME>, EcPoint<F, T, GE, ME>>
    for EcCurve<F, T, GE, ME>
where
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn identity(&self) -> EcPoint<F, T, GE, ME> {
        let u = self.field().identity();
        EcPoint {
            u,
            curve: self.clone(),
        }
    }

    fn contains(&self, val: &GenericFieldElement<T, F, GE, ME>) -> bool {
        if val.is_zero() {
            return true;
        }
        self.recover_v(val, true).is_ok()
    }

    fn of(&self, val: &GenericFieldElement<T, F, GE, ME>) -> Result<EcPoint<F, T, GE, ME>> {
        ensure!(!self.strict || self.contains(val));

        Ok(EcPoint {
            u: val.clone(),
            curve: self.clone(),
        })
    }

    fn wrap(&self, val: GenericFieldElement<T, F, GE, ME>) -> Result<EcPoint<F, T, GE, ME>> {
        ensure!(!self.strict || self.contains(&val));

        Ok(EcPoint {
            u: val,
            curve: self.clone(),
        })
    }

    fn order(&self) -> Option<&num::BigInt> {
        self.order.as_ref()
    }

    fn from_bytes(&self, val: &[u8]) -> Result<EcPoint<F, T, GE, ME>> {
        let u = self.field().from_bytes(val)?;
        ensure!(self.contains(&u));
        self.wrap(u)
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
        .wrap(CRYPTO_PALS_MONTGOMERY.field().wrap(4.into()).unwrap())
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
