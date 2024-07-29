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
        let a = &self.curve.a;
        let b = &self.curve.b;

        let x1 = &self.point.u;
        let y1 = self.point.v.as_ref().unwrap();
        let x2 = &rhs.point.u;
        let y2 = rhs.point.v.as_ref().unwrap();

        if x1 != x2 {
            let y2_m_y1 = y2.gop(&y1.gneg());
            let y2_m_y1_sq = y2_m_y1.mop(&y2_m_y1);
            let x2_m_x1 = x2.gop(&x1.gneg());
            let x2_m_x1_sq = x2_m_x1.mop(&x2_m_x1);

            let x2_m_x1_sq_inv = x2_m_x1_sq.m_inv().unwrap();

            let x3 = self
                .curve
                .b
                .mop(&y2_m_y1_sq)
                .mop(&x2_m_x1_sq_inv)
                .gop(&a.gneg())
                .gop(&x1.gneg())
                .gop(&x2.gneg());

            let tmp1 = x1.gop(&x1).gop(&x2).gop(a).mop(&y2_m_y1);
            let x2_m_x1_inv = x2_m_x1.m_inv().unwrap();
            let tmp1 = tmp1.mop(&x2_m_x1_inv);

            let tmp2 = b.mop(&y2_m_y1_sq).mop(&y2_m_y1);

            let tmp3 = b.mop(y1);
            let tmp3 = tmp3.gop(&tmp3);
            let tmp3 = tmp3.mop(&tmp3).mop(&tmp3);
            let tmp3 = tmp3.m_inv().unwrap();

            let tmp2 = tmp2.mop(&tmp3);

            let y3 = tmp1.gop(&tmp2.gneg()).gop(&y1.gneg());
            let inf = x3.is_zero();

            let point = MontgomeryPoint {
                u: x3,
                v: Some(y3),
                inf,
            };
            Self {
                point,
                curve: self.curve.clone(),
            }
        } else {
            if self.is_infinity() {
                return self.clone();
            }
            let one = x1.field().mult_identity();
            let x1_sq = x1.mop(x1);
            let three_x1_sq = x1_sq.gop(&x1_sq).gop(&x1_sq);
            let a_x1 = a.gop(x1);
            let two_a_x1 = a_x1.gop(&a_x1);
            let three_x1sq_two_a_x1_one = three_x1_sq.gop(&two_a_x1).gop(&one);
            let tmp1 = three_x1sq_two_a_x1_one.mop(&three_x1sq_two_a_x1_one);
            let tmp1 = b.mop(&tmp1);

            let b_y1 = b.mop(y1);
            let two_b_y1 = b_y1.gop(&b_y1);
            let two_b_y1_sq = two_b_y1.mop(&two_b_y1);
            let two_b_y1_sq_inv = two_b_y1_sq.m_inv().unwrap();
            let tmp1 = tmp1.mop(&two_b_y1_sq_inv);
            let x3 = tmp1.gop(&a.gneg()).gop(&x1.gneg()).gop(&x1.gneg());

            let tmp1 = x1.gop(x1).gop(x1).gop(a);
            let tmp2 = three_x1_sq.gop(&two_a_x1).gop(&one);
            let two_b_y1_inv = two_b_y1.m_inv().unwrap();
            let tmp2 = tmp1.mop(&tmp2).mop(&two_b_y1_inv);

            let tmp3 = three_x1sq_two_a_x1_one
                .mop(&three_x1sq_two_a_x1_one)
                .mop(&three_x1sq_two_a_x1_one);
            let tmp3 = b.mop(&tmp3);
            let two_b_y1_cube = two_b_y1.mop(&two_b_y1_sq);
            let two_b_y1_cube_inv = two_b_y1_cube.m_inv().unwrap();
            let tmp3 = tmp3.mop(&two_b_y1_cube_inv);

            let y3 = tmp2.gop(&tmp3.gneg()).gop(&y1.gneg());

            let inf = x3.is_zero();

            let point = MontgomeryPoint {
                u: x3,
                v: Some(y3),
                inf,
            };
            Self {
                point,
                curve: self.curve.clone(),
            }
        }
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
        let x1 = &self.point.u;
        let p = x1.field().order().unwrap();
        let p_minus2 = p - BigInt::from(2);

        let mut x2 = x1.field().mult_identity();
        let mut z2 = x1.field().identity();
        let mut x3 = x1.field().identity();
        let mut z3 = x1.field().mult_identity();

        println!("({:?}, {:?}) ({:?}, {:?})", x2.raw(), z2.raw(), x3.raw(), z3.raw());

        let mut prev_bit = false;
        for i in (0..p.bits()).rev() {
            let bit = k.bit(i);
            let b = bit ^ prev_bit;
            prev_bit = bit;

            ((x2, z2), (x3, z3)) = cswap((x2, z2), (x3, z3), b);
            ((x2, z2), (x3, z3)) = self.curve.ladder_step(x2, z2, x3, z3, x1);
        }
        
        let new_u = x2 * z3.pow(&p_minus2);
        let inf = new_u.is_zero();
        Self { point: MontgomeryPoint { u: new_u, v: None, inf}, curve: self.curve.clone() }
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

    fn ladder_step(&self, x2: GenericFieldElement<T, F, GE, ME>, z2: GenericFieldElement<T, F, GE, ME>, x3: GenericFieldElement<T, F, GE, ME>, z3: GenericFieldElement<T, F, GE, ME>, x1: &GenericFieldElement<T, F, GE, ME>) ->
    ((GenericFieldElement<T, F, GE, ME>, GenericFieldElement<T, F, GE, ME>), (GenericFieldElement<T, F, GE, ME>, GenericFieldElement<T, F, GE, ME>)) {
        let one = x2.field().mult_identity();
        let two = &one + &one;
        let four = &two + &two;
        let a_plus_2 = &self.a + &two;
        let a24 = &a_plus_2 / &four;

        let t1 = &x2 + &z2;
        let t2 = &x2 - &z2;
        let t3 = &x3 + &z3;
        let t4 = &x3 - &z3;
        let t5 = &t1 * &t1;
        let t6 = &t2 * &t2;
        let t2 = t2 * t3;
        let t1 = t1 * t4;
        let t1 = t1 + &t2;
        let t2 = &t1 - &t2;
        let x3 = &t1 * &t1;
        let t2 = &t2 * &t2;
        let z3 = &t2 * x1;
        let x2 = &t5 * &t6;
        let t5 = t5 - &t6;
        let t1 = a24 * &t5;
        let t6 = t6 + t1;
        let z2 = t5 * t6;

        ((x2, z2), (x3, z3))
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
    use crate::ec::{montgomery, weierstrass::CRYPTO_PALS_WEIERSTRASS_G};

    use super::*;

    #[test]
    fn smoke() -> Result<()> {
        println!("{}", *CRYPTO_PALS_MONTGOMERY);
        let inf = CRYPTO_PALS_MONTGOMERY.identity();
        println!("{}", inf);
        let tmp = CRYPTO_PALS_MONTGOMERY_G.scalar_mult(CRYPTO_PALS_MONTGOMERY.order().unwrap());
        println!("{}", tmp);
        println!("Order = {}", CRYPTO_PALS_MONTGOMERY.order().unwrap());
        assert!(tmp.is_infinity());

        let offset = CRYPTO_PALS_MONTGOMERY.field().wrap(178i32.into())?;
        let mult = BigInt::from(1);
        let affine = CRYPTO_PALS_WEIERSTRASS_G.scalar_mult(&mult);
        let montgomery = CRYPTO_PALS_MONTGOMERY_G.scalar_mult(&mult);

        println!("{} ?= {}", affine, montgomery);

        assert_eq!(affine.x() - offset, *montgomery.u());
        Ok(())
    }

    #[test]
    fn decompression() -> Result<()> {
        Ok(())
    }
}
