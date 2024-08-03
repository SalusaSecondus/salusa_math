use std::{
    collections::HashMap, fmt::{Debug, Display}, hash::Hash, marker::PhantomData, ops::{Add, Div, Mul, Neg, Sub}
};

use anyhow::{bail, Result};
use num::{bigint::Sign, BigInt, One, Zero};
use salusa_math_macros::{FieldOps, GroupOps};

/// A helper trait for types with a group operation.
pub trait GroupOps<Rhs = Self, Output = Self>:
    Add<Rhs, Output = Output> + Sub<Rhs, Output = Output> // + AddAssign<Rhs> + SubAssign<Rhs>
{
}

impl<T, Rhs, Output> GroupOps<Rhs, Output> for T where
    T: Add<Rhs, Output = Output> + Sub<Rhs, Output = Output> // + AddAssign<Rhs> + SubAssign<Rhs>
{
}

/// A helper trait for references with a group operation.
pub trait GroupOpsOwned<Rhs = Self, Output = Self>: for<'r> GroupOps<&'r Rhs, Output> {}
impl<T, Rhs, Output> GroupOpsOwned<Rhs, Output> for T where T: for<'r> GroupOps<&'r Rhs, Output> {}

/// A helper trait for types with a field operation.
pub trait FieldOps<Rhs = Self, Output = Self>:
    Mul<Rhs, Output = Output> + Div<Rhs, Output = Output> // + MulAssign<Rhs> + DivAssign<Rhs>
{
}

impl<T, Rhs, Output> FieldOps<Rhs, Output> for T where
    T: Mul<Rhs, Output = Output> + Div<Rhs, Output = Output> // + MulAssign<Rhs> + DivAssign<Rhs>
{
}

/// A helper trait for references with a field operation.
pub trait FieldOpsOwned<Rhs = Self, Output = Self>: for<'r> FieldOps<&'r Rhs, Output> {}
impl<T, Rhs, Output> FieldOpsOwned<Rhs, Output> for T where T: for<'r> FieldOps<&'r Rhs, Output> {}


pub trait GroupElement<T>: std::fmt::Debug + Sized + Clone + Eq + GroupOps + GroupOpsOwned
where
    T: Eq,
{
    fn consume(self) -> T;
    fn raw(&self) -> &T;
    fn gop(&self, rhs: &Self) -> Self;
    fn gneg(&self) -> Self;
    fn identity(&self) -> Self;
    fn to_bytes(&self) -> Vec<u8>;

    fn scalar_mult(&self, mult: &BigInt) -> Self {
        let mut r0 = self.identity();
        if mult.is_zero() {
            r0
        } else {
            let mut r1 = self.clone();
            let mut mult = mult.to_owned();
            if mult.sign() == Sign::Minus {
                r1 = r1.gneg();
                mult = mult.neg();
            }
            for i in (0..=mult.bits()).rev() {
                if mult.bit(i) {
                    r0 = r0.gop(&r1);
                    r1 = r1.gop(&r1);
                } else {
                    r1 = r0.gop(&r1);
                    r0 = r0.gop(&r0);
                }
            }
            r0
        }
    }

    fn is_identity(&self) -> bool {
        self.identity() == *self
    }

    fn is_raw_identity(raw: &T) -> Option<bool>;
}

pub trait Group<T, GE>: std::fmt::Debug + Sized + Clone + Eq
where
    T: Eq,
    GE: GroupElement<T>,
{
    fn identity(&self) -> GE;
    fn contains(&self, val: &T) -> bool;
    fn of(&self, val: &T) -> Result<GE>;
    fn wrap(&self, val: T) -> Result<GE>;
    fn order(&self) -> Option<&BigInt>;


}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ZAddGroup {
    modulus: BigInt,
}

impl ZAddGroup {
    pub fn modulus(modulus: &BigInt) -> ZAddGroup {
        ZAddGroup {
            modulus: modulus.to_owned(),
        }
    }
}

impl Group<BigInt, ZAddElement> for ZAddGroup {
    fn contains(&self, val: &BigInt) -> bool {
        val.sign() != Sign::Minus && val < &self.modulus
    }

    fn order(&self) -> Option<&BigInt> {
        Some(&self.modulus)
    }

    fn identity(&self) -> ZAddElement {
        ZAddElement {
            value: BigInt::zero(),
            group: self.clone(),
        }
    }

    #[allow(refining_impl_trait)]
    fn of(&self, val: &BigInt) -> Result<ZAddElement> {
        if self.contains(val) {
            Ok(ZAddElement {
                value: val.to_owned(),
                group: self.clone(),
            })
        } else {
            bail!("{:?} is not a group element mod {}", val, self.modulus);
        }
    }

    fn wrap(&self, val: BigInt) -> Result<ZAddElement> {
        if self.contains(&val) {
            Ok(ZAddElement {
                value: val,
                group: self.clone(),
            })
        } else {
            bail!("{:?} is not a group element mod {}", val, self.modulus);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, GroupOps)]
pub struct ZAddElement {
    value: BigInt,
    group: ZAddGroup,
}

impl GroupElement<BigInt> for ZAddElement {
    fn identity(&self) -> Self {
        self.group.identity()
    }

    fn raw(&self) -> &BigInt {
        &self.value
    }

    fn consume(self) -> BigInt {
        self.value
    }
    fn gop(&self, rhs: &Self) -> Self {
        assert_eq!(self.group, rhs.group);
        let raw_result = self.raw() + rhs.raw();
        self.group.wrap(raw_result % &self.group.modulus).unwrap()
    }

    fn scalar_mult(&self, mult: &BigInt) -> Self {
        let result = (self.raw() * mult) % &self.group.modulus;
        self.group.wrap(result).unwrap()
    }

    fn gneg(&self) -> Self {
        if self.value.is_zero() {
            return self.clone();
        }
        let raw_result = self.raw().neg();
        self.group.wrap(raw_result + &self.group.modulus).unwrap()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.raw().to_bytes_be().1
    }

    fn is_identity(&self) -> bool {
        self.raw().is_zero()
    }
    
    fn is_raw_identity(raw: &BigInt) -> Option<bool> {
        Some(raw.is_zero())
    }
}

impl Display for ZAddElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.raw())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ZMultGroup {
    modulus: BigInt,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, GroupOps)]
pub struct ZMultElement {
    value: BigInt,
    group: ZMultGroup,
}


impl ZMultGroup {
    pub fn modulus(modulus: &BigInt) -> ZMultGroup {
        ZMultGroup {
            modulus: modulus.to_owned(),
        }
    }
}

impl Group<BigInt, ZMultElement> for ZMultGroup {
    fn identity(&self) -> ZMultElement {
        self.wrap(BigInt::one()).unwrap()
    }

    fn contains(&self, val: &BigInt) -> bool {
        val.sign() == Sign::Plus && val < &self.modulus
    }

    fn of(&self, val: &BigInt) -> Result<ZMultElement> {
        if self.contains(val) {
            Ok(ZMultElement {
                value: val.to_owned(),
                group: self.clone(),
            })
        } else {
            bail!("{:?} is not a group element", val);
        }
    }

    fn wrap(&self, val: BigInt) -> Result<ZMultElement> {
        if self.contains(&val) {
            Ok(ZMultElement {
                value: val,
                group: self.clone(),
            })
        } else {
            bail!("{:?} is not a group element", val);
        }
    }

    fn order(&self) -> Option<&BigInt> {
        todo!()
    }
}

impl Display for ZMultElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.raw())
    }
}

impl GroupElement<BigInt> for ZMultElement {
    fn raw(&self) -> &BigInt {
        &self.value
    }

    fn consume(self) -> BigInt {
        self.value
    }

    fn gop(&self, rhs: &Self) -> Self {
        assert_eq!(self.group, rhs.group);
        let raw = (self.raw() * rhs.raw()) % &self.group.modulus;
        self.group.wrap(raw).unwrap()
    }

    fn scalar_mult(&self, mult: &BigInt) -> Self {
        let result = self.raw().modpow(mult, &self.group.modulus);
        self.group.wrap(result).unwrap()
    }
    
    fn identity(&self) -> Self {
        self.group.wrap(BigInt::one()).unwrap()
    }

    fn gneg(&self) -> Self {
        if self.value.is_one() {
            return self.clone();
        }
        let modulo = &self.group.modulus;
        let (gcd, x, _) = gcd(self.raw(), modulo);
        assert!(gcd.is_one());
        match x.sign() {
            Sign::Plus => self.group.wrap(x).unwrap(),
            Sign::Minus => self.group.wrap(x + modulo).unwrap(),
            _ => panic!("Impossible result"),
        }
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.raw().to_bytes_be().1
    }
    
    fn is_identity(&self) -> bool {
        self.raw().is_one()
    }
    
    fn is_raw_identity(raw: &BigInt) -> Option<bool> {
        Some(raw.is_one())
    }    
}

pub trait Field<T, FE, GE, ME>: Group<T, FE>
where
    T: Eq,
    FE: FieldElement<T, Self, GE, ME>,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn add_group(&self) -> &impl Group<T, GE>;
    fn mult_group(&self) -> &impl Group<T, ME>;
    fn me2fe(&self, me: &ME) -> Result<FE> {
        self.of(me.raw())
    }

    fn me2fe_wrap(&self, me: ME) -> Result<FE> {
        self.wrap(me.consume())
    }

    fn ge2fe(&self, ge: &GE) -> Result<FE> {
        self.of(ge.raw())
    }

    fn ge2fe_wrap(&self, ge: GE) -> Result<FE> {
        self.wrap(ge.consume())
    }

    fn mult_identity(&self) -> FE {
        self.me2fe_wrap(self.mult_group().identity()).unwrap()
    }
}

pub trait FieldElement<T, F, GE, ME>: GroupElement<T> + FieldOps + FieldOpsOwned
where
    T: Eq,
    F: Field<T, Self, GE, ME>,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn field(&self) -> &F;

    fn mop(&self, rhs: &Self) -> Self {
        assert_eq!(self.field(), rhs.field());
        if self.is_zero() || rhs.is_zero() {
            return self.field().identity();
        }
        let raw = self.mult_element().unwrap().gop(&rhs.mult_element().unwrap());
        self.field().me2fe_wrap(raw).unwrap()
    }

    fn pow(&self, rhs: &BigInt) -> Self {
        if self.is_zero() {
            assert!(!rhs.is_zero());

            return self.clone();
        } else if self.is_one() {
            return self.clone();
        }
        self.field().me2fe_wrap(self.mult_element().unwrap().scalar_mult(rhs)).unwrap()
    }

    fn is_zero(&self) -> bool {
        self.add_element().is_identity()
    }

    fn is_one(&self) -> bool {
        if let Ok(me) = self.mult_element() {
            me.is_identity()
        } else {
            false
        }
    }

    fn mult_element(&self) -> Result<ME> {
        self.field().mult_group().of(self.raw())
    }

    fn add_element(&self) -> GE {
        self.field().add_group().of(self.raw()).unwrap()
    }

    fn m_inv(&self) -> Result<Self> {
        self.field().wrap(self.mult_element()?.gneg().consume())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ZField {
    add_group: ZAddGroup,
    mult_group: ZMultGroup,
}

impl ZField {
    pub fn modulus(modulus: &BigInt) -> Self {
        ZField {
            add_group: ZAddGroup::modulus(&modulus),
            mult_group: ZMultGroup::modulus(&modulus),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, GroupOps, FieldOps)]
pub struct GenericFieldElement<T, F, GE, ME>
where
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
{
    value: T,
    field: F,
    phantom_1: PhantomData<GE>,
    phantom_2: PhantomData<ME>,
}

impl<T, F, GE, ME> GenericFieldElement<T, F, GE, ME>
where
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>
{
    pub fn of(value: &T, field: &F) -> Self {
        Self::wrap(value.clone(), field)
    }

    pub fn wrap(value: T, field: &F) -> Self {
        let field = field.clone();
        Self { value, field, phantom_1: PhantomData::default(), phantom_2: PhantomData::default()}
    }
}

impl<T, F, GE, ME> GroupElement<T> for GenericFieldElement<T, F, GE, ME>
where
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
    F: Field<T, GenericFieldElement<T, F, GE, ME>, GE, ME>,
{
    fn consume(self) -> T {
        self.value
    }

    fn raw(&self) -> &T {
        &self.value
    }

    fn gop(&self, rhs: &Self) -> Self {
        assert_eq!(self.field, rhs.field);
        self.field
            .wrap(self.add_element().gop(&rhs.add_element()).consume()).unwrap()
    }
    
    fn identity(&self) -> Self {
        self.field.ge2fe_wrap(self.field.add_group().identity()).unwrap()
    }

    fn gneg(&self) -> Self {
        self.field.wrap(self.add_element().gneg().consume()).unwrap()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.add_element().to_bytes()
    }
    
    fn is_raw_identity(raw: &T) -> Option<bool> {
        GE::is_raw_identity(raw)
    }    
}

impl<T, F, GE, ME> FieldElement<T, F, GE, ME> for GenericFieldElement<T, F, GE, ME>
where
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
    F: Field<T, Self, GE, ME>,
{
    #[allow(refining_impl_trait)]
    fn field(&self) -> &F {
        &self.field
    }
    
    fn is_zero(&self) -> bool {
        if let Some(raw_zero) = GE::is_raw_identity(self.raw()) {
            raw_zero
        } else {
            self.add_element().is_identity()
        }
    }
    
    fn is_one(&self) -> bool {
        if let Some(raw_one) = ME::is_raw_identity(self.raw()) {
            raw_one
        } else if let Ok(me) = self.mult_element() {
            me.is_identity()
        } else {
            false
        }
    }
    
    fn mult_element(&self) -> Result<ME> {
        self.field().mult_group().of(self.raw())
    }
    
    fn add_element(&self) -> GE {
        self.field().add_group().of(self.raw()).unwrap()
    }
    
    fn m_inv(&self) -> Result<Self> {
        self.field().wrap(self.mult_element()?.gneg().consume())
    }

    
}

impl<T, F, GE, ME> Display for GenericFieldElement<T, F, GE, ME>
where
    T: Eq + Clone + Debug + Display,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
    F: Field<T, Self, GE, ME>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.raw())
    }
}
impl Group<BigInt, GenericFieldElement<BigInt, Self, ZAddElement, ZMultElement>> for ZField {
    fn identity(&self) -> GenericFieldElement<BigInt, Self, ZAddElement, ZMultElement> {
        GenericFieldElement {
            value: self.add_group.identity().consume(),
            field: self.clone(),
            phantom_1: PhantomData,
            phantom_2: PhantomData,
        }
    }

    fn contains(&self, val: &BigInt) -> bool {
        self.add_group.contains(val)
    }

    fn of(
        &self,
        val: &BigInt,
    ) -> Result<GenericFieldElement<BigInt, Self, ZAddElement, ZMultElement>> {
        let mut clamped = val % &self.add_group.modulus;
        if clamped.sign() == Sign::Minus {
            clamped += &self.add_group.modulus;
        }
        Ok(GenericFieldElement {
            value: clamped,
            field: self.clone(),
            phantom_1: PhantomData,
            phantom_2: PhantomData,
        })
    }

    fn wrap(
        &self,
        val: BigInt,
    ) -> Result<GenericFieldElement<BigInt, Self, ZAddElement, ZMultElement>> {
        let mut clamped = val % &self.add_group.modulus;
        if clamped.sign() == Sign::Minus {
            clamped += &self.add_group.modulus;
        }
        Ok(GenericFieldElement {
            value: clamped,
            field: self.clone(),
            phantom_1: PhantomData,
            phantom_2: PhantomData,
        })
    }

    fn order(&self) -> Option<&BigInt> {
        self.add_group.order()
    }
}

impl
    Field<
        BigInt,
        GenericFieldElement<BigInt, Self, ZAddElement, ZMultElement>,
        ZAddElement,
        ZMultElement,
    > for ZField
{
    fn add_group(&self) -> &impl Group<BigInt, ZAddElement> {
        &self.add_group
    }

    fn mult_group(&self) -> &impl Group<BigInt, ZMultElement> {
        &self.mult_group
    }
}

pub fn kangaroo_table<F, GE, GT>( b: &BigInt, g: &GE, n: usize, f: &F) -> (HashMap<GE, BigInt>, BigInt)
where F: Fn(&GE) -> BigInt,
        GE: GroupElement<GT> + Display + Hash,
        GT: Eq
{
    let insert_count = 1.max(n / 16384);
    let mut result = HashMap::new();
    let mut xt = BigInt::zero();
    let mut yt = g.scalar_mult(&b);
    println!("Generating first table to {}", n);
    let n_f = n as f64;
    for _i in 1..=n  {
        // println!("i = {}; yt = {}", _i, yt);
        if _i % 1000000 == 0 {
            println!("{}/{} ({})", _i, n, _i as f64 / n_f);
        }
        if _i % insert_count == 0 {
            result.insert(yt.clone(), xt.clone());
        }
        let fyt = f(&yt);
        xt += &fyt;
        yt = yt.gop(&g.scalar_mult(&fyt));
        // xt %= m;
        // yt %= m;
    }
    result.insert(yt.clone(), xt.clone());
    (result, xt)
}

pub fn kangaroo_search<F, GE, GT>(table: &HashMap<GE, BigInt>, max_xt: &BigInt, y: &GE, a: &BigInt, b: &BigInt, g: &GE, f: &F) -> Result<BigInt>
where F: Fn(&GE) -> BigInt,
    GE: GroupElement<GT> + Display + Hash,
    GT: Eq {
        let mut xw = BigInt::zero();
        let mut yw = y.clone();
        let limit = (b - a) + max_xt;
    
        println!("Doing search");
    
        while xw < limit {
            let fyw = f(&yw);
            // println!("{} <? {}, {}, {}", xw, limit, yw, fyw);
            xw += &fyw;
            yw = yw.gop(&g.scalar_mult(&fyw));
            // yw *= g.modpow(&fyw, m);
            // xw %= m;
            // yw %= m;
    
            if let Some(xt) = table.get(&yw) {
                return Ok(b + xt - xw);
            }
        }
    
        bail!("Too many iterations");
    }

pub fn pollard_kangaroo<F, GE, GT>(y: &GE, a: &BigInt, b: &BigInt, g: &GE, n: usize, f: &F) -> Result<BigInt>
    where F: Fn(&GE) -> BigInt,
        GE: GroupElement<GT> + Display + Hash,
        GT: Eq {
    let (table, max_xt) = kangaroo_table(b, g, n, f);
    kangaroo_search(&table, &max_xt, y, a, b, g, f)
}

fn gcd(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
    let mut old_r: BigInt = a.to_owned();
    let mut r: BigInt = b.to_owned();
    let mut old_s = BigInt::one();
    let mut s = BigInt::zero();
    let mut old_t = BigInt::zero();
    let mut t = BigInt::one();

    while !r.is_zero() {
        let quotient = &old_r / &r;
        let tmp = r;
        r = &old_r - &quotient * &tmp;
        old_r = tmp;

        let tmp = s;
        s = &old_s - &quotient * &tmp;
        old_s = tmp;

        let tmp = t;
        t = &old_t - &quotient * &tmp;
        old_t = tmp;
    }

    (old_r, old_s, old_t)
}

#[cfg(test)]
mod tests {
    use num::{FromPrimitive as _, Num, One};

    use super::*;

    #[test]
    fn add7() -> Result<()> {
        let three = BigInt::from(3u32);
        let six = BigInt::from(6u32);
        let seven = BigInt::from(7u32);
        let ten = BigInt::from(10u32);
        let group = ZAddGroup::modulus(&seven);
        let zero = group.identity();
        assert_eq!(zero, group.identity());
        assert_eq!(zero.gop(&zero), zero);

        let one = group.of(&BigInt::one())?;
        let two = group.of(&2u32.into())?;
        assert_ne!(zero, one);
        assert_ne!(two, one);
        assert_ne!(two, zero);
        assert_eq!(&zero + &one, one);
        assert_eq!(&one + &zero, one);
        assert_eq!(&one + &one, two);

        assert_eq!(seven, *group.order().unwrap());

        assert_eq!(zero, &one - &one);
        assert_eq!(group.of(&three)?, &ten * &one);
        assert_eq!(group.of(&six)?, &ten * &two);
        assert_eq!(zero, &BigInt::zero() * &one);
        Ok(())
    }

    #[test]
    fn mult7() -> Result<()> {
        let two = BigInt::from(2u32);
        let three = BigInt::from(3u32);
        let seven = BigInt::from(7u32);
        let group = ZMultGroup::modulus(&seven);
        let identity = group.identity();
        println!("Identity = {}", identity);
        assert_eq!(identity, group.identity());
        assert_eq!(&identity + &identity, identity);

        let two_g = group.of(&2u32.into())?;
        let three_g = group.of(&3u32.into())?;
        let four_g = group.of(&4u32.into())?;
        // let eight_g = group.of(&8u32.into())?;
        assert_ne!(two_g, identity);
        assert_eq!(&two_g + &identity, two_g);
        assert_eq!(&identity + &two_g, two_g);
        assert_eq!(&two_g + &two_g, four_g);

        assert_eq!(BigInt::one() * &two_g, two_g);
        assert_eq!(&two * &two_g, four_g);
        println!("{} + {} = {}", four_g, four_g, four_g.gop(&four_g));
        assert_eq!(two_g.scalar_mult(&three), identity);

        // assert_eq!(seven, group.order().unwrap());

        assert_eq!(identity, &identity - &identity);
        println!("2^-1 = {}", -&two_g);
        assert_eq!(identity, &two_g - &two_g);
        println!("3^-1 = {}", -&three_g);
        assert_eq!(identity, &three_g - &three_g);
        // assert_eq!(group.of(&three)?, one_g.scalar_mult(&10u32.into()));
        // assert_eq!(group.of(&six)?, two.scalar_mult(&10u32.into()));
        // assert_eq!(zero, one_g.scalar_mult(&BigInt::zero()));
        Ok(())
    }

    #[test]
    fn field7() -> Result<()> {
        let two = BigInt::from(2u32);
        let three = BigInt::from(3u32);
        let six = BigInt::from(6u32);
        let seven = BigInt::from(7u32);
        let ten = BigInt::from(10u32);
        let field = ZField::modulus(&seven);
        let zero_f = field.identity();
        assert_eq!(zero_f, field.identity());
        assert_eq!(&zero_f + &zero_f, zero_f);

        let one_f = field.of(&BigInt::one())?;
        let two_f = field.of(&2u32.into())?;
        let three_f = field.of(&3u32.into())?;
        let four_f = field.of(&4u32.into())?;
        assert_ne!(zero_f, one_f);
        assert_ne!(two_f, one_f);
        assert_ne!(two_f, zero_f);
        assert_eq!(&zero_f + &one_f, one_f);
        assert_eq!(&one_f + &zero_f, one_f);
        assert_eq!(&one_f + &one_f, two_f);

        assert_eq!(zero_f, &one_f - &one_f);
        assert_eq!(field.of(&three)?, &ten * &one_f);
        assert_eq!(field.of(&six)?, &ten * &two_f);
        assert_eq!(zero_f, BigInt::zero() * &one_f);

        // Field stuff
        assert_eq!(&two_f * &one_f, two_f);
        assert_eq!(&one_f * &two_f, two_f);
        assert_eq!(&two_f * &two_f, four_f);

        assert_eq!(two_f.pow(&BigInt::one()), two_f);
        assert_eq!(two_f.pow(&two), four_f);
        println!("{} + {} = {}", four_f, four_f, &four_f + &four_f);
        assert_eq!(one_f.pow(&three), one_f);

        // assert_eq!(seven, group.order().unwrap());

        assert_eq!(one_f, one_f.mop(&one_f.m_inv()?));
        println!("2^-1 = {}", two_f.m_inv()?);
        assert_eq!(one_f, &two_f / &two_f);
        println!("3^-1 = {}", three_f.m_inv()?);
        assert_eq!(one_f, &three_f / &three_f);
        Ok(())
    }

    #[test]
    #[ignore = "slow"]
    fn kangaroo_test() -> Result<()> {
        let p = BigInt::from_str_radix("11470374874925275658116663507232161402086650258453896274534991676898999262641581519101074740642369848233294239851519212341844337347119899874391456329785623", 10).unwrap();
        let group = ZMultGroup::modulus(&p);
        // let _q = BigUint::from_str_radix("335062023296420808191071248367701059461", 10).unwrap();
        // let _j = BigUint::from_str_radix("34233586850807404623475048381328686211071196701374230492615844865929237417097514638999377942356150481334217896204702", 10).unwrap();
        let g = BigInt::from_str_radix("622952335333961296978159266084741085889881358738459939978290179936063635566740258555167783009058567397963466103140082647486611657350811560630587013183357", 10).unwrap();
        let g = group.of(&g)?;
        let k = 14;
        let n : u64 = 4 * (0..k).map(|v| 2u64.pow(v.try_into().unwrap())).sum::<u64>() / k;
        let two = BigInt::from_u32(2).unwrap();
        let f = |y: &ZMultElement| {
            let exp = y.raw() % k;
            two.modpow(&exp, &p)
        };

        let b = BigInt::one() << 20;
        let y = BigInt::from_str_radix("7760073848032689505395005705677365876654629189298052775754597607446617558600394076764814236081991643094239886772481052254010323780165093955236429914607119", 10).unwrap();
        let y = group.of(&y)?;
        let idx = pollard_kangaroo(&y, &BigInt::zero(), &b, &g, n as usize, &f)?;
        println!("g^{} = {} =? {}", idx, g.scalar_mult(&idx), y);
        assert_eq!(g.scalar_mult(&idx), y);

        let k = 20;
        let n : u64 = 4 * (0..k).map(|v| 2u64.pow(v.try_into().unwrap())).sum::<u64>() / k;
        let two = BigInt::from_u32(2).unwrap();
        let f = |y: &ZMultElement| {
            let exp = y.raw() % k;
            two.modpow(&exp, &p)
        };

        let b = BigInt::one() << 40;
        let y = BigInt::from_str_radix("9388897478013399550694114614498790691034187453089355259602614074132918843899833277397448144245883225611726912025846772975325932794909655215329941809013733", 10).unwrap();
        let y = group.of(&y)?;
        let idx = pollard_kangaroo(&y, &BigInt::zero(), &b, &g, n as usize, &f)?;
        println!("g^{} = {} =? {}", idx, g.scalar_mult(&idx), y);
        assert_eq!(g.scalar_mult(&idx), y);
        Ok(())
    }
}
