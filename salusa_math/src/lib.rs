use std::fmt::{Debug, Display};

use anyhow::{bail, ensure, Context, Result};
use group::{Field, FieldElement, Group, GroupElement};
use num::{BigInt, BigUint, One as _, Zero as _};
use num_bigint::{RandBigInt as _, Sign, ToBigInt as _};
use rand_core::OsRng;

pub mod group;
pub mod ec;

pub fn gcd(a: &BigUint, b: &BigUint) -> (BigUint, BigInt, BigInt) {
    let mut old_r: BigInt = a.to_bigint().unwrap();
    let mut r: BigInt = b.to_bigint().unwrap();
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

    (old_r.to_biguint().unwrap(), old_s, old_t)
}

pub fn inv_mod(base: &BigUint, modulo: &BigUint) -> Result<BigUint> {
    // ensure!(modulo > base, "Modulo must be greater than base");
    let (gcd, x, _) = gcd(base, modulo);
    ensure!(gcd.is_one(), "Modulo and base are not relatively prime");
    match x.sign() {
        Sign::Plus => x.to_biguint().context("Unable to convert to BigUint"),
        Sign::Minus => (&x + modulo.to_bigint().unwrap())
            .to_biguint()
            .context("Unable to convert to BigUint"),
        _ => bail!("Impossible result"),
    }
}

pub fn rand_bigint(limit: &BigUint) -> BigUint {
    OsRng.gen_biguint_range(&BigUint::zero(), limit)
}

pub fn rand_prime(bit_size: u64) -> BigUint {
    let mut rng = OsRng;
    let two = BigUint::from(2u32);
    let mut candidate = rng.gen_biguint(bit_size);
    candidate.set_bit(0, true);
    candidate.set_bit(bit_size - 1, true);
    // println!("Trying: {}", candidate);
    while !candidate.is_prime() {
        candidate += &two;
        // println!("Trying: {}", candidate);
        // limit -= 1;
    }
    candidate
}

pub trait IsPrime {
    fn is_prime(&self) -> bool;
}

impl IsPrime for BigUint {
    fn is_prime(&self) -> bool {
        if !self.bit(0) {
            // println!("Rejecting even: {}", self);
            return false;
        }
        // println!("Am I prime? {}", self);

        let mut s = 0;
        let one = BigUint::one();
        let neg_one = self - BigUint::one();
        let neg_two = &neg_one - BigUint::one();
        let mut d: BigUint = neg_one.clone();
        while !d.bit(0) {
            s += 1;
            d >>= 1;
        }

        // println!("s = {}, d = {}", s, d);
        'WitnessLoop: for _trial in 0..5 {
            let a = rand_bigint(&neg_two);
            // println!(" trial({}) a = {}", trial, a);
            let mut x = mod_exp(&a, &d, self);
            // println!("    Base test = {}", x);
            if x == one || x == neg_one {
                continue 'WitnessLoop;
            }
            for _ in 0..s {
                x = &x * &x;
                x %= self;
                // println!("    Test = {}", x);
                if x == neg_one {
                    continue 'WitnessLoop;
                }
            }
            return false;
        }

        true
    }
}

pub fn mod_exp(base: &BigUint, exp: &BigUint, modulo: &BigUint) -> BigUint {
    // println!("mod_exp({}, {}, {})", base, exp, modulo);
    // We're not going to bother with the iterative solution and will just do the recursive (so long as it doesn't crash)
    if exp.is_zero() {
        return BigUint::one();
    } else if exp.is_one() {
        return base.clone();
    }

    let mut r0 = BigUint::one();
    let mut r1 = base % modulo;
    for i in (0..=exp.bits()).rev() {
        if exp.bit(i) {
            r0 = (r0 * &r1) % modulo;
            r1 = (&r1 * &r1) % modulo;
        } else {
            r1 = (&r0 * &r1) % modulo;
            r0 = (&r0 * &r0) % modulo;
        }
    }
    r0
}

pub fn crt(factors: &[(BigUint, BigUint)]) -> Result<BigUint> {
    let mut f_iter = factors.iter();
    let mut current = f_iter.next().context("No factors")?.clone();

    for next in f_iter {
        let (gcd, curr_m, next_m) = gcd(&current.1, &next.1);
        ensure!(gcd.is_one(), "{} and {} are not coprime", current.1, next.1);
        // println!(
        //     "GCD({},{}) -> {} = {} * {} + {} * {}",
        //     current.1, next.1, gcd, curr_m, current.1, next.1, next_m
        // );
        // println!("{}, {}", curr_m, next_m);
        let new = (&next.0 * &current.1).to_bigint().unwrap() * curr_m
            + (&current.0 * &next.1).to_bigint().unwrap() * next_m;
        let product = &current.1 * &next.1;
        let new = new % product.to_bigint().unwrap();
        let remainder = if new.sign() == Sign::Minus {
            (new + product.to_bigint().unwrap()).to_biguint().unwrap()
        } else {
            new.to_biguint().unwrap()
        };
        current = (remainder, product);
        // println!("{:?}", current);
    }

    Ok(current.0)
}

pub fn euler_criterion(n: &BigInt, k: &BigInt) -> i8 {
    if n.is_zero() {
        return 0;
    }
    let exp = (k - BigInt::one()) >> 1;
    if n.modpow(&exp, k).is_one() {
        1
    } else {
        -1
    }
}

pub fn euler_criterion_fe<T, F, FE, GE, ME>(n: &FE) -> i8
where 
T: Clone + Debug + Eq,
F: Field<T, FE, GE, ME>,
FE: FieldElement<T, F, GE, ME>,
GE: GroupElement<T>,
ME: GroupElement<T>,
 {
    if n.is_zero() {
        return 0;
    }
    let exp = (n.field().order().unwrap() - BigInt::one()) >> 1;
    if n.pow(&exp).unwrap().is_one() {
        1
    } else {
        -1
    }
}

pub fn mod_sqrt<T, F, FE, GE, ME>(n: &FE) -> Result<FE>
where 
T: Clone + Debug + Eq,
F: Field<T, FE, GE, ME>,
FE: FieldElement<T, F, GE, ME>,
GE: GroupElement<T>,
ME: GroupElement<T>,
{
    let field = n.field();
    let p = field.order().context("Order required")?;
    let p_minus = p - BigInt::one();

    let s = p_minus.trailing_zeros().context("p may not be one")?;
    let q = &p_minus >> s;

    let one_f = field.me2fe_wrap(field.mult_group().identity())?;
    let neg_one_f = one_f.gneg();
    let neg_two_f = one_f.gop(&neg_one_f);    
    let neg_four_f = neg_two_f.gop(&neg_two_f);    

        let mut z= neg_four_f;
        while euler_criterion_fe(&z) != -1 {
            z = z.gop(&one_f);
        }

        let one = BigInt::one();
        let mut m = s;
        let mut c = z.pow(&q)?;
        let mut t = n.pow(&q)?;
        let mut r = n.pow(&((&q + &BigInt::one()) >> 1))?;
        
        loop {
            // println!("m = {}, c = {:?}, t = {:?}, r = {:?}", m, c, t, r);
            if t.is_zero() {
                bail!("n is not a quadratic residue")
            }
            if t.is_one() {
                return Ok(r);
            }
            let mut i = 0;
            let mut t_pow = t.clone();
            loop {
                i += 1;
                t_pow = t_pow.mop(&t_pow);
                if t_pow.is_one() {
                    // println!("{} - {} - 1", m, i);
                    let exp = &one << (m - i - 1);
                    let b = c.pow(&exp)?;
                    // println!("b = {}", b);
                    m = i;
                    c = b.mop(&b);
                    t = t.mop(&c);
                    r = r.mop(&b);
                    break;
                }
            }
        }
}

#[cfg(test)]
mod tests {
    use group::ZField;

    use super::*;

    #[test]
    fn exp_test() {
        let base: BigUint = 3u32.into();
        let prime: BigUint = 31u32.into();
        let mut expected = BigUint::one();

        for exp in 0u32..32 {
            assert_eq!(expected, mod_exp(&base, &exp.into(), &prime));
            println!("5^{} = {} mod {}", exp, expected, prime);
            expected = (expected * &base) % &prime;
        }
    }

    #[test]
    #[ignore = "slow"]
    fn test_is_prime() {
        for _ in 0..10 {
            println!("Prime? {}", rand_prime(1024));
        }
    }

    #[test]
    fn test_gcd() {
        for _ in 0..10 {
            let a = rand_bigint(&1000000u32.into());
            let b = rand_bigint(&1000000u32.into());
            let (gcd, s, t) = gcd(&a, &b);
            let a_s = a.to_bigint().unwrap();
            let b_s = b.to_bigint().unwrap();

            println!(
                "GCD({},{}) -> {} = {} * {} + {} * {}",
                a, b, gcd, s, a_s, t, b_s
            );
            assert_eq!(gcd.to_bigint().unwrap(), s * a_s + t * b_s);
            assert!((&a % &gcd).is_zero());
            assert!((&b % &gcd).is_zero());
        }
    }

    #[test]
    fn test_invmod() -> Result<()> {
        for _ in 0..30 {
            let modulo = rand_bigint(&1000000u32.into());
            let base = rand_bigint(&modulo);
            let (gcd, _, _) = gcd(&base, &modulo);

            let inverse = inv_mod(&base, &modulo);
            if gcd.is_one() {
                let inverse = inverse.unwrap();
                println!("{} * {} % {} = 1", base, inverse, modulo);
                let maybe_one = (base * inverse) % modulo;
                assert!(maybe_one.is_one());
            } else {
                println!("{} and {} are not mutually prime", modulo, base);
                assert!(inverse.is_err());
            }
        }
        Ok(())
    }

    #[test]
    fn test_crt() -> Result<()> {
        let factors = [
            (BigUint::from(0u32), BigUint::from(3u32)),
            (BigUint::from(3u32), BigUint::from(4u32)),
            (BigUint::from(4u32), BigUint::from(5u32))
        ];

        assert_eq!(BigUint::from(3u32), crt(&factors[0..2])?);
        assert_eq!(BigUint::from(39u32), crt(&factors)?);
        Ok(())
    }

    #[test]
    fn test_mod_sqrt() -> Result<()> {
        let field = ZField::modulus(&41i32.into());
        let five = field.wrap(5i32.into())?;
        let result = mod_sqrt(&five)?;
        println!("sqrt({} mod {}) =? {}", five, field.add_group().order().unwrap(), result);
        let square = result.mop(&result);
        assert_eq!(five, square);
        Ok(())
    }
}
