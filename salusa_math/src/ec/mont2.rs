// A clean montgomery implementation with no internal dependencies to figure out where I'm making mistakes.
// This also doesn't use any generic types to keep things really simple.

use std::str::FromStr;

use lazy_static::lazy_static;
use num::{BigInt, One, Zero};

#[derive(Clone, Eq)]
struct MontgomeryPoint {
    u: BigInt,
    v: Option<BigInt>,
}

impl PartialEq for MontgomeryPoint {
    fn eq(&self, other: &Self) -> bool {
        self.u == other.u
    }
}

impl std::fmt::Display for MontgomeryPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(v) = &self.v {
            write!(f, "({}, {})", self.u, v)
        } else {
            write!(f, "({}, _)", self.u)
        }
    }
}

struct CurveParams {
    a: BigInt,
    b: BigInt,
    p: BigInt,
    order: BigInt,
    g: MontgomeryPoint,
}

lazy_static! {
    static ref CURVE_PARAMS: CurveParams = {
        CurveParams {
            a: BigInt::from(534),
            b: BigInt::one(),
            p: BigInt::from_str("233970423115425145524320034830162017933").unwrap(),
            order: BigInt::from_str("29246302889428143187362802287225875743").unwrap(),
            g: MontgomeryPoint {
                u: BigInt::from(4),
                v: None,
            },
        }
    };
    static ref TWO : BigInt = BigInt::from(2);
    static ref FOUR : BigInt = BigInt::from(4);
}

// Not constant time.... I know.....
fn cswap<T>(a: T, b: T, condition: &BigInt) -> (T, T) {
    if condition.is_one() {
        (b, a)
    } else {
        (a, b)
    }
}

fn ladder(u: &BigInt, k: &BigInt) -> BigInt {
    let (mut u2, mut w2) = (BigInt::one(), BigInt::zero());
    let (mut u3, mut w3) = (u.clone(), BigInt::one());

    for i in (0..CURVE_PARAMS.p.bits()).rev() {
        let b = BigInt::one() & (k >> i);
        let b = &b;
        (u2, u3) = cswap(u2, u3, b);
        (w2, w3) = cswap(w2, w3, b);
        (u3, w3) = ((&u2*&u3 - &w2*&w3).modpow(&TWO, &CURVE_PARAMS.p),
                   u * (&u2*&w3 - &w2*&u3).modpow(&TWO, &CURVE_PARAMS.p));
        (u2, w2) = ((u2.modpow(&TWO, &CURVE_PARAMS.p) - w2.modpow(&TWO, &CURVE_PARAMS.p)).modpow(&TWO, &CURVE_PARAMS.p),
                   4*&u2*&w2 * (u2.modpow(&TWO, &CURVE_PARAMS.p) + &CURVE_PARAMS.a*&u2*&w2 + w2.modpow(&TWO, &CURVE_PARAMS.p)));
        (u2, u3) = cswap(u2, u3, b);
        (w2, w3) = cswap(w2, w3, b);
    }
    u2 * w2.modpow(&(&CURVE_PARAMS.p - &*TWO), &CURVE_PARAMS.p)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smoke() {
        let g = CURVE_PARAMS.g.clone();
        println!("{}", g);
        println!("{}", ladder(&g.u, &CURVE_PARAMS.order));

        println!("{}", ladder(&g.u, &BigInt::one()));
        println!("{}", ladder(&g.u, &BigInt::from(2)));

    }
}