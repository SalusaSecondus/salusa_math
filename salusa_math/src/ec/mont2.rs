#[allow(dead_code)]
// A clean montgomery implementation with no internal dependencies to figure out where I'm making mistakes.
// This also doesn't use any generic types to keep things really simple.

use crate::{group::FieldElement, Field, Group};

use std::str::FromStr;

use lazy_static::lazy_static;
use num::{BigInt, One, Zero};

use crate::group::{GenericFieldElement, ZAddElement, ZField, ZMultElement};

type FE = GenericFieldElement<BigInt, ZField, ZAddElement, ZMultElement>;

#[derive(Clone, Eq , Debug)]
struct MontgomeryPoint {
    u: FE,
    v: Option<FE>,
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
    a: FE,
    b: FE,
    order: BigInt,
    g: MontgomeryPoint,
}

lazy_static! {
    static ref GF : ZField = ZField::modulus(&BigInt::from_str("233970423115425145524320034830162017933").unwrap());
    static ref CURVE_PARAMS: CurveParams = {
        CurveParams {
            a: GF.wrap(BigInt::from(534)).unwrap(),
            b: GF.mult_identity(),
            order: BigInt::from_str("29246302889428143187362802287225875743").unwrap(),
            g: MontgomeryPoint {
                u: GF.wrap(BigInt::from(4)).unwrap(),
                v: Some(GF.wrap(85518893674295321206118380980485522083u128.into())
                .unwrap()),
            },
        }
    };
    static ref TWO : BigInt = BigInt::from(2);
    static ref FOUR : BigInt = BigInt::from(4);
}

// Not constant time.... I know.....
fn cswap<T>(a: T, b: T, condition: bool) -> (T, T) {
    if condition {
        (b, a)
    } else {
        (a, b)
    }
}

fn ladder(point: &MontgomeryPoint, k: &BigInt) -> MontgomeryPoint {
    let u = &point.u;
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
                   &*FOUR*&u2*&w2 * (u2.pow(&TWO) + &CURVE_PARAMS.a*&u2*&w2 + w2.pow(&TWO)));

        (u2, u3) = cswap(u2, u3, b);
        (w2, w3) = cswap(w2, w3, b);

    }
    let new_u = u2 * w2.pow(&(p - &*TWO));
    MontgomeryPoint { u: new_u, v: None }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smoke() {
        let g = CURVE_PARAMS.g.clone();
        println!("{}", g);
        println!("{}", ladder(&g, &CURVE_PARAMS.order));

        println!("{}", ladder(&g, &BigInt::one()));
        println!("{}", ladder(&g, &BigInt::from(2)));

        println!("{:?}", g);
    }
}