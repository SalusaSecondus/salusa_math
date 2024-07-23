use std::{
    fmt::{Debug, Display},
    marker::PhantomData,
};

use crate::group::{Field, FieldElement, Group, GroupElement};
use anyhow::{ensure, Result};

#[derive(Debug, Clone, PartialEq, Eq)]
struct AffinePoint<FE>
where
    FE: Clone + Debug,
{
    x: FE,
    y: FE,
    inf: bool,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, GE, ME>,
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
    FE: Eq + Clone + FieldElement<T, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.affine.fmt(f)
    }
}

impl<F, FE, T, GE, ME> GroupElement<AffinePoint<FE>> for EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, GE, ME>,
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
        assert_eq!(self.curve, rhs.curve);
        if self.is_infinity() {
            return rhs.clone();
        }
        if rhs.is_infinity() {
            return self.clone();
        }

        if self == &rhs.neg() {
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
            let top = y2.gop(&y1.neg());
            let bottom = x2.gop(&x1.neg());
            let bottom_inv = bottom.m_inv().unwrap();
            m = top.mop(&bottom_inv);
        }
        
        let m_sq = m.mop(&m);

        let x3 = m_sq.gop(&x1.neg()).gop(&x2.neg());
        let x1_m_x3 = x1.gop(&x3.neg());
        let y3 = m.mop(&x1_m_x3).gop(&y1.neg());

        let affine = AffinePoint {
            x: x3, y: y3, inf: false
        };
        EcPoint { affine, curve: self.curve.clone()}
    }

    fn neg(&self) -> Self {
        if self.is_infinity() {
            return self.clone();
        }
        let neg_y = self.affine.y.neg();
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
}

impl<F, FE, T, GE, ME> EcPoint<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, GE, ME>,
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
    FE: Eq + Clone + FieldElement<T, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    a: FE,
    b: FE,
    field: F,
    _pt: PhantomData<T>,
    _pge: PhantomData<GE>,
    _pme: PhantomData<ME>,
}

impl<F, FE, T, GE, ME> Group<AffinePoint<FE>, EcPoint<F, FE, T, GE, ME>>
    for EcCurve<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, GE, ME>,
    T: Eq + Clone + Debug,
    GE: GroupElement<T>,
    ME: GroupElement<T>,
{
    fn identity(&self) -> EcPoint<F, FE, T, GE, ME> {
        let zero = self.field.identity();
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

        let y_squared = val.y.mop(&val.y);
        let x_squared = val.x.mop(&val.x);
        let x_cubed = val.x.mop(&x_squared);

        let a_x = self.a.mop(&val.x);
        let rhs = x_cubed.gop(&a_x).gop(&self.b);

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

    fn order(&self) -> Option<num::BigInt> {
        todo!()
    }
}

impl<F, FE, T, GE, ME> Display for EcCurve<F, FE, T, GE, ME>
where
    F: Field<T, FE, GE, ME>,
    FE: Eq + Clone + FieldElement<T, GE, ME> + Display,
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
    use super::*;
}
