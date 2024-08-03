pub mod montgomery;
pub mod weierstrass;

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use num::{BigInt, One};

    use crate::group::{Group, GroupElement, ZAddElement, ZField, ZMultElement};

    use super::{montgomery::{self, CRYPTO_PALS_MONTGOMERY, CRYPTO_PALS_MONTGOMERY_G}, weierstrass::{self, CRYPTO_PALS_WEIERSTRASS, CRYPTO_PALS_WEIERSTRASS_G}};
    #[test]
    fn equality() -> Result<()> {
        let zero_w = CRYPTO_PALS_WEIERSTRASS.identity();
        let one_w = CRYPTO_PALS_WEIERSTRASS_G.clone();
        let two_w = one_w.gop(&one_w);
        let three_w = one_w.gop(&two_w);

        assert_eq!(zero_w, one_w.scalar_mult(&BigInt::ZERO));
        assert_eq!(one_w, one_w.scalar_mult(&BigInt::one()));
        assert_eq!(two_w, one_w.scalar_mult(&BigInt::from(2i32)));
        assert_eq!(three_w, one_w.scalar_mult(&BigInt::from(3i32)));

        let zero_m = CRYPTO_PALS_MONTGOMERY.identity();
        let one_m = CRYPTO_PALS_MONTGOMERY_G.clone();
        // let two_m = one_m.gop(&one_m);
        // let three_m = one_m.gop(&two_m);
// 
        points_equal(&zero_w, &zero_m);
        assert_eq!(zero_m, one_m.scalar_mult(&BigInt::ZERO));

        points_equal(&one_w, &one_m);
        println!("{} ?+ {}", one_w, one_m);
        assert_eq!(one_m, one_m.scalar_mult(&BigInt::one()));
        points_equal(&two_w, &one_m.scalar_mult(&2.into()));
        points_equal(&three_w, &one_m.scalar_mult(&3.into()));

        let inf_w = one_w.scalar_mult(CRYPTO_PALS_WEIERSTRASS.order().unwrap());
        let inf_m = one_m.scalar_mult(CRYPTO_PALS_MONTGOMERY.order().unwrap());

        println!("{}, {}", inf_w, inf_m);
        assert!(inf_w.is_infinity());
        assert!(inf_m.is_infinity());
        Ok(())
    }

    fn points_equal(w_point: &weierstrass::EcPoint<ZField, BigInt, ZAddElement, ZMultElement>,
        m_point: &montgomery::EcPoint<ZField, BigInt, ZAddElement, ZMultElement>) {
            assert_eq!(w_point.is_infinity(), m_point.is_infinity());
            if w_point.is_infinity() {
                return;
            }
            
            let offset = w_point.curve().field().wrap(BigInt::from(-178i32)).unwrap();
            let w_x = w_point.x();
            let m_x = m_point.u();
            assert_eq!(w_x.gop(&offset), *m_x);
    }
}