macro_rules! create_group_ops {
    ($type:tt) => {
        impl std::ops::Add<$type> for $type
        {
            type Output = $type;
        
            fn add(self, rhs: $type) -> Self::Output {
                self.gop(&rhs)
            }
        }

        impl std::ops::Add<$type> for &$type
        {
            type Output = $type;
        
            fn add(self, rhs: $type) -> Self::Output {
                self.gop(&rhs)
            }
        }

        impl std::ops::Add<&$type> for $type
        {
            type Output = $type;
        
            fn add(self, rhs: &$type) -> Self::Output {
                self.gop(rhs)
            }
        }

        impl std::ops::Add<&$type> for &$type
        {
            type Output = $type;
        
            fn add(self, rhs: &$type) -> Self::Output {
                self.gop(rhs)
            }
        }

        impl std::ops::Sub<$type> for $type
        {
            type Output = $type;
        
            fn sub(self, rhs: $type) -> Self::Output {
                self.gop(&rhs.neg())
            }
        }

        impl std::ops::Sub<$type> for &$type
        {
            type Output = $type;
        
            fn sub(self, rhs: $type) -> Self::Output {
                self.gop(&rhs.neg())
            }
        }

        impl std::ops::Sub<&$type> for $type
        {
            type Output = $type;
        
            fn sub(self, rhs: &$type) -> Self::Output {
                self.gop(&-rhs)
            }
        }

        impl std::ops::Sub<&$type> for &$type
        {
            type Output = $type;
        
            fn sub(self, rhs: &$type) -> Self::Output {
                self.gop(&-rhs)
            }
        }

        impl std::ops::Neg for &$type
        {
            type Output = $type;

            fn neg(self) -> Self::Output {
                self.gneg()
            }
        }

        impl std::ops::Neg for $type
        {
            type Output = $type;

            fn neg(self) -> Self::Output {
                self.gneg()
            }
        }

        impl std::ops::Mul<$type> for num::BigInt {
            type Output = $type;

            fn mul(self, rhs: $type) -> Self::Output {
                rhs.scalar_mult(&self)
            }
        }

        impl std::ops::Mul<$type> for &num::BigInt {
            type Output = $type;

            fn mul(self, rhs: $type) -> Self::Output {
                rhs.scalar_mult(self)
            }
        }

        impl std::ops::Mul<&$type> for num::BigInt {
            type Output = $type;

            fn mul(self, rhs: &$type) -> Self::Output {
                rhs.scalar_mult(&self)
            }
        }

        impl std::ops::Mul<&$type> for &num::BigInt {
            type Output = $type;

            fn mul(self, rhs: &$type) -> Self::Output {
                rhs.scalar_mult(self)
            }
        }
    }
}

macro_rules! create_group_ops_generic {
    ($type:tt) => {
        impl  std::ops::Add<$type> for $type
        // $where
        {
            type Output = $type;
        
            fn add(self, rhs: $type) -> Self::Output {
                self.gop(&rhs)
            }
        }

        // impl<$generics> std::ops::Add<$type> for &$type
        // $where
        // {
        //     type Output = $type;
        
        //     fn add(self, rhs: $type) -> Self::Output {
        //         self.gop(&rhs)
        //     }
        // }

        // impl<$generics> std::ops::Add<&$type> for $type
        // $where
        // {
        //     type Output = $type;
        
        //     fn add(self, rhs: &$type) -> Self::Output {
        //         self.gop(rhs)
        //     }
        // }

        // impl<$generics> std::ops::Add<&$type> for &$type
        // $where
        // {
        //     type Output = $type;
        
        //     fn add(self, rhs: &$type) -> Self::Output {
        //         self.gop(rhs)
        //     }
        // }

        // impl<$generics> std::ops::Sub<$type> for $type
        // $where
        // {
        //     type Output = $type;
        
        //     fn sub(self, rhs: $type) -> Self::Output {
        //         self.gop(&rhs.neg())
        //     }
        // }

        // impl<$generics> std::ops::Sub<$type> for &$type
        // $where
        // {
        //     type Output = $type;
        
        //     fn sub(self, rhs: $type) -> Self::Output {
        //         self.gop(&rhs.neg())
        //     }
        // }

        // impl<$generics> std::ops::Sub<&$type> for $type
        // $where
        // {
        //     type Output = $type;
        
        //     fn sub(self, rhs: &$type) -> Self::Output {
        //         self.gop(&-rhs)
        //     }
        // }

        // impl<$generics> std::ops::Sub<&$type> for &$type
        // $where
        // {
        //     type Output = $type;
        
        //     fn sub(self, rhs: &$type) -> Self::Output {
        //         self.gop(&-rhs)
        //     }
        // }

        // impl<$generics> std::ops::Neg for &$type
        // $where
        // {
        //     type Output = $type;

        //     fn neg(self) -> Self::Output {
        //         self.gneg()
        //     }
        // }

        // impl<$generics> std::ops::Neg for $type
        // $where
        // {
        //     type Output = $type;

        //     fn neg(self) -> Self::Output {
        //         self.gneg()
        //     }
        // }

        // impl<$generics> std::ops::Mul<$type> for num::BigInt
        // $where
        //  {
        //     type Output = $type;

        //     fn mul(self, rhs: $type) -> Self::Output {
        //         rhs.scalar_mult(&self)
        //     }
        // }

        // impl<$generics> std::ops::Mul<$type> for &num::BigInt
        // $where
        //  {
        //     type Output = $type;

        //     fn mul(self, rhs: $type) -> Self::Output {
        //         rhs.scalar_mult(self)
        //     }
        // }

        // impl<$generics> std::ops::Mul<&$type> for num::BigInt
        // $where
        //  {
        //     type Output = $type;

        //     fn mul(self, rhs: &$type) -> Self::Output {
        //         rhs.scalar_mult(&self)
        //     }
        // }

        // impl<$generics> std::ops::Mul<&$type> for &num::BigInt
        // $where
        //  {
        //     type Output = $type;

        //     fn mul(self, rhs: &$type) -> Self::Output {
        //         rhs.scalar_mult(self)
        //     }
        // }
    }
}