use crate::inner_types::{
    fp::{Fp, FpModulus, MODULUS_M1_DIV2},
    G2Projective,
};

use core::{
    borrow::Borrow,
    fmt::{self, Display, Formatter},
    iter::{Product, Sum},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use elliptic_curve::{
    bigint::{modular::constant_mod::ResidueParams, U256},
    generic_array::GenericArray,
    hash2curve::{ExpandMsg, Expander, FromOkm, MapToCurve, Sgn0},
    scalar::IsHigh,
    Field,
};
use rand_core::RngCore;
use subtle::{Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::DefaultIsZeroes;

/// A point in the multiplicative group of order p^2
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct Fp2 {
    /// The `a` portion
    pub c0: Fp,
    /// The `b` portion
    pub c1: Fp,
}

impl DefaultIsZeroes for Fp2 {}

impl AddAssign for Fp2 {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.addition(&rhs);
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, += , LHS = Fp2, RHS = Fp2, OUTPUT = Fp2);

impl SubAssign for Fp2 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.subtract(&rhs);
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -= , LHS = Fp2, RHS = Fp2, OUTPUT = Fp2);

impl MulAssign for Fp2 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.multiply(&rhs);
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *= , LHS = Fp2, RHS = Fp2, OUTPUT = Fp2);

impl MulAssign<Fp> for Fp2 {
    fn mul_assign(&mut self, rhs: Fp) {
        self.c0 *= rhs;
        self.c1 *= rhs;
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *= , LHS = Fp2, RHS = Fp, OUTPUT = Fp2);

impl Neg for Fp2 {
    type Output = Self;

    fn neg(self) -> Self {
        self.negate()
    }
}

impl Neg for &Fp2 {
    type Output = Fp2;

    fn neg(self) -> Fp2 {
        -*self
    }
}

impl Display for Fp2 {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Fp2({} + {} * u)", self.c0, self.c1)
    }
}

impl IsHigh for Fp2 {
    fn is_high(&self) -> Choice {
        self.c1.is_high() | self.c1.is_high() & self.c0.is_high()
    }
}

impl Sgn0 for Fp2 {
    fn sgn0(&self) -> Choice {
        self.c0.sgn0() | self.c0.is_zero() & self.c1.sgn0()
    }
}

impl ConstantTimeEq for Fp2 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0.ct_eq(&other.c0) & self.c1.ct_eq(&other.c1)
    }
}

impl Eq for Fp2 {}

impl PartialEq for Fp2 {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl ConditionallySelectable for Fp2 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            c0: Fp::conditional_select(&a.c0, &b.c0, choice),
            c1: Fp::conditional_select(&a.c1, &b.c1, choice),
        }
    }
}

impl<T: Borrow<Fp2>> Sum<T> for Fp2 {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x.borrow())
    }
}

impl<T: Borrow<Fp2>> Product<T> for Fp2 {
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, x| acc * x.borrow())
    }
}

impl Field for Fp2 {
    const ZERO: Self = Self {
        c0: Fp::ZERO,
        c1: Fp::ZERO,
    };
    const ONE: Self = Self {
        c0: Fp::ONE,
        c1: Fp::ZERO,
    };

    fn random(mut rng: impl RngCore) -> Self {
        Self {
            c0: Fp::random(&mut rng),
            c1: Fp::random(&mut rng),
        }
    }

    fn square(&self) -> Self {
        self.square()
    }

    fn double(&self) -> Self {
        self.double()
    }

    fn invert(&self) -> CtOption<Self> {
        (self.c0.square() + self.c1.square()).invert().map(|t| Fp2 {
            c0: self.c0 * t,
            c1: self.c1 * -t,
        })
    }

    fn sqrt_ratio(_num: &Self, _div: &Self) -> (Choice, Self) {
        unimplemented!()
    }

    fn sqrt(&self) -> CtOption<Self> {
        // Algorithm 9, https://eprint.iacr.org/2012/685.pdf
        // with constant time modifications.

        CtOption::new(Fp2::ZERO, self.is_zero()).or_else(|| {
            // a1 = self^((p - 3) / 4)
            let a1 = self.pow_vartime(
                FpModulus::MODULUS
                    .wrapping_sub(&U256::from_u8(3))
                    .shr_vartime(2)
                    .as_words(),
            );

            // alpha = a1^2 * self = self^((p - 3) / 2 + 1) = self^((p - 1) / 2)
            let alpha = a1.square() * self;

            // x0 = self^((p + 1) / 4)
            let x0 = a1 * self;

            // In the event that alpha = -1, the element is order p - 1 and so
            // we're just trying to get the square of an element of the subfield
            // Fp. This is given by x0 * u, since u = sqrt(-1). Since the element
            // x0 = a + bu has b = 0, the solution is therefore au.
            CtOption::new(
                Fp2 {
                    c0: -x0.c1,
                    c1: x0.c0,
                },
                alpha.ct_eq(&Fp2::ONE.neg()),
            )
            // Otherwise, the correct solution is (1 + alpha)^((q - 1) // 2) * x0
            .or_else(|| {
                CtOption::new(
                    (alpha + Fp2::ONE).pow_vartime(
                        FpModulus::MODULUS
                            .wrapping_sub(&U256::ONE)
                            .shr_vartime(1)
                            .as_words(),
                    ) * x0,
                    Choice::from(1),
                )
            })
            // Only return the result if it's really the square root (and so
            // self is actually quadratic nonresidue)
            .and_then(|sqrt| CtOption::new(sqrt, sqrt.square().ct_eq(self)))
        })
    }
}

impl MapToCurve for Fp2 {
    type Output = G2Projective;

    fn map_to_curve(&self) -> Self::Output {
        //c1 = g(Z)
        //c2 = -Z / 2
        //c3 = sqrt(-g(Z) * (3 * Z² + 4 * A))     # sgn0(c3) MUST equal 0
        //c4 = -4 * g(Z) / (3 * Z² + 4 * A)

        const Z: Fp2 = Fp2::ONE;
        const C1: Fp2 = Fp2 {
            c0: Fp::from_be_hex("2b149d40ceb8aaae81be18991be06ac3b5b4c5e559dbefa33267e6dc24a138e6"),
            c1: Fp::from_be_hex("009713b03af0fed4cd2cafadeed8fdf4a74fa084e52d1852e4a2bd0685c315d2"),
        };
        const C2: Fp2 = Fp2 {
            c0: Fp::from_be_hex("183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea3"),
            c1: Fp::ZERO,
        };

        const C3: Fp2 = Fp2 {
            c0: Fp::from_be_hex("29fd332ab7260112b801fa95b21af64e2e6da55f90a3e510fcbe57377b5ca1ec"),
            c1: Fp::from_be_hex("303d1eff1426764bf8408aee24ba0b865e76f77b1267a846b1e9154d01565034"),
        };

        const C4: Fp2 = Fp2 {
            c0: Fp::from_be_hex("17365bbe63b1d2078632fe0eb2ac5a41b4e6a9c08b98676721010b008d4eaf99"),
            c1: Fp::from_be_hex("0f57ffe5fc79e19cd689d7aa4209cad8fe164d7f4694786b388732a995d03755"),
        };

        let mut tv1 = self.square(); //    1.  tv1 = u²
        tv1 *= C1; //    2.  tv1 = tv1 * c1
        let tv2 = Self::ONE + tv1; //    3.  tv2 = 1 + tv1
        tv1 = Self::ONE - tv1; //    4.  tv1 = 1 - tv1
        let mut tv3 = tv1 * tv2; //    5.  tv3 = tv1 * tv2
        tv3 = tv3.invert().expect("non zero"); //    6.  tv3 = inv0(tv3)
        let mut tv4 = self * tv1; //    7.  tv4 = u * tv1
        tv4 *= tv3; //    8.  tv4 = tv4 * tv3
        tv4 *= C3; //    9.  tv4 = tv4 * c3
        let x1 = C2 - tv4; //    10.  x1 = c2 - tv4
        let mut gx1 = x1.square(); //    11. gx1 = x1²
                                   //    12. gx1 = gx1 + A     All curves in gnark-crypto have A=0 (j-invariant=0). It is crucial to include this step if the curve has nonzero A coefficient.
        gx1 *= x1; //    13. gx1 = gx1 * x1
        gx1 += Fp2::B; //    14. gx1 = gx1 + B
        let x2 = C2 + tv4; //    15.  x2 = c2 + tv4
        let mut gx2 = x2.square(); //    16. gx2 = x2²
                                   //    17. gx2 = gx2 + A (see 12.)
        gx2 *= x2; //    18. gx2 = gx2 * x2
        gx2 += Fp2::B; //    19. gx2 = gx2 + B
        let mut x3 = tv2.square(); //    20.  x3 = tv2²
        x3 *= tv3; //    21.  x3 = x3 * tv3
        x3 = x3.square(); //    22.  x3 = x3²
        x3 *= C4; //    23.  x3 = x3 * c4
        x3 += Z; //    24.  x3 = x3 + Z
        let e1 = gx1.is_square();
        let mut x = Fp2::conditional_select(&x3, &x1, e1); //    25.   x = CMOV(x3, x1, e1)   # x = x1 if gx1 is square, else x = x3
        x.conditional_assign(&x2, gx2.is_square() & !e1); //    26.   x = CMOV(x, x2, e2)    # x = x2 if gx2 is square and gx1 is not
        let mut gx = x.square(); //    27.  gx = x²
                                 //    28.  gx = gx + A
        gx *= x; //    29.  gx = gx * x
        gx += Fp2::B; //    30.  gx = gx + B
        let mut y = gx.sqrt().expect("to be a square"); //    31.   y = sqrt(gx)
        let e3 = self.sgn0() ^ y.sgn0(); // 32.  e3 = sgn0(u) == sgn0(y)
        y.conditional_negate(e3); //    33.   y = CMOV(-y, y, e3)       # Select correct sign of y

        G2Projective { x, y, z: Fp2::ONE }
    }
}

impl From<Fp> for Fp2 {
    fn from(f: Fp) -> Self {
        Self {
            c0: f,
            c1: Fp::ZERO,
        }
    }
}

impl Fp2 {
    /// The multiplicative identity element
    pub const ONE: Self = Self {
        c0: Fp::ONE,
        c1: Fp::ZERO,
    };

    pub const GEN_X: Self = Self {
        c0: Fp::from_montgomery([
            0x8e83b5d102bc2026,
            0xdceb1935497b0172,
            0xfbb8264797811adf,
            0x19573841af96503b,
        ]),
        c1: Fp::from_montgomery([
            0xafb4737da84c6140,
            0x6043dd5a5802d8c4,
            0x09e950fc52a02f86,
            0x14fef0833aea7b6b,
        ]),
    };

    pub const GEN_Y: Self = Self {
        c0: Fp::from_montgomery([
            0x619dfa9d886be9f6,
            0xfe7fd297f59e9b78,
            0xff9e1a62231b7dfe,
            0x28fd7eebae9e4206,
        ]),
        c1: Fp::from_montgomery([
            0x64095b56c71856ee,
            0xdc57f922327d3cbb,
            0x55f935be33351076,
            0x0da4a0e693fd6482,
        ]),
    };

    pub const B: Self = Self {
        c0: Fp::from_montgomery([
            0x3bf938e377b802a8,
            0x020b1b273633535d,
            0x26b7edf049755260,
            0x2514c6324384a86d,
        ]),
        c1: Fp::from_montgomery([
            0x38e7ecccd1dcff67,
            0x65f0b37d93ce0d3e,
            0xd749d0dd22ac00aa,
            0x0141b9ce4a688d4d,
        ]),
    };

    pub const B3: Self = Self::B.double().addition(&Self::B);

    pub fn is_one(&self) -> Choice {
        self.c0.is_one() & self.c1.is_zero()
    }

    pub const fn addition(&self, rhs: &Self) -> Self {
        Self {
            c0: self.c0.addition(&rhs.c0),
            c1: self.c1.addition(&rhs.c1),
        }
    }

    pub const fn double(&self) -> Self {
        Self {
            c0: self.c0.double(),
            c1: self.c1.double(),
        }
    }

    pub const fn subtract(&self, rhs: &Self) -> Self {
        Self {
            c0: self.c0.subtract(&rhs.c0),
            c1: self.c1.subtract(&rhs.c1),
        }
    }

    pub const fn multiply(&self, rhs: &Self) -> Self {
        // a = c0 * c1 - c1 * c1
        // b = c0 * c1 + c1 * c0
        Self {
            c0: self
                .c0
                .multiply(&rhs.c0)
                .subtract(&self.c1.multiply(&rhs.c1)),
            c1: self
                .c0
                .multiply(&rhs.c1)
                .addition(&self.c1.multiply(&rhs.c0)),
        }
    }

    pub const fn square(&self) -> Self {
        // a = 2 * (c0 + c1)(c0 - c1)
        // b = 2 * c0 * c1
        Self {
            c0: self
                .c0
                .addition(&self.c1)
                .multiply(&self.c0.subtract(&self.c1)),
            c1: self.c0.multiply(&self.c1).double(),
        }
    }

    pub const fn negate(&self) -> Self {
        Self {
            c0: self.c0.negate(),
            c1: self.c1.negate(),
        }
    }

    pub const fn mul_by_3b(&self) -> Self {
        self.multiply(&Self::B3)
    }

    pub const fn mul_by_nonresidue(&self) -> Self {
        Self {
            c0: self.c0.subtract(&self.c1),
            c1: self.c0.addition(&self.c1),
        }
    }

    /// True if this element is the additive identity
    pub fn is_zero(&self) -> Choice {
        self.c0.is_zero() & self.c1.is_zero()
    }

    /// Conjugation of this element
    pub const fn conjugate(&self) -> Self {
        Self {
            c0: self.c0,
            c1: self.c1.negate(),
        }
    }

    pub const fn frobenius_map(&self) -> Self {
        self.conjugate()
    }

    /// Returns true whenever `self` is a square in the field
    /// using Euler's criterion.
    pub fn is_square(&self) -> Choice {
        // 1. tv1 = x_1^2
        // 2. tv2 = I * x_2
        // 3. tv2 = tv2^2
        // 4. tv1 = tv1 - tv2
        // 5. tv1 = tv1^c1
        // 6.  e1 = tv1 != -1          # Note: -1 in F

        // Since I^2 = -1, this is x1^2 + x2^2
        let tv1 = (self.c0.square() + self.c1.square()).pow(MODULUS_M1_DIV2.as_words());
        tv1.is_zero() | tv1.ct_eq(&Fp::ONE)
    }

    pub fn from_random_bytes(okm: &[u8]) -> Self {
        let c0 = GenericArray::clone_from_slice(&okm[..48]);
        let c1 = GenericArray::clone_from_slice(&okm[48..]);
        Self {
            c0: Fp::from_okm(&c0),
            c1: Fp::from_okm(&c1),
        }
    }

    pub fn hash<X>(msg: &[u8], dst: &[u8]) -> [Self; 2]
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let dst = [dst];
        let mut random_bytes = [0u8; 192];
        let mut expander =
            X::expand_message(&[msg], &dst, random_bytes.len()).expect("To expand message");
        expander.fill_bytes(&mut random_bytes);
        [
            Fp2::from_random_bytes(&random_bytes[..96]),
            Fp2::from_random_bytes(&random_bytes[96..]),
        ]
    }

    pub fn encode<X>(msg: &[u8], dst: &[u8]) -> Self
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let dst = [dst];
        let mut random_bytes = [0u8; 96];
        let mut expander =
            X::expand_message(&[msg], &dst, random_bytes.len()).expect("To expand message");
        expander.fill_bytes(&mut random_bytes);
        Fp2::from_random_bytes(&random_bytes)
    }
}
