use super::*;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use elliptic_curve::Field;
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::DefaultIsZeroes;

/// Represents an element $c_0 + c_1 v + c_2 v^2$ of $\mathbb{F}_{p^6} = \mathbb{F}_{p^2} / v^3 - u - 1$
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct Fp6 {
    pub(crate) c0: Fp2,
    pub(crate) c1: Fp2,
    pub(crate) c2: Fp2,
}

impl ConstantTimeEq for Fp6 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0.ct_eq(&other.c0) & self.c1.ct_eq(&other.c1) & self.c2.ct_eq(&other.c2)
    }
}

impl ConditionallySelectable for Fp6 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            c0: Fp2::conditional_select(&a.c0, &b.c0, choice),
            c1: Fp2::conditional_select(&a.c1, &b.c1, choice),
            c2: Fp2::conditional_select(&a.c2, &b.c2, choice),
        }
    }
}

impl DefaultIsZeroes for Fp6 {}

impl Eq for Fp6 {}

impl From<Fp> for Fp6 {
    fn from(f: Fp) -> Self {
        Self {
            c0: Fp2::from(f),
            c1: Fp2::ZERO,
            c2: Fp2::ZERO,
        }
    }
}

impl From<Fp2> for Fp6 {
    fn from(c0: Fp2) -> Self {
        Self {
            c0,
            c1: Fp2::ZERO,
            c2: Fp2::ZERO,
        }
    }
}

impl PartialEq for Fp6 {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl AddAssign for Fp6 {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.addition(&rhs);
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = Fp6, RHS = Fp6, OUTPUT = Fp6);

impl SubAssign for Fp6 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.subtract(&rhs);
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = Fp6, RHS = Fp6, OUTPUT = Fp6);

impl Neg for Fp6 {
    type Output = Fp6;

    fn neg(self) -> Fp6 {
        -&self
    }
}

impl Neg for &Fp6 {
    type Output = Fp6;

    fn neg(self) -> Fp6 {
        self.negate()
    }
}

impl MulAssign for Fp6 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.multiply(&rhs);
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = Fp6, RHS = Fp6, OUTPUT = Fp6);

impl Fp6 {
    pub const ZERO: Self = Self {
        c0: Fp2::ZERO,
        c1: Fp2::ZERO,
        c2: Fp2::ZERO,
    };

    pub const ONE: Self = Self {
        c0: Fp2::ONE,
        c1: Fp2::ZERO,
        c2: Fp2::ZERO,
    };

    pub fn random(mut rng: impl RngCore) -> Self {
        Self {
            c0: Fp2::random(&mut rng),
            c1: Fp2::random(&mut rng),
            c2: Fp2::random(&mut rng),
        }
    }

    pub fn mul_by_1(&self, c1: &Fp2) -> Self {
        Self {
            c0: (self.c2 * c1).mul_by_nonresidue(),
            c1: self.c0 * c1,
            c2: self.c1 * c1,
        }
    }

    pub fn mul_by_01(&self, c0: &Fp2, c1: &Fp2) -> Self {
        let a_a = self.c0 * c0;
        let b_b = self.c1 * c1;

        let t1 = (self.c2 * c1).mul_by_nonresidue() + a_a;
        let t2 = (c0 + c1) * (self.c0 + self.c1) - a_a - b_b;
        let t3 = self.c2 * c0 + b_b;

        Self {
            c0: t1,
            c1: t2,
            c2: t3,
        }
    }

    pub fn mul_by_non_residue(&self) -> Self {
        Self {
            c0: self.c2.mul_by_nonresidue(),
            c1: self.c0,
            c2: self.c1,
        }
    }

    pub fn frobenius_map(&self) -> Self {
        let c0 = self.c0.frobenius_map();
        let c1 = self.c1.frobenius_map();
        let c2 = self.c2.frobenius_map();

        // c1 = c1 * (u + 1)^((p - 1) / 3)
        // Compute c1 = c1 * (u + 1)^((p - 1) / 3)
        // For BN254, this value is a specific constant
        let c1 = c1
            * Fp2 {
                c0: Fp::from_words([
                    0x7089552b319d465,
                    0xc6695f92b50a8313,
                    0x97e83cccd117228f,
                    0x1229e4ffa8ddab81,
                ]),
                c1: Fp::ZERO,
            };

        // Compute c2 = c2 * (u + 1)^((2p - 2) / 3)
        // For BN254, this is another specific constant
        let c2 = c2
            * Fp2 {
                c0: Fp::from_words([
                    0xe4bbdd0c2936b629,
                    0xbb30f162e133bacb,
                    0x31a9d1b6f9645366,
                    0x253570bea500f8dd,
                ]),
                c1: Fp::ZERO,
            };

        Self { c0, c1, c2 }
    }

    pub fn is_zero(&self) -> Choice {
        self.c0.is_zero() & self.c1.is_zero() & self.c2.is_zero()
    }

    pub fn addition(&self, other: &Self) -> Self {
        Self {
            c0: self.c0 + other.c0,
            c1: self.c1 + other.c1,
            c2: self.c2 + other.c2,
        }
    }

    pub fn double(&self) -> Self {
        Self {
            c0: self.c0 + self.c0,
            c1: self.c1 + self.c1,
            c2: self.c2 + self.c2,
        }
    }

    pub fn subtract(&self, other: &Self) -> Self {
        Self {
            c0: self.c0 - other.c0,
            c1: self.c1 - other.c1,
            c2: self.c2 - other.c2,
        }
    }

    pub fn negate(&self) -> Self {
        Self {
            c0: -self.c0,
            c1: -self.c1,
            c2: -self.c2,
        }
    }

    pub fn multiply(&self, other: &Self) -> Self {
        // Algorithm 13 from "High-Speed Software Implementation of the Optimal Ate Pairing over Barreto-Naehrig Curves"
        // by Jean-Luc Beuchat, Jorge E. González-Díaz, Shigeo Mitsunari, Eiji Okamoto, Francisco Rodríguez-Henríquez, and Tadanori Teruya

        let a_a = self.c0 * other.c0;
        let b_b = self.c1 * other.c1;
        let c_c = self.c2 * other.c2;

        let t0 = (self.c1 + self.c2) * (other.c1 + other.c2) - b_b - c_c;
        let t1 = (self.c0 + self.c1) * (other.c0 + other.c1) - a_a - b_b;
        let t2 = (self.c0 + self.c2) * (other.c0 + other.c2) - a_a - c_c;

        Self {
            c0: a_a + t0.mul_by_nonresidue(),
            c1: t1 + c_c.mul_by_nonresidue(),
            c2: t2 + b_b,
        }
    }

    pub fn square(&self) -> Self {
        // Algorithm 16 from "High-Speed Software Implementation of the Optimal Ate Pairing over Barreto-Naehrig Curves"
        // by Jean-Luc Beuchat, Jorge E. González-Díaz, Shigeo Mitsunari, Eiji Okamoto, Francisco Rodríguez-Henríquez, and Tadanori Teruya

        let s0 = self.c0.square();
        let s1 = (self.c0 * self.c1).double();
        let s2 = (self.c0 - self.c2 + self.c2).square();
        let s3 = (self.c1 * self.c2).double();
        let s4 = self.c2.square();

        Self {
            c0: s0 + s3.mul_by_nonresidue(),
            c1: s1 + s4.mul_by_nonresidue(),
            c2: s1 + s2 + s3 - s0 - s4,
        }
    }

    pub fn invert(&self) -> CtOption<Self> {
        // Algorithm 17 from "High-Speed Software Implementation of the Optimal Ate Pairing over Barreto-Naehrig Curves"
        // by Jean-Luc Beuchat, Jorge E. González-Díaz, Shigeo Mitsunari, Eiji Okamoto, Francisco Rodríguez-Henríquez, and Tadanori Teruya

        let t0 = self.c0.square();
        let t1 = self.c1.square();
        let t2 = self.c2.square();
        let t3 = self.c0 * self.c1;
        let t4 = self.c0 * self.c2;
        let t5 = self.c1 * self.c2;

        // c0 = t0 - β * t5
        let c0 = t0 - t5.mul_by_nonresidue();
        // c1 = β * t2 - t3
        let c1 = t2.mul_by_nonresidue() - t3;
        // c2 = t1 - t4
        let c2 = t1 - t4;

        // Calculate the denominator: c0 * a0 + c1 * a1 + c2 * a2
        let t6 = self.c0 * c0 + (self.c1 * c1 + self.c2 * c2).mul_by_nonresidue();

        t6.invert().map(|t6| Self {
            c0: c0 * t6,
            c1: c1 * t6,
            c2: c2 * t6,
        })
    }
}
