use super::*;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::DefaultIsZeroes;

/// Represents an element $c_0 + c_1 v$ of $\mathbb{F}_{p^{12}} = \mathbb{F}_{p^6} / v^2 - u$
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct Fp12 {
    pub(crate) c0: Fp6,
    pub(crate) c1: Fp6,
}

impl From<Fp> for Fp12 {
    fn from(f: Fp) -> Self {
        Self {
            c0: Fp6::from(f),
            c1: Fp6::ZERO,
        }
    }
}

impl From<Fp2> for Fp12 {
    fn from(f: Fp2) -> Self {
        Self {
            c0: Fp6::from(f),
            c1: Fp6::ZERO,
        }
    }
}

impl From<Fp6> for Fp12 {
    fn from(c0: Fp6) -> Self {
        Self { c0, c1: Fp6::ZERO }
    }
}

impl DefaultIsZeroes for Fp12 {}

impl ConstantTimeEq for Fp12 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0.ct_eq(&other.c0) & self.c1.ct_eq(&other.c1)
    }
}

impl ConditionallySelectable for Fp12 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            c0: Fp6::conditional_select(&a.c0, &b.c0, choice),
            c1: Fp6::conditional_select(&a.c1, &b.c1, choice),
        }
    }
}

impl Eq for Fp12 {}

impl PartialEq for Fp12 {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl AddAssign for Fp12 {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.addition(&rhs);
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = Fp12, RHS = Fp12, OUTPUT = Fp12);

impl SubAssign for Fp12 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.subtract(&rhs);
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = Fp12, RHS = Fp12, OUTPUT = Fp12);

impl Neg for Fp12 {
    type Output = Fp12;

    fn neg(self) -> Fp12 {
        -&self
    }
}

impl Neg for &Fp12 {
    type Output = Fp12;

    fn neg(self) -> Fp12 {
        self.negate()
    }
}

impl MulAssign for Fp12 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.multiply(&rhs);
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = Fp12, RHS = Fp12, OUTPUT = Fp12);

impl Fp12 {
    pub const ONE: Self = Self {
        c0: Fp6::ONE,
        c1: Fp6::ZERO,
    };

    pub fn is_zero(&self) -> Choice {
        self.c0.is_zero() & self.c1.is_zero()
    }

    pub fn random(mut rng: impl RngCore) -> Self {
        Self {
            c0: Fp6::random(&mut rng),
            c1: Fp6::random(&mut rng),
        }
    }

    pub fn mul_by_014(&self, c0: &Fp2, c1: &Fp2, c4: &Fp2) -> Self {
        let aa = self.c0.mul_by_01(c0, c1);
        let bb = self.c1.mul_by_1(c4);
        let o = c1 + c4;
        let c1 = self.c1 + self.c0;
        let c1 = c1.mul_by_01(c0, &o);
        let c1 = c1 - aa - bb;
        let c0 = bb.mul_by_non_residue() + aa;
        Self { c0, c1 }
    }

    pub fn conjugate(&self) -> Self {
        Self {
            c0: self.c0,
            c1: -self.c1,
        }
    }

    /// Raises this element to p.
    pub fn frobenius_map(&self) -> Self {
        // Frobenius map applies the p-power Frobenius automorphism
        // For Fp12 = Fp6[w]/(w^2 - v), where v is in Fp6
        // We need to compute (c0 + c1*w)^p = c0^p + c1^p*w^p
        // Since w^p = w * (some constant), we need to multiply c1 by this constant

        let c0 = self.c0.frobenius_map();
        let c1 = self.c1.frobenius_map();

        // c1 = c1 * (u + 1)^((p - 1) / 6)
        // Multiply c1 by the constant (u + 1)^((p - 1) / 6)
        // For BN254, this is a specific constant in Fp2
        let c1 = c1
            * Fp6::from(Fp2 {
                c0: Fp::from_words([
                    0x1904d3bf02bb0667,
                    0x790b65d7c486c4bc,
                    0x95a3c6b22a7fcfc,
                    0x4975e0cdc3905,
                ]),
                c1: Fp::from_words([
                    0x1a1c0cb0184ddc7,
                    0x1f23e0957a5bcfd,
                    0xca2e8bae6c4f4b8,
                    0x7f2f50f9a63fcce,
                ]),
            });

        Self { c0, c1 }
    }

    pub fn square(&self) -> Self {
        // Algorithm 22 from "High-Speed Software Implementation of the Optimal Ate Pairing over Barreto-Naehrig Curves"
        // by Jean-Luc Beuchat, Jorge E. González-Díaz, Shigeo Mitsunari, Eiji Okamoto, Francisco Rodríguez-Henríquez, and Tadanori Teruya

        let ab = self.c0 * self.c1;
        let c0c1 = self.c0 + self.c1;
        let c0 = (self.c1.mul_by_non_residue() + self.c0) * c0c1 - ab - ab.mul_by_non_residue();
        let c1 = ab.double();

        Self { c0, c1 }
    }

    pub fn addition(&self, other: &Self) -> Self {
        Self {
            c0: self.c0 + other.c0,
            c1: self.c1 + other.c1,
        }
    }

    pub fn subtract(&self, other: &Self) -> Self {
        Self {
            c0: self.c0 - other.c0,
            c1: self.c1 - other.c1,
        }
    }

    pub fn negate(&self) -> Self {
        Self {
            c0: -self.c0,
            c1: -self.c1,
        }
    }

    pub fn multiply(&self, other: &Self) -> Self {
        let a_a = self.c0 * other.c0;
        let b_b = self.c1 * other.c1;
        let o = other.c1 + other.c0;
        let c1 = (self.c1 + self.c0) * o - a_a - b_b;
        let c0 = b_b.mul_by_non_residue() + a_a;
        Self { c0, c1 }
    }

    pub fn invert(&self) -> CtOption<Self> {
        (self.c0.square() - self.c1.square().mul_by_non_residue())
            .invert()
            .map(|t| Self {
                c0: self.c0 * t,
                c1: self.c1 * -t,
            })
    }
}
