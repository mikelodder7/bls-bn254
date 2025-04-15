use super::*;

use crate::Bn254Error;
use core::ops::{Deref, DerefMut, Index};
use core::{
    borrow::Borrow,
    fmt::{self, Display, Formatter, LowerHex, UpperHex},
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use elliptic_curve::{group::GroupEncoding, Field, Group, PrimeField};
use pairing::{Engine, MultiMillerLoop, PairingCurveAffine};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::DefaultIsZeroes;

/// Represents results of a Miller Loop, one of the most expensive operations
/// of the pairing function. `MillerLoopResult` cannot be compared with each other
/// until `.final_exponentiation()` is called, which is also expensive.
#[derive(Copy, Clone, Debug)]
pub struct MillerLoopResult(pub(crate) Fp12);

impl Default for MillerLoopResult {
    fn default() -> Self {
        Self(Fp12::ONE)
    }
}

impl DefaultIsZeroes for MillerLoopResult {}

impl ConditionallySelectable for MillerLoopResult {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(Fp12::conditional_select(&a.0, &b.0, choice))
    }
}

impl AddAssign for MillerLoopResult {
    fn add_assign(&mut self, rhs: Self) {
        self.0 *= rhs.0;
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = MillerLoopResult, RHS = MillerLoopResult, OUTPUT = MillerLoopResult);

impl MillerLoopResult {
    /// This performs a "final exponentiation" routine to convert the result
    /// of a Miller loop into an element of `Gt` with help of efficient squaring
    /// operation in the so-called `cyclotomic subgroup` of `Fq6` so that
    /// it can be compared with other elements of `Gt`.
    pub fn final_exponentiation(&self) -> Gt {
        #[must_use]
        fn fp4_square(a: Fp2, b: Fp2) -> (Fp2, Fp2) {
            let t0 = a.square();
            let t1 = b.square();
            let mut t2 = t1.mul_by_nonresidue();
            let c0 = t2 + t0;
            t2 = a + b;
            t2 = t2.square();
            t2 -= t0;
            let c1 = t2 - t1;

            (c0, c1)
        }
        // Adaptation of Algorithm 5.5.4, Guide to Pairing-Based Cryptography
        // Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions
        // https://eprint.iacr.org/2009/565.pdf
        #[must_use]
        fn cyclotomic_square(f: Fp12) -> Fp12 {
            let mut z0 = f.c0.c0;
            let mut z4 = f.c0.c1;
            let mut z3 = f.c0.c2;
            let mut z2 = f.c1.c0;
            let mut z1 = f.c1.c1;
            let mut z5 = f.c1.c2;

            let (t0, t1) = fp4_square(z0, z1);

            // For A
            z0 = t0 - z0;
            z0 = z0 + z0 + t0;

            z1 = t1 + z1;
            z1 = z1 + z1 + t1;

            let (mut t0, t1) = fp4_square(z2, z3);
            let (t2, t3) = fp4_square(z4, z5);

            // For C
            z4 = t0 - z4;
            z4 = z4 + z4 + t0;

            z5 = t1 + z5;
            z5 = z5 + z5 + t1;

            // For B
            t0 = t3.mul_by_nonresidue();
            z2 = t0 + z2;
            z2 = z2 + z2 + t0;

            z3 = t2 - z3;
            z3 = z3 + z3 + t2;

            Fp12 {
                c0: Fp6 {
                    c0: z0,
                    c1: z4,
                    c2: z3,
                },
                c1: Fp6 {
                    c0: z2,
                    c1: z1,
                    c2: z5,
                },
            }
        }
        #[must_use]
        fn cycolotomic_exp(f: Fp12) -> Fp12 {
            let x = X;
            let mut tmp = Fp12::ONE;
            let mut found_one = false;
            for i in (0..64).rev().map(|b| ((x >> b) & 1) == 1) {
                if found_one {
                    tmp = cyclotomic_square(tmp)
                } else {
                    found_one = i;
                }

                if i {
                    tmp *= f;
                }
            }

            tmp.conjugate()
        }

        let mut f = self.0;
        let mut t0 = f
            .frobenius_map()
            .frobenius_map()
            .frobenius_map()
            .frobenius_map()
            .frobenius_map()
            .frobenius_map();
        Gt(f.invert()
            .map(|mut t1| {
                let mut t2 = t0 * t1;
                t1 = t2;
                t2 = t2.frobenius_map().frobenius_map();
                t2 *= t1;
                t1 = cyclotomic_square(t2).conjugate();
                let mut t3 = cycolotomic_exp(t2);
                let mut t4 = cyclotomic_square(t3);
                let mut t5 = t1 * t3;
                t1 = cycolotomic_exp(t5);
                t0 = cycolotomic_exp(t1);
                let mut t6 = cycolotomic_exp(t0);
                t6 *= t4;
                t4 = cycolotomic_exp(t6);
                t5 = t5.conjugate();
                t4 *= t5 * t2;
                t5 = t2.conjugate();
                t1 *= t2;
                t1 = t1.frobenius_map().frobenius_map().frobenius_map();
                t6 *= t5;
                t6 = t6.frobenius_map();
                t3 *= t0;
                t3 = t3.frobenius_map().frobenius_map();
                t3 *= t1;
                t3 *= t6;
                f = t3 * t4;

                f
            })
            // We unwrap() because `MillerLoopResult` can only be constructed
            // by a function within this crate, and we uphold the invariant
            // that the enclosed value is nonzero.
            .unwrap())
    }
}

/// Represents an element of the target group $\mathbb{G}_T$ as a byte array.
#[derive(Copy, Clone, Debug)]
pub struct GtRepr([u8; Gt::BYTES]);

impl Default for GtRepr {
    fn default() -> Self {
        Self([0u8; Gt::BYTES])
    }
}

impl AsRef<[u8]> for GtRepr {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for GtRepr {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl Deref for GtRepr {
    type Target = [u8; Gt::BYTES];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for GtRepr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Represents an element of the target group $\mathbb{G}_T$.
///
/// Written multiplicatively, but written additively to keep code consistent.
#[derive(Copy, Clone, Debug)]
pub struct Gt(pub(crate) Fp12);

impl Default for Gt {
    fn default() -> Self {
        Self(Fp12::ONE)
    }
}

impl DefaultIsZeroes for Gt {}

impl ConstantTimeEq for Gt {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl ConditionallySelectable for Gt {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(Fp12::conditional_select(&a.0, &b.0, choice))
    }
}

impl Eq for Gt {}

impl PartialEq for Gt {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl Display for Gt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:x}", self)
    }
}

impl LowerHex for Gt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let bytes = self.to_repr();
        for byte in &bytes {
            write!(f, "{:02x}", byte)?;
        }
        Ok(())
    }
}

impl UpperHex for Gt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let bytes = self.to_repr();
        for byte in &bytes {
            write!(f, "{:02X}", byte)?;
        }
        Ok(())
    }
}

impl AddAssign for Gt {
    fn add_assign(&mut self, rhs: Self) {
        self.0 *= rhs.0;
    }
}

impl Neg for Gt {
    type Output = Gt;

    fn neg(self) -> Self::Output {
        Self(self.0.conjugate())
    }
}

impl Neg for &Gt {
    type Output = Gt;

    fn neg(self) -> Self::Output {
        -*self
    }
}

impl SubAssign for Gt {
    fn sub_assign(&mut self, rhs: Self) {
        *self += -rhs;
    }
}

impl MulAssign for Gt {
    fn mul_assign(&mut self, rhs: Self) {
        self.0 *= rhs.0;
    }
}

impl MulAssign<Scalar> for Gt {
    fn mul_assign(&mut self, rhs: Scalar) {
        *self = self.mul_by_scalar(&rhs);
    }
}

impl Mul<Gt> for Scalar {
    type Output = Gt;

    fn mul(self, rhs: Gt) -> Self::Output {
        rhs.mul_by_scalar(&self)
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = Gt, RHS = Gt, OUTPUT = Gt);
ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = Gt, RHS = Gt, OUTPUT = Gt);
ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = Gt, RHS = Gt, OUTPUT = Gt);
ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = Gt, RHS = Scalar, OUTPUT = Gt);
ops_impl!(Mul, mul, *, LHS = Scalar, RHS = Gt, OUTPUT = Gt);

impl<T: Borrow<Gt>> Sum<T> for Gt {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::default(), |acc, item| acc + item.borrow())
    }
}

bytes_impl!(Gt, |g: &Gt| g.to_repr(), |bytes: &[u8]| {
    let repr = <[u8; Gt::BYTES]>::try_from(bytes).map_err(|_| Bn254Error::InvalidGtBytes)?;
    Option::<Gt>::from(Gt::from_repr(&repr)).ok_or(Bn254Error::InvalidGtBytes)
});

serde_impl!(
    Gt,
    |g: &Gt| g.to_repr(),
    |bytes: &[u8; Gt::BYTES]| {
        Option::<Gt>::from(Gt::from_repr(bytes)).ok_or(serde::de::Error::custom("Invalid bytes"))
    },
    Gt::BYTES
);

impl GroupEncoding for Gt {
    type Repr = GtRepr;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_repr(&bytes.0)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_repr(&bytes.0)
    }

    fn to_bytes(&self) -> Self::Repr {
        GtRepr(self.to_repr())
    }
}

impl Group for Gt {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        loop {
            let inner = Fp12::random(&mut rng);

            // Not all elements of Fp12 are elements of the prime-order multiplicative
            // subgroup. We run the random element through final_exponentiation to obtain
            // a valid element, which requires that it is non-zero.
            if !bool::from(inner.is_zero()) {
                return MillerLoopResult(inner).final_exponentiation();
            }
        }
    }

    fn identity() -> Self {
        Self::IDENTITY
    }

    fn generator() -> Self {
        // pairing(G1Affine::generator(), G2Affine::generator())
        Self(Fp12 {
            c0: Fp6 {
                c0: Fp2 {
                    c0: Fp::from_montgomery([
                        0x1fcc7530122aa420,
                        0xca59cdbc8c5ff43e,
                        0xc93fa82014778dee,
                        0x11cf2d9200e03b08,
                    ]),
                    c1: Fp::from_montgomery([
                        0x3e33a609372036c3,
                        0x40e8645147255722,
                        0xc4e03ffc78ecd954,
                        0x0fa63dfa64b91051,
                    ]),
                },
                c1: Fp2 {
                    c0: Fp::from_montgomery([
                        0xf77a17441a089e93,
                        0xdd5322f7e2e0e334,
                        0xbc963cc2d97a001f,
                        0x1e334b1238c8a847,
                    ]),
                    c1: Fp::from_montgomery([
                        0x930a23244d8891b2,
                        0x0a397e85dfeaa687,
                        0x8a93ff66badc3b5d,
                        0x02f1df15d6bf5637,
                    ]),
                },
                c2: Fp2 {
                    c0: Fp::from_montgomery([
                        0x188f447abf8e4663,
                        0xa396877ff7ca1341,
                        0x755a795b6396b12b,
                        0x17d1a276e4d2a0dd,
                    ]),
                    c1: Fp::from_montgomery([
                        0x39a474d59cb4e31b,
                        0xff0c322c63660a70,
                        0xf376db20f55ed1af,
                        0x2ce8d190ecae3fa8,
                    ]),
                },
            },
            c1: Fp6 {
                c0: Fp2 {
                    c0: Fp::from_montgomery([
                        0x5c44e5f4481f3d19,
                        0x547206c23aa70c9f,
                        0x226de9d63984b249,
                        0x0aa81430194ce2e7,
                    ]),
                    c1: Fp::from_montgomery([
                        0x502d431149c7c03a,
                        0x01638583759a883a,
                        0x2ed65bc6aa0e5a53,
                        0x0a27433f267de2ea,
                    ]),
                },
                c1: Fp2 {
                    c0: Fp::from_montgomery([
                        0xacfbc67a8013d453,
                        0x7fdf5a73aa1b8ed1,
                        0x5ce33a1eb291f303,
                        0x284ddcd79829e5a5,
                    ]),
                    c1: Fp::from_montgomery([
                        0x879f8683107b416d,
                        0x3f32a44f61ea80b7,
                        0x9eb4b3fc7b8171ce,
                        0x0540dec60612ac8f,
                    ]),
                },
                c2: Fp2 {
                    c0: Fp::from_montgomery([
                        0xfc326c1a911c4a06,
                        0x564f07561f8331cc,
                        0xba77058a1942ab0d,
                        0x2e21d3f799d9eed6,
                    ]),
                    c1: Fp::from_montgomery([
                        0x9bf1141e95e072f6,
                        0xf688c6024990ddfb,
                        0xdd1995c74032bfeb,
                        0x15490b65495c089b,
                    ]),
                },
            },
        })
    }

    fn is_identity(&self) -> Choice {
        self.ct_eq(&Self::IDENTITY)
    }

    fn double(&self) -> Self {
        self.double()
    }
}

impl Gt {
    pub const IDENTITY: Self = Self(Fp12::ONE);

    pub const BYTES: usize = 384;

    pub fn double(&self) -> Self {
        Self(self.0.square())
    }

    pub fn to_repr(self) -> [u8; Self::BYTES] {
        let mut bytes = [0u8; Self::BYTES];
        bytes[0..32].copy_from_slice(&self.0.c0.c0.c0.to_repr());
        bytes[32..64].copy_from_slice(&self.0.c0.c0.c1.to_repr());
        bytes[64..96].copy_from_slice(&self.0.c0.c1.c0.to_repr());
        bytes[96..128].copy_from_slice(&self.0.c0.c1.c1.to_repr());
        bytes[128..160].copy_from_slice(&self.0.c0.c2.c0.to_repr());
        bytes[160..192].copy_from_slice(&self.0.c0.c2.c1.to_repr());
        bytes[192..224].copy_from_slice(&self.0.c1.c0.c0.to_repr());
        bytes[224..256].copy_from_slice(&self.0.c1.c0.c1.to_repr());
        bytes[256..288].copy_from_slice(&self.0.c1.c1.c0.to_repr());
        bytes[288..320].copy_from_slice(&self.0.c1.c1.c1.to_repr());
        bytes[320..352].copy_from_slice(&self.0.c1.c2.c0.to_repr());
        bytes[352..384].copy_from_slice(&self.0.c1.c2.c1.to_repr());
        bytes
    }

    pub fn from_repr(bytes: &[u8; Self::BYTES]) -> CtOption<Self> {
        let c0c0c0 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[0..32]).expect("32 bytes"));
        let c0c0c1 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[32..64]).expect("32 bytes"));
        let c0c1c0 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[64..96]).expect("32 bytes"));
        let c0c1c1 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[96..128]).expect("32 bytes"));
        let c0c2c0 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[128..160]).expect("32 bytes"));
        let c0c2c1 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[160..192]).expect("32 bytes"));
        let c1c0c0 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[192..224]).expect("32 bytes"));
        let c1c0c1 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[224..256]).expect("32 bytes"));
        let c1c1c0 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[256..288]).expect("32 bytes"));
        let c1c1c1 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[288..320]).expect("32 bytes"));
        let c1c2c0 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[320..352]).expect("32 bytes"));
        let c1c2c1 = Fp::from_repr(<[u8; 32]>::try_from(&bytes[352..384]).expect("32 bytes"));

        let c0c0 = c0c0c0.and_then(|c000| {
            c0c0c1.and_then(|c001| CtOption::new(Fp2 { c0: c000, c1: c001 }, Choice::from(1)))
        });
        let c0c1 = c0c1c0.and_then(|c010| {
            c0c1c1.and_then(|c011| CtOption::new(Fp2 { c0: c010, c1: c011 }, Choice::from(1)))
        });
        let c0c2 = c0c2c0.and_then(|c020| {
            c0c2c1.and_then(|c021| CtOption::new(Fp2 { c0: c020, c1: c021 }, Choice::from(1)))
        });
        let c1c0 = c1c0c0.and_then(|c100| {
            c1c0c1.and_then(|c101| CtOption::new(Fp2 { c0: c100, c1: c101 }, Choice::from(1)))
        });
        let c1c1 = c1c1c0.and_then(|c110| {
            c1c1c1.and_then(|c111| CtOption::new(Fp2 { c0: c110, c1: c111 }, Choice::from(1)))
        });
        let c1c2 = c1c2c0.and_then(|c120| {
            c1c2c1.and_then(|c121| CtOption::new(Fp2 { c0: c120, c1: c121 }, Choice::from(1)))
        });

        let c0 = c0c0.and_then(|c0c0| {
            c0c1.and_then(|c0c1| {
                c0c2.and_then(|c0c2| {
                    CtOption::new(
                        Fp6 {
                            c0: c0c0,
                            c1: c0c1,
                            c2: c0c2,
                        },
                        Choice::from(1),
                    )
                })
            })
        });
        let c1 = c1c0.and_then(|c1c0| {
            c1c1.and_then(|c1c1| {
                c1c2.and_then(|c1c2| {
                    CtOption::new(
                        Fp6 {
                            c0: c1c0,
                            c1: c1c1,
                            c2: c1c2,
                        },
                        Choice::from(1),
                    )
                })
            })
        });

        c0.and_then(|c0| c1.and_then(|c1| CtOption::new(Self(Fp12 { c0, c1 }), Choice::from(1))))
    }

    pub fn invert(&self) -> CtOption<Self> {
        self.0.invert().map(Self)
    }

    pub fn mul_by_scalar(&self, scalar: &Scalar) -> Self {
        let mut acc = Self::IDENTITY;

        // Simple double and add algorithm
        for bit in scalar
            .0
            .to_le_bytes()
            .iter()
            .rev()
            .flat_map(|b| (0..8).rev().map(move |i| Choice::from((b >> i) & 1u8)))
        {
            acc = acc.double();
            acc.conditional_assign(&(acc + self), bit);
        }
        acc
    }
}

/// This structure contains cached computations to a $\mathbb{G}_2$
/// element as part of the pairing function (specifically, the Miller loop)
/// and so should be computed whenever a $\mathbb{G}_2$ element is being used
/// in multiple pairings or is otherwise known in advance. This should be used
/// in conjunction with [`multi_miller_loop`] to compute the pairing function
#[derive(Copy, Clone, Debug)]
pub struct G2Prepared {
    infinity: Choice,
    coeffs: PairingCoefficients,
}

impl From<G2Affine> for G2Prepared {
    fn from(g: G2Affine) -> Self {
        struct Adder {
            cur: G2Projective,
            base: G2Affine,
            coeffs: PairingCoefficients,
        }

        impl MillerLoopDriver for Adder {
            type Output = ();

            fn doubling_step(&mut self, _f: Self::Output) -> Self::Output {
                let coeffs = doubling_step(&mut self.cur);
                self.coeffs.push(coeffs);
            }

            fn addition_step(&mut self, _f: Self::Output) -> Self::Output {
                let coeffs = addition_step(&mut self.cur, &self.base);
                self.coeffs.push(coeffs);
            }

            fn square_output(_f: Self::Output) -> Self::Output {}

            fn conjugate(_f: Self::Output) -> Self::Output {}

            fn one() -> Self::Output {}
        }

        let is_identity = g.is_identity();
        let g = G2Affine::conditional_select(&g, &G2Affine::generator(), is_identity);

        let mut adder = Adder {
            cur: G2Projective::from(g),
            base: g,
            coeffs: PairingCoefficients::default(),
        };

        miller_loop(&mut adder);

        debug_assert_eq!(adder.coeffs.len(), 68);

        G2Prepared {
            infinity: is_identity,
            coeffs: adder.coeffs,
        }
    }
}

impl PairingCurveAffine for G1Affine {
    type Pair = G2Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        pairing(self, other)
    }
}

impl PairingCurveAffine for G2Affine {
    type Pair = G1Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        pairing(other, self)
    }
}

/// A [`pairing::Engine`] for BN254 pairing operations.
#[cfg_attr(docsrs, doc(cfg(feature = "pairings")))]
#[derive(Clone, Debug)]
pub struct Bn254;

impl Engine for Bn254 {
    type Fr = Scalar;
    type G1 = G1Projective;
    type G1Affine = G1Affine;
    type G2 = G2Projective;
    type G2Affine = G2Affine;
    type Gt = Gt;

    fn pairing(p: &Self::G1Affine, q: &Self::G2Affine) -> Self::Gt {
        pairing(p, q)
    }
}

impl pairing::MillerLoopResult for MillerLoopResult {
    type Gt = Gt;

    fn final_exponentiation(&self) -> Self::Gt {
        self.final_exponentiation()
    }
}

impl MultiMillerLoop for Bn254 {
    type G2Prepared = G2Prepared;
    type Result = MillerLoopResult;

    fn multi_miller_loop(terms: &[(&Self::G1Affine, &Self::G2Prepared)]) -> Self::Result {
        multi_miller_loop(terms)
    }
}

trait MillerLoopDriver {
    type Output;

    fn doubling_step(&mut self, f: Self::Output) -> Self::Output;
    fn addition_step(&mut self, f: Self::Output) -> Self::Output;
    fn square_output(f: Self::Output) -> Self::Output;
    fn conjugate(f: Self::Output) -> Self::Output;
    fn one() -> Self::Output;
}

#[derive(Copy, Clone, Debug)]
struct PairingCoefficients {
    space: [(Fp2, Fp2, Fp2); 68],
    length: usize,
}

impl Default for PairingCoefficients {
    fn default() -> Self {
        Self {
            space: [(Fp2::ZERO, Fp2::ZERO, Fp2::ZERO); 68],
            length: 0,
        }
    }
}

impl Index<usize> for PairingCoefficients {
    type Output = (Fp2, Fp2, Fp2);

    fn index(&self, index: usize) -> &Self::Output {
        &self.space[index]
    }
}

impl PairingCoefficients {
    pub fn push(&mut self, value: (Fp2, Fp2, Fp2)) {
        self.space[self.length] = value;
        self.length += 1;
    }

    pub fn len(&self) -> usize {
        self.length
    }
}

/// Invoke the pairing function without the use of precomputation and other optimizations.
pub fn pairing(p: &G1Affine, q: &G2Affine) -> Gt {
    struct Adder {
        cur: G2Projective,
        base: G2Affine,
        p: G1Affine,
    }

    impl MillerLoopDriver for Adder {
        type Output = Fp12;

        fn doubling_step(&mut self, f: Self::Output) -> Self::Output {
            let coeffs = doubling_step(&mut self.cur);
            ell(f, &coeffs, &self.p)
        }
        fn addition_step(&mut self, f: Self::Output) -> Self::Output {
            let coeffs = addition_step(&mut self.cur, &self.base);
            ell(f, &coeffs, &self.p)
        }
        fn square_output(f: Self::Output) -> Self::Output {
            f.square()
        }
        fn conjugate(f: Self::Output) -> Self::Output {
            f.conjugate()
        }
        fn one() -> Self::Output {
            Fp12::ONE
        }
    }

    let either_identity = p.is_identity() | q.is_identity();
    let p = G1Affine::conditional_select(p, &G1Affine::generator(), either_identity);
    let q = G2Affine::conditional_select(q, &G2Affine::generator(), either_identity);

    let mut adder = Adder {
        cur: G2Projective::from(q),
        base: q,
        p,
    };

    let tmp = miller_loop(&mut adder);
    let tmp = MillerLoopResult(Fp12::conditional_select(&tmp, &Fp12::ONE, either_identity));
    tmp.final_exponentiation()
}

/// Computes $$\sum_{i=1}^n \textbf{ML}(a_i, b_i)$$ given a series of terms
/// $$(a_1, b_1), (a_2, b_2), ..., (a_n, b_n).$$
///
/// Requires the `pairing` crate features to be enabled.
pub fn multi_miller_loop(terms: &[(&G1Affine, &G2Prepared)]) -> MillerLoopResult {
    struct Adder<'a, 'b, 'c> {
        terms: &'c [(&'a G1Affine, &'b G2Prepared)],
        index: usize,
    }

    impl MillerLoopDriver for Adder<'_, '_, '_> {
        type Output = Fp12;

        fn doubling_step(&mut self, mut f: Self::Output) -> Self::Output {
            let index = self.index;
            for term in self.terms {
                let either_identity = term.0.is_identity() | term.1.infinity;

                let new_f = ell(f, &term.1.coeffs[index], term.0);
                f = Fp12::conditional_select(&new_f, &f, either_identity);
            }
            self.index += 1;

            f
        }
        fn addition_step(&mut self, mut f: Self::Output) -> Self::Output {
            let index = self.index;
            for term in self.terms {
                let either_identity = term.0.is_identity() | term.1.infinity;

                let new_f = ell(f, &term.1.coeffs[index], term.0);
                f = Fp12::conditional_select(&new_f, &f, either_identity);
            }
            self.index += 1;

            f
        }
        fn square_output(f: Self::Output) -> Self::Output {
            f.square()
        }
        fn conjugate(f: Self::Output) -> Self::Output {
            f.conjugate()
        }
        fn one() -> Self::Output {
            Fp12::ONE
        }
    }

    let mut adder = Adder { terms, index: 0 };

    let tmp = miller_loop(&mut adder);

    MillerLoopResult(tmp)
}

/// This is a "generic" implementation of the Miller loop to avoid duplicating code
/// structure elsewhere; instead, we'll write concrete instantiations of
/// `MillerLoopDriver` for whatever purposes we need (such as caching modes).
fn miller_loop<D: MillerLoopDriver>(driver: &mut D) -> D::Output {
    let mut f = D::one();

    let mut found_one = false;
    for i in (0..64).rev().map(|b| (((X >> 1) >> b) & 1) == 1) {
        if !found_one {
            found_one = i;
            continue;
        }

        f = driver.doubling_step(f);

        if i {
            f = driver.addition_step(f);
        }

        f = D::square_output(f);
    }

    f = driver.doubling_step(f);

    f = D::conjugate(f);

    f
}

fn ell(f: Fp12, coeffs: &(Fp2, Fp2, Fp2), p: &G1Affine) -> Fp12 {
    let mut c0 = coeffs.0;
    let mut c1 = coeffs.1;

    c0.c0 *= p.y;
    c0.c1 *= p.y;

    c1.c0 *= p.x;
    c1.c1 *= p.x;

    f.mul_by_014(&coeffs.2, &c1, &c0)
}

fn doubling_step(r: &mut G2Projective) -> (Fp2, Fp2, Fp2) {
    // Adaptation of Algorithm 26, https://eprint.iacr.org/2010/354.pdf
    let tmp0 = r.x.square();
    let tmp1 = r.y.square();
    let tmp2 = tmp1.square();
    let tmp3 = (tmp1 + r.x).square() - tmp0 - tmp2;
    let tmp3 = tmp3 + tmp3;
    let tmp4 = tmp0 + tmp0 + tmp0;
    let tmp6 = r.x + tmp4;
    let tmp5 = tmp4.square();
    let zsquared = r.z.square();
    r.x = tmp5 - tmp3 - tmp3;
    r.z = (r.z + r.y).square() - tmp1 - zsquared;
    r.y = (tmp3 - r.x) * tmp4;
    let tmp2 = tmp2 + tmp2;
    let tmp2 = tmp2 + tmp2;
    let tmp2 = tmp2 + tmp2;
    r.y -= tmp2;
    let tmp3 = tmp4 * zsquared;
    let tmp3 = tmp3 + tmp3;
    let tmp3 = -tmp3;
    let tmp6 = tmp6.square() - tmp0 - tmp5;
    let tmp1 = tmp1 + tmp1;
    let tmp1 = tmp1 + tmp1;
    let tmp6 = tmp6 - tmp1;
    let tmp0 = r.z * zsquared;
    let tmp0 = tmp0 + tmp0;

    (tmp0, tmp3, tmp6)
}

fn addition_step(r: &mut G2Projective, q: &G2Affine) -> (Fp2, Fp2, Fp2) {
    // Adaptation of Algorithm 27, https://eprint.iacr.org/2010/354.pdf
    let zsquared = r.z.square();
    let ysquared = q.y.square();
    let t0 = zsquared * q.x;
    let t1 = ((q.y + r.z).square() - ysquared - zsquared) * zsquared;
    let t2 = t0 - r.x;
    let t3 = t2.square();
    let t4 = t3 + t3;
    let t4 = t4 + t4;
    let t5 = t4 * t2;
    let t6 = t1 - r.y - r.y;
    let t9 = t6 * q.x;
    let t7 = t4 * r.x;
    r.x = t6.square() - t5 - t7 - t7;
    r.z = (r.z + t2).square() - zsquared - t3;
    let t10 = q.y + r.z;
    let t8 = (t7 - r.x) * t6;
    let t0 = r.y * t5;
    let t0 = t0 + t0;
    r.y = t8 - t0;
    let t10 = t10.square() - ysquared;
    let ztsquared = r.z.square();
    let t10 = t10 - ztsquared;
    let t9 = t9 + t9 - t10;
    let t10 = r.z + r.z;
    let t6 = -t6;
    let t1 = t6 + t6;

    (t10, t1, t9)
}

#[cfg(test)]
mod tests {
    use elliptic_curve::hash2curve::ExpandMsgXmd;
    use elliptic_curve::scalar::FromUintUnchecked;
    use super::*;

    #[test]
    fn pairing_test() {
        let g1 = G1Affine::generator();
        let g2 = G2Affine::generator();
        let gt = pairing(&g1, &g2);
        println!("{:?}", gt);
        assert_eq!(gt, Gt::generator());
        let r = Scalar::from_uint_unchecked(FqModulus::MODULUS);
        assert_eq!(gt * r, Gt::identity());
        assert_eq!(Gt::generator() * r, Gt::IDENTITY);
    }
}