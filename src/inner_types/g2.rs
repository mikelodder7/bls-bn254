use super::{Fp2, FqModulus, G1Affine};
use crate::inner_types::{fp::Fp, scalar::Scalar};
use crate::Bn254Error;
use core::{
    borrow::Borrow,
    fmt::{self, Display, Formatter},
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use crypto_bigint::{modular::constant_mod::ResidueParams, Encoding};
use elliptic_curve::{
    consts::{U128, U64},
    generic_array::GenericArray,
    group::{
        cofactor::CofactorGroup,
        prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
        Curve, GroupEncoding, UncompressedEncoding,
    },
    hash2curve::{ExpandMsg, ExpandMsgXmd, MapToCurve, Sgn0},
    ops::{LinearCombination, MulByGenerator},
    point::AffineCoordinates,
    Field, Group, PrimeField,
};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::DefaultIsZeroes;

/// The representation of the compressed representation of a G2 element, in bytes.
pub type G2Repr = GenericArray<u8, U64>;
/// The representation of the uncompressed representation of a G2 element, in bytes.
pub type G2UncompressedRepr = GenericArray<u8, U128>;

/// An element of \$mathbb{G}_2\$ represented in the affine coordinate space.
#[derive(Copy, Clone, Debug)]
pub struct G2Affine {
    pub(crate) x: Fp2,
    pub(crate) y: Fp2,
    pub(crate) infinity: Choice,
}

impl Default for G2Affine {
    fn default() -> G2Affine {
        G2Affine::identity()
    }
}

impl DefaultIsZeroes for G2Affine {}

impl ConstantTimeEq for G2Affine {
    fn ct_eq(&self, other: &Self) -> Choice {
        (self.infinity & other.infinity)
            | ((!self.infinity & !other.infinity) & self.x.ct_eq(&other.x) & self.y.ct_eq(&other.y))
    }
}

impl ConditionallySelectable for G2Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G2Affine {
            x: Fp2::conditional_select(&a.x, &b.x, choice),
            y: Fp2::conditional_select(&a.y, &b.y, choice),
            infinity: Choice::conditional_select(&a.infinity, &b.infinity, choice),
        }
    }
}

impl Eq for G2Affine {}

impl PartialEq for G2Affine {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl Display for G2Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:x}", self)
    }
}

impl fmt::LowerHex for G2Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for b in self.to_compressed() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl fmt::UpperHex for G2Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for b in self.to_compressed() {
            write!(f, "{:02X}", b)?;
        }
        Ok(())
    }
}

impl From<&G2Projective> for G2Affine {
    fn from(p: &G2Projective) -> G2Affine {
        let zinv = p.z.invert().unwrap_or(Fp2::ZERO);
        let x = p.x * zinv;
        let y = p.y * zinv;

        let tmp = G2Affine {
            x,
            y,
            infinity: Choice::from(0),
        };

        G2Affine::conditional_select(&tmp, &G2Affine::identity(), zinv.is_zero())
    }
}

impl From<G2Projective> for G2Affine {
    fn from(p: G2Projective) -> G2Affine {
        Self::from(&p)
    }
}

impl Neg for &G2Affine {
    type Output = G2Affine;

    fn neg(self) -> G2Affine {
        G2Affine {
            x: self.x,
            y: Fp2::conditional_select(&-self.y, &Fp2::ONE, self.infinity),
            infinity: self.infinity,
        }
    }
}

impl Neg for G2Affine {
    type Output = G2Affine;

    fn neg(self) -> G2Affine {
        -&self
    }
}

impl Add<G2Projective> for G2Affine {
    type Output = G2Projective;

    fn add(self, rhs: G2Projective) -> G2Projective {
        rhs.addition_mixed(&self)
    }
}

ops_impl!(Add, add, +, LHS = G2Affine, RHS = G2Projective, OUTPUT = G2Projective);

impl Sub<G2Projective> for G2Affine {
    type Output = G2Projective;

    fn sub(self, rhs: G2Projective) -> G2Projective {
        rhs.addition_mixed(&-self)
    }
}

ops_impl!(Sub, sub, -, LHS = G2Affine, RHS = G2Projective, OUTPUT = G2Projective);

impl Mul<Scalar> for G2Affine {
    type Output = G2Projective;

    fn mul(self, scalar: Scalar) -> G2Projective {
        G2Projective::from(&self).multiply(&scalar.to_le_bytes())
    }
}

ops_impl!(Mul, mul, *, LHS = G2Affine, RHS = Scalar, OUTPUT = G2Projective);

impl Mul<G2Affine> for Scalar {
    type Output = G2Projective;

    fn mul(self, rhs: G2Affine) -> G2Projective {
        G2Projective::from(&rhs).multiply(&self.to_le_bytes())
    }
}

ops_impl!(Mul, mul, *, LHS = Scalar, RHS = G2Affine, OUTPUT = G2Projective);

impl AffineCoordinates for G2Affine {
    type FieldRepr = G2Repr;

    fn x(&self) -> Self::FieldRepr {
        let mut x_repr = G2Repr::default();
        x_repr[..Fp::BYTES].copy_from_slice(&self.x.c1.to_repr());
        x_repr[Fp::BYTES..].copy_from_slice(&self.x.c0.to_repr());
        x_repr
    }

    fn y_is_odd(&self) -> Choice {
        self.y.sgn0()
    }
}

bytes_impl!(
    G2Affine,
    |p: &G2Affine| p.to_compressed(),
    |bytes: &[u8]| {
        let repr = <[u8; G2Affine::COMPRESSED_BYTES]>::try_from(bytes)
            .map_err(|_| Bn254Error::InvalidG2Bytes)?;
        Option::<G2Affine>::from(G2Affine::from_compressed(&repr)).ok_or(Bn254Error::InvalidG2Bytes)
    }
);

serde_impl!(
    G2Affine,
    |p: &G2Affine| p.to_compressed(),
    |bytes: &[u8; G2Affine::COMPRESSED_BYTES]| {
        Option::<G2Affine>::from(G2Affine::from_compressed(bytes))
            .ok_or(serde::de::Error::custom("Invalid bytes"))
    },
    G2Affine::COMPRESSED_BYTES
);

impl GroupEncoding for G2Affine {
    type Repr = G2Repr;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed(bytes.as_ref())
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        GenericArray::clone_from_slice(&self.to_compressed())
    }
}

impl G2Affine {
    /// The size of the compressed representation of a G2 element, in bytes.
    pub const COMPRESSED_BYTES: usize = 2 * G1Affine::COMPRESSED_BYTES;
    /// The size of the uncompressed representation of a G2 element, in bytes.
    pub const UNCOMPRESSED_BYTES: usize = 2 * G1Affine::UNCOMPRESSED_BYTES;

    /// Returns the identity of the group: the point at infinity.
    pub fn identity() -> Self {
        Self {
            x: Fp2::ZERO,
            y: Fp2::ONE,
            infinity: Choice::from(1),
        }
    }

    /// Returns the generator of the group.
    pub fn generator() -> Self {
        Self {
            x: Fp2::GEN_X,
            y: Fp2::GEN_Y,
            infinity: Choice::from(0),
        }
    }

    /// Returns the compressed representation of this point.
    pub fn to_compressed(&self) -> [u8; Self::COMPRESSED_BYTES] {
        let mut repr = [0u8; Self::COMPRESSED_BYTES];
        repr[..Fp::BYTES].copy_from_slice(&self.x.c1.to_repr());
        repr[Fp::BYTES..].copy_from_slice(&self.x.c0.to_repr());

        let y_is_odd = self.y.sgn0();
        repr[0] |= y_is_odd.unwrap_u8() << 7;

        repr
    }

    #[cfg(any(feature = "std", feature = "alloc"))]
    /// Returns the compressed representation of this point as a hex string.
    pub fn to_compressed_hex(&self) -> crate::String {
        hex::encode(&self.to_compressed())
    }

    /// Attempts to parse the compressed representation of a point.
    pub fn to_uncompressed(&self) -> [u8; Self::UNCOMPRESSED_BYTES] {
        let mut repr = [0u8; Fp::BYTES * 4];
        repr[..Fp::BYTES].copy_from_slice(&self.x.c1.to_repr());
        repr[Fp::BYTES..Fp::BYTES * 2].copy_from_slice(&self.x.c0.to_repr());
        repr[Fp::BYTES * 2..3 * Fp::BYTES].copy_from_slice(&self.y.c1.to_repr());
        repr[Fp::BYTES * 3..].copy_from_slice(&self.y.c0.to_repr());

        repr
    }

    #[cfg(any(feature = "std", feature = "alloc"))]
    /// Returns the compressed representation of this point as a hex string.
    pub fn to_uncompressed_hex(&self) -> crate::String {
        hex::encode(&self.to_uncompressed())
    }

    /// Attempts to parse the compressed representation of a point.
    pub fn from_compressed(repr: &[u8; Self::COMPRESSED_BYTES]) -> CtOption<Self> {
        let xc1 = {
            let mut tmp = [0u8; Fp::BYTES];
            tmp.copy_from_slice(&repr[..Fp::BYTES]);
            tmp[0] &= 0x7F;
            Fp::from_repr(tmp)
        };

        let xc0 = {
            let mut tmp = [0u8; Fp::BYTES];
            tmp.copy_from_slice(&repr[Fp::BYTES..]);
            Fp::from_repr(tmp)
        };

        let y_is_odd = Choice::from((repr[0] >> 7) & 1);

        xc1.and_then(|xc1| {
            xc0.and_then(|xc0| {
                let x = Fp2 { c0: xc0, c1: xc1 };

                CtOption::new(G2Affine::identity(), x.is_zero()).or_else(|| {
                    ((x.square() * x) + Fp2::B).sqrt().and_then(|y| {
                        let y = Fp2::conditional_select(&y, &-y, y.sgn0() ^ y_is_odd);

                        let infinity = y.is_one();

                        CtOption::new(G2Affine { x, y, infinity }, Choice::from(1u8))
                    })
                })
            })
        })
    }

    /// Attempts to parse the compressed representation of a point from a hex string.
    pub fn from_compressed_hex(hex: &str) -> CtOption<Self> {
        let mut bytes = [0u8; Self::COMPRESSED_BYTES];
        let res = hex::decode_to_slice(hex, &mut bytes);
        Self::from_compressed(&bytes)
            .and_then(|p| CtOption::new(p, Choice::from(res.is_ok() as u8)))
    }

    pub fn from_uncompressed(repr: &[u8; Self::UNCOMPRESSED_BYTES]) -> CtOption<Self> {
        let xc1 = {
            let mut tmp = [0u8; Fp::BYTES];
            tmp.copy_from_slice(&repr[..Fp::BYTES]);
            Fp::from_repr(tmp)
        };
        let xc0 = {
            let mut tmp = [0u8; Fp::BYTES];
            tmp.copy_from_slice(&repr[Fp::BYTES..2 * Fp::BYTES]);
            Fp::from_repr(tmp)
        };

        let yc1 = {
            let mut tmp = [0u8; Fp::BYTES];
            tmp.copy_from_slice(&repr[2 * Fp::BYTES..3 * Fp::BYTES]);
            Fp::from_repr(tmp)
        };

        let yc0 = {
            let mut tmp = [0u8; Fp::BYTES];
            tmp.copy_from_slice(&repr[3 * Fp::BYTES..]);
            Fp::from_repr(tmp)
        };

        xc1.and_then(|xc1| {
            xc0.and_then(|xc0| {
                let x = Fp2 { c0: xc0, c1: xc1 };
                CtOption::new(G2Affine::identity(), x.is_zero()).or_else(|| {
                    yc1.and_then(|yc1| {
                        yc0.and_then(|yc0| {
                            let y = Fp2 { c0: yc0, c1: yc1 };
                            let infinity = y.is_one();
                            CtOption::new(G2Affine { x, y, infinity }, Choice::from(1u8))
                        })
                    })
                })
            })
        })
    }

    /// Attempts to parse the compressed representation of a point from a hex string.
    pub fn from_uncompressed_hex(hex: &str) -> CtOption<Self> {
        let mut bytes = [0u8; Self::UNCOMPRESSED_BYTES];
        let res = hex::decode_to_slice(hex, &mut bytes);
        Self::from_uncompressed(&bytes)
            .and_then(|p| CtOption::new(p, Choice::from(res.is_ok() as u8)))
    }

    /// Returns whether this point is the identity point.
    pub fn is_identity(&self) -> Choice {
        self.infinity
    }

    /// Returns whether this point is free of an h-torsion component
    pub fn is_torsion_free(&self) -> Choice {
        G2Projective::from(self).is_torsion_free()
    }

    /// Returns whether this point is on the curve.
    pub fn is_on_curve(&self) -> Choice {
        // Y^2 - X^3 = 4(u+1)
        let lhs = self.y.square();
        let rhs = (self.x.square() * self.x) + Fp2::B;
        lhs.ct_eq(&rhs) | self.infinity
    }
}

#[derive(Copy, Clone, Debug)]
pub struct G2Projective {
    pub(crate) x: Fp2,
    pub(crate) y: Fp2,
    pub(crate) z: Fp2,
}

impl Default for G2Projective {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl DefaultIsZeroes for G2Projective {}

impl ConstantTimeEq for G2Projective {
    fn ct_eq(&self, other: &Self) -> Choice {
        // Is (xz, yz, z) equal to (x'z', y'z', z')?

        let x1 = self.x * other.z;
        let x2 = other.x * self.z;

        let y1 = self.y * other.z;
        let y2 = other.y * self.z;

        let self_is_zero = self.z.is_zero();
        let other_is_zero = other.z.is_zero();

        (self_is_zero & other_is_zero) // Both infinity
            | ((!self_is_zero & !other_is_zero) & x1.ct_eq(&x2) & y1.ct_eq(&y2))
    }
}

impl Eq for G2Projective {}

impl PartialEq for G2Projective {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl ConditionallySelectable for G2Projective {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            x: Fp2::conditional_select(&a.x, &b.x, choice),
            y: Fp2::conditional_select(&a.y, &b.y, choice),
            z: Fp2::conditional_select(&a.z, &b.z, choice),
        }
    }
}

impl From<&G2Affine> for G2Projective {
    fn from(value: &G2Affine) -> Self {
        Self {
            x: value.x,
            y: value.y,
            z: Fp2::conditional_select(&Fp2::ONE, &Fp2::ZERO, value.infinity),
        }
    }
}

impl From<G2Affine> for G2Projective {
    fn from(value: G2Affine) -> Self {
        G2Projective::from(&value)
    }
}

impl Neg for &G2Projective {
    type Output = G2Projective;

    fn neg(self) -> G2Projective {
        -*self
    }
}

impl Neg for G2Projective {
    type Output = G2Projective;

    fn neg(self) -> G2Projective {
        G2Projective {
            x: self.x,
            y: -self.y,
            z: self.z,
        }
    }
}

impl AddAssign for G2Projective {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.addition(&rhs);
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = G2Projective, RHS = G2Projective, OUTPUT = G2Projective);

impl AddAssign<G2Affine> for G2Projective {
    fn add_assign(&mut self, rhs: G2Affine) {
        *self = self.addition_mixed(&rhs);
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = G2Projective, RHS = G2Affine, OUTPUT = G2Projective);

impl SubAssign for G2Projective {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.addition(&-rhs);
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = G2Projective, RHS = G2Projective, OUTPUT = G2Projective);

impl SubAssign<G2Affine> for G2Projective {
    fn sub_assign(&mut self, rhs: G2Affine) {
        *self = self.addition_mixed(&-rhs);
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = G2Projective, RHS = G2Affine, OUTPUT = G2Projective);

impl MulAssign<Scalar> for G2Projective {
    fn mul_assign(&mut self, rhs: Scalar) {
        *self = self.multiply(&rhs.to_le_bytes());
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = G2Projective, RHS = Scalar, OUTPUT = G2Projective);

impl Mul<G2Projective> for Scalar {
    type Output = G2Projective;

    fn mul(self, rhs: G2Projective) -> G2Projective {
        rhs.multiply(&self.to_le_bytes())
    }
}

ops_impl!(Mul, mul, *, LHS = Scalar, RHS = G2Projective, OUTPUT = G2Projective);

bytes_impl!(
    G2Projective,
    |p: &G2Projective| p.to_compressed(),
    |bytes: &[u8]| {
        let repr = <[u8; G2Projective::COMPRESSED_BYTES]>::try_from(bytes)
            .map_err(|_| Bn254Error::InvalidG2Bytes)?;
        Option::<G2Projective>::from(G2Projective::from_compressed(&repr))
            .ok_or(Bn254Error::InvalidG2Bytes)
    }
);

serde_impl!(
    G2Projective,
    |p: &G2Projective| p.to_compressed(),
    |bytes: &[u8; G2Projective::COMPRESSED_BYTES]| {
        Option::<G2Projective>::from(G2Projective::from_compressed(bytes))
            .ok_or(serde::de::Error::custom("Invalid bytes"))
    },
    G2Projective::COMPRESSED_BYTES
);

impl MulByGenerator for G2Projective {}

impl LinearCombination for G2Projective {}

impl<T: Borrow<G2Projective>> Sum<T> for G2Projective {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::IDENTITY, |acc, item| acc + item.borrow())
    }
}

impl Group for G2Projective {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        let mut ikm = [0u8; 32];
        rng.fill_bytes(&mut ikm);
        G2Projective::hash::<ExpandMsgXmd<sha2::Sha256>>(&ikm, b"BN254G2_XMD:SHA-256_SVDW_RO_")
    }

    fn identity() -> Self {
        Self::IDENTITY
    }

    fn generator() -> Self {
        Self::GENERATOR
    }

    fn is_identity(&self) -> Choice {
        self.is_identity()
    }

    fn double(&self) -> Self {
        self.double()
    }
}

impl GroupEncoding for G2Projective {
    type Repr = G2Repr;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let bytes = (*bytes).into();
        G2Projective::from_compressed(&bytes)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        let bytes = (*bytes).into();
        G2Projective::from_compressed(&bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.to_compressed().into()
    }
}

impl PrimeGroup for G2Projective {}

impl Curve for G2Projective {
    type AffineRepr = G2Affine;

    fn to_affine(&self) -> G2Affine {
        self.into()
    }
}

impl PrimeCurve for G2Projective {
    type Affine = G2Affine;
}

impl PrimeCurveAffine for G2Affine {
    type Scalar = Scalar;
    type Curve = G2Projective;

    fn identity() -> Self {
        Self::identity()
    }

    fn generator() -> Self {
        Self::generator()
    }

    fn is_identity(&self) -> Choice {
        self.infinity
    }

    fn to_curve(&self) -> Self::Curve {
        self.into()
    }
}

impl UncompressedEncoding for G2Projective {
    type Uncompressed = G2UncompressedRepr;

    fn from_uncompressed(bytes: &Self::Uncompressed) -> CtOption<Self> {
        let bytes = (*bytes).into();
        G2Affine::from_uncompressed(&bytes).map(G2Projective::from)
    }

    fn from_uncompressed_unchecked(bytes: &Self::Uncompressed) -> CtOption<Self> {
        let bytes = (*bytes).into();
        G2Affine::from_uncompressed(&bytes).map(G2Projective::from)
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        G2Affine::from(self).to_uncompressed().into()
    }
}

impl CofactorGroup for G2Projective {
    type Subgroup = G2Projective;

    fn clear_cofactor(&self) -> Self::Subgroup {
        const X_GEN: Scalar = Scalar::from_u64(X);
        let mut points = [G2Projective::IDENTITY; 4];
        points[0] = self * X_GEN;
        points[1] = (points[0].double() + points[0]).psi();
        points[2] = points[0].psi().psi();
        points[3] = self.psi().psi().psi();
        points.iter().sum()
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(self.clear_cofactor(), Choice::from(1u8))
    }

    fn is_torsion_free(&self) -> Choice {
        self.is_torsion_free()
    }
}

const X: u64 = 0x44e992b44a6909f1;
impl G2Projective {
    /// Bytes to represent the compressed form of the point.
    pub const COMPRESSED_BYTES: usize = 64;

    /// Bytes to represent the uncompressed form of the point.
    pub const UNCOMPRESSED_BYTES: usize = 128;

    /// Returns the identity of the group
    pub const IDENTITY: Self = Self {
        x: Fp2::ZERO,
        y: Fp2::ONE,
        z: Fp2::ZERO,
    };

    /// Returns the generator of the group
    pub const GENERATOR: Self = Self {
        x: Fp2::GEN_X,
        y: Fp2::GEN_Y,
        z: Fp2::ONE,
    };

    /// Returns true if this point is the identity.
    pub fn is_identity(&self) -> Choice {
        self.z.is_zero()
    }

    /// Returns true if this point is free of an h-torsion component, and so it
    /// exists within the q-order subgroup. This should always return true
    /// unless an "unchecked" API was used.
    pub fn is_torsion_free(&self) -> Choice {
        self.multiply(&FqModulus::MODULUS.to_le_bytes())
            .is_identity()
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub fn is_on_curve(&self) -> Choice {
        // Y^2 Z = X^3 + b Z^3

        (self.y.square() * self.z)
            .ct_eq(&(self.x.square() * self.x + self.z.square() * self.z * Fp2::B))
            | self.z.is_zero()
    }

    /// Adds this point to another point in the affine model.
    pub(crate) fn addition_mixed(&self, rhs: &G2Affine) -> G2Projective {
        // Algorithm 8, https://eprint.iacr.org/2015/1060.pdf

        let t0 = self.x * rhs.x;
        let t1 = self.y * rhs.y;
        let t3 = rhs.x + rhs.y;
        let t4 = self.x + self.y;
        let t3 = t3 * t4;
        let t4 = t0 + t1;
        let t3 = t3 - t4;
        let t4 = rhs.y * self.z;
        let t4 = t4 + self.y;
        let y3 = rhs.x * self.z;
        let y3 = y3 + self.x;
        let x3 = t0 + t0;
        let t0 = x3 + t0;
        let t2 = self.z.mul_by_3b();
        let z3 = t1 + t2;
        let t1 = t1 - t2;
        let y3 = y3.mul_by_3b();
        let x3 = t4 * y3;
        let t2 = t3 * t1;
        let x3 = t2 - x3;
        let y3 = y3 * t0;
        let t1 = t1 * z3;
        let y3 = t1 + y3;
        let t0 = t0 * t3;
        let z3 = z3 * t4;
        let z3 = z3 + t0;

        let tmp = G2Projective {
            x: x3,
            y: y3,
            z: z3,
        };

        G2Projective::conditional_select(&tmp, self, rhs.is_identity())
    }

    /// Adds this point to another point.
    pub(crate) fn addition(&self, rhs: &G2Projective) -> G2Projective {
        // Algorithm 7, https://eprint.iacr.org/2015/1060.pdf

        let t0 = self.x * rhs.x;
        let t1 = self.y * rhs.y;
        let t2 = self.z * rhs.z;
        let t3 = self.x + self.y;
        let t4 = rhs.x + rhs.y;
        let t3 = t3 * t4;
        let t4 = t0 + t1;
        let t3 = t3 - t4;
        let t4 = self.y + self.z;
        let x3 = rhs.y + rhs.z;
        let t4 = t4 * x3;
        let x3 = t1 + t2;
        let t4 = t4 - x3;
        let x3 = self.x + self.z;
        let y3 = rhs.x + rhs.z;
        let x3 = x3 * y3;
        let y3 = t0 + t2;
        let y3 = x3 - y3;
        let x3 = t0 + t0;
        let t0 = x3 + t0;
        let t2 = t2.mul_by_3b();
        let z3 = t1 + t2;
        let t1 = t1 - t2;
        let y3 = y3.mul_by_3b();
        let x3 = t4 * y3;
        let t2 = t3 * t1;
        let x3 = t2 - x3;
        let y3 = y3 * t0;
        let t1 = t1 * z3;
        let y3 = t1 + y3;
        let t0 = t0 * t3;
        let z3 = z3 * t4;
        let z3 = z3 + t0;

        G2Projective {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// Computes the doubling of this point.
    pub(crate) fn double(&self) -> G2Projective {
        // Algorithm 9, https://eprint.iacr.org/2015/1060.pdf

        let t0 = self.y.square();
        let z3 = t0 + t0;
        let z3 = z3 + z3;
        let z3 = z3 + z3;
        let t1 = self.y * self.z;
        let t2 = self.z.square();
        let t2 = t2.mul_by_3b();
        let x3 = t2 * z3;
        let y3 = t0 + t2;
        let z3 = t1 * z3;
        let t1 = t2 + t2;
        let t2 = t1 + t2;
        let t0 = t0 - t2;
        let y3 = t0 * y3;
        let y3 = x3 + y3;
        let t1 = self.x * self.y;
        let x3 = t0 * t1;
        let x3 = x3 + x3;

        let tmp = G2Projective {
            x: x3,
            y: y3,
            z: z3,
        };

        G2Projective::conditional_select(&tmp, &G2Projective::IDENTITY, self.is_identity())
    }

    /// Multiplies this point by a scalar.
    pub(crate) fn multiply(&self, by: &[u8]) -> G2Projective {
        let mut acc = G2Projective::IDENTITY;

        // This is a simple double-and-add implementation of point
        // multiplication, moving from most significant to least
        // significant bit of the scalar.
        //
        // We skip the leading bit because it's always unset for Fq
        // elements.
        for bit in by
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
            .skip(1)
        {
            acc = acc.double();
            acc.conditional_assign(&(acc + self), bit);
        }

        acc
    }

    /// Converts a point to its compressed representation.
    pub fn to_compressed(&self) -> [u8; Self::COMPRESSED_BYTES] {
        G2Affine::from(self).to_compressed()
    }

    /// Decodes a point from its compressed representation.
    pub fn from_compressed(bytes: &[u8; Self::COMPRESSED_BYTES]) -> CtOption<Self> {
        G2Affine::from_compressed(bytes).map(Self::from)
    }

    /// Converts a point to its uncompressed representation.
    pub fn to_uncompressed(&self) -> [u8; Self::UNCOMPRESSED_BYTES] {
        G2Affine::from(self).to_uncompressed()
    }

    /// Decodes a point from its uncompressed representation.
    pub fn from_uncompressed(bytes: &[u8; Self::UNCOMPRESSED_BYTES]) -> CtOption<Self> {
        G2Affine::from_uncompressed(bytes).map(Self::from)
    }

    /// Decodes a point from its compressed hex representation.
    pub fn from_compressed_hex(hex: &str) -> CtOption<Self> {
        G2Affine::from_compressed_hex(hex).map(Self::from)
    }

    /// Decodes a point from its uncompressed hex representation.
    pub fn from_uncompressed_hex(hex: &str) -> CtOption<Self> {
        G2Affine::from_uncompressed_hex(hex).map(Self::from)
    }

    /// Hashes a message to a point on the curve.
    pub fn hash<X>(msg: &[u8], dst: &[u8]) -> Self
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let u = Fp2::hash::<X>(msg, dst);
        let q0 = u[0].map_to_curve();
        let q1 = u[1].map_to_curve();
        (q0 + q1).clear_cofactor()
    }

    /// Encodes a message to a point on the curve.
    pub fn encode<X>(msg: &[u8], dst: &[u8]) -> Self
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let u = Fp2::encode::<X>(msg, dst);
        u.map_to_curve().clear_cofactor()
    }

    pub(crate) const fn psi(&self) -> Self {
        const ENDO_U: Fp2 = Fp2 {
            c0: Fp::from_be_hex("2fb347984f7911f74c0bec3cf559b143b78cc310c2c3330c99e39557176f553d"),
            c1: Fp::from_be_hex("16c9e55061ebae204ba4cc8bd75a079432ae2a1d0b7c9dce1665d51c640fcba2"),
        };

        const ENDO_V: Fp2 = Fp2 {
            c0: Fp::from_be_hex("063cf305489af5dcdc5ec698b6e2f9b9dbaae0eda9c95998dc54014671a0135a"),
            c1: Fp::from_be_hex("07c03cbcac41049a0704b5a7ec796f2b21807dc98fa25bd282d37f632623b0e3"),
        };

        Self {
            x: self.x.frobenius_map().multiply(&ENDO_U),
            y: self.y.frobenius_map().multiply(&ENDO_V),
            z: self.z.frobenius_map(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(any(feature = "alloc", feature = "std"))]
    #[test]
    fn affine_serialization() {
        let g = G2Affine::generator();
        let bytes = g.to_compressed();
        let hex = g.to_compressed_hex();
        let from_bytes = G2Affine::from_compressed(&bytes).unwrap();
        let from_hex = G2Affine::from_compressed_hex(&hex).unwrap();
        assert_eq!(from_bytes, from_hex);
        assert_eq!(from_bytes, g);

        let bytes = g.to_uncompressed();
        let hex = g.to_uncompressed_hex();
        let from_bytes = G2Affine::from_uncompressed(&bytes).unwrap();
        let from_hex = G2Affine::from_uncompressed_hex(&hex).unwrap();
        assert_eq!(from_bytes, from_hex);
        assert_eq!(from_bytes, g);
    }

    #[test]
    fn affine_repr() {
        let g = G2Affine::generator();
        let x: [u8; G2Affine::COMPRESSED_BYTES] = g.x().into();
        let y = g.y_is_odd();
        let mut expected_x = [0u8; G2Affine::COMPRESSED_BYTES];
        expected_x[..Fp::BYTES].copy_from_slice(&Fp2::GEN_X.c1.0.to_be_bytes()[..]);
        expected_x[Fp::BYTES..].copy_from_slice(&Fp2::GEN_X.c0.0.to_be_bytes()[..]);

        assert_eq!(x, expected_x);
        assert_eq!(y.unwrap_u8(), 0);
    }

    #[test]
    fn affine_is_tests() {
        let bad = G2Projective {
            x: Fp2 {
                c0: Fp::from_be_hex(
                    "1800deef121f1e7645fb98b23b47b6672f5e9c77e3b6d2c0c6a47013149d46c2",
                ),
                c1: Fp::from_be_hex(
                    "198e9393920d483a7260bfb731fb5db6466f6dcb02d4981f3e185a6f1b1cae1b",
                ),
            },
            y: Fp2 {
                c0: Fp::from_be_hex(
                    "12c85ea5db8c6deb43b4a02d921b03d73092fa8315dbb3a6db69a58a3d41e4a1",
                ),
                c1: Fp::from_be_hex(
                    "090689d0585ff0756b1e3e034293a225187f7e0caa96c1f54dbd8c7f4a26c4bd",
                ),
            },
            z: Fp2::ONE,
        };

        assert_eq!(bad.is_identity().unwrap_u8(), 0);
        assert_eq!(bad.is_torsion_free().unwrap_u8(), 0);
        assert_eq!(bad.is_on_curve().unwrap_u8(), 0);

        let g = G2Affine::generator();
        assert_eq!(g.is_identity().unwrap_u8(), 0);
        assert_eq!(g.is_on_curve().unwrap_u8(), 1);
        assert_eq!(g.is_torsion_free().unwrap_u8(), 1);

        let g = G2Affine::identity();
        assert_eq!(g.is_identity().unwrap_u8(), 1);
        assert_eq!(g.is_torsion_free().unwrap_u8(), 1);
        assert_eq!(g.is_on_curve().unwrap_u8(), 1);
    }

    #[test]
    fn arithmetic() {
        assert_eq!(
            G2Projective::GENERATOR.double().double() + G2Projective::GENERATOR,
            G2Projective::GENERATOR * Scalar::from(5u8),
        );
    }

    #[test]
    fn encode() {
        struct TestVector {
            msg: &'static [u8],
            p: G2Affine,
        }
        const DST_ENCODE: &'static [u8] = b"QUUX-V01-CS02-with-BN254G2_XMD:SHA-256_SVDW_NU_";

        let encode_vectors: [TestVector; 5] = [
            TestVector {
                msg: b"abc",
                p: G2Affine {
                    x: Fp2 {
                        c0: Fp::from_words([
                            0xe1812e0bcea5afd8,
                            0xc247856d6de4e420,
                            0x35ecb67d5284dc27,
                            0x101e2f3d9fa22cb4,
                        ]),
                        c1: Fp::from_words([
                            0xb17236325be3b6b7,
                            0x0c82d443fd953481,
                            0x1599274bf9e80505,
                            0x29226a3ca7415a54,
                        ]),
                    },
                    y: Fp2 {
                        c0: Fp::from_words([
                            0xfaf347cfb7b68715,
                            0xa2cb364c443981d0,
                            0x11effe86af369c11,
                            0x290bf12841dd2762,
                        ]),
                        c1: Fp::from_words([
                            0x34e57f3096f7047d,
                            0xafe0ef8221918d55,
                            0x52597ac564966560,
                            0x2e7c8a61fe367358,
                        ]),
                    },
                    infinity: Choice::from(0u8),
                },
            },
            TestVector {
                msg: b"",
                p: G2Affine {
                    x: Fp2 {
                        c0: Fp::from_words([
                            0x7fd75cffed6e994d,
                            0xe6cadf0135ebedd9,
                            0x97a99e234e91d4b9,
                            0x04e9ea7f58071983,
                        ]),
                        c1: Fp::from_words([
                            0xed0e07074b440a7b,
                            0xf4b734e678494bf4,
                            0x92fb30222ba96b63,
                            0x070077acfda84433,
                        ]),
                    },
                    y: Fp2 {
                        c0: Fp::from_words([
                            0xcbc8531e269227f9,
                            0xd5f60fee5690b4f8,
                            0xe2d48774d02393c8,
                            0x2d3653bf41ec170c,
                        ]),
                        c1: Fp::from_words([
                            0x8199a95ce02242b4,
                            0x49bf91dc2a7d9ba5,
                            0xd163570209e5f8f7,
                            0x0a7cf5d0d356f0c4,
                        ]),
                    },
                    infinity: Choice::from(0u8),
                },
            },
            TestVector {
                msg: b"abcdef0123456789",
                p: G2Affine {
                    x: Fp2 {
                        c0: Fp::from_words([
                            0x5cfef247c6e1e8a6,
                            0x63a05c9a5c7a2886,
                            0x27bf828e63fe2a1f,
                            0x0fcda542dd52f0e5,
                        ]),
                        c1: Fp::from_words([
                            0x0c7ddc364ae55a3a,
                            0xb5f96b6dcad56b3a,
                            0x106af8285fae5be0,
                            0x2d0bb492bb59847c,
                        ]),
                    },
                    y: Fp2 {
                        c0: Fp::from_words([
                            0x2614533311071780,
                            0xaf1b73c1643bbd02,
                            0xa230e7cb82fbd522,
                            0x172d50b483e9bb9a,
                        ]),
                        c1: Fp::from_words([
                            0xb798e9f1927a47b9,
                            0xe07fd4d0b13a9519,
                            0x9d6ab4c3014e73f7,
                            0xafb68b6e28f44f4,
                        ]),
                    },
                    infinity: Choice::from(0u8),
                },
            },
            TestVector {
                msg: b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
                p: G2Affine {
                    x: Fp2 {
                        c0: Fp::from_words([
                            0x3493bcc2a946b38d,
                            0x4ddf21691ab6418a,
                            0x07014cab4752d824,
                            0x1d050758368c65df,
                        ]),
                        c1: Fp::from_words([
                            0xc293c7e40c27387f,
                            0x890a4295dc17d053,
                            0x9cdc7cfe0b9d247a,
                            0x2596aa6bcb29439a,
                        ]),
                    },
                    y: Fp2 {
                        c0: Fp::from_words([
                            0xa78b76841aca8e82,
                            0xe1a00d0ba307d8fd,
                            0xd0d81c93c3f470c1,
                            0x2f84eec5eaa87952,
                        ]),
                        c1: Fp::from_words([
                            0x54ebd5f69c5c3443,
                            0xb15042dea92304fc,
                            0xc6f076e9fdae2f9e,
                            0x27aef639d6eb4157,
                        ]),
                    },
                    infinity: Choice::from(0u8),
                },
            },
            TestVector {
                msg: b"a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                p: G2Affine {
                    x: Fp2 {
                        c0: Fp::from_words([
                            0xd18153a9ec3854a7,
                            0x3a4e6be06ea712b0,
                            0x13bc742960afa905,
                            0x13729abbd4fbe2a,
                        ]),
                        c1: Fp::from_words([
                            0x4d90ac60437819a9,
                            0xe8a663b27cfb6d79,
                            0x4599465bb52880e8,
                            0x261e8ebaff343806,
                        ]),
                    },
                    y: Fp2 {
                        c0: Fp::from_words([
                            0x56fb890d1f7ba16e,
                            0xe574155ebaece328,
                            0x4da2d145390a6328,
                            0x132285a30dc36cc1,
                        ]),
                        c1: Fp::from_words([
                            0xb17885f71a394986,
                            0x168329a113d358c3,
                            0x4d17695042dcbaf0,
                            0x6bd9197b3c0c1cc,
                        ]),
                    },
                    infinity: Choice::from(0u8),
                },
            },
        ];

        for vector in &encode_vectors {
            let p = G2Affine::from(G2Projective::encode::<ExpandMsgXmd<sha2::Sha256>>(
                vector.msg, DST_ENCODE,
            ));
            assert_eq!(p, vector.p);
        }
    }

    #[test]
    fn hash() {
        struct TestVector {
            msg: &'static [u8],
            p: G2Affine,
        }
        const DST_HASH: &'static [u8] = b"QUUX-V01-CS02-with-BN254G2_XMD:SHA-256_SVDW_RO_";
        let hash_vectors: [TestVector; 5] = [
            TestVector {
                msg: b"",
                p: G2Affine {
                    x: Fp2{
                        c0: Fp::from_be_hex("1192005a0f121921a6d5629946199e4b27ff8ee4d6dd4f9581dc550ade851300"),
                        c1: Fp::from_be_hex("1747d950a6f23c16156e2171bce95d1189b04148ad12628869ed21c96a8c9335")
                    },
                    y: Fp2{
                        c0: Fp::from_be_hex("0498f6bb5ac309a07d9a8b88e6ff4b8de0d5f27a075830e1eb0e68ea318201d8"),
                        c1: Fp::from_be_hex("2c9755350ca363ef2cf541005437221c5740086c2e909b71d075152484e845f4")
                    },
                    infinity: Choice::from(0u8),
                },
            },
            TestVector {
                msg: b"abc",
                p: G2Affine {
                    x: Fp2{
                        c0: Fp::from_be_hex("16c88b54eec9af86a41569608cd0f60aab43464e52ce7e6e298bf584b94fccd2"),
                        c1: Fp::from_be_hex("0b5db3ca7e8ef5edf3a33dfc3242357fbccead98099c3eb564b3d9d13cba4efd")
                    },
                    y: Fp2{
                        c0: Fp::from_be_hex("1c42ba524cb74db8e2c680449746c028f7bea923f245e69f89256af2d6c5f3ac"),
                        c1: Fp::from_be_hex("22d02d2da7f288545ff8789e789902245ab08c6b1d253561eec789ec2c1bd630")
                    },
                    infinity: Choice::from(0u8),
                },
            },
            TestVector {
                msg: b"abcdef0123456789",
                p: G2Affine {
                    x: Fp2 {
                        c0: Fp::from_be_hex("1435fd84aa43c699230e371f6fea3545ce7e053cbbb06a320296a2b81efddc70"),
                        c1: Fp::from_be_hex("2a8a360585b6b05996ef69c3c09b2c6fb17afe2b1e944f07559c53178eabf171")
                    },
                    y: Fp2 {
                        c0: Fp::from_be_hex("2820188dcdc13ffdca31694942418afa1d6dfaaf259d012fab4da52b0f592e38"),
                        c1: Fp::from_be_hex("142f08e2441ec431defc24621b73cfe0252d19b243cb55b84bdeb85de039207a"),
                    },
                    infinity: Choice::from(0u8),
                }
            },
            TestVector {
                msg: b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
                p: G2Affine {
                    x: Fp2 {
                        c0: Fp::from_be_hex("2cffc213fb63d00d923cb22cda5a2904837bb93a2fe6e875c532c51744388341"),
                        c1: Fp::from_be_hex("2718ef38d1bc4347f0266c774c8ef4ee5fa7056cc27a4bd7ecf7a888efb95b26"),
                    },
                    y: Fp2 {
                        c0: Fp::from_be_hex("232553f728341afa64ce66d00535764557a052e38657594e10074ad28728c584"),
                        c1: Fp::from_be_hex("2206ec0a9288f31ed78531c37295df3b56c42a1284443ee9893adb1521779001"),
                    },
                    infinity: Choice::from(0u8),
                },
            },
            TestVector {
                msg: b"a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                p: G2Affine {
                    x: Fp2{
                        c0: Fp::from_be_hex("242a0a159f36f87065e7c5170426012087023165ce47a486e53d6e2845ca625a"),
                        c1: Fp::from_be_hex("17f9f6292998cf18ccc155903c1fe6b6465d40c794a3e1ed644a4182ad639f4a"),
                    },
                    y: Fp2{
                        c0: Fp::from_be_hex("2dc5b7b65c9c79e6ef4afab8fbe3083c66d4ce31c78f6621ece17ecc892cf4b3"),
                        c1: Fp::from_be_hex("18ef4886c818f01fdf309bc9a46dd904273917f85e74ecd0de62460a68122037"),
                    },
                    infinity: Choice::from(0u8),
                },
            },
        ];

        for vector in &hash_vectors {
            let p = G2Affine::from(G2Projective::hash::<ExpandMsgXmd<sha2::Sha256>>(
                vector.msg, DST_HASH,
            ));
            assert_eq!(p, vector.p);
        }
    }
}
