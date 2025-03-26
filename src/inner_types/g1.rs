use crate::inner_types::fp::Fp;
use crate::inner_types::{FqModulus, Scalar};
use crate::*;
use core::{
    borrow::Borrow,
    fmt::{self, Debug, Display, Formatter},
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use elliptic_curve::hash2curve::ExpandMsg;
use elliptic_curve::{
    bigint::{modular::constant_mod::ResidueParams, Encoding},
    consts::{U32, U64},
    generic_array::GenericArray,
    group::{
        cofactor::CofactorGroup,
        prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
        Curve, Group, GroupEncoding, UncompressedEncoding,
    },
    hash2curve::{ExpandMsgXmd, MapToCurve},
    ops::{LinearCombination, MulByGenerator},
    point::AffineCoordinates,
    scalar::IsHigh,
    Field, PrimeField,
};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::DefaultIsZeroes;

/// A representation of a compressed point on the curve.
pub type G1Repr = GenericArray<u8, U32>;
/// A representation of an uncompressed point on the curve.
pub type G1UncompressedRepr = GenericArray<u8, U64>;

/// An element in $\mathbb{G}_1$ represented in the affine coordinate space.
/// It is ideal to keep elements in this representation to reduce memory usage
/// and improve performance through the use of mixed curve model arithmetic.
///
/// Values of [`G1Affine`] are guaranteed to be in the prime-order subgroup.
#[derive(Copy, Clone, Debug)]
pub struct G1Affine {
    pub(crate) x: Fp,
    pub(crate) y: Fp,
    pub(crate) infinity: Choice,
}

impl Default for G1Affine {
    fn default() -> Self {
        Self::identity()
    }
}

impl DefaultIsZeroes for G1Affine {}

impl ConstantTimeEq for G1Affine {
    fn ct_eq(&self, other: &Self) -> Choice {
        (self.infinity & other.infinity)
            | ((!self.infinity & !other.infinity) & self.x.ct_eq(&other.x) & self.y.ct_eq(&other.y))
    }
}

impl Eq for G1Affine {}

impl PartialEq for G1Affine {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl ConditionallySelectable for G1Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            x: Fp::conditional_select(&a.x, &b.x, choice),
            y: Fp::conditional_select(&a.y, &b.y, choice),
            infinity: Choice::conditional_select(&a.infinity, &b.infinity, choice),
        }
    }
}

impl Display for G1Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:x}", self)
    }
}

impl fmt::LowerHex for G1Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for b in self.to_compressed() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl fmt::UpperHex for G1Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for b in self.to_compressed() {
            write!(f, "{:02X}", b)?;
        }
        Ok(())
    }
}

impl From<&G1Projective> for G1Affine {
    fn from(p: &G1Projective) -> G1Affine {
        let zinv = p.z.invert().unwrap_or(Fp::ZERO);
        let x = p.x * zinv;
        let y = p.y * zinv;

        let tmp = G1Affine {
            x,
            y,
            infinity: Choice::from(0u8),
        };

        G1Affine::conditional_select(&tmp, &G1Affine::identity(), zinv.is_zero())
    }
}

impl From<G1Projective> for G1Affine {
    fn from(p: G1Projective) -> G1Affine {
        Self::from(&p)
    }
}

impl Neg for &G1Affine {
    type Output = G1Affine;

    #[inline]
    fn neg(self) -> G1Affine {
        -*self
    }
}

impl Neg for G1Affine {
    type Output = G1Affine;

    #[inline]
    fn neg(self) -> G1Affine {
        Self {
            x: self.x,
            y: Fp::conditional_select(&-self.y, &Fp::ONE, self.infinity),
            infinity: self.infinity,
        }
    }
}

impl Add<G1Projective> for G1Affine {
    type Output = G1Projective;

    fn add(self, rhs: G1Projective) -> G1Projective {
        rhs.addition_mixed(&self)
    }
}

ops_impl!(Add, add, +, LHS = G1Affine, RHS = G1Projective, OUTPUT = G1Projective);

impl Sub<G1Projective> for G1Affine {
    type Output = G1Projective;

    fn sub(self, rhs: G1Projective) -> G1Projective {
        let rhs = -rhs;
        rhs.addition_mixed(&self)
    }
}

ops_impl!(Sub, sub, -, LHS = G1Affine, RHS = G1Projective, OUTPUT = G1Projective);

impl Mul<Scalar> for G1Affine {
    type Output = G1Projective;

    fn mul(self, scalar: Scalar) -> G1Projective {
        G1Projective::from(&self).multiply(&scalar.to_le_bytes())
    }
}

ops_impl!(Mul, mul, *, LHS = G1Affine, RHS = Scalar, OUTPUT = G1Projective);

impl Mul<G1Affine> for Scalar {
    type Output = G1Projective;

    fn mul(self, rhs: G1Affine) -> G1Projective {
        rhs.mul(self)
    }
}

ops_impl!(Mul, mul, *, LHS = Scalar, RHS = G1Affine, OUTPUT = G1Projective);

impl AffineCoordinates for G1Affine {
    type FieldRepr = G1Repr;

    fn x(&self) -> Self::FieldRepr {
        GenericArray::clone_from_slice(&self.x.to_repr()[..])
    }

    fn y_is_odd(&self) -> Choice {
        self.y.is_odd()
    }
}

bytes_impl!(
    G1Affine,
    |p: &G1Affine| p.to_compressed(),
    |bytes: &[u8]| {
        let repr = <[u8; G1Affine::COMPRESSED_BYTES]>::try_from(bytes)
            .map_err(|_| Bn254Error::InvalidG1Bytes)?;
        Option::<G1Affine>::from(G1Affine::from_compressed(&repr)).ok_or(Bn254Error::InvalidG1Bytes)
    }
);

serde_impl!(
    G1Affine,
    |p: &G1Affine| p.to_compressed(),
    |bytes: &[u8; G1Affine::COMPRESSED_BYTES]| {
        Option::<G1Affine>::from(G1Affine::from_compressed(bytes))
            .ok_or(serde::de::Error::custom("Invalid bytes"))
    },
    G1Affine::COMPRESSED_BYTES
);

impl GroupEncoding for G1Affine {
    type Repr = G1Repr;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let bytes = (*bytes).into();
        G1Affine::from_compressed(&bytes)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        let bytes = (*bytes).into();
        G1Affine::from_compressed(&bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.to_compressed().into()
    }
}

impl G1Affine {
    /// Bytes to represent the compressed form of the point.
    pub const COMPRESSED_BYTES: usize = 32;

    /// Bytes to represent the uncompressed form of the point.
    pub const UNCOMPRESSED_BYTES: usize = 64;

    /// Returns the identity of the group
    pub fn identity() -> Self {
        Self {
            x: Fp::ZERO,
            y: Fp::ONE,
            infinity: Choice::from(1u8),
        }
    }

    /// Return the fixed generator of the group
    pub fn generator() -> Self {
        Self {
            x: Fp::ONE,
            y: Fp::TWO,
            infinity: Choice::from(0u8),
        }
    }

    /// Serializes this element into compressed form.
    pub fn to_compressed(&self) -> [u8; Self::COMPRESSED_BYTES] {
        let mut bytes = self.x.to_repr();
        let y_is_odd = self.y_is_odd().unwrap_u8();
        bytes[0] |= y_is_odd << 7;
        bytes
    }

    #[cfg(any(feature = "alloc", feature = "std"))]
    /// Serializes this element into compressed hex string.
    pub fn to_compressed_hex(&self) -> crate::String {
        hex::encode(self.to_compressed())
    }

    /// Serializes this element into uncompressed form.
    pub fn to_uncompressed(&self) -> [u8; Self::UNCOMPRESSED_BYTES] {
        let mut bytes = [0u8; Self::UNCOMPRESSED_BYTES];
        bytes[..32].copy_from_slice(&self.x.to_repr());
        bytes[32..].copy_from_slice(&self.y.to_repr());
        bytes
    }

    #[cfg(any(feature = "alloc", feature = "std"))]
    /// Serializes this element into uncompressed hex string.
    pub fn to_uncompressed_hex(&self) -> crate::String {
        hex::encode(self.to_uncompressed())
    }

    /// Attempts to deserialize an element from compressed form.
    pub fn from_compressed(bytes: &[u8; Self::COMPRESSED_BYTES]) -> CtOption<Self> {
        // Y^2 Z = X^3 + 3
        let mut bytes = *bytes;
        let y_is_odd = Choice::from(bytes[0] >> 7);
        bytes[0] &= 0x7F;

        Fp::from_repr(bytes).and_then(|x| {
            CtOption::new(G1Affine::identity(), x.is_zero()).or_else(|| {
                (x.square() * x + Fp::THREE).sqrt().and_then(|y| {
                    let y = Fp::conditional_select(&y, &-y, y.is_high() ^ y_is_odd);

                    let infinity = y.ct_eq(&Fp::ONE);

                    CtOption::new(G1Affine { x, y, infinity }, Choice::from(1))
                })
            })
        })
    }

    /// Attempts to deserialize an element from compressed hex string.
    pub fn from_compressed_hex(hex: &str) -> CtOption<Self> {
        let mut bytes = [0u8; Self::COMPRESSED_BYTES];
        let res = hex::decode_to_slice(hex, &mut bytes);
        Self::from_compressed(&bytes)
            .and_then(|p| CtOption::new(p, Choice::from(res.is_ok() as u8)))
    }

    /// Attempts to deserialize an element from uncompressed form.
    pub fn from_uncompressed(bytes: &[u8; Self::UNCOMPRESSED_BYTES]) -> CtOption<Self> {
        let mut x_bytes = <[u8; 32]>::try_from(&bytes[..Self::COMPRESSED_BYTES])
            .expect("Invalid number of bytes for x-coordinate");
        let mut y_bytes = <[u8; 32]>::try_from(&bytes[Self::COMPRESSED_BYTES..])
            .expect("Invalid number of bytes for x-coordinate");

        // Mask away the top bit
        x_bytes[0] &= 0x7F;
        y_bytes[0] &= 0x7F;

        let x = Fp::from_repr(x_bytes);
        let y = Fp::from_repr(y_bytes);

        x.and_then(|x| {
            CtOption::new(G1Affine::identity(), x.is_zero()).or_else(|| {
                y.and_then(|y| {
                    let infinity = y.ct_eq(&Fp::ONE);
                    CtOption::new(G1Affine { x, y, infinity }, Choice::from(1))
                })
            })
        })
    }

    /// Attempts to deserialize an element from uncompressed hex string.
    pub fn from_uncompressed_hex(hex: &str) -> CtOption<Self> {
        let mut bytes = [0u8; 64];
        let res = hex::decode_to_slice(hex, &mut bytes);
        Self::from_uncompressed(&bytes)
            .and_then(|p| CtOption::new(p, Choice::from(res.is_ok() as u8)))
    }

    /// Return true if this element is the identity of the group
    pub fn is_identity(&self) -> Choice {
        self.infinity
    }

    /// All points on G1 are in the prime order subgroup since the cofactor is 1.
    /// Thus, this function always returns true unless an "unchecked" point is used.
    pub fn is_torsion_free(&self) -> Choice {
        G1Projective::from(self).is_torsion_free()
    }

    /// Returns true if this point is on the curve. This should always return true
    /// unless an "unchecked" point is used.
    pub fn is_on_curve(&self) -> Choice {
        // Y^2 Z = X^3 + b Z^3
        let z = Fp::conditional_select(&Fp::ONE, &Fp::ZERO, self.infinity);
        let x2 = self.x.square();
        let y2 = self.y.square();
        let lhs = y2 * z;
        let rhs = x2 * self.x + Fp::THREE * z;
        lhs.ct_eq(&rhs)
    }
}

/// An element in $\mathbb{G}_1$ represented in the projective coordinate space.
#[derive(Copy, Clone, Debug)]
pub struct G1Projective {
    pub(crate) x: Fp,
    pub(crate) y: Fp,
    pub(crate) z: Fp,
}

impl Default for G1Projective {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl Display for G1Projective {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:x}", G1Affine::from(self))
    }
}

impl From<&G1Affine> for G1Projective {
    fn from(value: &G1Affine) -> Self {
        Self {
            x: value.x,
            y: value.y,
            z: Fp::conditional_select(&Fp::ONE, &Fp::ZERO, value.infinity),
        }
    }
}

impl From<G1Affine> for G1Projective {
    fn from(value: G1Affine) -> Self {
        G1Projective::from(&value)
    }
}

impl ConstantTimeEq for G1Projective {
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

impl Eq for G1Projective {}

impl PartialEq for G1Projective {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl ConditionallySelectable for G1Projective {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            x: Fp::conditional_select(&a.x, &b.x, choice),
            y: Fp::conditional_select(&a.y, &b.y, choice),
            z: Fp::conditional_select(&a.z, &b.z, choice),
        }
    }
}

impl Neg for &G1Projective {
    type Output = G1Projective;

    fn neg(self) -> G1Projective {
        -*self
    }
}

impl Neg for G1Projective {
    type Output = G1Projective;

    fn neg(self) -> G1Projective {
        Self {
            x: self.x,
            y: -self.y,
            z: self.z,
        }
    }
}

impl AddAssign for G1Projective {
    fn add_assign(&mut self, rhs: G1Projective) {
        *self = self.addition(&rhs);
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = G1Projective, RHS = G1Projective, OUTPUT = G1Projective);

impl AddAssign<G1Affine> for G1Projective {
    fn add_assign(&mut self, rhs: G1Affine) {
        *self = self.addition_mixed(&rhs);
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = G1Projective, RHS = G1Affine, OUTPUT = G1Projective);

impl SubAssign for G1Projective {
    fn sub_assign(&mut self, rhs: G1Projective) {
        *self = self.addition(&-rhs);
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = G1Projective, RHS = G1Projective, OUTPUT = G1Projective);

impl SubAssign<G1Affine> for G1Projective {
    fn sub_assign(&mut self, rhs: G1Affine) {
        *self = self.addition_mixed(&-rhs);
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = G1Projective, RHS = G1Affine, OUTPUT = G1Projective);

impl MulAssign<Scalar> for G1Projective {
    fn mul_assign(&mut self, rhs: Scalar) {
        *self = self.multiply(&rhs.to_le_bytes());
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = G1Projective, RHS = Scalar, OUTPUT = G1Projective);

impl Mul<G1Projective> for Scalar {
    type Output = G1Projective;

    fn mul(self, rhs: G1Projective) -> G1Projective {
        rhs.multiply(&self.to_le_bytes())
    }
}

ops_impl!(Mul, mul, *, LHS = Scalar, RHS = G1Projective, OUTPUT = G1Projective);

bytes_impl!(
    G1Projective,
    |p: &G1Projective| p.to_compressed(),
    |bytes: &[u8]| {
        let repr = <[u8; G1Projective::COMPRESSED_BYTES]>::try_from(bytes)
            .map_err(|_| Bn254Error::InvalidG1Bytes)?;
        Option::<G1Projective>::from(G1Projective::from_compressed(&repr))
            .ok_or(Bn254Error::InvalidG1Bytes)
    }
);

serde_impl!(
    G1Projective,
    |p: &G1Projective| p.to_compressed(),
    |bytes: &[u8; G1Projective::COMPRESSED_BYTES]| {
        Option::<G1Projective>::from(G1Projective::from_compressed(bytes))
            .ok_or(serde::de::Error::custom("Invalid bytes"))
    },
    G1Projective::COMPRESSED_BYTES
);

impl MulByGenerator for G1Projective {}

impl LinearCombination for G1Projective {}

impl<T: Borrow<G1Projective>> Sum<T> for G1Projective {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::IDENTITY, |acc, item| acc + item.borrow())
    }
}

impl Group for G1Projective {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        let mut ikm = [0u8; 32];
        rng.fill_bytes(&mut ikm);
        G1Projective::hash::<ExpandMsgXmd<sha2::Sha256>>(&ikm, b"BN254G1_XMD:SHA-256_SVDW_RO_")
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

impl GroupEncoding for G1Projective {
    type Repr = G1Repr;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let bytes = (*bytes).into();
        G1Projective::from_compressed(&bytes)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        let bytes = (*bytes).into();
        G1Projective::from_compressed(&bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.to_compressed().into()
    }
}

impl PrimeGroup for G1Projective {}

impl Curve for G1Projective {
    type AffineRepr = G1Affine;

    fn to_affine(&self) -> Self::AffineRepr {
        self.into()
    }
}

impl PrimeCurve for G1Projective {
    type Affine = G1Affine;
}

impl PrimeCurveAffine for G1Affine {
    type Scalar = Scalar;
    type Curve = G1Projective;

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

impl DefaultIsZeroes for G1Projective {}

impl UncompressedEncoding for G1Projective {
    type Uncompressed = G1UncompressedRepr;

    fn from_uncompressed(bytes: &Self::Uncompressed) -> CtOption<Self> {
        let bytes = (*bytes).into();
        G1Affine::from_uncompressed(&bytes).map(G1Projective::from)
    }

    fn from_uncompressed_unchecked(bytes: &Self::Uncompressed) -> CtOption<Self> {
        let bytes = (*bytes).into();
        G1Affine::from_uncompressed(&bytes).map(G1Projective::from)
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        G1Affine::from(self).to_uncompressed().into()
    }
}

impl CofactorGroup for G1Projective {
    type Subgroup = Self;

    fn clear_cofactor(&self) -> Self::Subgroup {
        *self
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(self, Choice::from(1u8))
    }

    fn is_torsion_free(&self) -> Choice {
        self.is_torsion_free()
    }
}

impl G1Projective {
    /// Bytes to represent the compressed form of the point.
    pub const COMPRESSED_BYTES: usize = 32;

    /// Bytes to represent the uncompressed form of the point.
    pub const UNCOMPRESSED_BYTES: usize = 64;

    /// Returns the identity of the group
    pub const IDENTITY: Self = Self {
        x: Fp::ZERO,
        y: Fp::ONE,
        z: Fp::ZERO,
    };

    /// Returns the fixed generator of the group
    pub const GENERATOR: Self = Self {
        x: Fp::ONE,
        y: Fp::TWO,
        z: Fp::ONE,
    };

    /// Adds this point to another point in the affine model.
    pub(crate) fn addition_mixed(&self, rhs: &G1Affine) -> G1Projective {
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

        let tmp = G1Projective {
            x: x3,
            y: y3,
            z: z3,
        };

        G1Projective::conditional_select(&tmp, self, rhs.is_identity())
    }

    /// Adds this point to another point.
    pub(crate) fn addition(&self, rhs: &G1Projective) -> G1Projective {
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

        G1Projective {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// Computes the doubling of this point.
    pub(crate) fn double(&self) -> G1Projective {
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

        let tmp = G1Projective {
            x: x3,
            y: y3,
            z: z3,
        };

        G1Projective::conditional_select(&tmp, &G1Projective::IDENTITY, self.is_identity())
    }

    /// Multiplies this point by a scalar.
    pub(crate) fn multiply(&self, by: &[u8; 32]) -> G1Projective {
        let mut acc = G1Projective::IDENTITY;

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
            acc = G1Projective::conditional_select(&acc, &(acc + self), bit);
        }

        acc
    }

    /// Returns true if this element is the identity (the point at infinity).
    #[inline]
    pub fn is_identity(&self) -> Choice {
        self.z.is_zero()
    }

    /// Returns true if this point is free of an $h$-torsion component, and so it
    /// exists within the $q$-order subgroup $\mathbb{G}_1$. This should always return true
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
            .ct_eq(&(self.x.square() * self.x + self.z.square() * self.z * Fp::THREE))
            | self.z.is_zero()
    }

    /// Converts a point to its compressed representation.
    pub fn to_compressed(&self) -> [u8; Self::COMPRESSED_BYTES] {
        G1Affine::from(self).to_compressed()
    }

    /// Decodes a point from its compressed representation.
    pub fn from_compressed(bytes: &[u8; Self::COMPRESSED_BYTES]) -> CtOption<Self> {
        G1Affine::from_compressed(bytes).map(Self::from)
    }

    #[cfg(any(feature = "alloc", feature = "std"))]
    /// Converts a point to its compressed hex representation.
    pub fn to_compressed_hex(&self) -> String {
        G1Affine::from(self).to_compressed_hex()
    }

    /// Decodes a point from its compressed hex representation.
    pub fn from_compressed_hex(hex: &str) -> CtOption<Self> {
        G1Affine::from_compressed_hex(hex).map(Self::from)
    }

    /// Converts a point to its uncompressed representation.
    pub fn to_uncompressed(&self) -> [u8; Self::UNCOMPRESSED_BYTES] {
        G1Affine::from(self).to_uncompressed()
    }

    /// Decodes a point from its uncompressed representation.
    pub fn from_uncompressed(bytes: &[u8; Self::UNCOMPRESSED_BYTES]) -> CtOption<Self> {
        G1Affine::from_uncompressed(bytes).map(Self::from)
    }

    #[cfg(any(feature = "alloc", feature = "std"))]
    /// Converts a point to its uncompressed hex representation.
    pub fn to_uncompressed_hex(&self) -> String {
        G1Affine::from(self).to_uncompressed_hex()
    }

    /// Decodes a point from its uncompressed hex representation.
    pub fn from_uncompressed_hex(hex: &str) -> CtOption<Self> {
        G1Affine::from_uncompressed_hex(hex).map(Self::from)
    }

    /// Hashes a message to a point on the curve.
    pub fn hash<X>(msg: &[u8], dst: &[u8]) -> Self
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let u = Fp::hash::<X>(msg, dst);
        let q0 = u[0].map_to_curve();
        let q1 = u[1].map_to_curve();
        // No need to clear cofactor since the cofactor is 1
        q0 + q1
    }

    /// Encodes a message to a point on the curve.
    pub fn encode<X>(msg: &[u8], dst: &[u8]) -> Self
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let u = Fp::encode::<X>(msg, dst);
        u.map_to_curve()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use elliptic_curve::hash2curve::MapToCurve;

    #[cfg(any(feature = "alloc", feature = "std"))]
    #[test]
    fn affine_serialization() {
        let g = G1Affine::generator();
        let bytes = g.to_compressed();
        let hex = g.to_compressed_hex();
        let from_bytes = G1Affine::from_compressed(&bytes).unwrap();
        let from_hex = G1Affine::from_compressed_hex(&hex).unwrap();
        assert_eq!(from_bytes, from_hex);
        assert_eq!(from_bytes, g);

        let bytes = g.to_uncompressed();
        let hex = g.to_uncompressed_hex();
        let from_bytes = G1Affine::from_uncompressed(&bytes).unwrap();
        let from_hex = G1Affine::from_uncompressed_hex(&hex).unwrap();
        assert_eq!(from_bytes, from_hex);
        assert_eq!(from_bytes, g);
    }

    #[test]
    fn affine_repr() {
        let g = G1Affine::generator();
        let x: [u8; 32] = g.x().into();
        let y = g.y_is_odd();
        let mut expected_x = [0u8; 32];
        expected_x[31] = 1;

        assert_eq!(x, expected_x);
        assert_eq!(y.unwrap_u8(), 0);
    }

    #[test]
    fn affine_is_tests() {
        let g = G1Affine::generator();
        assert_eq!(g.is_identity().unwrap_u8(), 0);
        assert_eq!(g.is_torsion_free().unwrap_u8(), 1);
        assert_eq!(g.is_on_curve().unwrap_u8(), 1);

        let g = G1Affine::identity();
        assert_eq!(g.is_identity().unwrap_u8(), 1);
        assert_eq!(g.is_torsion_free().unwrap_u8(), 1);
        assert_eq!(g.is_on_curve().unwrap_u8(), 1);
    }

    #[test]
    fn encode() {
        struct TestVector {
            msg: &'static [u8],
            p_x: &'static str,
            p_y: &'static str,
            q_x: &'static str,
            q_y: &'static str,
            u: &'static str,
        }
        const DST_ENCODE: &'static [u8] = b"QUUX-V01-CS02-with-BN254G1_XMD:SHA-256_SVDW_NU_";

        const ENCODE_VECTORS: [TestVector; 5] = [
            TestVector {
                msg: b"",
                p_x: "1bb8810e2ceaf04786d4efd216fc2820ddd9363712efc736ada11049d8af5925",
                p_y: "1efbf8d54c60d865cce08437668ea30f5bf90d287dbd9b5af31da852915e8f11",
                q_x: "1bb8810e2ceaf04786d4efd216fc2820ddd9363712efc736ada11049d8af5925",
                q_y: "1efbf8d54c60d865cce08437668ea30f5bf90d287dbd9b5af31da852915e8f11",
                u:   "0cb81538a98a2e3580076eed495256611813f6dae9e16d3d4f8de7af0e9833e1",
            },
            TestVector {
                msg: b"abc",
                p_x: "0da4a96147df1f35b0f820bd35c6fac3b80e8e320de7c536b1e054667b22c332",
                p_y: "189bd3fbffe4c8740d6543754d95c790e44cd2d162858e3b733d2b8387983bb7",
                q_x: "0da4a96147df1f35b0f820bd35c6fac3b80e8e320de7c536b1e054667b22c332",
                q_y: "189bd3fbffe4c8740d6543754d95c790e44cd2d162858e3b733d2b8387983bb7",
                u:   "0ba35e127276e9000b33011860904ddee28f1d48ddd3577e2a797ef4a5e62319",
            },
            TestVector {
                msg: b"abcdef0123456789",
                p_x :"2ff727cfaaadb3acab713fa22d91f5fddab3ed77948f3ef6233d7ea9b03f4da1",
                p_y: "304080768fd2f87a852155b727f97db84b191e41970506f0326ed4046d1141aa",
                q_x: "2ff727cfaaadb3acab713fa22d91f5fddab3ed77948f3ef6233d7ea9b03f4da1",
                q_y: "304080768fd2f87a852155b727f97db84b191e41970506f0326ed4046d1141aa",
                u:   "11852286660cd970e9d7f46f99c7cca2b75554245e91b9b19d537aa6147c28fc",
            },
            TestVector {
                msg: b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
                p_x: "11a2eaa8e3e89de056d1b3a288a7f733c8a1282efa41d28e71af065ab245df9b",
                p_y: "060f37c447ac29fd97b9bb83be98ddccf15e34831a9cdf5493b7fede0777ae06",
                q_x: "11a2eaa8e3e89de056d1b3a288a7f733c8a1282efa41d28e71af065ab245df9b",
                q_y: "060f37c447ac29fd97b9bb83be98ddccf15e34831a9cdf5493b7fede0777ae06",
                u:   "174d1c85d8a690a876cc1deba0166d30569fafdb49cb3ed28405bd1c5357a1cc",
            },
            TestVector {
                msg: b"a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                p_x: "27409dccc6ee4ce90e24744fda8d72c0bc64e79766f778da0c1c0ef1c186ea84",
                p_y: "1ac201a542feca15e77f30370da183514dc99d8a0b2c136d64ede35cd0b51dc0",
                q_x: "27409dccc6ee4ce90e24744fda8d72c0bc64e79766f778da0c1c0ef1c186ea84",
                q_y: "1ac201a542feca15e77f30370da183514dc99d8a0b2c136d64ede35cd0b51dc0",
                u:   "073b81432b4cf3a8a9076201500d1b94159539f052a6e0928db7f2df74bff672",
            },
        ];

        for vector in &ENCODE_VECTORS {
            let u = Fp::encode::<ExpandMsgXmd<sha2::Sha256>>(vector.msg, DST_ENCODE);
            assert_eq!(u, Fp::from_be_hex(vector.u));
            let p: G1Projective = u.map_to_curve();
            let q = p;
            assert_eq!(p.x, Fp::from_be_hex(vector.p_x));
            assert_eq!(p.y, Fp::from_be_hex(vector.p_y));
            assert_eq!(q.x, Fp::from_be_hex(vector.q_x));
            assert_eq!(q.y, Fp::from_be_hex(vector.q_y));

            assert!(!bool::from(q.is_identity()));
            assert!(bool::from(p.is_on_curve()));
            assert!(bool::from(q.is_torsion_free()));
        }
    }

    #[test]
    fn hash() {
        struct TestVector {
            msg: &'static [u8],
            p_x: &'static str,
            p_y: &'static str,
            q0_x: &'static str,
            q0_y: &'static str,
            q1_x: &'static str,
            q1_y: &'static str,
            u0: &'static str,
            u1: &'static str,
        }
        const DST_HASH: &'static [u8] = b"QUUX-V01-CS02-with-BN254G1_XMD:SHA-256_SVDW_RO_";
        const HASH_VECTORS: [TestVector; 5] = [
            TestVector {
                msg: b"",
                p_x:  "0a976ab906170db1f9638d376514dbf8c42aef256a54bbd48521f20749e59e86",
                p_y:  "02925ead66b9e68bfc309b014398640ab55f6619ab59bc1fab2210ad4c4d53d5",
                q0_x: "0e449b959abbd0e5ab4c873eaeb1ccd887f1d9ad6cd671fd72cb8d77fb651892",
                q0_y: "29ff1e36867c60374695ee0c298fcbef2af16f8f97ed356fa75e61a797ebb265",
                q1_x: "19388d9112a306fba595c3a8c63daa8f04205ad9581f7cf105c63c442d7c6511", 
                q1_y: "182da356478aa7776d1de8377a18b41e933036d0b71ab03f17114e4e673ad6e4",
                u0:   "2f87b81d9d6ef05ad4d249737498cc27e1bd485dca804487844feb3c67c1a9b5",
                u1:   "06de2d0d7c0d9c7a5a6c0b74675e7543f5b98186b5dbf831067449000b2b1f8e",
            },
            TestVector {
                msg: b"abc", 
                p_x:  "23f717bee89b1003957139f193e6be7da1df5f1374b26a4643b0378b5baf53d1",
                p_y:  "04142f826b71ee574452dbc47e05bc3e1a647478403a7ba38b7b93948f4e151d",
                q0_x: "1452c8cc24f8dedc25b24d89b87b64e25488191cecc78464fea84077dd156f8d", 
                q0_y: "209c3633505ba956f5ce4d974a868db972b8f1b69d63c218d360996bcec1ad41",
                q1_x: "04e8357c98524e6208ae2b771e370f0c449e839003988c2e4ce1eaf8d632559f",
                q1_y: "04396ec43dd8ec8f2b4a705090b5892219759da30154c39490fc4d59d51bb817",
                u0:   "11945105b5e3d3b9392b5a2318409cbc28b7246aa47fa30da5739907737799a9",
                u1:   "1255fc9ad5a6e0fb440916f091229bda611c41be2f2283c3d8f98c596be4c8c9",
            },
            TestVector {
                msg: b"abcdef0123456789", 
                p_x:  "187dbf1c3c89aceceef254d6548d7163fdfa43084145f92c4c91c85c21442d4a",
                p_y:  "0abd99d5b0000910b56058f9cc3b0ab0a22d47cf27615f588924fac1e5c63b4d",
                q0_x: "28d01790d2a1cc4832296774438acd46c2ce162d03099926478cf52319daba8d", 
                q0_y: "10227ab2707fd65fb45e87f0a48cfe3556f04113d27b1da9a7ae1709007355e1",
                q1_x: "07dc256c7aadac1b4e1d23b3b2bbb5e2ffd9c753b9073d8d952ead8f812ce1b3",
                q1_y: "2589008b2e15dcb3d16cdc1fed2634778001b1b28f0ab433f4f5ec6635c55e1e",
                u0:   "2f7993a6b43a8dbb37060e790011a888157f456b895b925c3568690685f4983d",
                u1:   "2677d0532b47a4cead2488845e7df7ebc16c0b8a2cd8a6b7f4ce99f51659794e",
            },
            TestVector {
                msg: b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq", 
                p_x:  "00fe2b0743575324fc452d590d217390ad48e5a16cf051bee5c40a2eba233f5c",
                p_y:  "0794211e0cc72d3cbbdf8e4e5cd6e7d7e78d101ff94862caae8acbe63e9fdc78",
                q0_x: "1c53b05f2fce15ba0b9100650c0fb46de1fb62f1d0968b69151151bd25dfefa4", 
                q0_y: "1fe783faf4bdbd79b717784dc59619106e4acccfe3b5d9750799729d855e7b81",
                q1_x: "214a4e6e97adda47558f80088460eabd71ed35bc8ceafb99a493dd6f4e2b3f0a", 
                q1_y: "0faaeb29cc23f9d09b187a99741613aed84443e7c35736258f57982d336d13bd",
                u0:   "2a50be15282ee276b76db1dab761f75401cdc8bd9fff81fcf4d428db16092a7b",
                u1:   "23b41953676183c30aca54b5c8bd3ffe3535a6238c39f6b15487a5467d5d20eb",
            },
            TestVector {
                msg: b"a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", 
                p_x:  "01b05dc540bd79fd0fea4fbb07de08e94fc2e7bd171fe025c479dc212a2173ce",
                p_y:  "1bf028afc00c0f843d113758968f580640541728cfc6d32ced9779aa613cd9b0",
                q0_x: "2298ba379768da62495af6bb390ffca9156fde1dc167235b89c6dd008d2f2f3b", 
                q0_y: "0660564cf6fce5cdea4780f5976dd0932559336fd072b4ddd83ec37f00fc7699",
                q1_x: "2811dea430f7a1f6c8c941ecdf0e1e725b8ad1801ad15e832654bd8f10b62f16", 
                q1_y: "253390ed4fb39e58c30ca43892ab0428684cfb30b9df05fc239ab532eaa02444",
                u0:   "048527470f534978bae262c0f3ba8380d7f560916af58af9ad7dcb6a4238e633",
                u1:   "19a6d8be25702820b9b11eada2d42f425343889637a01ecd7672fbcf590d9ffe",
            },
        ];

        for vector in &HASH_VECTORS {
            let u = Fp::hash::<ExpandMsgXmd<sha2::Sha256>>(vector.msg, DST_HASH);
            assert_eq!(u[0], Fp::from_be_hex(vector.u0));
            assert_eq!(u[1], Fp::from_be_hex(vector.u1));
            let q0: G1Projective = u[0].map_to_curve();
            assert_eq!(q0.x, Fp::from_be_hex(vector.q0_x));
            assert_eq!(q0.y, Fp::from_be_hex(vector.q0_y));
            let q1: G1Projective = u[1].map_to_curve();
            assert_eq!(q1.x, Fp::from_be_hex(vector.q1_x));
            assert_eq!(q1.y, Fp::from_be_hex(vector.q1_y));
            let p = G1Affine::from(q0 + q1);
            assert_eq!(p.x, Fp::from_be_hex(vector.p_x));
            assert_eq!(p.y, Fp::from_be_hex(vector.p_y));

            assert!(!bool::from(p.is_identity()));
            assert!(bool::from(p.is_on_curve()));
            assert!(bool::from(p.is_torsion_free()));
        }
    }

    #[test]
    fn arithmetic() {
        assert_eq!(
            G1Projective::GENERATOR.double().double() + G1Projective::GENERATOR,
            G1Projective::GENERATOR * Scalar::from(5u8),
        );
    }
}
