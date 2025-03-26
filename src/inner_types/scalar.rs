use crate::inner_types::{Bn254G1, G1Repr};
use crate::Bn254Error;
use core::{
    borrow::Borrow,
    fmt::{self, Debug, Display, Formatter, LowerHex, UpperHex},
    iter::{Product, Sum},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Shr, ShrAssign, Sub, SubAssign},
};
use elliptic_curve::bigint::Limb;
use elliptic_curve::consts::U32;
use elliptic_curve::{
    bigint::{
        impl_modulus,
        modular::constant_mod::{Residue, ResidueParams},
        Encoding, Integer, NonZero, Zero, U256, U384, U512,
    },
    consts::{U48, U64},
    ff::{helpers::sqrt_ratio_generic, FieldBits, PrimeFieldBits},
    generic_array::GenericArray,
    hash2curve::{ExpandMsg, Expander, FromOkm},
    ops::{Invert, Reduce, ReduceNonZero},
    scalar::{FromUintUnchecked, IsHigh, ScalarPrimitive},
    Field, PrimeField,
};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, CtOption};
use zeroize::DefaultIsZeroes;

impl_modulus!(
    FqModulus,
    U256,
    "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"
);

pub(crate) type FqResidue = Residue<FqModulus, { FqModulus::LIMBS }>;

const HALF_MODULUS: U256 = FqModulus::MODULUS.shr_vartime(1);
const MODULUS_U256: NonZero<U256> = NonZero::<U256>::const_new(FqModulus::MODULUS).0;
const MODULUS_M1_U256: NonZero<U256> =
    NonZero::<U256>::const_new(FqModulus::MODULUS.wrapping_sub(&U256::ONE)).0;
const MODULUS_M1_U384: NonZero<U384> =
    NonZero::<U384>::const_new(FqModulus::MODULUS.wrapping_sub(&U256::ONE).resize()).0;
const MODULUS_U512: NonZero<U512> = NonZero::<U512>::const_new(FqModulus::MODULUS.resize()).0;
const MODULUS_M1_U512: NonZero<U512> =
    NonZero::<U512>::const_new(FqModulus::MODULUS.wrapping_sub(&U256::ONE).resize()).0;

/// 32-byte (256-bit) scalar field element.
pub type ScalarBytes = GenericArray<u8, U32>;

#[derive(Copy, Clone, Debug, Default)]
pub struct Scalar(pub(crate) U256);

impl DefaultIsZeroes for Scalar {}

impl Display for Scalar {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:x}", self.0)
    }
}

impl LowerHex for Scalar {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:x}", self.0)
    }
}

impl UpperHex for Scalar {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:X}", self.0)
    }
}

impl From<u8> for Scalar {
    fn from(value: u8) -> Self {
        Self(U256::from_u8(value))
    }
}

impl From<u16> for Scalar {
    fn from(value: u16) -> Self {
        Self(U256::from_u16(value))
    }
}

impl From<u32> for Scalar {
    fn from(value: u32) -> Self {
        Self(U256::from_u32(value))
    }
}

impl From<u64> for Scalar {
    fn from(value: u64) -> Self {
        Self(U256::from_u64(value))
    }
}

#[cfg(target_pointer_width = "64")]
impl From<u128> for Scalar {
    fn from(value: u128) -> Self {
        Self(U256::from_u128(value))
    }
}

impl ConstantTimeEq for Scalar {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl ConditionallySelectable for Scalar {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(U256::conditional_select(&a.0, &b.0, choice))
    }
}

impl PartialEq for Scalar {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl Eq for Scalar {}

impl Ord for Scalar {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for Scalar {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl AddAssign for Scalar {
    fn add_assign(&mut self, other: Self) {
        *self = self.addition(&other)
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = Scalar, RHS = Scalar, OUTPUT = Scalar);

impl SubAssign for Scalar {
    fn sub_assign(&mut self, other: Self) {
        *self = self.subtract(&other)
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = Scalar, RHS = Scalar, OUTPUT = Scalar);

impl MulAssign for Scalar {
    fn mul_assign(&mut self, other: Self) {
        *self = self.multiply(&other)
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = Scalar, RHS = Scalar, OUTPUT = Scalar);

impl ShrAssign<usize> for Scalar {
    fn shr_assign(&mut self, shift: usize) {
        self.0 >>= shift;
    }
}

ops_impl!(Shr, shr, >>, ShrAssign, shr_assign, >>=, LHS = Scalar, RHS = usize, OUTPUT = Scalar);

impl Neg for &Scalar {
    type Output = Scalar;

    fn neg(self) -> Scalar {
        self.negate()
    }
}

impl Neg for Scalar {
    type Output = Scalar;

    fn neg(self) -> Scalar {
        -&self
    }
}

impl<T: Borrow<Scalar>> Sum<T> for Scalar {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, item| acc + item.borrow())
    }
}

impl<T: Borrow<Scalar>> Product<T> for Scalar {
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, item| acc * item.borrow())
    }
}

impl Field for Scalar {
    const ZERO: Self = Self(U256::ZERO);
    const ONE: Self = Self(U256::ONE);

    fn random(mut rng: impl RngCore) -> Self {
        let mut bytes = [0u8; U512::BYTES];
        rng.fill_bytes(&mut bytes);
        let inner = (U512::from_be_slice(&bytes) % MODULUS_U512).resize();
        Self(inner)
    }

    fn square(&self) -> Self {
        let sqr = self.0.square_wide();
        Self(U256::const_rem_wide(sqr, &FqModulus::MODULUS).0)
    }

    fn double(&self) -> Self {
        Self(self.0.add_mod(&self.0, &FqModulus::MODULUS))
    }

    fn invert(&self) -> CtOption<Self> {
        let (inv, not_zero) = self.0.inv_mod(&FqModulus::MODULUS);
        CtOption::new(Self(inv), Choice::from(not_zero))
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        sqrt_ratio_generic(num, div)
    }
}

impl PrimeField for Scalar {
    type Repr = ScalarBytes;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let inner = U256::from_be_slice(&repr);
        let value = inner % MODULUS_U256;
        CtOption::new(Self(value), inner.ct_eq(&value))
    }

    fn to_repr(&self) -> Self::Repr {
        let mut bytes = GenericArray::default();
        bytes.copy_from_slice(&self.0.to_le_bytes()[..]);
        bytes
    }

    fn is_odd(&self) -> Choice {
        self.0.is_odd()
    }

    const MODULUS: &'static str =
        "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";
    const NUM_BITS: u32 = 254;
    const CAPACITY: u32 = Self::NUM_BITS - 1;
    const TWO_INV: Self = Self(U256::from_be_hex(
        "10c441f29d0c5e3f9c3f539a6a7f52936a9d23257fc15e6f74fd1a274edbcea1",
    ));
    const MULTIPLICATIVE_GENERATOR: Self = Self(U256::from_u8(5));
    const S: u32 = 28;
    const ROOT_OF_UNITY: Self = Self(U256::from_be_hex(
        "1cdb5c39ff3b56c597ba56981c3f8af123cfd46efb164118423f59db933a6b4c",
    ));
    const ROOT_OF_UNITY_INV: Self = Self(U256::from_be_hex(
        "0f78afc5f9a9e41c6f2f4de7faed5d2bf49c1203da7f40b8860c7b9b81b9b53b",
    ));
    const DELTA: Self = Self(U256::from_be_hex(
        "2c3f4b0d4dd837e7799b6d1e4da4c8e60a80a53ab530fda6e6809dffb040e6e9",
    ));
}

#[cfg(not(target_pointer_width = "64"))]
type ReprBits = [u32; 8];
#[cfg(target_pointer_width = "64")]
type ReprBits = [u64; 4];

impl PrimeFieldBits for Scalar {
    type ReprBits = ReprBits;

    fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        self.0.to_words().into()
    }

    fn char_le_bits() -> FieldBits<Self::ReprBits> {
        FqModulus::MODULUS.to_words().into()
    }
}

impl FromUintUnchecked for Scalar {
    type Uint = U256;

    fn from_uint_unchecked(uint: Self::Uint) -> Self {
        Self(uint)
    }
}

impl Invert for Scalar {
    type Output = CtOption<Self>;

    fn invert(&self) -> Self::Output {
        <Self as Field>::invert(self)
    }
}

impl IsHigh for Scalar {
    fn is_high(&self) -> Choice {
        self.0.ct_gt(&HALF_MODULUS)
    }
}

impl From<Scalar> for [u8; 32] {
    fn from(value: Scalar) -> Self {
        value.to_repr().into()
    }
}

impl From<&Scalar> for [u8; 32] {
    fn from(value: &Scalar) -> Self {
        value.to_repr().into()
    }
}

impl From<Scalar> for ScalarBytes {
    fn from(value: Scalar) -> Self {
        value.to_repr()
    }
}

impl From<&Scalar> for ScalarBytes {
    fn from(value: &Scalar) -> Self {
        value.to_repr()
    }
}

impl From<Scalar> for U256 {
    fn from(value: Scalar) -> Self {
        value.0
    }
}

impl From<Scalar> for U384 {
    fn from(value: Scalar) -> Self {
        value.0.resize()
    }
}

impl From<Scalar> for U512 {
    fn from(value: Scalar) -> Self {
        value.0.resize()
    }
}

impl FromOkm for Scalar {
    type Length = U48;

    fn from_okm(data: &GenericArray<u8, Self::Length>) -> Self {
        Self::reduce(U384::from_be_slice(data))
    }
}

impl From<ScalarPrimitive<Bn254G1>> for Scalar {
    fn from(value: ScalarPrimitive<Bn254G1>) -> Self {
        Self(*value.as_uint())
    }
}

impl From<&ScalarPrimitive<Bn254G1>> for Scalar {
    fn from(value: &ScalarPrimitive<Bn254G1>) -> Self {
        Self(*value.as_uint())
    }
}

impl From<Scalar> for ScalarPrimitive<Bn254G1> {
    fn from(value: Scalar) -> ScalarPrimitive<Bn254G1> {
        Self::from_uint_unchecked(value.0)
    }
}

impl From<&Scalar> for ScalarPrimitive<Bn254G1> {
    fn from(value: &Scalar) -> ScalarPrimitive<Bn254G1> {
        Self::from_uint_unchecked(value.0)
    }
}

impl Reduce<U256> for Scalar {
    type Bytes = G1Repr;

    fn reduce(n: U256) -> Self {
        let (r, underflow) = n.sbb(&FqModulus::MODULUS, Limb::ZERO);
        let underflow = Choice::from((underflow.0 >> (Limb::BITS - 1)) as u8);
        Self(U256::conditional_select(&n, &r, !underflow))
    }

    fn reduce_bytes(bytes: &Self::Bytes) -> Self {
        Self::reduce(U256::from_be_slice(bytes))
    }
}

impl Reduce<U384> for Scalar {
    type Bytes = GenericArray<u8, U48>;

    fn reduce(n: U384) -> Self {
        let (r, underflow) = n.sbb(&FqModulus::MODULUS.resize(), Limb::ZERO);
        let underflow = Choice::from((underflow.0 >> (Limb::BITS - 1)) as u8);
        Self(U256::conditional_select(
            &n.resize(),
            &r.resize(),
            !underflow,
        ))
    }

    fn reduce_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_okm(bytes)
    }
}

impl Reduce<U512> for Scalar {
    type Bytes = GenericArray<u8, U64>;

    fn reduce(n: U512) -> Self {
        let (r, underflow) = n.sbb(&FqModulus::MODULUS.resize(), Limb::ZERO);
        let underflow = Choice::from((underflow.0 >> (Limb::BITS - 1)) as u8);
        Self(U256::conditional_select(
            &n.resize(),
            &r.resize(),
            !underflow,
        ))
    }

    fn reduce_bytes(bytes: &Self::Bytes) -> Self {
        Self::reduce(U512::from_be_slice(bytes))
    }
}

impl ReduceNonZero<U256> for Scalar {
    fn reduce_nonzero(n: U256) -> Self {
        let (r, underflow) = n.sbb(&MODULUS_M1_U256, Limb::ZERO);
        let underflow = Choice::from((underflow.0 >> (Limb::BITS - 1)) as u8);
        Self(U256::conditional_select(&n, &r, !underflow).wrapping_add(&U256::ONE))
    }

    fn reduce_nonzero_bytes(bytes: &Self::Bytes) -> Self {
        Self::reduce_nonzero(U256::from_be_slice(bytes))
    }
}

impl ReduceNonZero<U384> for Scalar {
    fn reduce_nonzero(n: U384) -> Self {
        let (r, underflow) = n.sbb(&MODULUS_M1_U384, Limb::ZERO);
        let underflow = Choice::from((underflow.0 >> (Limb::BITS - 1)) as u8);
        Self(
            U256::conditional_select(&n.resize(), &r.resize(), !underflow).wrapping_add(&U256::ONE),
        )
    }

    fn reduce_nonzero_bytes(bytes: &Self::Bytes) -> Self {
        Self::reduce_nonzero(U384::from_be_slice(bytes))
    }
}

impl ReduceNonZero<U512> for Scalar {
    fn reduce_nonzero(n: U512) -> Self {
        let (r, underflow) = n.sbb(&MODULUS_M1_U512, Limb::ZERO);
        let underflow = Choice::from((underflow.0 >> (Limb::BITS - 1)) as u8);
        Self(
            U256::conditional_select(&n.resize(), &r.resize(), !underflow).wrapping_add(&U256::ONE),
        )
    }

    fn reduce_nonzero_bytes(bytes: &Self::Bytes) -> Self {
        Self::reduce_nonzero(U512::from_be_slice(bytes))
    }
}

bytes_impl!(Scalar, |s: &Scalar| s.to_repr(), |bytes: &[u8]| {
    let repr =
        <[u8; Scalar::BYTES]>::try_from(bytes).map_err(|_| Bn254Error::InvalidScalarBytes)?;
    Option::<Scalar>::from(Scalar::from_repr(repr.into())).ok_or(Bn254Error::InvalidScalarBytes)
});

serde_impl!(
    Scalar,
    |s: &Scalar| s.to_repr(),
    |bytes: &[u8; Scalar::BYTES]| {
        let bytes = (*bytes).into();
        Option::<Scalar>::from(Scalar::from_repr(bytes))
            .ok_or(serde::de::Error::custom("Invalid bytes"))
    },
    Scalar::BYTES
);

impl AsRef<Scalar> for Scalar {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl Scalar {
    pub const BYTES: usize = 32;

    pub const fn from_u8(value: u8) -> Self {
        Self(U256::from_u8(value))
    }

    pub const fn from_u16(value: u16) -> Self {
        Self(U256::from_u16(value))
    }

    pub const fn from_u32(value: u32) -> Self {
        Self(U256::from_u32(value))
    }

    pub const fn from_u64(value: u64) -> Self {
        Self(U256::from_u64(value))
    }

    #[cfg(target_pointer_width = "64")]
    pub const fn from_u128(value: u128) -> Self {
        Self(U256::from_u128(value))
    }

    pub fn is_zero(&self) -> Choice {
        self.0.is_zero()
    }

    pub const fn double(&self) -> Self {
        self.addition(self)
    }

    pub const fn addition(&self, rhs: &Self) -> Self {
        Self(self.0.add_mod(&rhs.0, &FqModulus::MODULUS))
    }

    pub const fn subtract(&self, rhs: &Self) -> Self {
        Self(self.0.sub_mod(&rhs.0, &FqModulus::MODULUS))
    }

    pub const fn multiply(&self, rhs: &Self) -> Self {
        let m = self.0.mul_wide(&rhs.0);
        Self(U256::const_rem_wide(m, &FqModulus::MODULUS).0)
    }

    pub const fn square(&self) -> Self {
        let sqr = self.0.square_wide();
        Self(U256::const_rem_wide(sqr, &FqModulus::MODULUS).0)
    }

    pub const fn negate(&self) -> Self {
        Self(self.0.neg_mod(&FqModulus::MODULUS))
    }

    pub const fn exp(&self, e: &U256) -> Self {
        let base = FqResidue::new(&self.0);
        Self(base.pow(e).retrieve())
    }

    pub(crate) fn to_le_bytes(self) -> [u8; 32] {
        self.0.to_le_bytes()
    }

    pub fn hash<X>(msg: &[u8], dst: &[u8]) -> Self
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let d = [dst];
        let mut expander = X::expand_message(&[msg], &d, 48).expect("Failed to expand message");
        let mut buf = GenericArray::<u8, U48>::default();
        expander.fill_bytes(&mut buf);
        Self::from_okm(&buf)
    }
}
