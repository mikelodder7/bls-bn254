use crate::inner_types::G1Projective;
use core::{
    borrow::Borrow,
    fmt::{self, Debug, Display, Formatter, LowerHex, UpperHex},
    iter::{Product, Sum},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use crypto_bigint::modular::constant_mod::Residue;
use crypto_bigint::Limb;
use elliptic_curve::hash2curve::MapToCurve;
use elliptic_curve::scalar::IsHigh;
use elliptic_curve::{
    bigint::{
        impl_modulus, modular::constant_mod::ResidueParams, Encoding, Integer, NonZero, Zero, U256,
        U384, U512,
    },
    consts::U48,
    generic_array::GenericArray,
    hash2curve::{ExpandMsg, Expander, FromOkm, Sgn0},
    Field, PrimeField,
};
use rand_core::RngCore;
use subtle::{
    Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater,
    CtOption,
};
use zeroize::DefaultIsZeroes;

impl_modulus!(
    FpModulus,
    U256,
    "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"
);

pub type FpResidue = Residue<FpModulus, { U256::LIMBS }>;
const HALF_MODULUS: U256 = FpModulus::MODULUS.shr_vartime(1);
pub(crate) const MODULUS_M1_DIV2: U256 = FpModulus::MODULUS.wrapping_sub(&U256::ONE).shr_vartime(1);
const MODULUS_U384: NonZero<U384> = NonZero::<U384>::const_new(FpModulus::MODULUS.resize()).0;
const MODULUS_U512: NonZero<U512> = NonZero::<U512>::const_new(FpModulus::MODULUS.resize()).0;

#[derive(Debug, Copy, Clone, Default)]
pub(crate) struct Fp(pub(crate) U256);

impl DefaultIsZeroes for Fp {}

impl Display for Fp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<u8> for Fp {
    fn from(value: u8) -> Self {
        Self(U256::from_u8(value))
    }
}

impl From<u16> for Fp {
    fn from(value: u16) -> Self {
        Self(U256::from_u16(value))
    }
}

impl From<u32> for Fp {
    fn from(value: u32) -> Self {
        Self(U256::from_u32(value))
    }
}

impl From<u64> for Fp {
    fn from(value: u64) -> Self {
        Self(U256::from_u64(value))
    }
}

#[cfg(target_pointer_width = "64")]
impl From<u128> for Fp {
    fn from(value: u128) -> Self {
        Self(U256::from_u128(value))
    }
}

impl LowerHex for Fp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:x}", self.0)
    }
}

impl UpperHex for Fp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:X}", self.0)
    }
}

impl ConstantTimeEq for Fp {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl ConditionallySelectable for Fp {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp(U256::conditional_select(&a.0, &b.0, choice))
    }
}

impl PartialEq for Fp {
    fn eq(&self, other: &Self) -> bool {
        self.0.ct_eq(&other.0).into()
    }
}

impl Eq for Fp {}

impl FromOkm for Fp {
    type Length = U48;

    fn from_okm(okm: &GenericArray<u8, Self::Length>) -> Self {
        let inner = (U384::from_be_slice(okm) % MODULUS_U384).resize();
        Self(inner)
    }
}

impl AddAssign for Fp {
    fn add_assign(&mut self, rhs: Fp) {
        *self = self.addition(&rhs);
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = Fp, RHS = Fp, OUTPUT = Fp);

impl SubAssign for Fp {
    fn sub_assign(&mut self, rhs: Fp) {
        *self = self.subtract(&rhs);
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = Fp, RHS = Fp, OUTPUT = Fp);

impl MulAssign for Fp {
    fn mul_assign(&mut self, rhs: Fp) {
        *self = self.multiply(&rhs);
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = Fp, RHS = Fp, OUTPUT = Fp);

impl Neg for &Fp {
    type Output = Fp;

    fn neg(self) -> Fp {
        -*self
    }
}

impl Neg for Fp {
    type Output = Fp;

    fn neg(self) -> Fp {
        Self(self.0.neg_mod(&FpModulus::MODULUS))
    }
}

impl Sgn0 for Fp {
    fn sgn0(&self) -> Choice {
        self.0.is_odd()
    }
}

impl<T: Borrow<Fp>> Sum<T> for Fp {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, item| acc + item.borrow())
    }
}

impl<T: Borrow<Fp>> Product<T> for Fp {
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, item| acc * item.borrow())
    }
}

impl IsHigh for Fp {
    fn is_high(&self) -> Choice {
        self.0.ct_gt(&HALF_MODULUS)
    }
}

impl Field for Fp {
    const ZERO: Self = Self(U256::ZERO);
    const ONE: Self = Self(U256::ONE);

    fn random(mut rng: impl RngCore) -> Self {
        let mut bytes = [0u8; U512::BYTES];
        rng.fill_bytes(&mut bytes);
        let inner = (U512::from_be_slice(&bytes) % MODULUS_U512).resize();
        Self(inner)
    }

    fn square(&self) -> Self {
        self.square()
    }

    fn double(&self) -> Self {
        self.double()
    }

    fn invert(&self) -> CtOption<Self> {
        let (inv, not_zero) = self.0.inv_odd_mod(&FpModulus::MODULUS);
        CtOption::new(Self(inv), Choice::from(not_zero))
    }

    fn sqrt_ratio(u: &Self, v: &Self) -> (Choice, Self) {
        // F.2.1.2.  Optimized sqrt_ratio for q = 3 mod 4
        // 1. c1 = (q - 3) / 4     # Integer arithmetic
        // 2. c2 = sqrt(-Z)
        const C1: [u64; 4] = FpModulus::MODULUS
            .wrapping_sub(&U256::from_u8(3))
            .shr_vartime(2)
            .to_words();

        // 1. tv1 = v^2
        let mut tv1 = v.square();
        // 2. tv2 = u * v
        let tv2 = u * v;
        // 3. tv1 = tv1 * tv2
        tv1 *= tv2;
        // 4. y1 = tv1^c1
        let mut y1 = tv1.pow(C1);
        // 5. y1 = y1 * tv2
        y1 *= tv2;
        // 6. y2 = y1 * c2
        let y2 = y1;
        // 7. tv3 = y1^2
        let mut tv3 = y1.square();
        // 8. tv3 = tv3 * v
        tv3 *= v;
        // 9. isQR = tv3 == u
        let is_qr = tv3.ct_eq(u);
        // 10. y = CMOV(y2, y1, isQR)
        let y = Fp::conditional_select(&y1, &y2, is_qr);
        // 11. return (isQR, y)
        (is_qr, y)
    }
}

impl PrimeField for Fp {
    type Repr = [u8; 32];

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let inner = U256::from_be_slice(&repr);
        let (_, underflow) = inner.sbb(&FpModulus::MODULUS, Limb::ZERO);
        let underflow = Choice::from((underflow.0 >> (Limb::BITS - 1)) as u8);
        CtOption::new(Self(inner), !underflow)
    }

    fn to_repr(&self) -> Self::Repr {
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(&self.0.to_be_bytes()[..]);
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
        "183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea4",
    ));
    const MULTIPLICATIVE_GENERATOR: Self = Self(U256::from_u8(3));
    const S: u32 = 1;
    const ROOT_OF_UNITY: Self = Self(U256::from_be_hex(
        "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd46",
    ));
    const ROOT_OF_UNITY_INV: Self = Self(U256::from_be_hex(
        "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd46",
    ));
    const DELTA: Self = Self(U256::from_u8(9));
}

impl MapToCurve for Fp {
    type Output = G1Projective;

    /// see https://github.com/ConsenSys/gnark-crypto/blob/master/ecc/bn254/hash_to_g1.go
    /// which implements
    /// MapToCurve1 implements the Shallue and van de Woestijne method, applicable to any elliptic curve in Weierstrass form
    /// No cofactor clearing or isogeny
    /// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-16.html#straightline-svdw
    fn map_to_curve(&self) -> Self::Output {
        //constants
        //c1 = g(Z)
        //c2 = -Z / 2
        //c3 = sqrt(-g(Z) * (3 * Z² + 4 * A))     # sgn0(c3) MUST equal 0
        //c4 = -4 * g(Z) / (3 * Z² + 4 * A)
        const Z: Fp = Fp::ONE;
        const C1: Fp = Fp(U256::from_u8(4));
        const C2: Fp = Fp(U256::from_words([
            0x9e10460b6c3e7ea3,
            0xcbc0b548b438e546,
            0xdc2822db40c0ac2e,
            0x183227397098d014,
        ]));
        const C3: Fp = Fp(U256::from_words([
            0x5d8d1cc5dffffffa,
            0x53c98fc6b36d713d,
            0x6789af3a83522eb3,
            0x0000000000000001,
        ]));
        const C4: Fp = Fp(U256::from_words([
            0x69602eb24829a9bd,
            0xdd2b2385cd7b4384,
            0xe81ac1e7808072c9,
            0x10216f7ba065e00d,
        ]));

        let mut tv1 = self.square(); //    1.  tv1 = u²
        tv1 *= C1; //    2.  tv1 = tv1 * c1
        let tv2 = Fp::ONE + tv1; //    3.  tv2 = 1 + tv1
        tv1 = Fp::ONE - tv1; //    4.  tv1 = 1 - tv1
        let mut tv3 = tv1 * tv2; //    5.  tv3 = tv1 * tv2

        tv3 = tv3.invert().expect("to not be zero"); //    6.  tv3 = inv0(tv3)
        let mut tv4 = self * tv1; //    7.  tv4 = u * tv1
        tv4 *= tv3; //    8.  tv4 = tv4 * tv3
        tv4 *= C3; //    9.  tv4 = tv4 * c3
        let x1 = C2 - tv4; //    10.  x1 = c2 - tv4

        let mut gx1 = x1.square(); //    11. gx1 = x1²
                                   //12. gx1 = gx1 + A  It is crucial to include this step if the curve has nonzero A coefficient.
        gx1 *= x1; //    13. gx1 = gx1 * x1
        gx1 += Fp::THREE; //    14. gx1 = gx1 + B

        // let gx1NotSquare: i32 = if gx1.legendre().is_qr() {0} else {-1};    //    15.  e1 = is_square(gx1)
        // gx1NotSquare = 0 if gx1 is a square, -1 otherwise

        let x2 = C2 + tv4; //    16.  x2 = c2 + tv4
        let mut gx2 = x2.square(); //    17. gx2 = x2²
                                   //    18. gx2 = gx2 + A     See line 12
        gx2 *= x2; //    19. gx2 = gx2 * x2
        gx2 += Fp::THREE; //    20. gx2 = gx2 + B

        let mut x3 = tv2.square(); //    22.  x3 = tv2²
        x3 *= tv3; //    23.  x3 = x3 * tv3
        x3 = x3.square(); //    24.  x3 = x3²
        x3 *= C4; //    25.  x3 = x3 * c4

        x3 += Z; //    26.  x3 = x3 + Z

        let e1 = gx1.is_square();
        let mut x = Fp::conditional_select(&x3, &x1, e1); //    27.   x = CMOV(x3, x1, e1)   # x = x1 if gx1 is square, else x = x3

        x.conditional_assign(&x2, gx2.is_square() & !e1); //    28.   x = CMOV(x, x2, e2)    # x = x2 if gx2 is square and gx1 is not
                                                          // Select x2 iff gx2 is square and gx1 is not, iff gx1SquareOrGx2Not = 0

        let mut gx = x.square(); //    29.  gx = x²
                                 //    30.  gx = gx + A
        gx *= x; //    31.  gx = gx * x
        gx += Fp::THREE; //    32.  gx = gx + B

        let mut y = gx.sqrt().expect("sqrt to work"); //    33.   y = sqrt(gx)

        let e3 = self.sgn0() ^ y.sgn0();

        y.conditional_negate(e3);

        G1Projective { x, y, z: Fp::ONE }
    }
}

impl Fp {
    /// The size of the field in bytes
    pub const BYTES: usize = 32;
    pub const B: Self = Self::from_montgomery([
        0x7a17caa950ad28d7,
        0x1f6ac17ae15521b9,
        0x334bea4e696bd284,
        0x2a1f6744ce179d8e,
    ]);

    /// Two
    pub const TWO: Self = Self(U256::from_u8(2));
    /// The value of B
    pub const THREE: Self = Self(U256::from_u8(3));

    pub const fn addition(&self, rhs: &Self) -> Self {
        Self(self.0.add_mod(&rhs.0, &FpModulus::MODULUS))
    }

    pub const fn double(&self) -> Self {
        Self(self.0.add_mod(&self.0, &FpModulus::MODULUS))
    }

    pub const fn subtract(&self, rhs: &Self) -> Self {
        Self(self.0.sub_mod(&rhs.0, &FpModulus::MODULUS))
    }

    pub const fn negate(&self) -> Self {
        Self(self.0.neg_mod(&FpModulus::MODULUS))
    }

    pub const fn multiply(&self, rhs: &Self) -> Self {
        let tmp = self.0.mul_wide(&rhs.0);
        Self(U256::const_rem_wide(tmp, &FpModulus::MODULUS).0)
    }

    pub const fn square(&self) -> Self {
        let tmp = self.0.square_wide();
        Self(U256::const_rem_wide(tmp, &FpModulus::MODULUS).0)
    }

    pub const fn mul_by_3b(&self) -> Self {
        self.double().double().double().addition(self)
    }

    pub fn is_zero(&self) -> Choice {
        self.0.is_zero()
    }

    pub fn is_one(&self) -> Choice {
        self.0.ct_eq(&U256::ONE)
    }

    /// Returns true whenever `self` is a square in the field
    /// using Euler's criterion.
    pub fn is_square(&self) -> Choice {
        let res = self.pow(MODULUS_M1_DIV2.as_words());
        res.is_zero() | res.ct_eq(&Self::ONE)
    }

    pub fn hash<X>(msg: &[u8], dst: &[u8]) -> [Self; 2]
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let dst = [dst];
        let mut random_bytes = [0u8; 96];
        let mut expander =
            X::expand_message(&[msg], &dst, random_bytes.len()).expect("Expander to succeed");
        expander.fill_bytes(&mut random_bytes);
        [
            Self::from_okm(&GenericArray::clone_from_slice(&random_bytes[..48])),
            Self::from_okm(&GenericArray::clone_from_slice(&random_bytes[48..])),
        ]
    }

    pub fn encode<X>(msg: &[u8], dst: &[u8]) -> Self
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let dst = [dst];
        let mut random_bytes = [0u8; 48];
        let mut expander =
            X::expand_message(&[msg], &dst, random_bytes.len()).expect("Expander to succeed");
        expander.fill_bytes(&mut random_bytes);
        Self::from_okm(&GenericArray::clone_from_slice(&random_bytes))
    }

    pub const fn from_be_hex(hex: &str) -> Self {
        Self(U256::from_be_hex(hex))
    }

    pub const fn from_montgomery(words: [u64; 4]) -> Self {
        Self(FpResidue::from_montgomery(U256::from_words(words)).retrieve())
    }
}
