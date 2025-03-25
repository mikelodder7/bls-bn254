#[macro_use]
mod macros;
mod fp;
mod fp2;
mod g1;
mod g2;
mod scalar;

pub use g1::*;
pub use g2::*;
pub use scalar::*;

use fp::*;
use fp2::*;

use elliptic_curve::bigint::Encoding;
use elliptic_curve::{
    bigint::{modular::constant_mod::ResidueParams, U256},
    consts::{U32, U64},
    point::PointCompression,
    Curve, CurveArithmetic, FieldBytes, FieldBytesEncoding, PrimeCurve,
};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Bn254G1;

unsafe impl Send for Bn254G1 {}
unsafe impl Sync for Bn254G1 {}

impl Curve for Bn254G1 {
    type FieldBytesSize = U32;
    type Uint = U256;

    const ORDER: U256 = FpModulus::MODULUS;
}

impl PrimeCurve for Bn254G1 {}

impl PointCompression for Bn254G1 {
    const COMPRESS_POINTS: bool = true;
}

impl FieldBytesEncoding<Bn254G1> for U256 {
    fn decode_field_bytes(field_bytes: &FieldBytes<Bn254G1>) -> Self {
        U256::from_be_slice(field_bytes)
    }

    fn encode_field_bytes(&self) -> FieldBytes<Bn254G1> {
        FieldBytes::<Bn254G1>::clone_from_slice(&self.to_be_bytes()[..])
    }
}

impl CurveArithmetic for Bn254G1 {
    type AffinePoint = G1Affine;
    type ProjectivePoint = G1Projective;
    type Scalar = Scalar;
}

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Bn254G2;

unsafe impl Send for Bn254G2 {}
unsafe impl Sync for Bn254G2 {}

impl Curve for Bn254G2 {
    type FieldBytesSize = U64;
    type Uint = U256;

    const ORDER: U256 = FpModulus::MODULUS;
}

impl PrimeCurve for Bn254G2 {}

impl FieldBytesEncoding<Bn254G2> for U256 {
    fn decode_field_bytes(field_bytes: &FieldBytes<Bn254G2>) -> Self {
        U256::from_be_slice(field_bytes)
    }

    fn encode_field_bytes(&self) -> FieldBytes<Bn254G2> {
        FieldBytes::<Bn254G2>::clone_from_slice(&self.to_be_bytes()[..])
    }
}

impl PointCompression for Bn254G2 {
    const COMPRESS_POINTS: bool = true;
}
