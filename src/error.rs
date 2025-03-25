use core::fmt::{self, Display, Formatter};
use core2::error::Error;

#[derive(Debug)]
pub enum Bn254Error {
    InvalidScalarBytes,
    InvalidG1Bytes,
    InvalidG2Bytes,
}

impl Display for Bn254Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Bn254Error::InvalidScalarBytes => write!(f, "Invalid scalar bytes"),
            Bn254Error::InvalidG1Bytes => write!(f, "Invalid G1 bytes"),
            Bn254Error::InvalidG2Bytes => write!(f, "Invalid G2 bytes"),
        }
    }
}

impl Error for Bn254Error {}
