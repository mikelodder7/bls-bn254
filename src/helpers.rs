use subtle::Choice;

pub const KEYGEN_SALT: &[u8] = b"BLS-SIG-KEYGEN-SALT-";

pub trait IsZero {
    fn is_zero(&self) -> Choice;
}

impl IsZero for [u8; 32] {
    fn is_zero(&self) -> Choice {
        let mut t = 0i8;
        for b in self {
            t |= *b as i8;
        }
        Choice::from((((t | -t) >> 7) + 1) as u8)
    }
}
