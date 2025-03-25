#![no_std]

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{boxed::Box, string::String, vec::Vec};
#[cfg(feature = "std")]
use std::{boxed::Box, string::String, vec::Vec};

mod error;
mod helpers;
pub mod inner_types;

pub use error::*;
