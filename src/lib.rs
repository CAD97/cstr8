//! String types that are both valid UTF-8 and nul-terminated.

#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

#[macro_use]
mod macros;

#[cfg(feature = "alloc")]
mod buf;

mod slice;

pub use self::{buf::*, macros::*, slice::*};

#[cfg(not(feature = "std"))]
compile_error!("std feature is currently required");
