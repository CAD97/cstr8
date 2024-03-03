//! String types that are both valid UTF-8 and nul-terminated.

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

#[macro_use]
mod macros;

#[cfg(feature = "alloc")]
mod buf;

mod slice;

#[cfg(feature = "alloc")]
pub use self::buf::*;

pub use self::{macros::*, slice::*};
