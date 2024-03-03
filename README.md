Guaranteed valid nul-terminated UTF-8 C strings.

[![Latest version](https://img.shields.io/crates/v/cstr8.svg)](https://crates.io/crates/cstr8)
[![Documentation](https://docs.rs/cstr8/badge.svg)](https://docs.rs/cstr8)
![License](https://img.shields.io/crates/l/cstr8.svg)
![MSRV](https://img.shields.io/badge/MSRV-1.72-blue)
___


If there's some functionality you need which std's `str` or `CStr` provide but
`CStr8` doesn't, or similarly with `CString` and `CString8`, please open an
issue; lack of feature parity is considered a bug.

The name is derived from analogy with C++'s `std::char8_t` and `std::u8string`.

The minimum supported version of Rust will always be at least three months old
(stable - 2). Actual updates to the MSRV are expected to be fairly sporadic,
but will happen without ceremony as soon as they are desired for any reason.
