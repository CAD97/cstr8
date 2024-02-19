Guaranteed valid nul-terminated UTF-8 C strings.

[![Latest version](https://img.shields.io/crates/v/cstr8.svg)](https://crates.io/crates/cstr8)
[![Documentation](https://docs.rs/cstr8/badge.svg)](https://docs.rs/cstr8)
![License](https://img.shields.io/crates/l/cstr8.svg)
![MSRV](https://img.shields.io/badge/MSRV-1.69-blue)
___


If there's some functionality you need which std's `str` or `CStr` provide but
`CStr8` doesn't, or similarly with `CString` and `CString8`, please open an
issue; the lack of feature parity is considered a bug.

The name is derived from analogy with C++'s `std::char8_t` and `std::u8string`.
