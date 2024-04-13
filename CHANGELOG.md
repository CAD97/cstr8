# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.4] - 2024-04-13

- Extend `cstr8!` to accept more types (#3, @kupiakos)

## [0.1.3] - 2024-03-02

- Now works in a `#![no_std]` configuration (#1, @kupiakos)
- Added some `From` implementations mirroring those on `str` and `CStr`
- Internal improvements, started keeping a proper changelog
- Fixed potential "unsafe leakage" in `cstr8!` macro

## [0.1.2] - 2023-08-05

- Added `CStr8::from_utf8_until_nul`

## [0.1.1] - 2022-06-13

- Added `CString8::into_string_with_nul`

[unreleased]: https://github.com/cad97/cstr8/compare/v0.1.4...HEAD
[0.1.3]: https://github.com/cad97/cstr8/compare/v0.1.3...v0.1.4
[0.1.3]: https://github.com/cad97/cstr8/compare/v0.1.2...v0.1.3
[0.1.2]: https://github.com/cad97/cstr8/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/cad97/cstr8/compare/v0.1.0...v0.1.1
