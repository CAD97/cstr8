Guaranteed valid nul-terminated UTF-8 C strings.

If there's some functionality you need which std's `str` or `CStr` provide but
`CStr8` doesn't, or similarly with `CString` and `CString8`, please open an
issue; the lack of feature parity is considered a bug.

The name is derived from analogy with C++'s `std::char8_t` and `std::u8string`.
