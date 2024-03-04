#[cfg(doc)]
use crate::CStr8;

/// Create a const <code>&'static [CStr8]</code> from a const string.
///
/// The macro accepts these types as input, rejecting them at compile time
/// if they contain a nul byte or aren't UTF-8:
///
/// - `&str`
/// - `&CStr`
/// - `&[u8]`
/// - `&[u8; N]`
/// - `[u8; N]`
///
/// # Examples
///
/// ```rust
/// use core::ffi::CStr;
/// use cstr8::{cstr8, CStr8};
///
/// const LITERAL: &CStr8 = cstr8!("literal");
/// assert_eq!(LITERAL, "literal");
/// assert_eq!(LITERAL.as_bytes_with_nul(), b"literal\0");
///
/// const CONSTANT: &str = "constant";
/// const WITH_NUL: &CStr8 = cstr8!(CONSTANT);
/// assert_eq!(WITH_NUL, "constant");
/// assert_eq!(WITH_NUL.as_bytes_with_nul(), b"constant\0");
///
/// const CSTR_CONSTANT: &CStr = match CStr::from_bytes_until_nul(b"cstr constant\0") {
///     Ok(x) => x,
///     Err(_) => unreachable!(),
/// };
/// assert_eq!(cstr8!(CSTR_CONSTANT).as_bytes_with_nul(), b"cstr constant\0");
///
/// const BYTES_CONSTANT: &[u8] = b"bytes constant";
/// assert_eq!(cstr8!(BYTES_CONSTANT), "bytes constant");
///
/// const BYTE_ARRAY_REF_CONSTANT: &[u8; 23] = b"byte array ref constant";
/// assert_eq!(cstr8!(BYTE_ARRAY_REF_CONSTANT).as_bytes_with_nul(), b"byte array ref constant\0");
///
/// const BYTE_ARRAY_CONSTANT: [u8; 19] = *b"byte array constant";
/// assert_eq!(cstr8!(BYTE_ARRAY_CONSTANT).as_bytes_with_nul(), b"byte array constant\0");
///
/// ```
///
/// Internal nul bytes will cause a compilation error:
///
/// ```rust,compile_fail
/// # use cstr8::{cstr8, CStr8};
/// const ERROR: &CStr8 = cstr8!("oh \0 no");
/// //~^ ERROR: cstr8: input contains nul byte
/// ```
///
/// Invalid UTF-8 will also cause a compilation error:
///
/// ```rust,compile_fail
/// # use cstr8::{cstr8, CStr8};
/// const ERROR: &CStr8 = cstr8!(b"Invalid sequence identifier: \xa0\xa1");
/// //~^ ERROR: cstr8: input is not valid UTF-8
/// ```
///
/// # Restrictions
///
/// The `cstr8!` macro can't access local generic types, even if constant.
/// This can be fixed when [`inline_const`] stabilizes.
///
/// ```compile_fail
/// use cstr8::{cstr8, CStr8};
/// trait Name {
///    const NAME: &'static str = "sample name";
/// }
/// fn cstr8_name<T: Name>() -> &'static CStr8 {
///    cstr8!(T::NAME)
///    //~^ ERROR: can't use generic parameters from outer item
/// }
/// ```
///
/// [`inline_const`]: https://github.com/rust-lang/rust/issues/76001
#[macro_export]
macro_rules! cstr8 {
    ($s:expr) => {{
        const __CSTR8_ARRAY: $crate::__internal_unstable::CStr8Array<
            { $crate::__internal_unstable::CStr8Builder($s).len_before_nul() },
        > = $crate::__internal_unstable::CStr8Builder($s).build_or_const_panic();
        __CSTR8_ARRAY.as_cstr8()
    }};
}

/// NOT PUBLIC API. DO NOT USE DIRECTLY.
///
/// Macro-only utilities.
#[doc(hidden)]
pub mod __internal_unstable {
    use {
        crate::CStr8,
        core::{ffi::CStr, slice, str},
    };

    pub struct CStr8Builder<T>(pub T);

    impl CStr8Builder<&'static str> {
        pub const fn len_before_nul(self) -> usize {
            self.0.len()
        }

        pub const fn build_or_const_panic<const N: usize>(self) -> CStr8Array<N> {
            CStr8Array::from_str(self.0)
        }
    }

    impl CStr8Builder<&'static [u8]> {
        pub const fn len_before_nul(self) -> usize {
            self.0.len()
        }

        pub const fn build_or_const_panic<const N: usize>(self) -> CStr8Array<N> {
            CStr8Array::from_bytes(self.0)
        }
    }

    impl<const N: usize> CStr8Builder<&'static [u8; N]> {
        pub const fn len_before_nul(self) -> usize {
            N
        }

        pub const fn build_or_const_panic(self) -> CStr8Array<N> {
            CStr8Array::from_bytes(self.0)
        }
    }

    impl<const N: usize> CStr8Builder<[u8; N]> {
        pub const fn len_before_nul(self) -> usize {
            N
        }

        pub const fn build_or_const_panic(self) -> CStr8Array<N> {
            CStr8Array::from_bytes(&self.0)
        }
    }

    impl CStr8Builder<&'static CStr> {
        pub const fn len_before_nul(self) -> usize {
            self.0.to_bytes().len()
        }

        pub const fn build_or_const_panic<const N: usize>(self) -> CStr8Array<N> {
            CStr8Array::from_bytes(self.0.to_bytes())
        }
    }

    /// N is the length of the string excluding the nul byte.
    #[repr(C)]
    pub struct CStr8Array<const N: usize>([u8; N], u8);

    impl<const N: usize> CStr8Array<N> {
        const fn from_str(s: &str) -> Self {
            assert!(s.len() == N);
            let bytes = s.as_bytes();
            let mut out = [0; N];
            let mut i = 0;
            while i < N {
                let c = bytes[i];
                if c == 0 {
                    panic!("cstr8: input contains nul byte");
                }
                out[i] = c;
                i += 1;
            }
            Self(out, 0)
        }

        const fn from_bytes(b: &[u8]) -> Self {
            Self::from_str(match str::from_utf8(b) {
                Ok(x) => x,
                Err(_) => panic!("cstr8: input is not valid UTF-8"),
            })
        }

        pub const fn as_cstr8(&'static self) -> &'static CStr8 {
            // SAFETY:
            // - `Self` is #[repr(C)] and has no padding, and therefore
            //   is initialized for every byte.
            // - The only `\0` byte is guaranteed by `new` to be the last byte.
            unsafe {
                CStr8::from_utf8_with_nul_unchecked(slice::from_raw_parts(
                    (self as *const Self).cast(),
                    N + 1,
                ))
            }
        }
    }

    /// Doctests to ensure that the `cstr8!` macro compile-fails as expected.
    /// It must be located in a public module to be checked with `cargo test`.
    ///
    /// ```
    /// use core::ffi::CStr;
    /// use cstr8::{cstr8, CStr8};
    /// cstr8!("control test");
    /// cstr8!(match CStr::from_bytes_until_nul(b"control cstr\0") {
    ///     Ok(x) => x,
    ///     Err(_) => unreachable!(),
    /// });
    /// ```
    ///
    /// ```compile_fail
    /// use cstr8::{cstr8, CStr8};
    /// cstr8!("ends in nul \0");
    /// ```
    ///
    /// ```compile_fail
    /// use cstr8::{cstr8, CStr8};
    /// cstr8!("str with \0 nul");
    /// ```
    ///
    /// ```compile_fail
    /// use cstr8::{cstr8, CStr8};
    /// cstr8!(b"bytes with \0 nul");
    /// ```
    ///
    /// ```compile_fail
    /// use cstr8::{cstr8, CStr8};
    /// cstr8!(b"bytes with \xa0\xa1 invalid utf-8");
    /// ```
    ///
    /// ```compile_fail
    /// use cstr8::{cstr8, CStr8};
    /// cstr8!(&b"bytes with \0 nul"[..]);
    /// ```
    ///
    /// ```compile_fail
    /// use cstr8::{cstr8, CStr8};
    /// cstr8!(&b"bytes with \xa0\xa1 invalid utf-8"[..]);
    /// ```
    ///
    /// ```compile_fail
    /// use cstr8::{cstr8, CStr8};
    /// cstr8!(*b"byte array with \0 nul");
    /// ```
    ///
    /// ```compile_fail
    /// use cstr8::{cstr8, CStr8};
    /// cstr8!(b"bytes with \xa0\xa1 invalid utf-8");
    /// ```
    ///
    /// ```compile_fail
    /// use core::ffi::CStr;
    /// use cstr8::{cstr8, CStr8};
    /// cstr8!(match CStr::from_bytes_until_nul(b"cstr with \xa0\xa1 invalid utf-8\0") {
    ///     Ok(x) => x,
    ///     Err(_) => unreachable!(),
    /// });
    /// ```
    #[allow(dead_code)]
    pub struct TestMacroCompileFail;
}

#[cfg(test)]
mod tests {
    use {
        crate::{cstr8, CStr8},
        core::ffi::CStr,
    };

    #[test]
    fn test_cstr8_macro() {
        const STR_LITERAL: &CStr8 = cstr8!("literal");
        assert_eq!(STR_LITERAL, "literal");
        assert_eq!(STR_LITERAL.as_bytes_with_nul(), b"literal\0");

        const STR_CONSTANT: &str = "constant";
        const STR_WITH_NUL: &CStr8 = cstr8!(STR_CONSTANT);
        assert_eq!(STR_WITH_NUL, "constant");
        assert_eq!(STR_WITH_NUL.as_bytes_with_nul(), b"constant\0");

        // There is no `&[u8]` literal syntax.

        const BYTES_CONSTANT: &[u8] = b"bytes constant";
        const BYTES_WITH_NUL: &CStr8 = cstr8!(BYTES_CONSTANT);
        assert_eq!(BYTES_WITH_NUL, "bytes constant");
        assert_eq!(BYTES_WITH_NUL.as_bytes_with_nul(), b"bytes constant\0");

        const BYTE_ARRAY_REF_LITERAL: &CStr8 = cstr8!(b"bytes literal");
        assert_eq!(BYTE_ARRAY_REF_LITERAL, "bytes literal");
        assert_eq!(
            BYTE_ARRAY_REF_LITERAL.as_bytes_with_nul(),
            b"bytes literal\0"
        );

        const BYTE_ARRAY_REF_CONSTANT: &[u8; 14] = b"bytes constant";
        const BYTE_ARRAY_REF_WITH_NUL: &CStr8 = cstr8!(BYTE_ARRAY_REF_CONSTANT);
        assert_eq!(BYTE_ARRAY_REF_WITH_NUL, "bytes constant");
        assert_eq!(
            BYTE_ARRAY_REF_WITH_NUL.as_bytes_with_nul(),
            b"bytes constant\0"
        );

        const BYTE_ARRAY_LITERAL: &CStr8 = cstr8!([b'h', b'i']);
        assert_eq!(BYTE_ARRAY_LITERAL, "hi");
        assert_eq!(BYTE_ARRAY_LITERAL.as_bytes_with_nul(), b"hi\0");

        const BYTE_ARRAY_CONSTANT: [u8; 19] = *b"byte array constant";
        const BYTE_ARRAY_WITH_NUL: &CStr8 = cstr8!(BYTE_ARRAY_CONSTANT);
        assert_eq!(BYTE_ARRAY_WITH_NUL, "byte array constant");
        assert_eq!(
            BYTE_ARRAY_WITH_NUL.as_bytes_with_nul(),
            b"byte array constant\0"
        );

        // CStr literals cannot yet be tested because the MSRV of this crate is before
        // the stabilization of c"" literals scheduled for 1.77.

        const CSTR_CONSTANT: &CStr = match CStr::from_bytes_until_nul(b"cstr constant\0") {
            Ok(x) => x,
            Err(_) => unreachable!(),
        };
        const CSTR_UTF8: &CStr8 = cstr8!(CSTR_CONSTANT);
        assert_eq!(CSTR_UTF8, "cstr constant");
        assert_eq!(CSTR_UTF8.as_bytes_with_nul(), b"cstr constant\0");
    }
}
