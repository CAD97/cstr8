#[cfg(doc)]
use crate::CStr8;

/// Create a const <code>&'static [CStr8]</code> from a const string.
///
/// # Example
///
/// ```rust
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
/// ```
///
/// Internal nul bytes will cause a compilation error:
///
/// ```rust,compile_fail
/// # use cstr8::{cstr8, CStr8};
/// const ERROR: &CStr8 = cstr8!("oh \0 no");
/// //~^ ERROR: string contains nul byte
/// ```
#[macro_export]
macro_rules! cstr8 {
    ($s:expr) => {{
        const __CSTR: $crate::__internal_unstable::CStr8Array<
            { $crate::__internal_unstable::str_len($s) },
        > = $crate::__internal_unstable::CStr8Array::new($s);
        __CSTR.as_cstr8()
    }};
}

/// NOT PUBLIC API. DO NOT USE DIRECTLY.
///
/// Macro-only utilities.
#[doc(hidden)]
pub mod __internal_unstable {
    use crate::CStr8;
    use core::slice;

    pub const fn str_len(x: &str) -> usize {
        x.len()
    }

    #[repr(C)]
    pub struct CStr8Array<const N: usize>([u8; N], u8);

    impl<const N: usize> CStr8Array<N> {
        pub const fn new(s: &str) -> Self {
            assert!(s.len() == N);
            let bytes = s.as_bytes();
            let mut out = [0; N];
            let mut i = 0;
            while i < N {
                let c = bytes[i];
                if c == 0 {
                    panic!("cstr8: string contains nul byte");
                }
                out[i] = c;
                i += 1;
            }
            Self(out, 0)
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
}
