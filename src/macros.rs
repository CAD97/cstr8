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
    ($s:expr) => {
        unsafe {
            const __CSTR: [$crate::u8; $crate::cstr_len_for($s)] = unsafe {
                $crate::transmute_prefix($crate::Concat(
                    $crate::str_as_byte_array::<{ $crate::str_len($s) }>($s),
                    b'\0',
                ))
            };
            $crate::CStr8::from_utf8_with_nul_unchecked(&__CSTR)
        }
    };
}

#[doc(hidden)]
/// NOT PUBLIC API. DO NOT USE DIRECTLY.
pub use u8;

#[doc(hidden)]
/// NOT PUBLIC API. DO NOT USE DIRECTLY.
#[repr(C)]
pub struct Concat<A, B>(pub A, pub B);

#[doc(hidden)]
/// NOT PUBLIC API. DO NOT USE DIRECTLY.
///
/// # Safety
///
/// It's `transmute_copy` but without the reference.
pub const unsafe fn transmute_prefix<From, To>(from: From) -> To {
    use core::mem::ManuallyDrop;

    #[repr(C)]
    union Transmute<From, To> {
        from: ManuallyDrop<From>,
        to: ManuallyDrop<To>,
    }

    ManuallyDrop::into_inner(
        Transmute {
            from: ManuallyDrop::new(from),
        }
        .to,
    )
}

#[doc(hidden)]
/// NOT PUBLIC API. DO NOT USE DIRECTLY.
pub const fn cstr_len_for(s: &str) -> usize {
    let mut len = 0;
    while len < s.len() {
        if s.as_bytes()[len] == 0 {
            panic!("cstr8: string contains nul byte");
        }
        len += 1;
    }
    len + 1
}

#[doc(hidden)]
/// NOT PUBLIC API. DO NOT USE DIRECTLY.
pub const fn str_len(s: &str) -> usize {
    s.len()
}

#[doc(hidden)]
/// NOT PUBLIC API. DO NOT USE DIRECTLY.
///
/// # Safety
///
/// `N <= s.len()`
pub const unsafe fn str_as_byte_array<const N: usize>(s: &str) -> [u8; N] {
    *(s.as_ptr() as *const [u8; N])
}
