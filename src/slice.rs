#[cfg(feature = "alloc")]
use {
    crate::CString8,
    alloc::{borrow::ToOwned, string::String},
};

#[cfg(feature = "std")]
use std::path::Path;

use {
    core::{
        cmp, fmt, mem,
        ops::{Deref, Index},
        slice::SliceIndex,
        str::{self, Utf8Error},
    },
    std::ffi::{CStr, FromBytesWithNulError, OsStr},
    thiserror::Error,
};

/// String slice which is guaranteed UTF-8 and nul-terminated.
///
/// This dereferences to `str` *without the nul terminator*. If you want to
/// use the nul terminator, use [`as_c_str`](Self::as_c_str) instead.
#[repr(transparent)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CStr8 {
    raw: str,
}

impl Deref for CStr8 {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl Default for &'_ CStr8 {
    fn default() -> Self {
        cstr8!("")
    }
}

impl fmt::Debug for CStr8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl fmt::Display for CStr8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl AsRef<str> for CStr8 {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<CStr> for CStr8 {
    fn as_ref(&self) -> &CStr {
        self.as_c_str()
    }
}

impl AsRef<[u8]> for CStr8 {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<OsStr> for CStr8 {
    fn as_ref(&self) -> &OsStr {
        self.as_os_str()
    }
}

impl AsRef<Path> for CStr8 {
    fn as_ref(&self) -> &Path {
        self.as_path()
    }
}

impl PartialEq<str> for CStr8 {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<CStr8> for str {
    fn eq(&self, other: &CStr8) -> bool {
        self == other.as_str()
    }
}

impl PartialOrd<str> for CStr8 {
    fn partial_cmp(&self, other: &str) -> Option<cmp::Ordering> {
        self.as_str().partial_cmp(other)
    }
}

impl PartialOrd<CStr8> for str {
    fn partial_cmp(&self, other: &CStr8) -> Option<cmp::Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl PartialEq<CStr> for CStr8 {
    fn eq(&self, other: &CStr) -> bool {
        self.as_c_str() == other
    }
}

impl PartialEq<CStr8> for CStr {
    fn eq(&self, other: &CStr8) -> bool {
        self == other.as_c_str()
    }
}

impl PartialOrd<CStr> for CStr8 {
    fn partial_cmp(&self, other: &CStr) -> Option<cmp::Ordering> {
        self.as_c_str().partial_cmp(other)
    }
}

impl PartialOrd<CStr8> for CStr {
    fn partial_cmp(&self, other: &CStr8) -> Option<cmp::Ordering> {
        self.partial_cmp(other.as_c_str())
    }
}

impl PartialEq<String> for CStr8 {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<CStr8> for String {
    fn eq(&self, other: &CStr8) -> bool {
        self == other.as_str()
    }
}

#[cfg(feature = "alloc")]
impl ToOwned for CStr8 {
    type Owned = CString8;

    fn to_owned(&self) -> CString8 {
        unsafe { CString8::from_vec_unchecked(self.as_bytes_with_nul().to_owned()) }
    }

    fn clone_into(&self, target: &mut CString8) {
        let mut b = mem::take(target).into_bytes_with_nul();
        self.as_bytes_with_nul().clone_into(&mut b);
        *target = unsafe { CString8::from_vec_unchecked(b) }
    }
}

impl<I> Index<I> for CStr8
where
    I: SliceIndex<str>,
{
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        &self.as_str()[index]
    }
}

/// Explicit conversions.
impl CStr8 {
    /// Converts this to a normal string slice.
    /// *This will not include the nul terminator*.
    ///
    /// You can also just use the generic prelude [`AsRef::as_ref`] instead.
    pub const fn as_str(&self) -> &str {
        match self.raw.as_bytes() {
            [rest @ .., _nul] => unsafe { str::from_utf8_unchecked(rest) },
            [] => unreachable!(),
        }
    }

    /// Converts this to a normal C string.
    /// *This will include the nul terminator*.
    ///
    /// You can also just use the generic prelude [`AsRef::as_ref`] instead.
    pub const fn as_c_str(&self) -> &CStr {
        unsafe { CStr::from_bytes_with_nul_unchecked(self.raw.as_bytes()) }
    }

    /// Converts this to a normal byte slice.
    /// *This will not include the nul terminator*.
    ///
    /// You can also just use the generic prelude [`AsRef::as_ref`] instead.
    pub const fn as_bytes(&self) -> &[u8] {
        self.as_str().as_bytes()
    }

    /// Converts this to a normal byte slice.
    /// *This will include the nul terminator*.
    ///
    /// Note that [`AsRef::as_ref`] *excludes* the nul terminator.
    pub const fn as_bytes_with_nul(&self) -> &[u8] {
        self.raw.as_bytes()
    }

    /// Converts this to a normal OS string slice.
    /// *This will not include the nul terminator*.
    ///
    /// You can also just use the generic prelude [`AsRef::as_ref`] instead.
    #[cfg(feature = "std")]
    pub fn as_os_str(&self) -> &OsStr {
        self.as_str().as_ref()
    }

    /// Converts this to a normal path slice.
    /// *This will not include the nul terminator*.
    ///
    /// You can also just use the generic prelude [`AsRef::as_ref`] instead.
    #[cfg(feature = "std")]
    pub fn as_path(&self) -> &Path {
        self.as_str().as_ref()
    }
}

/// Constructors.
impl CStr8 {
    /// Asserts that the byte slice is valid UTF-8 and nul-terminated.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// use cstr8::CStr8;
    ///
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150, 0];
    ///
    /// // We know these are valid UTF-8 and nul-terminated, so just unwrap.
    /// let sparkle_heart = CStr8::from_utf8_with_nul(&sparkle_heart).unwrap();
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    ///
    /// Incorrect bytes:
    ///
    /// ```rust
    /// use cstr8::CStr8;
    ///
    /// // Invalid UTF-8
    /// let sparkle_heart = vec![1, 159, 146, 150, 0];
    /// assert!(CStr8::from_utf8_with_nul(&sparkle_heart).is_err());
    ///
    /// // Missing nul terminator
    /// let sparkle_heart = vec![240, 159, 146, 150];
    /// assert!(CStr8::from_utf8_with_nul(&sparkle_heart).is_err());
    ///
    /// // Embedded nul terminator
    /// let sparkle_heart = vec![0, 240, 159, 146, 150, 0];
    /// assert!(CStr8::from_utf8_with_nul(&sparkle_heart).is_err());
    /// ```
    pub fn from_utf8_with_nul(v: &[u8]) -> Result<&CStr8, CStr8Error> {
        let _ = str::from_utf8(v)?;
        let _ = CStr::from_bytes_with_nul(v)?;
        Ok(unsafe { CStr8::from_utf8_with_nul_unchecked(v) })
    }

    /// Unsafely assumes that the byte slice is valid UTF-8 and nul-terminated.
    ///
    /// # Safety
    ///
    /// The provided bytes must be valid UTF-8, nul-terminated, and not contain
    /// any interior nul bytes.
    pub const unsafe fn from_utf8_with_nul_unchecked(v: &[u8]) -> &CStr8 {
        &*(v as *const [u8] as *const CStr8)
    }

    /// Wraps a raw C string into a `CStr8`.
    ///
    /// # Safety
    ///
    /// The provided pointer must reference valid nul-terminated UTF-8, and the
    /// chosen lifetime must not outlive the raw C string's provenance.
    pub unsafe fn from_ptr<'a>(ptr: *const u8) -> &'a CStr8 {
        CStr8::from_utf8_with_nul_unchecked(CStr::from_ptr(ptr as _).to_bytes_with_nul())
    }
}

/// An error converting to [`CStr8`].
///
/// If multiple errors apply, which one you get back is unspecified.
#[derive(Debug, Error)]
pub enum CStr8Error {
    /// The string is not valid UTF-8.
    #[error("invalid UTF-8")]
    InvalidUtf8(#[from] Utf8Error),
    /// The string does not contain a singular terminating nul byte.
    #[error("invalid nul terminator")]
    NulError(#[from] FromBytesWithNulError),
}
