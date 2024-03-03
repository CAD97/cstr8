#[cfg(feature = "std")]
use std::{ffi::OsStr, path::Path};

use core::{
    cmp,
    ffi::{CStr, FromBytesWithNulError},
    fmt,
    ops::{Deref, Index},
    slice::SliceIndex,
    str::{self, Utf8Error},
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

impl<'a> TryFrom<&'a CStr> for &'a CStr8 {
    type Error = CStr8Error;

    fn try_from(s: &'a CStr) -> Result<&'a CStr8, CStr8Error> {
        CStr8::from_utf8_with_nul(s.to_bytes_with_nul())
    }
}

#[cfg(feature = "alloc")]
mod alloc_impls {
    use {
        crate::{CStr8, CString8},
        alloc::{
            borrow::{Cow, ToOwned},
            boxed::Box,
            ffi::CString,
            rc::Rc,
            string::String,
            sync::Arc,
        },
        core::ffi::CStr,
    };

    // We only provide From impls matching CStr, not str. This helps avoid some
    // "does it include the nul terminator" confusion around inferred .into()s.

    impl From<&CStr8> for Arc<CStr8> {
        fn from(s: &CStr8) -> Arc<CStr8> {
            let arc = Arc::<[u8]>::from(s.as_bytes_with_nul());
            // SAFETY: This is how you spell a transmute of Arc's pointee type.
            unsafe { Arc::from_raw(Arc::into_raw(arc) as *const CStr8) }
        }
    }

    impl From<&CStr8> for Arc<CStr> {
        fn from(s: &CStr8) -> Arc<CStr> {
            s.as_c_str().into()
        }
    }

    impl From<&CStr8> for Arc<str> {
        fn from(s: &CStr8) -> Arc<str> {
            s.as_str().into()
        }
    }

    impl From<&CStr8> for Box<CStr8> {
        fn from(s: &CStr8) -> Box<CStr8> {
            let boxed = Box::<[u8]>::from(s.as_bytes_with_nul());
            // SAFETY: This is how you spell a transmute of Box's pointee type.
            unsafe { Box::from_raw(Box::into_raw(boxed) as *mut CStr8) }
        }
    }

    impl From<&CStr8> for Box<CStr> {
        fn from(s: &CStr8) -> Box<CStr> {
            s.as_c_str().into()
        }
    }

    impl From<&CStr8> for Box<str> {
        fn from(s: &CStr8) -> Box<str> {
            s.as_str().into()
        }
    }

    impl<'a> From<&'a CStr8> for Cow<'a, CStr8> {
        fn from(s: &'a CStr8) -> Cow<'a, CStr8> {
            Cow::Borrowed(s)
        }
    }

    impl<'a> From<&'a CStr8> for Cow<'a, CStr> {
        fn from(s: &'a CStr8) -> Cow<'a, CStr> {
            s.as_c_str().into()
        }
    }

    impl<'a> From<&'a CStr8> for Cow<'a, str> {
        fn from(s: &'a CStr8) -> Cow<'a, str> {
            s.as_str().into()
        }
    }

    impl From<&CStr8> for Rc<CStr8> {
        fn from(s: &CStr8) -> Rc<CStr8> {
            let rc = Rc::<[u8]>::from(s.as_bytes_with_nul());
            // SAFETY: This is how you spell a transmute of Rc's pointee type.
            unsafe { Rc::from_raw(Rc::into_raw(rc) as *const CStr8) }
        }
    }

    impl From<&CStr8> for Rc<CStr> {
        fn from(s: &CStr8) -> Rc<CStr> {
            s.as_c_str().into()
        }
    }

    impl From<&CStr8> for Rc<str> {
        fn from(s: &CStr8) -> Rc<str> {
            s.as_str().into()
        }
    }

    impl From<&CStr8> for CString8 {
        fn from(s: &CStr8) -> CString8 {
            s.to_owned()
        }
    }

    impl From<&CStr8> for CString {
        fn from(s: &CStr8) -> CString {
            s.as_c_str().into()
        }
    }

    impl From<&CStr8> for String {
        fn from(s: &CStr8) -> String {
            s.as_str().into()
        }
    }

    impl From<Cow<'_, CStr8>> for Box<CStr8> {
        fn from(s: Cow<'_, CStr8>) -> Box<CStr8> {
            match s {
                Cow::Borrowed(s) => Box::from(s),
                Cow::Owned(s) => Box::from(s),
            }
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

    impl ToOwned for CStr8 {
        type Owned = CString8;

        fn to_owned(&self) -> CString8 {
            // SAFETY: The single nul terminator is maintained.
            unsafe { CString8::from_vec_unchecked(self.as_bytes_with_nul().to_owned()) }
        }

        // fn clone_into(&self, target: &mut CString8) {
        //     let mut b = mem::take(target).into_bytes_with_nul();
        //     self.as_bytes_with_nul().clone_into(&mut b);
        //     *target = unsafe { CString8::from_vec_unchecked(b) }
        // }
    }
}

#[cfg(feature = "std")]
mod std_impls {
    use crate::CStr8;
    use core::cmp;
    use std::{
        ffi::{OsStr, OsString},
        path::Path,
    };

    impl AsRef<OsStr> for CStr8 {
        fn as_ref(&self) -> &OsStr {
            self.as_str().as_ref()
        }
    }

    impl AsRef<Path> for CStr8 {
        fn as_ref(&self) -> &Path {
            self.as_str().as_ref()
        }
    }

    impl PartialEq<OsStr> for CStr8 {
        fn eq(&self, other: &OsStr) -> bool {
            self.as_str() == other
        }
    }

    impl PartialEq<OsString> for &'_ CStr8 {
        fn eq(&self, other: &OsString) -> bool {
            self.as_str() == other
        }
    }

    impl PartialEq<OsString> for CStr8 {
        fn eq(&self, other: &OsString) -> bool {
            self.as_str() == other
        }
    }

    impl PartialEq<CStr8> for OsStr {
        fn eq(&self, other: &CStr8) -> bool {
            self == other.as_str()
        }
    }

    impl PartialEq<CStr8> for OsString {
        fn eq(&self, other: &CStr8) -> bool {
            self == other.as_str()
        }
    }

    impl PartialOrd<CStr8> for OsStr {
        fn partial_cmp(&self, other: &CStr8) -> Option<cmp::Ordering> {
            self.partial_cmp(other.as_str())
        }
    }

    impl PartialOrd<CStr8> for OsString {
        fn partial_cmp(&self, other: &CStr8) -> Option<cmp::Ordering> {
            self.partial_cmp(other.as_str())
        }
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
        self.as_ref()
    }

    /// Converts this to a normal path slice.
    /// *This will not include the nul terminator*.
    ///
    /// You can also just use the generic prelude [`AsRef::as_ref`] instead.
    #[cfg(feature = "std")]
    pub fn as_path(&self) -> &Path {
        self.as_ref()
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

    /// Asserts that the byte slice contains a nul-terminator and is valid UTF-8
    /// up to that point.
    ///
    /// If the first byte is a nul character, this method will return an empty
    /// `CStr8`. If multiple nul characters are present, the `CStr8` will end
    /// at the first one.
    ///
    /// If the slice only has a single nul byte at the end, this method is
    /// equivalent to [`CStr8::from_utf8_with_nul`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cstr8::CStr8;
    ///
    /// let mut buffer = [0u8; 16];
    /// unsafe {
    ///     // Here we might call an unsafe C function that writes a string
    ///     // into the buffer.
    ///     let buf_ptr = buffer.as_mut_ptr();
    ///     buf_ptr.write_bytes(b'A', 8);
    /// }
    /// // Attempt to extract a nul-terminated string from the buffer.
    /// let c_str = CStr8::from_utf8_until_nul(&buffer)?;
    /// assert_eq!(c_str, "AAAAAAAA");
    /// # Ok::<_, cstr8::CStr8Error>(())
    /// ```
    pub fn from_utf8_until_nul(v: &[u8]) -> Result<&CStr8, CStr8Error> {
        let v = CStr::from_bytes_until_nul(v)
            .map(CStr::to_bytes_with_nul)
            .unwrap_or_default();
        Self::from_utf8_with_nul(v)
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
        CStr8::from_utf8_with_nul_unchecked(CStr::from_ptr(ptr.cast()).to_bytes_with_nul())
    }
}

/// An error converting to [`CStr8`].
///
/// If multiple errors apply, which one you get back is unspecified.
#[derive(Debug)]
pub enum CStr8Error {
    /// The string is not valid UTF-8.
    InvalidUtf8(Utf8Error),
    /// The string does not contain a singular terminating nul byte.
    NulError(FromBytesWithNulError),
}

#[cfg(feature = "std")]
impl std::error::Error for CStr8Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            CStr8Error::InvalidUtf8(source) => Some(source),
            CStr8Error::NulError(source) => Some(source),
        }
    }
}

impl fmt::Display for CStr8Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CStr8Error::InvalidUtf8(_) => f.write_str("invalid UTF-8"),
            CStr8Error::NulError(_) => f.write_str("invalid nul terminator"),
        }
    }
}

impl From<Utf8Error> for CStr8Error {
    fn from(source: Utf8Error) -> Self {
        CStr8Error::InvalidUtf8(source)
    }
}

impl From<FromBytesWithNulError> for CStr8Error {
    fn from(source: FromBytesWithNulError) -> Self {
        CStr8Error::NulError(source)
    }
}
