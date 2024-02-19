use {
    crate::CStr8,
    alloc::{
        ffi::{CString, FromVecWithNulError, NulError},
        string::{FromUtf8Error, String},
        vec::Vec,
    },
    core::{borrow::Borrow, ffi::CStr, fmt, ops::Deref, str},
};

/// Owned string which is guaranteed UTF-8 and nul-terminated.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CString8 {
    raw: CString,
}

impl Deref for CString8 {
    type Target = CStr8;

    fn deref(&self) -> &CStr8 {
        unsafe { CStr8::from_utf8_with_nul_unchecked(self.raw.as_bytes_with_nul()) }
    }
}

impl fmt::Debug for CString8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl fmt::Display for CString8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl AsRef<CStr8> for CString8 {
    fn as_ref(&self) -> &CStr8 {
        self
    }
}

impl AsRef<CStr> for CString8 {
    fn as_ref(&self) -> &CStr {
        self.as_c_str()
    }
}

impl AsRef<str> for CString8 {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Borrow<CStr8> for CString8 {
    fn borrow(&self) -> &CStr8 {
        self
    }
}

/// Constructors.
impl CString8 {
    /// Creates a new C-compatible string.
    ///
    /// This function will consume the provided data and use the underlying
    /// bytes to construct a new string, ensuring that there is a trailing 0
    /// byte. This trailing 0 byte will be appended by this function; the
    /// provided data should not contain any 0 bytes in it.
    pub fn new<T: Into<String>>(t: T) -> Result<CString8, NulError> {
        let t = CString::new(t.into())?.into_bytes_with_nul();
        Ok(unsafe { CString8::from_vec_with_nul_unchecked(t) })
    }

    /// Asserts that a vec is valid UTF-8 and contains no interior nul bytes.
    ///
    /// A trailing 0 byte will be appended by this function.
    ///
    /// # Safety
    ///
    /// The provided data must be valid UTF-8 without any interior nul bytes.
    pub unsafe fn from_vec_unchecked(vec: Vec<u8>) -> Self {
        CString8 {
            raw: CString::from_vec_unchecked(vec),
        }
    }

    /// Retakes ownership of a `CString8` that was previously transfered via
    /// [`CString8::into_raw`].
    ///
    /// The length of the string will be recalculated from the pointer.
    ///
    /// # Safety
    ///
    /// The pointer must have been obtained by calling [`CString8::into_raw`].
    pub unsafe fn from_raw(ptr: *mut u8) -> Self {
        CString8 {
            raw: CString::from_raw(ptr as _),
        }
    }

    /// Converts a <code>[Vec]<[u8]></code> to a <code>CString8</code>
    /// without checking the invariants on the given [`Vec`].
    ///
    /// # Safety
    ///
    /// The given [`Vec`] must be valid UTF-8 without any interior nul bytes and
    /// a singular terminating nul byte.
    pub unsafe fn from_vec_with_nul_unchecked(vec: Vec<u8>) -> Self {
        CString8 {
            raw: CString::from_vec_with_nul_unchecked(vec),
        }
    }

    /// Converts a <code>[Vec]<[u8]></code> to a <code>CString8</code>.
    ///
    /// Runtime checks are present to ensure the vector is valid UTF-8 and there
    /// is only one nul byte in the [`Vec`], its last element.
    pub fn from_vec_with_nul(v: Vec<u8>) -> Result<Self, CString8Error> {
        let v = String::from_utf8(v)?.into_bytes();
        let v = CString::from_vec_with_nul(v)?.into_bytes_with_nul();
        Ok(unsafe { CString8::from_vec_with_nul_unchecked(v) })
    }
}

/// Destructors.
impl CString8 {
    /// Consumes the `CString8` and returns an owning raw pointer.
    pub fn into_raw(self) -> *mut u8 {
        self.raw.into_raw() as _
    }

    /// Converts the `CString8` into a [`String`]
    /// *without* the trailing nul terminator.
    pub fn into_string(self) -> String {
        unsafe { String::from_utf8_unchecked(self.into_bytes()) }
    }

    /// Converts the `CString8` into a [`String`]
    /// *with* the trailing nul terminator.
    pub fn into_string_with_nul(self) -> String {
        unsafe { String::from_utf8_unchecked(self.into_bytes_with_nul()) }
    }

    /// Converts the `CString8` into its underlying byte buffer
    /// *without* the trailing nul terminator.
    pub fn into_bytes(self) -> Vec<u8> {
        self.raw.into_bytes()
    }

    /// Converts the `CString8` into its underlying byte buffer
    /// *with* the trailing nul terminator.
    pub fn into_bytes_with_nul(self) -> Vec<u8> {
        self.raw.into_bytes_with_nul()
    }
}

/// An error converting to [`CString8`].
///
/// If multiple errors apply, which one you get back is unspecified.
#[derive(Debug)]
pub enum CString8Error {
    /// The string is not valid UTF-8.
    InvalidUtf8(FromUtf8Error),
    /// The string does not contain a singular terminating nul byte.
    NulError(FromVecWithNulError),
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "doc_nightly", doc(cfg(feature = "std")))]
impl std::error::Error for CString8Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            CString8Error::InvalidUtf8(source) => Some(source),
            CString8Error::NulError(source) => Some(source),
        }
    }
}

impl fmt::Display for CString8Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CString8Error::InvalidUtf8(_) => f.write_str("invalid UTF-8"),
            CString8Error::NulError(_) => f.write_str("invalid nul terminator"),
        }
    }
}

impl From<FromUtf8Error> for CString8Error {
    fn from(source: FromUtf8Error) -> Self {
        CString8Error::InvalidUtf8(source)
    }
}

impl From<FromVecWithNulError> for CString8Error {
    fn from(source: FromVecWithNulError) -> Self {
        CString8Error::NulError(source)
    }
}
