use {
    crate::CStr8,
    alloc::{
        borrow::Cow,
        boxed::Box,
        ffi::{CString, FromVecWithNulError, NulError},
        rc::Rc,
        string::{FromUtf8Error, String},
        sync::Arc,
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

impl<'a> From<&'a CString8> for Cow<'a, CStr8> {
    fn from(s: &'a CString8) -> Cow<'a, CStr8> {
        Cow::Borrowed(s.as_ref())
    }
}

impl From<Box<CStr8>> for CString8 {
    fn from(s: Box<CStr8>) -> CString8 {
        // SAFETY: This is how you spell a transmute of Box's pointee type.
        let s: Box<CStr> = unsafe { Box::from_raw(Box::into_raw(s) as *mut CStr) };
        CString8 {
            raw: s.into_c_string(),
        }
    }
}

impl From<CString8> for Arc<CStr8> {
    fn from(s: CString8) -> Arc<CStr8> {
        let arc: Arc<[u8]> = Arc::from(s.into_bytes_with_nul().into_boxed_slice());
        // SAFETY: This is how you spell a transmute of Arc's pointee type.
        unsafe { Arc::from_raw(Arc::into_raw(arc) as *const CStr8) }
    }
}

impl From<CString8> for Box<CStr8> {
    fn from(s: CString8) -> Box<CStr8> {
        let s: Box<[u8]> = s.into_bytes_with_nul().into_boxed_slice();
        // SAFETY: This is how you spell a transmute of Box's pointee type.
        unsafe { Box::from_raw(Box::into_raw(s) as *mut CStr8) }
    }
}

impl<'a> From<CString8> for Cow<'a, CStr8> {
    fn from(s: CString8) -> Cow<'a, CStr8> {
        Cow::Owned(s)
    }
}

impl From<CString8> for Rc<CStr8> {
    fn from(s: CString8) -> Rc<CStr8> {
        let rc: Rc<[u8]> = Rc::from(s.into_bytes_with_nul().into_boxed_slice());
        // SAFETY: This is how you spell a transmute of Rc's pointee type.
        unsafe { Rc::from_raw(Rc::into_raw(rc) as *const CStr8) }
    }
}

#[cfg(feature = "std")]
mod std_impls {
    use {
        crate::CString8,
        std::{
            ffi::{OsStr, OsString},
            path::{Path, PathBuf},
        },
    };

    impl AsRef<OsStr> for CString8 {
        fn as_ref(&self) -> &OsStr {
            self.as_str().as_ref()
        }
    }

    impl AsRef<Path> for CString8 {
        fn as_ref(&self) -> &Path {
            self.as_str().as_ref()
        }
    }

    impl From<CString8> for OsString {
        fn from(s: CString8) -> OsString {
            s.into_string().into()
        }
    }

    impl From<CString8> for PathBuf {
        fn from(s: CString8) -> PathBuf {
            s.into_string().into()
        }
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

    /// Retakes ownership of a `CString8` that was previously transferred via
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
