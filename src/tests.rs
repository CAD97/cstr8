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

    const CSTR_LITERAL: &CStr8 = cstr8!(c"cstr literal");
    assert_eq!(CSTR_LITERAL, "cstr literal");
    assert_eq!(CSTR_LITERAL.as_bytes_with_nul(), b"cstr literal\0");

    const CSTR_CONSTANT: &CStr = c"cstr constant";
    const CSTR_UTF8: &CStr8 = cstr8!(CSTR_CONSTANT);
    assert_eq!(CSTR_UTF8, "cstr constant");
    assert_eq!(CSTR_UTF8.as_bytes_with_nul(), b"cstr constant\0");
}
