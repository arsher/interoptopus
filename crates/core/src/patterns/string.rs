//! Raw `*const char` pointer on C-level but a (ASCII) `string` like in supported languages.
//!
//! # Example
//!
//! In your library you can accept (ASCII- / C-) strings like this:
//!
//! ```
//! use interoptopus::ffi_function;
//! use interoptopus::patterns::string::CStrPointer;
//!
//! #[ffi_function]
//! #[no_mangle]
//! pub extern "C" fn call_with_string(s: CStrPointer) {
//!     //
//! }
//! ```
//!
//! Backends supporting this pattern might generate the equivalent to the following pseudo-code:
//!
//! ```csharp
//! void call_with_string(string s);
//! ```
//!
//! Backends not supporting this pattern, and C FFI, will see the equivalent of the following C code:
//! ```c
//! void call_with_string(uint8_t* s);
//! ```
//!

use crate::lang::c::{CType, CompositeType, Documentation, Field, Layout, Meta, PrimitiveType, Representation, Visibility};
use crate::lang::rust::CTypeInfo;
use crate::patterns::TypePattern;
use crate::Error;
use std::ffi::CStr;
use std::marker::PhantomData;
use std::option::Option::None;
use std::os::raw::c_char;
use std::ptr::null;

static EMPTY: &[u8] = b"\0";

/// Represents a `*const char` on FFI level pointing to an `0x0` terminated ASCII string.
///
/// # Antipattern
///
/// It's discouraged to use [`FFIOption`](crate::patterns::option::FFIOption) with [`CStrPointer`]
/// and some backend might not generate proper bindings (like C#).
///
/// Instead use [`CStrPointer`] alone since it already has a pointer that's nullable.
/// In this case, [`CStrPointer::as_c_str()`] will return [`None`] and [`CStrPointer::as_str`]
/// will return an [`Error::Null`].
#[repr(transparent)]
#[derive(Debug)]
pub struct CStrPointer<'a> {
    ptr: *const c_char,
    _phantom: PhantomData<&'a ()>,
}

impl<'a> Default for CStrPointer<'a> {
    fn default() -> Self {
        Self {
            ptr: null(),
            _phantom: Default::default(),
        }
    }
}

impl<'a> CStrPointer<'a> {
    pub fn empty() -> Self {
        Self {
            ptr: EMPTY.as_ptr().cast(),
            _phantom: Default::default(),
        }
    }

    /// Create a `CStrPointer` from a `&[u8]` slice reference.
    ///
    /// The parameter `cstr_with_nul` must contain nul (`0x0`), but it does not need to contain nul
    /// at the end.
    pub fn from_slice_with_nul(cstr_with_nul: &'a [u8]) -> Result<CStrPointer<'a>, Error> {
        // Check we actually contain one `0x0`.
        if !cstr_with_nul.contains(&0) {
            return Err(Error::NulTerminated);
        }

        // Can't do this, C# treats ASCII as extended and bytes > 127 might show up, which
        // is going to be a problem when returning a string we previously accepted.
        //
        // Any previous characters must not be extended ASCII.
        // if ascii_with_nul.iter().any(|x| *x > 127) {
        //     return Err(Error::Ascii);
        // }

        Ok(Self {
            ptr: cstr_with_nul.as_ptr().cast(),
            _phantom: Default::default(),
        })
    }

    /// Create a pointer from a CStr.
    pub fn from_cstr(cstr: &'a CStr) -> CStrPointer<'a> {
        Self {
            ptr: cstr.as_ptr(),
            _phantom: Default::default(),
        }
    }

    /// Create a [`CStr`] for the pointer.
    pub fn as_c_str(&self) -> Option<&'a CStr> {
        if self.ptr.is_null() {
            None
        } else {
            // TODO: Write something about safety
            unsafe { Some(CStr::from_ptr(self.ptr)) }
        }
    }

    /// Attempts to return a Rust `str`.
    pub fn as_str(&self) -> Result<&'a str, Error> {
        Ok(self.as_c_str().ok_or(Error::Null)?.to_str()?)
    }
}

unsafe impl<'a> CTypeInfo for CStrPointer<'a> {
    fn type_info() -> CType {
        CType::Pattern(TypePattern::CStrPointer)
    }
}

/// Owned ANSI zero terminated string with a fixed size.
/// Size includes the zero terminator.
#[repr(C)]
pub struct OwnedString<'a, const N: usize> {
    data: [u8; N],
    _phantom: PhantomData<&'a ()>,
}

unsafe impl<'a, const N: usize> CTypeInfo for OwnedString<'a, N> {
    fn type_info() -> CType {
        CType::Pattern(TypePattern::OwnedString(N))
    }
}

impl<'a, const N: usize> OwnedString<'a, N> {
    pub fn from_str(s: &str) -> Result<Self, Error> {
        let mut buffer = [0u8; N];
        let ansi_bytes = s.as_bytes();

        if N < ansi_bytes.len() + 1 {
            return Err(Error::StringTooLong);
        }

        let length = ansi_bytes.len().min(N - 1);
        buffer[..length].copy_from_slice(&ansi_bytes[..length]);

        Ok(Self {
            data: buffer,
            _phantom: Default::default(),
        })
    }

    pub fn from_string(s: String) -> Result<Self, crate::Error> {
        Self::from_str(&s)
    }

    pub fn as_str(&'a self) -> Result<&'a str, Error> {
        CStr::from_bytes_with_nul(&self.data)
            .map_err(|_| Error::NulTerminated)
            .and_then(|cstr| cstr.to_str().map_err(|e| Error::UTF8(e)))
    }
}

impl<'a, const N: usize> TryFrom<&str> for OwnedString<'a, N> {
    type Error = Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Self::from_str(value)
    }
}

impl<'a, const N: usize> TryFrom<String> for OwnedString<'a, N> {
    type Error = Error;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        Self::from_string(value)
    }
}

impl<'a, const N: usize> TryInto<String> for OwnedString<'a, N> {
    type Error = Error;

    fn try_into(self) -> Result<String, Self::Error> {
        Ok(self.as_str()?.to_string())
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct CStrMutPointer<'a> {
    ptr: *mut c_char,
    capacity: u32,
    _phantom: PhantomData<&'a ()>,
}

unsafe impl<'a> CTypeInfo for CStrMutPointer<'a> {
    fn type_info() -> CType {
        let doc_data = Documentation::from_line("Pointer to start of mutable ANSI string data.");
        let doc_len = Documentation::from_line("Number of characters.");
        let fields = vec![
            Field::with_documentation("data".to_string(), CType::ReadPointer(Box::new(c_char::type_info())), Visibility::Private, doc_data),
            Field::with_documentation("capacity".to_string(), CType::Primitive(PrimitiveType::U64), Visibility::Private, doc_len),
        ];

        let doc = Documentation::from_line("A pointer to an array of chars someone else owns which may be modified.");
        let repr = Representation::new(Layout::C, None);
        let meta = Meta::with_namespace_documentation(c_char::type_info().namespace().map(|e| e.into()).unwrap_or_else(String::new), doc);
        let composite = CompositeType::with_meta_repr("StringBuffer".to_string(), fields, meta, repr);
        CType::Pattern(TypePattern::CStrMutPointer(composite))
    }
}

impl<'a> CStrMutPointer<'a> {
    pub fn as_str(&'a self) -> Result<&'a str, Error> {
        unsafe {
           // let slice = std::slice::from_raw_parts(self.ptr as *const u8, self.capacity as usize);
            //println!("SLICE");
            let cstr = CStr::from_ptr(self.ptr);
            cstr.to_str().map_err(|e| Error::UTF8(e))
        }
    }

    pub fn write(&mut self, s: &str) -> Result<(), Error> {
        unsafe {
            let cstr_count =  {
                CStr::from_ptr(self.ptr).count_bytes()
            };
            if cstr_count + s.len() + 1 > self.capacity as usize {
                Err(Error::StringTooLong)
            } else {
                let slice = std::slice::from_raw_parts_mut(self.ptr as *mut u8, self.capacity as usize);
                slice[cstr_count..cstr_count + s.len()].copy_from_slice(s.as_bytes());
                slice[cstr_count + s.len() + 1] = 0;
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::patterns::string::CStrPointer;
    use std::ffi::CString;

    #[test]
    fn can_create() {
        let s = "hello world";
        let cstr = CString::new(s).unwrap();

        let ptr_some = CStrPointer::from_cstr(&cstr);

        assert_eq!(s, ptr_some.as_str().unwrap());
    }

    #[test]
    fn from_slice_with_nul_works() {
        let s = b"hello\0world";
        let ptr_some = CStrPointer::from_slice_with_nul(&s[..]).unwrap();

        assert_eq!("hello", ptr_some.as_str().unwrap());
    }

    #[test]
    fn from_slice_with_nul_fails_if_not_nul() {
        let s = b"hello world";
        let ptr_some = CStrPointer::from_slice_with_nul(&s[..]);

        assert!(ptr_some.is_err());
    }
}
