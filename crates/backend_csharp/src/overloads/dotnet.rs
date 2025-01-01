use crate::converter::FunctionNameFlavor;
use crate::overloads::{write_common_service_method_overload, write_function_overloaded_invoke_with_error_handling, Helper};
use crate::{OverloadWriter, Unsafe};
use core::panic;
use interoptopus::lang::c::{CType, CompositeType, Field, Function, FunctionSignature, Parameter};
use interoptopus::patterns::callbacks::NamedCallback;
use interoptopus::patterns::service::Service;
use interoptopus::patterns::TypePattern;
use interoptopus::writer::{IndentWriter, WriteFor};
use interoptopus::{indented, Error};
use std::iter::zip;
use std::ops::Deref;

/// The kind of types to use when generating FFI method overloads.
// TODO - THIS SHOULD BE DotNet config
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum ParamSliceType {
    /// Slices should be passed in as C# arrays.
    Array,
    /// Slices should be passed in as Span and ReadOnlySpan.
    Span,
}

impl Default for ParamSliceType {
    fn default() -> Self {
        Self::Array
    }
}

/// **Highly recommended**, provides most convenience methods.
///
/// In most cases adding this overload provider is the right thing to do, as it generates
///
/// - `my_array[]` or `Span<my_array>`/`ReadOnlySpan<my_array>` support for slices,
/// - much faster (up to 150x) .NET Core slice copies (with [`Unsafe::UnsafePlatformMemCpy`](crate::Unsafe::UnsafePlatformMemCpy)),
/// - service overloads.
#[derive(Clone, Debug, Default)]
pub struct DotNet {
    /// If signatures that normally use arrays should instead use span and readonly span.
    /// Requires use_unsafe, as pinning spans requires the fixed keyword.
    param_slice_type: ParamSliceType,
}

impl DotNet {
    /// Creates a new .NET overload generator.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new .NET overload generator.
    pub fn new_built() -> Box<Self> {
        Self::new().build()
    }

    pub fn param_slice_type(mut self, param_slice_type: ParamSliceType) -> Self {
        self.param_slice_type = param_slice_type;
        self
    }

    fn has_overloadable(&self, signature: &FunctionSignature) -> bool {
        signature.params().iter().any(|x| match x.the_type() {
            CType::ReadPointer(x) | CType::ReadWritePointer(x) => match x.deref() {
                CType::Pattern(x) => matches!(x, TypePattern::Slice(_) | TypePattern::SliceMut(_)),
                _ => false,
            },
            CType::Pattern(x) => matches!(x, TypePattern::Slice(_) | TypePattern::SliceMut(_)),
            _ => false,
        })
    }

    fn pattern_to_native_in_signature(&self, h: &Helper, param: &Parameter) -> String {
        if h.config.use_unsafe == Unsafe::None && self.param_slice_type == ParamSliceType::Span {
            panic!("param_slice_type: Span requires unsafe support (use_unsafe must be anything other than None)");
        }

        let slice_type_name = |mutable: bool, element_type: &CType| -> String {
            match (self.param_slice_type, mutable) {
                (ParamSliceType::Array, _) => format!("{}[]", h.converter.to_typespecifier_in_param(element_type)),
                (ParamSliceType::Span, true) => format!("System.Span<{}>", h.converter.to_typespecifier_in_param(element_type)),
                (ParamSliceType::Span, false) => format!("System.ReadOnlySpan<{}>", h.converter.to_typespecifier_in_param(element_type)),
            }
        };
        match param.the_type() {
            CType::Pattern(p) => match p {
                TypePattern::Slice(p) => {
                    let element_type = p.try_deref_pointer().expect("Must be pointer");
                    slice_type_name(false, &element_type)
                }
                TypePattern::SliceMut(p) => {
                    let element_type = p.try_deref_pointer().expect("Must be pointer");
                    slice_type_name(true, &element_type)
                }
                _ => h.converter.to_typespecifier_in_param(param.the_type()),
            },
            CType::ReadPointer(x) | CType::ReadWritePointer(x) => match x.deref() {
                CType::Pattern(x) => match x {
                    TypePattern::Slice(p) => {
                        let element_type = p.try_deref_pointer().expect("Must be pointer");
                        slice_type_name(false, &element_type)
                    }
                    TypePattern::SliceMut(p) => {
                        let element_type = p.try_deref_pointer().expect("Must be pointer");
                        slice_type_name(true, &element_type)
                    }
                    _ => h.converter.to_typespecifier_in_param(param.the_type()),
                },
                _ => h.converter.to_typespecifier_in_param(param.the_type()),
            },

            x => h.converter.to_typespecifier_in_param(x),
        }
    }

    pub fn build(self) -> Box<Self> {
        Box::new(self)
    }
}

impl OverloadWriter for DotNet {
    fn write_imports(&self, w: &mut IndentWriter, h: Helper) -> Result<(), Error> {
        if h.config.use_unsafe == Unsafe::UnsafePlatformMemCpy {
            indented!(w, r#"using System.Runtime.CompilerServices;"#)?;
        }
        Ok(())
    }

    fn write_field_decorators(&self, w: &mut IndentWriter, _h: Helper, field: &Field, _strct: &CompositeType) -> Result<(), Error> {
        if let CType::Pattern(TypePattern::OwnedString(x)) = field.the_type() {
            indented!(w, r#"[MarshalAs(UnmanagedType.ByValTStr, SizeConst = {})]"#, x)?;
        }
        Ok(())
    }

    fn write_callback_overload(&self, w: &mut IndentWriter, h: Helper, the_type: &NamedCallback) -> Result<(), Error> {
        if !h.config.work_around_exception_in_callback_no_reentry {
            return Ok(());
        }

        let ffi_error = match the_type.fnpointer().signature().rval() {
            CType::Pattern(TypePattern::FFIErrorEnum(rval)) => rval,
            _ => return Ok(()),
        };

        let name = format!("{}ExceptionSafe", the_type.name());
        let rval = h.converter.to_typespecifier_in_rval(the_type.fnpointer().signature().rval());
        let mut function_signature = Vec::new();
        let mut function_param_names = Vec::new();

        for p in the_type.fnpointer().signature().params().iter() {
            let name = p.name();
            let the_type = h.converter.function_parameter_to_csharp_typename(p);

            let x = format!("{} {}", the_type, name);
            function_signature.push(x);
            function_param_names.push(name);
        }

        w.newline()?;
        indented!(w, "// Internal helper that works around an issue where exceptions in callbacks don't reenter Rust.")?;
        indented!(w, "{} class {} {{", h.config.visibility_types.to_access_modifier(), name)?;
        indented!(w, [_], "private Exception failure = null;")?;
        indented!(w, [_], "private readonly {} _callback;", the_type.name())?;
        w.newline()?;
        indented!(w, [_], "public {}({} original)", name, the_type.name())?;
        indented!(w, [_], "{{")?;
        indented!(w, [_ _], "_callback = original;")?;
        indented!(w, [_], "}}")?;
        w.newline()?;
        indented!(w, [_], "public {} Call({})", rval, function_signature.join(", "))?;
        indented!(w, [_], "{{")?;
        indented!(w, [_ _], "try")?;
        indented!(w, [_ _], "{{")?;
        indented!(w, [_ _ _], "return _callback({});", function_param_names.join(", "))?;
        indented!(w, [_ _], "}}")?;
        indented!(w, [_ _], "catch (Exception e)")?;
        indented!(w, [_ _], "{{")?;
        indented!(w, [_ _ _], "failure = e;")?;
        indented!(w, [_ _ _], "return {}.{};", rval, ffi_error.panic_variant().name())?;
        indented!(w, [_ _], "}}")?;
        indented!(w, [_], "}}")?;
        w.newline()?;
        indented!(w, [_], "public void Rethrow()")?;
        indented!(w, [_], "{{")?;
        indented!(w, [_ _], "if (this.failure != null)")?;
        indented!(w, [_ _], "{{")?;
        indented!(w, [_ _ _], "throw this.failure;")?;
        indented!(w, [_ _], "}}")?;
        indented!(w, [_], "}}")?;
        indented!(w, "}}")?;

        Ok(())
    }

    fn write_function_overload(&self, w: &mut IndentWriter, h: Helper, function: &Function, write_for: WriteFor) -> Result<(), Error> {
        let has_overload = self.has_overloadable(function.signature());
        let has_error_enum = h.converter.has_ffi_error_rval(function.signature());

        // If there is nothing to write, don't do it
        if !has_overload && !has_error_enum {
            return Ok(());
        }

        let mut to_pin_name = Vec::new();
        let mut to_pin_slice_type = Vec::new();
        let mut to_invoke = Vec::new();
        let mut to_wrap_delegates = Vec::new();
        let mut to_wrap_delegate_types = Vec::new();

        let raw_name = h.converter.function_name_to_csharp_name(
            function,
            match h.config.rename_symbols {
                true => FunctionNameFlavor::CSharpMethodNameWithClass,
                false => FunctionNameFlavor::RawFFIName,
            },
        );
        let this_name = if has_error_enum && !has_overload {
            format!("{}_checked", raw_name)
        } else {
            raw_name
        };

        let rval = match function.signature().rval() {
            CType::Pattern(TypePattern::FFIErrorEnum(_)) => "void".to_string(),
            CType::Pattern(TypePattern::CStrPointer) => "string".to_string(),
            _ => h.converter.to_typespecifier_in_rval(function.signature().rval()),
        };

        let mut params = Vec::new();
        for p in function.signature().params().iter() {
            let name = p.name();
            let native = self.pattern_to_native_in_signature(&h, p);
            let the_type = h.converter.function_parameter_to_csharp_typename(p);

            let mut fallback = || {
                if native.contains("out ") {
                    to_invoke.push(format!("out {}", name));
                } else if native.contains("ref ") {
                    to_invoke.push(format!("ref {}", name));
                } else {
                    to_invoke.push(name.to_string());
                }
            };

            match p.the_type() {
                CType::Pattern(TypePattern::Slice(_) | TypePattern::SliceMut(_)) => {
                    to_pin_name.push(name);
                    to_pin_slice_type.push(the_type);
                    to_invoke.push(format!("{}_slice", name));
                }
                CType::Pattern(TypePattern::NamedCallback(callback)) => match callback.fnpointer().signature().rval() {
                    CType::Pattern(TypePattern::FFIErrorEnum(_)) if h.config.work_around_exception_in_callback_no_reentry => {
                        to_wrap_delegates.push(name);
                        to_wrap_delegate_types.push(h.converter.to_typespecifier_in_param(p.the_type()));
                        to_invoke.push(format!("{}_safe_delegate.Call", name));
                    }
                    _ => fallback(),
                },
                CType::ReadPointer(x) | CType::ReadWritePointer(x) => match x.deref() {
                    CType::Pattern(x) => match x {
                        TypePattern::Slice(_) => {
                            to_pin_name.push(name);
                            to_pin_slice_type.push(the_type.replace("ref ", ""));
                            to_invoke.push(format!("ref {}_slice", name));
                        }
                        TypePattern::SliceMut(_) => {
                            to_pin_name.push(name);
                            to_pin_slice_type.push(the_type.replace("ref ", ""));
                            to_invoke.push(format!("ref {}_slice", name));
                        }
                        _ => fallback(),
                    },
                    _ => fallback(),
                },
                _ => fallback(),
            }

            params.push(format!("{} {}", native, name));
        }

        let signature = format!(r#"public static {} {}({})"#, rval, this_name, params.join(", "));
        if write_for == WriteFor::Docs {
            indented!(w, r#"{};"#, signature)?;
            return Ok(());
        }

        w.newline()?;

        if write_for == WriteFor::Code {
            self.write_documentation(w, function.meta().documentation())?;
        }

        indented!(w, "{}", signature)?;
        indented!(w, r#"{{"#)?;

        for (name, ty) in zip(&to_wrap_delegates, &to_wrap_delegate_types) {
            indented!(w, [_], r#"var {}_safe_delegate = new {}ExceptionSafe({});"#, name, ty, name)?;
        }

        if h.config.use_unsafe.any_unsafe() {
            if !to_pin_name.is_empty() {
                indented!(w, [_], r#"unsafe"#)?;
                indented!(w, [_], r#"{{"#)?;
                w.indent();

                for (pin_var, slice_struct) in to_pin_name.iter().zip(to_pin_slice_type.iter()) {
                    indented!(w, [_], r#"fixed (void* ptr_{} = {})"#, pin_var, pin_var)?;
                    indented!(w, [_], r#"{{"#)?;
                    indented!(w, [_ _], r#"var {}_slice = new {}(new IntPtr(ptr_{}), (ulong) {}.Length);"#, pin_var, slice_struct, pin_var, pin_var)?;
                    w.indent();
                }
            }

            let fn_name = h.converter.function_name_to_csharp_name(
                function,
                match h.config.rename_symbols {
                    true => FunctionNameFlavor::CSharpMethodNameWithClass,
                    false => FunctionNameFlavor::RawFFIName,
                },
            );
            let call = format!(r#"{}({});"#, fn_name, to_invoke.join(", "));

            write_function_overloaded_invoke_with_error_handling(w, function, &call, to_wrap_delegates.as_slice())?;

            if !to_pin_name.is_empty() {
                for _ in to_pin_name.iter() {
                    w.unindent();
                    indented!(w, [_], r#"}}"#)?;
                }

                w.unindent();
                indented!(w, [_], r#"}}"#)?;
            }
        } else {
            if !to_pin_name.is_empty() {
                for (pin_var, slice_struct) in to_pin_name.iter().zip(to_pin_slice_type.iter()) {
                    indented!(w, [_], r#"var {}_pinned = GCHandle.Alloc({}, GCHandleType.Pinned);"#, pin_var, pin_var)?;
                    indented!(
                        w,
                        [_],
                        r#"var {}_slice = new {}({}_pinned, (ulong) {}.Length);"#,
                        pin_var,
                        slice_struct,
                        pin_var,
                        pin_var
                    )?;
                }

                indented!(w, [_], r#"try"#)?;
                indented!(w, [_], r#"{{"#)?;

                w.indent();
            }

            let fn_name = h.converter.function_name_to_csharp_name(
                function,
                match h.config.rename_symbols {
                    true => FunctionNameFlavor::CSharpMethodNameWithClass,
                    false => FunctionNameFlavor::RawFFIName,
                },
            );
            let call = format!(r#"{}({});"#, fn_name, to_invoke.join(", "));

            write_function_overloaded_invoke_with_error_handling(w, function, &call, &[])?;

            for name in to_wrap_delegates {
                indented!(w, [_], r#"{}_safe_delegate.Rethrow();"#, name)?;
            }

            if !to_pin_name.is_empty() {
                w.unindent();
                indented!(w, [_], r#"}}"#)?;
                indented!(w, [_], r#"finally"#)?;
                indented!(w, [_], r#"{{"#)?;
                for pin in &to_pin_name {
                    indented!(w, [_ _], r#"{}_pinned.Free();"#, pin)?;
                }
                indented!(w, [_], r#"}}"#)?;
            }
        }

        indented!(w, r#"}}"#)
    }

    fn write_service_method_overload(
        &self,
        w: &mut IndentWriter,
        h: Helper,
        _class: &Service,
        function: &Function,
        fn_pretty: &str,
        write_for: WriteFor,
    ) -> Result<(), Error> {
        if !self.has_overloadable(function.signature()) {
            return Ok(());
        }

        if write_for == WriteFor::Code {
            w.newline()?;
            self.write_documentation(w, function.meta().documentation())?;
        }

        write_common_service_method_overload(w, h, function, fn_pretty, |h, p| self.pattern_to_native_in_signature(h, p), write_for)?;

        Ok(())
    }

    fn write_pattern_slice_overload(&self, w: &mut IndentWriter, h: Helper, _context_type_name: &str, type_string: &str) -> Result<(), Error> {
        if h.config.use_unsafe.any_unsafe() {
            indented!(w, [_], r#"#if (NETSTANDARD2_1_OR_GREATER || NET5_0_OR_GREATER || NETCOREAPP2_1_OR_GREATER)"#)?;
            indented!(w, [_], r#"public ReadOnlySpan<{}> ReadOnlySpan"#, type_string)?;
            indented!(w, [_], r#"{{"#)?;
            indented!(w, [_ _], r#"get"#)?;
            indented!(w, [_ _], r#"{{"#)?;
            indented!(w, [_ _ _], r#"unsafe"#)?;
            indented!(w, [_ _ _], r#"{{"#)?;
            indented!(w, [_ _ _ _], r#"return new ReadOnlySpan<{}>(this.data.ToPointer(), (int) this.len);"#, type_string)?;
            indented!(w, [_ _ _], r#"}}"#)?;
            indented!(w, [_ _], r#"}}"#)?;
            indented!(w, [_], r#"}}"#)?;
            indented!(w, [_], r#"#endif"#)?;
        }
        Ok(())
    }

    fn write_pattern_slice_mut_overload(&self, w: &mut IndentWriter, h: Helper, _context_type_name: &str, type_string: &str) -> Result<(), Error> {
        if h.config.use_unsafe.any_unsafe() {
            indented!(w, [_], r#"#if (NETSTANDARD2_1_OR_GREATER || NET5_0_OR_GREATER || NETCOREAPP2_1_OR_GREATER)"#)?;
            indented!(w, [_], r#"public Span<{}> Span"#, type_string)?;
            indented!(w, [_], r#"{{"#)?;
            indented!(w, [_ _], r#"get"#)?;
            indented!(w, [_ _], r#"{{"#)?;
            indented!(w, [_ _ _], r#"unsafe"#)?;
            indented!(w, [_ _ _], r#"{{"#)?;
            indented!(w, [_ _ _ _], r#"return new Span<{}>(this.data.ToPointer(), (int) this.len);"#, type_string)?;
            indented!(w, [_ _ _], r#"}}"#)?;
            indented!(w, [_ _], r#"}}"#)?;
            indented!(w, [_], r#"}}"#)?;
            indented!(w, [_], r#"#endif"#)?;
        }
        Ok(())
    }

    fn write_pattern_slice_unsafe_copied_fragment(&self, w: &mut IndentWriter, _h: Helper, type_string: &str) -> Result<(), Error> {
        indented!(w, [_ _ _ _ _], r#"#elif NETCOREAPP"#)?;
        indented!(w, [_ _ _ _ _], r#"Unsafe.CopyBlock(dst, data.ToPointer(), (uint) len * (uint) sizeof({}));"#, type_string)?;
        Ok(())
    }
}
