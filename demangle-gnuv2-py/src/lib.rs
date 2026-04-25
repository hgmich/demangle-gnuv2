use pyo3::{exceptions, prelude::*};

#[pyclass(frozen, from_py_object)]
#[derive(Debug, Clone)]
enum DemangledType {
    Void(),
    Boolean(),
    Int {
        signed: bool,
    },
    Short {
        signed: bool,
    },
    Char {
        signed: Option<bool>,
    },
    WideChar {
        signed: Option<bool>,
    },
    Long {
        signed: bool,
    },
    LongLong {
        signed: bool,
    },
    StdInt {
        bitwidth: usize,
        signed: bool,
    },
    Float(),
    Double(),
    LongDouble(),
    Reference {
        r#const: bool,
        restrict: bool,
        inner: Py<DemangledType>,
    },
    Pointer {
        r#const: bool,
        restrict: bool,
        inner: Py<DemangledType>,
    },
    Array {
        length: Option<u64>,
        inner: Py<DemangledType>,
    },
    Volatile {
        inner: Py<DemangledType>,
    },
    ClassOrStruct {
        name: String,
        templated: bool,
    },
    Function {
        args: Vec<Py<DemangledType>>,
        return_type: Option<Py<DemangledType>>,
        r#const: bool,
        has_varargs: bool,
    },
    VarArgs(),
}

#[pyclass(frozen, from_py_object)]
#[derive(Debug, Clone)]
struct DemangledSymbol {
    #[pyo3(get)]
    cxxdecl: String,
    #[pyo3(get)]
    r#type: SymbolType,
}

impl DemangledType {
    fn from_rust(py: Python, demangled: &demangle_gnuv2::DemangledType) -> PyResult<Py<Self>> {
        Ok(match demangled {
            demangle_gnuv2::DemangledType::Void => Self::Void(),
            demangle_gnuv2::DemangledType::Boolean => Self::Boolean(),
            demangle_gnuv2::DemangledType::Int { signed } => Self::Int { signed: *signed },
            demangle_gnuv2::DemangledType::Short { signed } => Self::Short { signed: *signed },
            demangle_gnuv2::DemangledType::Char { signed } => Self::Char { signed: *signed },
            demangle_gnuv2::DemangledType::WideChar { signed } => {
                Self::WideChar { signed: *signed }
            }
            demangle_gnuv2::DemangledType::Long { signed } => Self::Long { signed: *signed },
            demangle_gnuv2::DemangledType::LongLong { signed } => {
                Self::LongLong { signed: *signed }
            }
            demangle_gnuv2::DemangledType::StdInt { bitwidth, signed } => Self::StdInt {
                bitwidth: *bitwidth,
                signed: *signed,
            },
            demangle_gnuv2::DemangledType::Float => Self::Float(),
            demangle_gnuv2::DemangledType::Double => Self::Float(),
            demangle_gnuv2::DemangledType::LongDouble => Self::LongDouble(),
            demangle_gnuv2::DemangledType::Reference {
                r#const,
                restrict,
                inner,
            } => Self::Reference {
                r#const: *r#const,
                restrict: *restrict,
                inner: DemangledType::from_rust(py, inner.as_ref())?,
            },
            demangle_gnuv2::DemangledType::Pointer {
                r#const,
                restrict,
                inner,
            } => Self::Pointer {
                r#const: *r#const,
                restrict: *restrict,
                inner: DemangledType::from_rust(py, inner.as_ref())?,
            },
            demangle_gnuv2::DemangledType::Array { length, inner } => Self::Array {
                length: *length,
                inner: DemangledType::from_rust(py, inner.as_ref())?,
            },
            demangle_gnuv2::DemangledType::Volatile { inner } => Self::Volatile {
                inner: DemangledType::from_rust(py, inner.as_ref())?,
            },
            demangle_gnuv2::DemangledType::ClassOrStruct { name, templated } => {
                Self::ClassOrStruct {
                    name: name.clone(),
                    templated: *templated,
                }
            }
            demangle_gnuv2::DemangledType::Function {
                args,
                return_type,
                r#const,
                has_varargs,
            } => {
                let args = args
                    .iter()
                    .map(|arg| DemangledType::from_rust(py, arg))
                    .collect::<PyResult<Vec<_>>>()?;

                let return_type = return_type
                    .as_ref()
                    .map(|ty| DemangledType::from_rust(py, ty))
                    .transpose()?;

                Self::Function {
                    args,
                    return_type,
                    r#const: *r#const,
                    has_varargs: *has_varargs,
                }
            }
        }
        .into_pyobject(py)?
        .unbind())
    }
}

/// What kind of symbol this is.
#[pyclass(frozen, from_py_object)]
#[derive(Debug, Clone)]
enum SymbolType {
    /// Symbol refers to the vtable of a specified class.
    VTable(),
    /// Symbol refers to a function entry point.
    Function {
        qualified_name: String,
        qualified_path: Vec<String>,
        args: Vec<Py<DemangledType>>,
        return_type: Option<Py<DemangledType>>,
        r#const: bool,
        has_varargs: bool,
    },
    /// Symbol refers to the static member of a container type.
    StaticMember(),
    /// Symbol is type reflection information.
    TypeInfo { r#type: TypeInfoType },
    /// Symbol is a global constructor for a static value.
    GlobalConstructor(),
    /// Symbol is a global destructor for a static value.
    GlobalDestructor(),
    /// Symbol is a stub for a symbol dllimported from another module.
    DllImportStub(),
}

impl SymbolType {
    fn from_rust(py: Python, sym: demangle_gnuv2::SymbolKind) -> PyResult<Self> {
        use demangle_gnuv2::SymbolKind;
        match sym {
            SymbolKind::VTable => Ok(Self::VTable()),
            SymbolKind::Function {
                qualified_name,
                qualified_path,
                args,
                return_type,
                r#const,
                has_varargs,
            } => {
                let args = args
                    .iter()
                    .map(|arg| DemangledType::from_rust(py, arg))
                    .collect::<PyResult<Vec<_>>>()?;

                let return_type = return_type
                    .as_ref()
                    .map(|ty| DemangledType::from_rust(py, ty))
                    .transpose()?;

                Ok(Self::Function {
                    qualified_name,
                    qualified_path,
                    args,
                    return_type,
                    r#const,
                    has_varargs,
                })
            }
            SymbolKind::StaticMember => Ok(Self::StaticMember()),
            SymbolKind::TypeInfo(ty_info) => Ok(Self::TypeInfo {
                r#type: TypeInfoType::from_rust(py, ty_info)?,
            }),
            SymbolKind::GlobalConstructor => Ok(Self::GlobalConstructor()),
            SymbolKind::GlobalDestructor => Ok(Self::GlobalDestructor()),
            SymbolKind::DllImportStub => Ok(Self::DllImportStub()),
            other => Err(PyErr::new::<exceptions::PyTypeError, _>(format!(
                "unknown symbol type {other:?}"
            ))),
        }
    }
}

/// Specifies what variety of type info this is.
#[pyclass(from_py_object, frozen, eq, eq_int)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TypeInfoType {
    /// typeinfo is for a type node (class, struct, etc).
    Node,
    /// typeinfo is for a function or method.
    Function,
}

impl TypeInfoType {
    fn from_rust(_py: Python, kind: demangle_gnuv2::TypeInfoKind) -> PyResult<Self> {
        Ok(match kind {
            demangle_gnuv2::TypeInfoKind::Node => Self::Node,
            demangle_gnuv2::TypeInfoKind::Function => Self::Function,
            other => {
                return Err(PyErr::new::<exceptions::PyTypeError, _>(format!(
                    "unknown TypeInfoType {other:?}"
                )));
            }
        })
    }
}

#[pymethods]
impl TypeInfoType {
    fn __repr__(&self) -> String {
        let variant = match self {
            Self::Node => "node",
            Self::Function => "function",
        };

        format!("<typeinfo {variant}>")
    }
}

impl DemangledSymbol {
    fn from_rust(py: Python, demangled: demangle_gnuv2::DemangledSymbol) -> PyResult<Self> {
        // TODO: Implement structured demangling

        Ok(DemangledSymbol {
            cxxdecl: demangled.cxxdecl,
            r#type: SymbolType::from_rust(py, demangled.kind)?,
        })
    }
}

/// Demangles a symbol mangled with the GNU v2 mangling conventions.
///
/// If ansi is True, (the default), ansi qualifiers (const, __restrict,
/// volatile) will be included in the demangled symbol. If params is True,
/// parameters will be included in the demangled symbol if it is a function symbol.
#[pyfunction(signature = (symbol, *, ansi = true, params = true))]
fn cplus_demangle_v2(
    py: Python,
    symbol: String,
    ansi: bool,
    params: bool,
) -> PyResult<DemangledSymbol> {
    let opts = demangle_gnuv2::DemangleOpts::new()
        .with_ansi(ansi)
        .with_params(params);

    let rust = demangle_gnuv2::cplus_demangle_v2(symbol.as_bytes(), opts).map_err(|e| {
        PyErr::new::<exceptions::PyTypeError, _>(format!("Failed to demangle: {e}"))
    })?;

    DemangledSymbol::from_rust(py, rust)
}

/// A Python module implemented in Rust.
#[pymodule(name = "demangle_gnuv2")]
fn demangle_gnuv2_module(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(cplus_demangle_v2, m)?)?;
    m.add_class::<DemangledSymbol>()?;
    m.add_class::<DemangledType>()?;
    m.add_class::<SymbolType>()?;
    m.add_class::<TypeInfoType>()?;
    Ok(())
}
