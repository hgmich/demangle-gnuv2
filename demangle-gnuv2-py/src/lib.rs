use pyo3::{exceptions, prelude::*};

#[pyclass]
#[derive(Debug, Clone)]
struct DemangledType {
    #[pyo3(get)]
    name: String,
}

#[pyclass]
#[derive(Debug, Clone)]
struct DemangledSymbol {
    #[pyo3(get)]
    qualified_name: String,
    #[pyo3(get, name = "type")]
    type_: SymbolType,
}

impl DemangledType {
    fn from_rust(py: Python, demangled: &demangle_gnuv2::DemangledType) -> PyResult<Self> {
        match demangled {
            demangle_gnuv2::DemangledType::Void => Ok(Self {
                name: "void".into(),
            }),
        }
    }
}

/// What kind of symbol this is.
#[pyclass]
#[derive(Debug, Clone)]
enum SymbolType {
    /// Symbol refers to the vtable of a specified class.
    VTable(),
    /// Symbol refers to a function entry point.
    Function {
        args: Vec<DemangledType>,
        return_type: DemangledType,
    },
    /// Symbol refers to the static member of a container type.
    StaticMember(),
    /// Symbol is type reflection information.
    TypeInfo { r#type: TypeInfoType },
}

impl SymbolType {
    fn from_rust(py: Python, sym: demangle_gnuv2::SymbolKind) -> PyResult<Self> {
        use demangle_gnuv2::SymbolKind;
        match sym {
            SymbolKind::VTable => Ok(Self::VTable()),
            SymbolKind::Function { args, return_type } => Ok(Self::Function {
                args: args
                    .iter()
                    .map(|arg| DemangledType::from_rust(py, arg))
                    .collect::<PyResult<Vec<_>>>()?,
                return_type: DemangledType::from_rust(py, &return_type)?,
            }),
            SymbolKind::StaticMember => Ok(Self::StaticMember()),
            SymbolKind::TypeInfo(ty_info) => Ok(Self::TypeInfo {
                r#type: TypeInfoType::from_rust(py, ty_info)?,
            }),
            other => {
                return Err(PyErr::new::<exceptions::PyTypeError, _>(format!(
                    "unknown symbol type {other:?}"
                )));
            }
        }
    }
}

/// Specifies what variety of type info this is.
#[pyclass(eq, eq_int)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TypeInfoType {
    /// typeinfo is for a type node (class, struct, etc).
    Node,
    /// typeinfo is for a function or method.
    Function,
}

impl TypeInfoType {
    fn from_rust(py: Python, kind: demangle_gnuv2::TypeInfoKind) -> PyResult<Self> {
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
            qualified_name: demangled.qualified_name,
            type_: SymbolType::from_rust(py, demangled.kind)?,
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
