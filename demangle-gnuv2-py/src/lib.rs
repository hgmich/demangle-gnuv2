use pyo3::{exceptions, prelude::*, types::PyList};

#[pyclass]
#[derive(Debug)]
struct DemangledType {
    #[pyo3(get)]
    name: String,
}

#[pyclass]
#[derive(Debug)]
struct DemangledSymbol {
    #[pyo3(get)]
    qualified_name: String,
}

impl DemangledType {
    fn from_rust(py: Python, demangled: demangle_gnuv2::DemangledType) -> PyResult<Self> {
        match demangled {
            demangle_gnuv2::DemangledType::Void => Ok(Self {
                name: "void".into(),
            }),
        }
    }
}

impl DemangledSymbol {
    fn from_rust(py: Python, demangled: demangle_gnuv2::DemangledSymbol) -> PyResult<Self> {
        // TODO: Implement structured demangling

        Ok(DemangledSymbol {
            qualified_name: demangled.qualified_name,
        })
    }
}

/// Formats the sum of two numbers as string.
#[pyfunction]
fn sum_as_string(a: usize, b: usize) -> PyResult<String> {
    Ok((a + b).to_string())
}

#[pyfunction]
fn cplus_demangle_v2(py: Python, symbol: String) -> PyResult<DemangledSymbol> {
    let opts = demangle_gnuv2::DemangleOpts::new();

    let rust = demangle_gnuv2::cplus_demangle_v2(symbol.as_bytes(), opts)
        .map_err(|_| PyErr::new::<exceptions::PyTypeError, _>("Failed to demangle"))?;

    DemangledSymbol::from_rust(py, rust)
}

/// A Python module implemented in Rust.
#[pymodule(name = "demangle_gnuv2")]
fn demangle_gnuv2_module(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(sum_as_string, m)?)?;
    m.add_function(wrap_pyfunction!(cplus_demangle_v2, m)?)?;
    m.add_class::<DemangledSymbol>()?;
    Ok(())
}
