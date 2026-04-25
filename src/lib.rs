#![deny(unused_must_use)]

use std::borrow::Cow;

use anyhow::{Context, Result};
use bitfield_struct::bitfield;
use memchr::memmem;

fn debug_log_bytes(bs: &[u8], name: &str) {
    if log::log_enabled!(log::Level::Debug) {
        let bs_s =
            std::str::from_utf8(bs).unwrap_or_else(|_| panic!("failed to deserialize {name}"));
        log::debug!("{name}: {bs_s}");
    }
}

/// Options for controlling demangling.
#[bitfield(u32)]
pub struct DemangleOpts {
    /// Demangle function arguments as well as symbol name.
    pub params: bool,

    /// Include ANSI language features such as const, volatile, etc.
    pub ansi: bool,

    /// Demangle as Java instead of as C++.
    pub java: bool,

    /// Reserved space for future options.
    #[bits(5)]
    __0: u8,

    /// Which demangling style(s) to apply.
    /// If none are set, defaults are loaded from (X)
    #[bits(8)]
    pub style: DemangleStyle,

    /// Padding/reserved space.
    #[bits(16)]
    __1: u16,
}

/// Options specifically concerning which demangling convention
/// should be used.
#[bitfield(u8)]
pub struct DemangleStyle {
    /// Automatically detect the mangling style used by the mangled symbols.
    pub auto: bool,

    /// GNU-style symbol mangling.
    pub gnu: bool,

    /// Lucid compiler symbol mangling.
    pub lucid: bool,

    /// arm-gcc symbol mangling.
    pub arm: bool,

    /// HP aCC compiler symbol mangling.
    pub hp: bool,

    /// EDG compiler symbol mangling.
    pub edg: bool,

    /// Padding
    #[bits(2)]
    __: u8,
}

/// Types that can be encoded in the signatures of mangled functions.
#[derive(Debug, PartialEq, Clone, Copy)]
enum TypeKind {
    None,
    Pointer,
    Reference,
    Integral,
    Bool,
    Char,
    Real,
}

/// Overloadable operators in C++.
#[derive(Debug)]
enum OperatorKind {
    New,
    Delete,
    ArrayNew,
    ArrayDelete,
    Assignment,
    NonEquality,
    Equality,
    GreaterEqual,
    GreaterThan,
    LessEqual,
    LessThan,
    Addition,
    AssigningAddition,
    Subtraction,
    AssigningSubtraction,
    Multiplication,
    AssigningMultiplication,
    UnaryPlus,
    Negate,
    Modulus,
    AssigningModulus,
    Division,
    AssigningDivision,
    LogicalAnd,
    LogicalOr,
    LogicalNot,
    Postincrement,
    Postdecrement,
    BitwiseOr,
    AssigningBitwiseOr,
    BitwiseXor,
    AssigningBitwiseXor,
    BitwiseAnd,
    AssigningBitwiseAnd,
    BitwiseNot,
    FunctionCall,
    ArithmeticLeftShift,
    AssigningArithmeticLeftShift,
    ArithmeticRightShift,
    AssigningArithmeticRightShift,
    IndirectMemberLookup,
    Dereference,
    MethodCall,
    AddressOf,
    ArrayIndex,
    Compound,
    Conditional,
    Maximum,
    Minimum,
    Nop,
    DereferenceIndirectMemberLookup,
    Sizeof,
}

impl OperatorKind {
    pub fn from_symbol_op(sym: &[u8], opts: DemangleOpts) -> Result<Self> {
        let is_ansi = opts.ansi();
        Ok(match sym {
            b"nw" if is_ansi => Self::New,
            b"dl" if is_ansi => Self::Delete,
            b"new" => Self::New,
            b"delete" => Self::Delete,
            b"vn" if is_ansi => Self::ArrayNew,
            b"vd" if is_ansi => Self::ArrayDelete,
            b"as" if is_ansi => Self::Assignment,
            b"ne" if is_ansi => Self::NonEquality,
            b"eq" if is_ansi => Self::Equality,
            b"ge" if is_ansi => Self::GreaterEqual,
            b"gt" if is_ansi => Self::GreaterThan,
            b"le" if is_ansi => Self::LessEqual,
            b"lt" if is_ansi => Self::LessThan,
            b"plus" => Self::Addition,
            b"pl" if is_ansi => Self::Addition,
            b"apl" if is_ansi => Self::AssigningAddition,
            b"minus" => Self::Subtraction,
            b"mi" if is_ansi => Self::Subtraction,
            b"ami" if is_ansi => Self::AssigningSubtraction,
            b"mult" => Self::Multiplication,
            b"ml" if is_ansi => Self::Multiplication,
            b"amu" if is_ansi => Self::AssigningMultiplication,
            b"aml" if is_ansi => Self::AssigningMultiplication,
            b"convert" => Self::UnaryPlus,
            b"negate" => Self::Negate,
            b"trunc_mod" => Self::Modulus,
            b"md" if is_ansi => Self::Modulus,
            b"amd" if is_ansi => Self::AssigningModulus,
            b"trunc_div" => Self::Division,
            b"dv" if is_ansi => Self::Division,
            b"adv" if is_ansi => Self::AssigningDivision,
            b"truth_andif" => Self::LogicalAnd,
            b"aa" if is_ansi => Self::LogicalAnd,
            b"truth_orif" => Self::LogicalOr,
            b"oo" if is_ansi => Self::LogicalOr,
            b"truth_not" => Self::LogicalNot,
            b"nt" if is_ansi => Self::LogicalAnd,
            b"postincrement" => Self::Postincrement,
            b"pp" if is_ansi => Self::Postincrement,
            b"postdecrement" => Self::Postdecrement,
            b"mm" if is_ansi => Self::Postdecrement,
            b"bit_ior" => Self::BitwiseOr,
            b"or" if is_ansi => Self::BitwiseOr,
            b"aor" if is_ansi => Self::AssigningBitwiseOr,
            b"bit_xor" => Self::BitwiseXor,
            b"er" if is_ansi => Self::BitwiseXor,
            b"aer" if is_ansi => Self::AssigningBitwiseXor,
            b"bit_and" => Self::BitwiseAnd,
            b"ad" if is_ansi => Self::BitwiseAnd,
            b"aad" if is_ansi => Self::AssigningBitwiseAnd,
            b"bit_not" => Self::BitwiseNot,
            b"co" if is_ansi => Self::BitwiseNot,
            b"call" => Self::FunctionCall,
            b"cl" => Self::FunctionCall,
            b"alshift" => Self::ArithmeticLeftShift,
            b"ls" if is_ansi => Self::ArithmeticLeftShift,
            b"als" if is_ansi => Self::AssigningArithmeticLeftShift,
            b"arshift" => Self::ArithmeticRightShift,
            b"rs" if is_ansi => Self::ArithmeticRightShift,
            b"ars" if is_ansi => Self::AssigningArithmeticRightShift,
            b"component" => Self::IndirectMemberLookup,
            b"pt" if is_ansi => Self::IndirectMemberLookup,
            b"rf" if is_ansi => Self::IndirectMemberLookup,
            b"indirect" => Self::Dereference,
            b"method_call" => Self::MethodCall,
            b"addr" => Self::AddressOf,
            b"array" => Self::ArrayIndex,
            b"vc" if is_ansi => Self::ArrayIndex,
            b"compound" => Self::Compound,
            b"cm" if is_ansi => Self::Compound,
            b"cond" => Self::Conditional,
            b"cn" if is_ansi => Self::Conditional,
            b"max" => Self::Maximum,
            b"mx" if is_ansi => Self::Maximum,
            b"min" => Self::Minimum,
            b"mn" if is_ansi => Self::Minimum,
            b"nop" => Self::Nop,
            b"rm" => Self::DereferenceIndirectMemberLookup,
            b"sz" => Self::Sizeof,
            bs => {
                if let Ok(s) = std::str::from_utf8(bs) {
                    anyhow::bail!("unknown symbol {s}");
                } else {
                    anyhow::bail!("got operator symbol with invalid utf8 bytes");
                }
            }
        })
    }

    pub fn overload_name(&self) -> &'static [u8] {
        match *self {
            OperatorKind::New => b" new",
            OperatorKind::Delete => b" delete",
            OperatorKind::ArrayNew => b" new []",
            OperatorKind::ArrayDelete => b" delete []",
            OperatorKind::Assignment => b"=",
            OperatorKind::NonEquality => b"!=",
            OperatorKind::Equality => b"==",
            OperatorKind::GreaterEqual => b">=",
            OperatorKind::GreaterThan => b">",
            OperatorKind::LessEqual => b"<=",
            OperatorKind::LessThan => b"<",
            OperatorKind::Addition => b"+",
            OperatorKind::AssigningAddition => b"+=",
            OperatorKind::Subtraction => b"-",
            OperatorKind::AssigningSubtraction => b"-=",
            OperatorKind::Multiplication => b"*",
            OperatorKind::AssigningMultiplication => b"*=",
            OperatorKind::UnaryPlus => b"+",
            OperatorKind::Negate => b"-",
            OperatorKind::Modulus => b"%",
            OperatorKind::AssigningModulus => b"%=",
            OperatorKind::Division => b"/",
            OperatorKind::AssigningDivision => b"/=",
            OperatorKind::LogicalAnd => b"&&",
            OperatorKind::LogicalOr => b"||",
            OperatorKind::LogicalNot => b"!",
            OperatorKind::Postincrement => b"++",
            OperatorKind::Postdecrement => b"--",
            OperatorKind::BitwiseOr => b"|",
            OperatorKind::AssigningBitwiseOr => b"|=",
            OperatorKind::BitwiseXor => b"^",
            OperatorKind::AssigningBitwiseXor => b"^=",
            OperatorKind::BitwiseAnd => b"&",
            OperatorKind::AssigningBitwiseAnd => b"&=",
            OperatorKind::BitwiseNot => b"~",
            OperatorKind::FunctionCall => b"()",
            OperatorKind::ArithmeticLeftShift => b"<<",
            OperatorKind::AssigningArithmeticLeftShift => b"=<<",
            OperatorKind::ArithmeticRightShift => b">>",
            OperatorKind::AssigningArithmeticRightShift => b"=>>",
            OperatorKind::IndirectMemberLookup => b"->",
            OperatorKind::Dereference => b"*",
            OperatorKind::MethodCall => b"->()",
            OperatorKind::AddressOf => b"&",
            OperatorKind::ArrayIndex => b"[]",
            OperatorKind::Compound => b", ",
            OperatorKind::Conditional => b"?:",
            OperatorKind::Maximum => b">?",
            OperatorKind::Minimum => b"<?",
            OperatorKind::Nop => b"",
            OperatorKind::DereferenceIndirectMemberLookup => b"->*",
            OperatorKind::Sizeof => b"sizeof ",
        }
    }
}

/// C++ type qualifiers
#[bitfield(u8)]
struct TypeQualifiers {
    /// Type is qualified with `const`.
    #[allow(
        non_snake_case,
        reason = "needed to avoid keyword clash, violating members are internal to macro"
    )]
    r#const: bool,

    /// Type is qualified with `volatile`.
    volatile: bool,

    /// Type is qualified with `restrict`/
    restrict: bool,

    #[bits(5)]
    __: u8,
}

impl TypeQualifiers {
    fn to_str(&self) -> &'static str {
        match (self.r#const(), self.volatile(), self.restrict()) {
            (true, true, true) => "const volatile __restrict",
            (false, true, true) => "volatile __restrict",
            (true, false, true) => "const __restrict",
            (true, true, false) => "const volatile",
            (true, _, _) => "const",
            (_, true, _) => "volatile",
            (_, _, true) => "__restrict",
            _ => "",
        }
    }

    fn from_code(code: u8) -> Self {
        let res = Self::new();

        match code {
            b'C' => res.with_const(true),
            b'V' => res.with_volatile(true),
            b'u' => res.with_restrict(true),
            _ => res,
        }
    }
}

#[derive(Debug, Clone)]
pub enum DemangledType {
    Void,
    Boolean,
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
    Float,
    Double,
    LongDouble,
    Reference {
        r#const: bool,
        restrict: bool,
        inner: Box<DemangledType>,
    },
    Pointer {
        r#const: bool,
        restrict: bool,
        inner: Box<DemangledType>,
    },
    Volatile {
        inner: Box<DemangledType>,
    },
    ClassOrStruct {
        name: String,
        templated: bool,
    },
    Function {
        args: Vec<DemangledType>,
        return_type: Option<Box<DemangledType>>,
        r#const: bool,
        has_varargs: bool,
    },
}

/// What kind of symbol this is.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum SymbolKind {
    /// Symbol refers to the vtable of a specified class.
    VTable,
    /// Symbol refers to a function entry point.
    Function {
        /// Qualified name of the function.
        qualified_name: String,
        /// Arguments to the function.
        args: Vec<DemangledType>,
        /// Return type of function.
        /// Not all GNUv2 mangling conventions include return type information.
        return_type: Option<DemangledType>,
        /// Whether or not this function is declared to be const (i.e. member function which does not mutate its instance)
        r#const: bool,
        /// Whether or not this function takes a variable number of additional arguments.
        has_varargs: bool,
    },
    /// Symbol refers to the static member of a container type.
    StaticMember,
    /// Symbol is type reflection information.
    TypeInfo(TypeInfoKind),
    GlobalConstructor,
    GlobalDestructor,
    DllImportStub,
}

/// Specifies what variety of type info this is.
#[non_exhaustive]
#[derive(Debug, Clone, Copy)]
pub enum TypeInfoKind {
    /// typeinfo is for a type node (class, struct, etc).
    Node,
    /// typeinfo is for a function or method.
    Function,
}

/// Information on a demangled symbol.
#[derive(Debug, Clone)]
pub struct DemangledSymbol {
    /// The full textual representation of the symbol after demangling.
    /// Same as you would expect to get by demangling with c++filt.
    pub cxxdecl: String,

    /// Structured information on the demangled symbol.
    pub kind: SymbolKind,
}

// #[derive(Debug, thiserror::Error)]
// pub enum DemangleError {
//     #[error("failed to demangle symbol")]
//     DemangleFailed,
// }

/// Result type for all demangle operations.
// pub type Result<T> = std::result::Result<T, DemangleError>;

const DEFAULT_DEMANGLE_STYLE: DemangleStyle = DemangleStyle::new().with_gnu(true);

#[derive(Default, Debug, Clone)]
enum StateSymbolKind {
    #[default]
    Unknown,
    VTable,
    Function,
    StaticMember,
    TypeInfoNode,
    TypeInfoFunction,
    GlobalConstructor,
    GlobalDestructor,
    DllImportStub,
}

// TODO: remove and rename internal state fields as appropriate
#[derive(Default, Debug)]
struct DemanglerState {
    opts: DemangleOpts,
    btypes: BTypeStore,
    raw_types: Vec<Vec<u8>>,
    ktypes: Vec<Vec<u8>>,
    constructor: i32,
    destructor: i32,
    static_type: bool,
    temp_start: i32,
    dllimported: bool,
    tmpl_argvec: Vec<Vec<u8>>,
    forgetting_types: i32,
    previous_argument: Vec<u8>,
    previous_argument_type: Option<CxxType>,
    nrepeats: i32,
    symbol_kind: StateSymbolKind,
    type_quals: TypeQualifiers,
    fn_state: FunctionState,
    decl_fn_qname_len: usize,
}

#[derive(Debug)]
struct BTypeStore {
    next_idx: usize,
    storage: Vec<Option<BType>>,
}

#[derive(Debug)]
struct BType {
    name: Vec<u8>,
    kind: BTypeKind,
}

#[derive(Debug)]
enum BTypeKind {
    Class { templated: bool },
    Unknown,
}

impl BTypeStore {
    fn new() -> Self {
        Self {
            next_idx: 0,
            storage: vec![],
        }
    }

    fn register(&mut self) -> usize {
        let idx = self.next_idx;
        self.storage.push(None);
        self.next_idx += 1;
        idx
    }

    fn remember(&mut self, idx: usize, btype: &[u8], kind: BTypeKind) -> Result<()> {
        let cell = self
            .storage
            .get_mut(idx)
            .with_context(|| format!("failed to lookup btype {idx}"))?;
        *cell = Some(BType {
            name: btype.to_owned(),
            kind,
        });

        Ok(())
    }

    fn get(&self, idx: usize) -> Option<&BType> {
        self.storage.get(idx)?.as_ref()
    }
}

impl Default for BTypeStore {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Default, Debug, Clone)]
struct FunctionState {
    return_type: Option<CxxType>,
    arg_types: Vec<CxxType>,
    type_quals: TypeQualifiers,
    has_varargs: bool,
}

#[derive(Debug, Clone)]
pub enum CxxType {
    Void,
    Boolean,
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
    Float,
    Double,
    LongDouble,
    Reference {
        r#const: bool,
        restrict: bool,
        inner: Box<CxxType>,
    },
    Pointer {
        r#const: bool,
        restrict: bool,
        inner: Box<CxxType>,
    },
    Volatile {
        inner: Box<CxxType>,
    },
    BType {
        index: usize,
    },
    Function {
        args: Vec<CxxType>,
        return_type: Option<Box<CxxType>>,
        r#const: bool,
        has_varargs: bool,
    },
}
impl CxxType {
    fn is_integral_type(&self) -> bool {
        match self {
            CxxType::Int { .. }
            | CxxType::Short { .. }
            | CxxType::Long { .. }
            | CxxType::LongLong { .. }
            | CxxType::StdInt { .. } => true,
            _ => false,
        }
    }

    fn is_realnum_type(&self) -> bool {
        match self {
            CxxType::Float | CxxType::Double | CxxType::LongDouble => true,
            _ => false,
        }
    }

    fn is_reference_type(&self) -> bool {
        match self {
            CxxType::Pointer { .. } | CxxType::Reference { .. } => true,
            _ => false,
        }
    }

    fn to_demangled(&self, btypes: &BTypeStore) -> Result<DemangledType> {
        Ok(match self {
            CxxType::Void => DemangledType::Void,
            CxxType::Boolean => DemangledType::Boolean,
            CxxType::Int { signed } => DemangledType::Int { signed: *signed },
            CxxType::Short { signed } => DemangledType::Short { signed: *signed },
            CxxType::Char { signed } => DemangledType::Char { signed: *signed },
            CxxType::WideChar { signed } => DemangledType::WideChar { signed: *signed },
            CxxType::Long { signed } => DemangledType::Long { signed: *signed },
            CxxType::LongLong { signed } => DemangledType::LongLong { signed: *signed },
            CxxType::StdInt { bitwidth, signed } => DemangledType::StdInt {
                bitwidth: *bitwidth,
                signed: *signed,
            },
            CxxType::Float => DemangledType::Float,
            CxxType::Double => DemangledType::Double,
            CxxType::LongDouble => DemangledType::LongDouble,
            CxxType::Reference {
                r#const,
                restrict,
                inner,
            } => DemangledType::Reference {
                r#const: *r#const,
                restrict: *restrict,
                inner: Box::new(inner.to_demangled(btypes)?),
            },
            CxxType::Pointer {
                r#const,
                restrict,
                inner,
            } => DemangledType::Pointer {
                r#const: *r#const,
                restrict: *restrict,
                inner: Box::new(inner.to_demangled(btypes)?),
            },
            CxxType::Volatile { inner } => DemangledType::Volatile {
                inner: Box::new(inner.to_demangled(btypes)?),
            },
            CxxType::BType { index } => {
                let btype = btypes
                    .get(*index)
                    .with_context(|| format!("CxxType referenced undefined btype index {index}"))?;
                let name = String::from_utf8_lossy(&btype.name).to_string();

                match btype.kind {
                    BTypeKind::Class { templated } => {
                        DemangledType::ClassOrStruct { name, templated }
                    }
                    BTypeKind::Unknown => {
                        anyhow::bail!("CxxType referenced btype {index} which has unknown name")
                    }
                }
            }
            CxxType::Function {
                args,
                return_type,
                r#const,
                has_varargs,
            } => {
                let args = args
                    .iter()
                    .map(|cxxtype| cxxtype.to_demangled(btypes))
                    .collect::<Result<Vec<_>>>()?;
                DemangledType::Function {
                    args,
                    return_type: return_type
                        .as_ref()
                        .map(|cxxtype| cxxtype.to_demangled(btypes))
                        .transpose()?
                        .map(Box::new),
                    r#const: *r#const,
                    has_varargs: *has_varargs,
                }
            }
        })
    }
}

#[derive(Debug, Clone)]
enum IncompleteCxxType {
    Void,
    Boolean,
    Int { signed: bool },
    Short { signed: bool },
    Char { signed: Option<bool> },
    WideChar { signed: Option<bool> },
    Long { signed: bool },
    LongLong { signed: bool },
    StdInt { bitwidth: usize, signed: bool },
    Float,
    Double,
    LongDouble,
    Reference,
    Pointer,
    ConstModifier,
    VolatileModifier,
    RestrictModifier,
    UnsignedModifier,
    SignedModifier,
    BType { index: usize },
    Function { fn_state: FunctionState },
}

impl IncompleteCxxType {
    fn is_terminal(&self) -> bool {
        match self {
            Self::Function { .. }
            | Self::Reference { .. }
            | Self::Pointer { .. }
            | Self::ConstModifier
            | Self::VolatileModifier
            | Self::RestrictModifier => false,
            _ => true,
        }
    }
}

impl TryFrom<IncompleteCxxType> for CxxType {
    type Error = anyhow::Error;

    fn try_from(c_type: IncompleteCxxType) -> std::result::Result<Self, Self::Error> {
        Ok(match c_type {
            IncompleteCxxType::Void => CxxType::Void,
            IncompleteCxxType::Boolean => CxxType::Boolean,
            IncompleteCxxType::Int { signed } => CxxType::Int { signed },
            IncompleteCxxType::Short { signed } => CxxType::Short { signed },
            IncompleteCxxType::Char { signed } => CxxType::Char { signed },
            IncompleteCxxType::WideChar { signed } => CxxType::WideChar { signed },
            IncompleteCxxType::Long { signed } => CxxType::Long { signed },
            IncompleteCxxType::LongLong { signed } => CxxType::LongLong { signed },
            IncompleteCxxType::StdInt { bitwidth, signed } => CxxType::StdInt { bitwidth, signed },
            IncompleteCxxType::Float => CxxType::Float,
            IncompleteCxxType::Double => CxxType::Double,
            IncompleteCxxType::LongDouble => CxxType::LongDouble,
            IncompleteCxxType::BType { index } => CxxType::BType { index },
            IncompleteCxxType::Reference => {
                anyhow::bail!("reference cannot exist in non-terminal position")
            }
            IncompleteCxxType::Pointer => {
                anyhow::bail!("pointer cannot exist in non-terminal position")
            }
            IncompleteCxxType::ConstModifier => {
                anyhow::bail!("const modifier is incomplete C type")
            }
            IncompleteCxxType::VolatileModifier => {
                anyhow::bail!("volatile modifier is incomplete C type")
            }
            IncompleteCxxType::RestrictModifier => {
                anyhow::bail!("__restrict modifier is incomplete C type")
            }
            IncompleteCxxType::UnsignedModifier => {
                anyhow::bail!("unsigned modifier is incomplete C type")
            }
            IncompleteCxxType::SignedModifier => {
                anyhow::bail!("signed modifier is incomplete C type")
            }
            IncompleteCxxType::Function { fn_state } => CxxType::Function {
                args: fn_state.arg_types,
                return_type: fn_state.return_type.map(Box::new),
                r#const: false,
                has_varargs: fn_state.has_varargs,
            },
        })
    }
}

fn take_one_type(
    mut c_types: Vec<IncompleteCxxType>,
) -> std::result::Result<(CxxType, Vec<IncompleteCxxType>), anyhow::Error> {
    let last_c_type = c_types.pop().context("empty IncompleteCxxType stack")?;
    if c_types.is_empty() && !last_c_type.is_terminal() {
        anyhow::bail!("attempted to construct incomplete type stack");
    }
    let mut c_type = last_c_type.try_into()?;

    fn handle_const_modifier(c_type: &mut CxxType) -> Result<()> {
        match c_type {
            CxxType::Reference { r#const, .. } => {
                *r#const = true;
            }
            CxxType::Pointer { r#const, .. } => {
                *r#const = true;
            }
            ty => anyhow::bail!("const modifier applied to invalid type {ty:?}"),
        }

        Ok(())
    }

    fn handle_restrict_modifier(c_type: &mut CxxType) -> Result<()> {
        match c_type {
            CxxType::Reference { restrict, .. } => {
                *restrict = true;
            }
            CxxType::Pointer { restrict, .. } => {
                *restrict = true;
            }
            ty => anyhow::bail!("__restrict modifier applied to invalid type {ty:?}"),
        }

        Ok(())
    }

    fn handle_int_signedness_modifier(c_type: &mut CxxType, signed: bool) -> Result<()> {
        let signedness_str = if signed { "signed" } else { "unsigned" };

        let signed_field = match c_type {
            CxxType::Char { signed } => {
                // Placeholder value for now
                *signed = Some(false);
                // Just assigned; guaranteed not to panic
                signed.as_mut().unwrap()
            }
            CxxType::Int { signed } => signed,
            CxxType::StdInt { signed, .. } => signed,
            CxxType::Short { signed } => signed,
            CxxType::Long { signed } => signed,
            CxxType::LongLong { signed } => signed,
            ty => {
                anyhow::bail!("{signedness_str} modifier applied to non-integral/char type {ty:?}")
            }
        };

        *signed_field = signed;

        Ok(())
    }

    while let Some(flat_c_type) = c_types.pop() {
        c_type = match flat_c_type {
            IncompleteCxxType::Reference => CxxType::Reference {
                r#const: false,
                restrict: false,
                inner: Box::new(c_type),
            },
            IncompleteCxxType::Pointer => CxxType::Pointer {
                r#const: false,
                restrict: false,
                inner: Box::new(c_type),
            },
            IncompleteCxxType::Function { fn_state } => CxxType::Function {
                return_type: fn_state.return_type.map(Box::new),
                args: fn_state.arg_types,
                r#const: false,
                has_varargs: fn_state.has_varargs,
            },
            IncompleteCxxType::ConstModifier => match c_type {
                CxxType::Volatile { inner } => {
                    let mut inner = inner;
                    handle_const_modifier(&mut inner)?;
                    CxxType::Volatile { inner }
                }
                mut ty => {
                    handle_const_modifier(&mut ty)?;
                    ty
                }
            },
            IncompleteCxxType::RestrictModifier => match c_type {
                CxxType::Volatile { inner } => {
                    let mut inner = inner;
                    handle_restrict_modifier(&mut inner)?;
                    CxxType::Volatile { inner }
                }
                mut ty => {
                    handle_restrict_modifier(&mut ty)?;
                    ty
                }
            },
            IncompleteCxxType::VolatileModifier => match c_type {
                CxxType::Volatile { .. } => {
                    anyhow::bail!("volatile modifier cannot be specified multiple times")
                }
                ty => CxxType::Volatile {
                    inner: Box::new(ty),
                },
            },
            IncompleteCxxType::SignedModifier => match c_type {
                CxxType::Volatile { inner } => {
                    let mut inner = inner;
                    handle_int_signedness_modifier(&mut inner, true)?;
                    CxxType::Volatile { inner }
                }
                mut ty => {
                    handle_int_signedness_modifier(&mut ty, true)?;
                    ty
                }
            },

            IncompleteCxxType::UnsignedModifier => match c_type {
                CxxType::Volatile { inner } => {
                    let mut inner = inner;
                    handle_int_signedness_modifier(&mut inner, false)?;
                    CxxType::Volatile { inner }
                }
                mut ty => {
                    handle_int_signedness_modifier(&mut ty, false)?;
                    ty
                }
            },
            ty => anyhow::bail!("non-terminal type {ty:?} found in container position"),
        };
    }

    Ok((c_type, c_types))
}

impl TryFrom<Vec<IncompleteCxxType>> for CxxType {
    type Error = anyhow::Error;

    fn try_from(value: Vec<IncompleteCxxType>) -> std::result::Result<Self, Self::Error> {
        let (ty, unconsumed_types) = take_one_type(value)?;

        if !unconsumed_types.is_empty() {
            anyhow::bail!("unconsumed types remaining in flat type stack");
        }

        Ok(ty)
    }
}

trait VecExt<T> {
    fn prepend(&mut self, prepend_with: &[T]);
}

impl<T: Clone> VecExt<T> for Vec<T> {
    fn prepend(&mut self, prepend_with: &[T]) {
        self.splice(0..0, prepend_with.iter().cloned());
    }
}

pub fn cplus_demangle_v2(mangled: &[u8], opts: DemangleOpts) -> Result<DemangledSymbol> {
    let opts = {
        let style = match opts.style().into_bits() {
            0 => DEFAULT_DEMANGLE_STYLE,
            _ => opts.style(),
        };
        opts.with_style(style)
    };

    let mut state = DemanglerState {
        opts,
        ..Default::default()
    };

    let declp = state.internal_demangle(mangled)?;

    let kind = state.extract_symbol_info(&declp)?;

    let cxxdecl_base = String::from_utf8(declp).map_err(|e| {
        log::error!("failed to decode declp: {e:?}");
        anyhow::anyhow!("failed to decode symbol from utf-8")
    })?;

    let cxxdecl = match kind {
        SymbolKind::GlobalConstructor => {
            format!("global constructors keyed to {cxxdecl_base}")
        }
        SymbolKind::GlobalDestructor => {
            format!("global destructors keyed to {cxxdecl_base}")
        }
        SymbolKind::DllImportStub => format!("import stub for {cxxdecl_base}"),
        _ => cxxdecl_base,
    };

    Ok(DemangledSymbol { cxxdecl, kind })
}

/// Internal enum used to determine which case was previously hit in DemanglerState::gnu_special
#[derive(Debug)]
enum GnuMangleCase {
    Destructor,
    Vtable,
    StaticMember,
    VirtualThunk,
    TypeInfo,
}

/// Internal type used to indicate functions which consume the mangled symbol.
///
/// `mangled` indicates the unconsumed part of the mangled symbol.
/// `value` indicates the value produced by consuming part of the mangled symbol.
#[must_use]
struct ConsumeVal<'a, Inner> {
    mangled: &'a [u8],
    value: Inner,
}

impl DemanglerState {
    #[allow(unreachable_patterns)]
    fn extract_symbol_info(&self, declp: &[u8]) -> Result<SymbolKind> {
        match &self.symbol_kind {
            StateSymbolKind::Unknown => anyhow::bail!("unknown symbol kind"),
            StateSymbolKind::VTable => Ok(SymbolKind::VTable),
            StateSymbolKind::StaticMember => Ok(SymbolKind::StaticMember),
            StateSymbolKind::TypeInfoNode => Ok(SymbolKind::TypeInfo(TypeInfoKind::Node)),
            StateSymbolKind::TypeInfoFunction => Ok(SymbolKind::TypeInfo(TypeInfoKind::Function)),
            StateSymbolKind::Function => self.extract_function_info(declp),
            StateSymbolKind::GlobalConstructor => Ok(SymbolKind::GlobalConstructor),
            StateSymbolKind::GlobalDestructor => Ok(SymbolKind::GlobalDestructor),
            StateSymbolKind::DllImportStub => Ok(SymbolKind::DllImportStub),
            sym => unimplemented!("output translation not implemented for symbol {sym:?}"),
        }
    }

    fn extract_function_info(&self, declp: &[u8]) -> Result<SymbolKind> {
        for (i, ty) in self.raw_types.iter().enumerate() {
            debug_log_bytes(ty, &format!("type {i}"));
        }
        for (i, bty) in self.btypes.storage.iter().enumerate() {
            if let Some(bty) = bty {
                debug_log_bytes(&bty.name, &format!("btype {i}"));
                log::debug!("btype {i} kind: {:?}", bty.kind);
            } else {
                log::debug!("btype {i}: <none>");
            }
        }

        Ok(SymbolKind::Function {
            qualified_name: String::from_utf8_lossy(&declp[0..self.decl_fn_qname_len]).to_string(),
            args: self
                .fn_state
                .arg_types
                .iter()
                .map(|cxxtype| cxxtype.to_demangled(&self.btypes))
                .collect::<Result<Vec<_>>>()?,
            return_type: self
                .fn_state
                .return_type
                .as_ref()
                .map(|cxxtype| cxxtype.to_demangled(&self.btypes))
                .transpose()?,
            r#const: self.fn_state.type_quals.r#const(),
            has_varargs: self.fn_state.has_varargs,
        })
    }

    fn internal_demangle(&mut self, mangled: &[u8]) -> Result<Vec<u8>> {
        let style = self.opts.style();

        let mut declp = vec![];
        if mangled == b"" {
            return Ok(declp);
        }

        let result = if style.auto() || style.gnu() {
            self.gnu_special(mangled, &mut declp)
        } else {
            Err(anyhow::anyhow!("wrong style"))
        };

        let result = if let Err(_e) = result {
            log::debug!("gnu special: end  (success=0)");
            self.demangle_prefix(mangled, &mut declp)
        } else {
            log::debug!("gnu special: end  (success=1)");
            result
        };

        let _ = match result {
            Ok(ConsumeVal { mangled, .. }) if !mangled.is_empty() => {
                self.demangle_signature(mangled, &mut declp)
            }
            _ => result,
        }?;

        if self.constructor == 2 {
            self.symbol_kind = StateSymbolKind::GlobalConstructor;
            self.constructor = 0;
        } else if self.destructor == 2 {
            self.symbol_kind = StateSymbolKind::GlobalDestructor;
            self.destructor = 0;
        } else if self.dllimported {
            self.symbol_kind = StateSymbolKind::DllImportStub;
            self.dllimported = false;
        }

        Ok(declp)
    }

    #[must_use]
    fn demangle_prefix<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("demangle prefix: start");

        let mut success = true;
        let style = self.opts.style();

        if mangled.starts_with(b"__imp_") || mangled.starts_with(b"_imp__") {
            log::debug!("demangle prefix: import symbol");
            // it's a symbol imported from a PE dynamic library.
            // Check for both new style prefix _imp__ and legacy __imp_
            // used by older versions of dlltool.
            mangled = &mangled[6..];
            self.dllimported = true;
        } else if mangled.len() >= 11 && mangled.starts_with(b"_GLOBAL_") {
            log::debug!("demangle prefix: global constructor/destructor");
            let marker = CPLUS_MARKERS.iter().find(|&&c| c == mangled[8]);
            match (marker, mangled[9]) {
                (Some(&c), b'D') if c == mangled[10] => {
                    log::debug!("demangle prefix: global destructor");
                    // Global destructor called at exit
                    mangled = &mangled[11..];
                    self.destructor = 2;
                    if let res @ Ok(_) = self.gnu_special(mangled, declp) {
                        log::debug!("demangle prefix: end\t[global dtor]\t(success=1)");
                        return res;
                    }
                }
                (Some(&c), b'I') if c == mangled[10] => {
                    log::debug!("demangle prefix: global constructor");
                    // Global constructor called at init
                    mangled = &mangled[11..];
                    self.constructor = 2;
                    if let res @ Ok(_) = self.gnu_special(mangled, declp) {
                        return res;
                    }
                }
                _ => {}
            }
        } else if style.arm() || style.hp() || style.edg() {
            log::debug!("demangle prefix: arm style global ctor/dtor");
            if mangled.starts_with(b"__std__") {
                // Global destructor (ARM style)
                mangled = &mangled[7..];
                self.destructor += 2;
            } else if mangled.starts_with(b"__sti__") {
                // Global constructor (ARM style)
                mangled = &mangled[7..];
                self.constructor += 2;
            }
        }

        let scan_idx =
            memmem::find(mangled, b"__").context("failed to locate underscore prefix")?;
        let scan = &mangled[scan_idx..];

        if self.static_type {
            if !scan[0].is_ascii_digit() && scan[0] != b't' {
                success = false;
            }
        } else if scan_idx == 0
            && scan.len() > 2
            && (scan[2].is_ascii_digit()
                || (scan[2] == b'Q')
                || (scan[2] == b't')
                || (scan[2] == b'K')
                || (scan[2] == b'H'))
        {
            log::debug!("demangle prefix: prefix found");
            // The ARM says nothing about the mangling of local variables.
            // But cfront mangles local variables by prepending __<nesting_level>
            // to them. As an extension to ARM demangling we handle this case.
            if style.lucid() || style.arm() || style.hp() && scan[2].is_ascii_digit() {
                log::debug!("demangle prefix: cfront local variable");
                mangled = &scan[2..];
                ConsumeVal { mangled, .. } = consume_count(mangled)?;
                declp.extend(mangled);
                mangled = &mangled[mangled.len()..];
            } else {
                log::debug!("demangle prefix: gnu style constructor");
                self.symbol_kind = StateSymbolKind::Function;
                // A GNU style constructor starts with __[0-9Qt].  But cfront uses
                // names like __Q2_3foo3bar for nested type names.  So don't accept
                // this style of constructor for cfront demangling.  A GNU
                // style member-template constructor starts with 'H'
                if !(style.lucid() || style.arm() || style.hp() || style.edg()) {
                    self.constructor += 1;
                }
                mangled = &scan[2..];
            }
        } else if style.arm() && scan.len() > 3 && scan[2..4] == b"pt"[..] {
            log::debug!("demangle prefix: cfront parameterized type");
            // Cfront style parameterised type
            ConsumeVal { mangled, .. } =
                self.demangle_arm_hp_template(mangled, mangled.len(), declp)?;
        } else if style.edg()
            && scan.len() > 3
            && ((scan[2..4] == b"pt"[..]) || (scan[2..4] == b"tm"[..]) || (scan[2..4] == b"ps"[..]))
        {
            log::debug!("demangle prefix: edg parameterized type");
            // EDG-style parameterized type
            ConsumeVal { mangled, .. } =
                self.demangle_arm_hp_template(mangled, mangled.len(), declp)?;
        } else if scan_idx == 0 && scan.len() > 2 && !scan[2].is_ascii_digit() && scan[2] != b't' {
            log::debug!("demangle prefix: arm name");
            // mangled name that starts with "__"
            if !(style.arm() || style.lucid() || style.hp() || style.edg())
                && arm_special(mangled, declp).is_err()
            {
                log::debug!("Not arm special");
                let mut scan = scan;
                while !scan.is_empty() && scan[0] != b'_' {
                    scan = &scan[1..];
                }
                let scan_idx =
                    memmem::find(scan, b"__").context("failed to locate underscore prefix")?;
                scan = &scan[scan_idx..];

                log::debug!("demangle prefix: function name");
                self.symbol_kind = StateSymbolKind::Function;

                // Look for the LAST occurrence of __, allowing names to
                // have the '__' sequence embedded in them.
                if !(style.arm() || style.hp()) {
                    let scan_idx =
                        memmem::rfind(scan, b"__").context("failed to locate underscore suffix")?;
                    scan = &scan[scan_idx..];
                }

                if scan.len() <= 2 {
                    anyhow::bail!("malformed symbol: no name following __prefix__");
                }

                ConsumeVal { mangled, .. } = self.demangle_function_name(mangled, declp, scan)?;
            }
        } else if scan.len() > 2 {
            // Mangled name does not start with "__" but does have one somewhere
            // in there with non empty stuff after it.  Looks like a global
            // function name.
            log::debug!("demangle prefix: global function name");
            ConsumeVal { mangled, .. } = self.demangle_function_name(mangled, declp, scan)?;
            debug_log_bytes(declp, "demangle prefix: declp post demangle_function_name");
            self.decl_fn_qname_len = declp.len();
            self.symbol_kind = StateSymbolKind::Function;
        } else {
            log::debug!("demangle prefix: fail");
            log::debug!("demangle prefix: end\t(success=0)");
            // Doesn't look like a mangled name
            success = false;
        }

        if !success {
            if self.constructor == 2 || self.destructor == 2 {
                declp.extend(mangled);
                mangled = &mangled[mangled.len()..];
            } else {
                anyhow::bail!("failed to demangle prefix");
            }
        }

        log::debug!("demangle prefix: end\t(success=1)");

        Ok(ConsumeVal { mangled, value: () })
    }

    #[must_use]
    fn gnu_special<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("gnu special: start");
        let case: GnuMangleCase;
        (mangled, case) = match mangled {
            // GNU style destructor (_$_ or other markers)
            &[b'_', c, b'_', ref rest @ ..] if CPLUS_MARKERS.contains(&c) => {
                log::debug!("GNU demangler: destructor");
                (rest, GnuMangleCase::Destructor)
            }

            // GNU style vtable
            &[b'_', b'_', b'v', b't', b'_', ref rest @ ..] => (rest, GnuMangleCase::Vtable),
            &[b'_', b'v', b't', c, ref rest @ ..] if CPLUS_MARKERS.contains(&c) => {
                log::debug!("GNU demangler: vtable");

                (rest, GnuMangleCase::Vtable)
            }

            // static data member
            &[b'_', ref rest @ ..]
                if !rest.is_empty()
                    && b"0123456789Qt".contains(&rest[0])
                    && CPLUS_MARKERS.iter().any(|m| rest.contains(m)) =>
            {
                log::debug!("GNU demangler: static member");

                (rest, GnuMangleCase::StaticMember)
            }

            s if s.starts_with(b"__thunk_") => {
                log::debug!("GNU demangler: virtual member thunk");
                (&s[8..], GnuMangleCase::VirtualThunk)
            }

            // type info
            &[b'_', b'_', b't', ref rest @ ..]
                if !rest.is_empty() && rest[0] == b'i' || rest[0] == b'f' =>
            {
                log::debug!("GNU demangler: typeinfo");

                (rest, GnuMangleCase::TypeInfo)
            }

            // other case
            _ => anyhow::bail!("unknown GNU special case"),
        };

        let mut success = true;
        let mangled = match case {
            GnuMangleCase::Destructor => {
                self.destructor += 1;

                self.symbol_kind = StateSymbolKind::Function;

                mangled
            }
            GnuMangleCase::Vtable => {
                log::debug!("gnu special: demangle vtbl");
                while mangled != b"" {
                    match mangled[0] {
                        b'Q' | b'K' => {
                            ConsumeVal { mangled, .. } =
                                self.demangle_qualified(mangled, declp, false, true)?;
                        }
                        b't' => {
                            ConsumeVal { mangled, .. } =
                                self.demangle_template(mangled, declp, None, true, true)?;
                        }
                        c => {
                            let mut is_count = true;
                            let n = if c.is_ascii_digit() {
                                let n;
                                ConsumeVal { value: n, mangled } = consume_count(mangled)?;
                                if n > mangled.len() {
                                    is_count = false;
                                }
                                n
                            } else {
                                // strcspn equivalent
                                mangled
                                    .iter()
                                    .take_while(|&b| !CPLUS_MARKERS.contains(b))
                                    .count()
                            };
                            if is_count {
                                declp.extend(mangled[..n].iter());
                                mangled = &mangled[n..];
                            }
                        }
                    }

                    let p = strpbrk(mangled, CPLUS_MARKERS);
                    match p {
                        None if success => {}
                        Some(p) if success && p == mangled => {
                            declp.extend(self.scope_str());
                            mangled = &mangled[1..];
                        }
                        _ => {
                            success = false;
                            break;
                        }
                    }
                }

                if success {
                    self.symbol_kind = StateSymbolKind::VTable;
                    declp.extend(b" virtual table");
                }

                mangled
            }
            GnuMangleCase::StaticMember => {
                log::debug!("gnu special: demangle static member");
                let mut mangled = mangled;
                let p = strpbrk(mangled, CPLUS_MARKERS);

                match mangled[0] {
                    b'Q' | b'K' => {
                        ConsumeVal { mangled, .. } =
                            self.demangle_qualified(mangled, declp, false, true)?;
                    }
                    b't' => {
                        ConsumeVal { mangled, .. } =
                            self.demangle_template(mangled, declp, None, true, true)?;
                    }
                    _ => {
                        let n;

                        ConsumeVal { value: n, mangled } = consume_count(mangled)?;

                        if n > mangled.len() {
                            success = false;
                        } else {
                            declp.extend(&mangled[..n]);
                            mangled = &mangled[n..];
                        }
                    }
                }

                match (success, p) {
                    (true, Some(p)) if p == mangled => {
                        self.symbol_kind = StateSymbolKind::StaticMember;
                        mangled = &mangled[1..];
                        declp.extend(b"::");
                        declp.extend(mangled);
                        mangled = &mangled[mangled.len()..];
                    }
                    _ => anyhow::bail!("failed to parse static member"),
                }

                mangled
            }
            GnuMangleCase::VirtualThunk => {
                let delta;
                debug_log_bytes(mangled, "mangled");
                ConsumeVal {
                    mangled,
                    value: delta,
                } = consume_count(mangled)?;

                mangled = &mangled[1..];
                let method = self.internal_demangle(mangled)?;

                if method.is_empty() {
                    anyhow::bail!("failed to get method name for virtual thunk");
                }

                let thunk_preamble = format!("virtual function thunk (delta:-{delta}) for ");
                declp.extend(thunk_preamble.as_bytes());
                declp.extend(&method);
                self.decl_fn_qname_len += thunk_preamble.as_bytes().len(); // hack: "resize" the qname segment
                mangled = &mangled[mangled.len()..];

                mangled
            }
            GnuMangleCase::TypeInfo => {
                log::debug!("gnu special: demangle typeinfo");
                let (sym_k, p) = match mangled[0] {
                    b'i' => (StateSymbolKind::TypeInfoNode, &b" type_info node"[..]),
                    b'f' => (
                        StateSymbolKind::TypeInfoFunction,
                        &b" type_info function"[..],
                    ),
                    c => {
                        let chr = char::from_u32(c as u32)
                            .map(|chr| chr.to_string())
                            .unwrap_or_else(|| format!("{c:x}"));
                        anyhow::bail!("unknown typeinfo kind: {chr}");
                    }
                };
                let mut mangled = &mangled[1..];
                match mangled[0] {
                    b'Q' | b'K' => {
                        log::debug!("typeinfo: qualified");
                        ConsumeVal { mangled, .. } =
                            self.demangle_qualified(mangled, declp, false, true)?;
                    }
                    b't' => {
                        log::debug!("typeinfo: template");
                        ConsumeVal { mangled, .. } =
                            self.demangle_template(mangled, declp, None, true, true)?;
                    }
                    _ => {
                        log::debug!("typeinfo: fundamental type");
                        ConsumeVal { mangled, .. } = self.demangle_fund_type(mangled, declp)?;
                        debug_log_bytes(&*declp, "declp");
                    }
                }

                debug_log_bytes(mangled, "mangled typeinfo");

                if success && mangled != b"" {
                    log::debug!("demangle failed");
                    anyhow::bail!("demangle failed");
                } else {
                    declp.extend(p);
                }

                self.symbol_kind = sym_k;

                mangled
            }

            _ => mangled,
        };

        debug_log_bytes(mangled, "mangled after fund type");

        Ok(ConsumeVal { value: (), mangled })
    }

    #[must_use]
    fn demangle_qualified<'a>(
        &mut self,
        mut mangled: &'a [u8],
        result: &'_ mut Vec<u8>,
        isfuncname: bool,
        append: bool,
    ) -> Result<ConsumeVal<'a, Vec<u8>>> {
        let style = self.opts.style();
        let mut temp: Vec<u8> = vec![];
        let mut last_name: Vec<u8> = vec![];
        let mut qualifier_count = 0usize;

        let bindex = self.btypes.register();

        log::debug!("demangle qualified: start");

        // Only use isfuncname if the entity is a constructor or destructor.
        let isfuncname = isfuncname && ((self.constructor & 1) > 0 || (self.destructor & 1) > 0);

        if !mangled.is_empty() && mangled[0] == b'K' {
            let idx;
            // Squangling qualified name reuse
            mangled = &mangled[1..];
            ConsumeVal {
                mangled,
                value: idx,
            } = consume_count_with_underscores(mangled)?;

            if idx >= self.ktypes.len() {
                log::error!("Referenced unknown Ktype index {idx}");
                anyhow::bail!("Referenced unknown Ktype index {idx}");
            }
            temp.extend(&self.ktypes[idx]);
        } else {
            if mangled.len() >= 2 {
                match mangled[1] {
                    b'_' => {
                        // GNU mangled name with more than 9 classes
                        anyhow::bail!("TODO: Implement GNU mangled name with more than 9 classes");
                    }
                    c @ b'1'..=b'9' => {
                        qualifier_count = std::str::from_utf8(&[c])
                            .context("failed to parse count")?
                            .parse()
                            .context("failed to parse count")?;

                        // If there is an underscore after the digit, skip it.  This is
                        // said to be for ARM-qualified names, but the ARM makes no
                        // mention of such an underscore.  Perhaps cfront uses one.
                        if mangled.len() >= 3 && mangled[2] == b'_' {
                            mangled = &mangled[1..];
                        }
                        mangled = &mangled[2..];
                    }
                    _ => anyhow::bail!("expected Ktype index"),
                }
            }
        }

        for i in (0..qualifier_count).rev() {
            let mut remember_k = true;
            last_name.clear();

            if !mangled.is_empty() && mangled[0] == b'_' {
                mangled = &mangled[1..];
            }

            if !mangled.is_empty() {
                if mangled[0] == b't' {
                    // Here we always append to TEMP since we will want to use
                    // the template name without the template parameters as a
                    // constructor or destructor name.  The appropriate
                    // (parameter-less) value is returned by demangle_template
                    // in LAST_NAME.  We do not remember the template type here,
                    // in order to match the G++ mangling algorithm.
                    ConsumeVal { mangled, .. } = self.demangle_template(
                        mangled,
                        &mut temp,
                        Some(&mut last_name),
                        true,
                        false,
                    )?;
                } else if mangled[0] == b'K' {
                    let idx;
                    mangled = &mangled[1..];
                    ConsumeVal {
                        mangled,
                        value: idx,
                    } = consume_count_with_underscores(mangled)?;
                    if idx >= self.ktypes.len() {
                        anyhow::bail!("referenced unknown Ktype index {idx}");
                    } else {
                        temp.extend(&self.ktypes[idx]);
                    }
                    remember_k = false;
                } else {
                    if style.edg() {
                        anyhow::bail!("TODO: implement EDG recursive demangling");
                    } else {
                        ConsumeVal { mangled, .. } =
                            self.do_type(mangled, &mut last_name, false)?;
                        temp.extend(&last_name);
                    }
                }
            }

            if remember_k {
                self.ktypes.push(temp.clone());
            }

            if i > 0 {
                temp.extend(self.scope_str());
            }
        }

        self.btypes.remember(bindex, &temp, BTypeKind::Unknown)?;

        // If we are using the result as a function name, we need to append
        // the appropriate '::' separated constructor or destructor name.
        // We do this here because this is the most convenient place, where
        // we already have a pointer to the name and the length of the name.
        if isfuncname {
            temp.extend(self.scope_str());
            if (self.destructor & 1) > 0 {
                temp.push(b'~');
            }
            temp.extend(&last_name);
        }

        // Now either prepend the temp buffer to the result, or append it,
        // depending upon the state of the append flag.
        if append {
            result.extend(&temp);
        } else {
            if !result.is_empty() {
                temp.extend(self.scope_str());
            }
            result.prepend(&temp);
        }

        log::debug!("demangle qualified: done");

        Ok(ConsumeVal {
            mangled,
            value: temp,
        })
    }

    #[must_use]
    fn demangle_template<'a>(
        &mut self,
        mangled: &'a [u8],
        tname: &'_ mut Vec<u8>,
        trawname: Option<&'_ mut Vec<u8>>,
        is_type: bool,
        remember: bool,
    ) -> Result<ConsumeVal<'a, Option<usize>>> {
        let mut mangled = &mangled[1..];
        let mut is_java_array = false;
        let mut need_comma = false;
        let mut bindex = None;

        log::debug!("demangle template: start");

        if is_type {
            if remember {
                bindex = Some(self.btypes.register());
            }
            // Get template name
            if mangled[0] == b'z' {
                log::debug!("demangle template: is type, template param");
                mangled = &mangled[2..];

                let idx;
                ConsumeVal {
                    value: idx,
                    mangled,
                } = consume_count_with_underscores(mangled)?;

                anyhow::bail!("TODO: implement demangle_template/z");
            } else {
                log::debug!("demangle template: is type, NOT template param");

                debug_log_bytes(mangled, "demangle template: mangled (non-template param)");
                let r;
                ConsumeVal { value: r, mangled } = consume_count(mangled)?;

                if r > mangled.len() {
                    anyhow::bail!("count for template name is longer than remaining length");
                }
                is_java_array = self.opts.java() && mangled.starts_with(b"JArray1Z");
                if !is_java_array {
                    tname.extend(&mangled[..r]);
                }
                if let Some(t) = trawname {
                    t.extend(&mangled[..r]);
                }
                mangled = &mangled[r..];
            }
        }

        if !is_java_array {
            tname.extend(b"<");
        }

        let r;
        ConsumeVal { value: r, mangled } = get_count(mangled)?;

        log::debug!("demangle template: {r} template param(s)");

        if !is_type {
            let mut v = vec![];
            v.resize_with(r, Vec::new);
            self.tmpl_argvec = v;
        }

        debug_log_bytes(&*tname, "demangle template: tname");
        debug_log_bytes(mangled, "dmangle template: mangled");

        let mut last_cxxtype;
        for i in 0..r {
            log::debug!("demangle template: param {i}");
            if need_comma {
                tname.extend(b", ");
            }
            if mangled[0] == b'Z' {
                let mut temp: Vec<u8> = vec![];
                log::debug!("demangle template: type parameter");
                mangled = &mangled[1..];

                ConsumeVal { value: _, mangled } = self.do_type(mangled, &mut temp, true)?;

                tname.extend(&temp);

                if !is_type {
                    log::debug!("demangle template: add to argvec");
                    self.tmpl_argvec
                        .get_mut(i)
                        .with_context(|| format!("missing Z template backref {i}"))?
                        .extend(&temp);
                }
            } else if mangled[0] == b'z' {
                log::debug!("demangle template: template parameter");
                mangled = &mangled[1..];
                anyhow::bail!("TODO: implement template parameter demangle");
            } else {
                // value parameter
                let mut temp: Vec<u8> = vec![];
                ConsumeVal {
                    value: last_cxxtype,
                    mangled,
                } = self.do_type(mangled, &mut temp, true)?;
                log::debug!("demangle template: is_type = {is_type}");
                // Change here is because we don't want to have to do a weird dance with Cell to reborrow
                // tname mutably during this scope.
                // Arguably there was an overgeneralization in the original C code anyway.
                if !is_type {
                    log::debug!("demangle template: NOT TYPE");
                    let mut s = Vec::new();
                    ConsumeVal { mangled, .. } =
                        self.demangle_template_value_parm(mangled, &mut s, &last_cxxtype)?;

                    self.tmpl_argvec.push(s.clone());
                    tname.extend(&*s);
                } else {
                    ConsumeVal { mangled, .. } =
                        self.demangle_template_value_parm(mangled, tname, &last_cxxtype)?;
                }

                debug_log_bytes(tname, "demangle_template: tname");
            }
            need_comma = true;
        }

        tname.extend(if is_java_array { &b"[]"[..] } else { &b">"[..] });

        if is_type && remember {
            if let Some(idx) = bindex {
                debug_log_bytes(tname, "demangle template: tname in remember btype");
                self.btypes
                    .remember(idx, tname, BTypeKind::Class { templated: true })
                    .context("remember btype in demangle_template")?;
            }
        }

        log::debug!("demangle template: done");

        Ok(ConsumeVal {
            value: bindex,
            mangled,
        })
    }

    #[must_use]
    fn do_type<'a>(
        &mut self,
        mut mangled: &'a [u8],
        result: &'_ mut Vec<u8>,
        is_tmpl: bool,
    ) -> Result<ConsumeVal<'a, CxxType>> {
        let mut done = false;
        let mut decl: Vec<u8> = vec![];
        let mut type_quals;
        let mut cxxtype_stack = vec![];

        result.clear();
        log::debug!("do type: start");

        let mut last_fn_idx: Option<usize> = None;
        while !done {
            debug_log_bytes(mangled, "do type: mangled");
            match mangled[0] {
                // pointer types
                b'p' | b'P' => {
                    log::debug!("do type: pointer");
                    mangled = &mangled[1..];
                    if !self.opts.java() {
                        decl.prepend(b"*");
                    }
                    cxxtype_stack.push(IncompleteCxxType::Pointer);
                }
                b'R' => {
                    // reference types
                    log::debug!("do type: reference");
                    mangled = &mangled[1..];
                    decl.prepend(b"&");
                    cxxtype_stack.push(IncompleteCxxType::Reference);
                }
                b'A' => {
                    // array types
                    log::debug!("do type: array");
                    mangled = &mangled[1..];
                    if !decl.is_empty() && (decl[0] == b'*' || decl[0] == b'&') {
                        decl.prepend(b"(");
                        decl.push(b')');
                    }
                    decl.push(b'[');
                    anyhow::bail!("TODO: finish implementing array type");
                }
                b'T' => {
                    log::debug!("do type: backref");
                    anyhow::bail!("TODO: finish implementing backref type");
                }
                b'F' => {
                    log::debug!("do type: function");

                    mangled = &mangled[1..];
                    if !decl.is_empty() && [b'*', b'&'].contains(&decl[0]) {
                        decl.prepend(b"(");
                        decl.extend(b")");
                    }

                    let fn_state;
                    ConsumeVal {
                        mangled,
                        value: fn_state,
                    } = self.demangle_nested_args(mangled, &mut decl)?;
                    cxxtype_stack.insert(0, IncompleteCxxType::Function { fn_state });

                    debug_log_bytes(mangled, "mangled post demangle nested args");

                    if !mangled.is_empty() && mangled[0] != b'_' {
                        anyhow::bail!("malformed function type");
                    }

                    if !mangled.is_empty() && mangled[0] == b'_' {
                        mangled = &mangled[1..];
                    }
                }
                b'O' => {
                    log::debug!("do type: rvalue reference");
                    anyhow::bail!("TODO: finish implementing rvalue type");
                }
                b'M' => {
                    log::debug!("do type: member");
                    type_quals = TypeQualifiers::new();
                    let member = !mangled.is_empty() && mangled[0] == b'M';
                    mangled = &mangled[1..];
                    decl.push(b')');
                    decl.prepend(self.scope_str());
                    match mangled.first() {
                        Some(c) if c.is_ascii_digit() => {
                            let n;
                            ConsumeVal { mangled, value: n } = consume_count(mangled)?;
                            if mangled.len() < n {
                                anyhow::bail!(
                                    "malformed symbol: expected {n} bytes, found {}",
                                    mangled.len()
                                );
                            }
                            decl.prepend(&mangled[..n]);
                            mangled = &mangled[n..];
                        }
                        Some(b'X') | Some(b'Y') => {
                            let mut temp = vec![];
                            ConsumeVal { mangled, .. } =
                                self.do_type(mangled, &mut temp, is_tmpl)?;
                            decl.prepend(&temp);
                        }
                        Some(b't') => {
                            let mut temp = vec![];
                            ConsumeVal { mangled, .. } =
                                self.demangle_template(mangled, &mut temp, None, true, true)?;
                            decl.prepend(&temp);
                            temp.clear();
                        }
                        Some(&c) => {
                            let chr = char::from_u32(c as u32)
                                .map(|chr| chr.to_string())
                                .unwrap_or_else(|| format!("{c:x}"));
                            anyhow::bail!("unknown member type {chr}");
                        }
                        None => anyhow::bail!("unexpected end of symbol"),
                    }

                    self.symbol_kind = StateSymbolKind::Function;
                    debug_log_bytes(&decl, "do_type decl post StateSymbolKind::Function");

                    decl.prepend(b"(");
                    if member {
                        match mangled.first() {
                            Some(c @ b'C') | Some(c @ b'V') | Some(c @ b'u') => {
                                type_quals = TypeQualifiers::from_bits(
                                    type_quals.into_bits()
                                        | TypeQualifiers::from_code(*c).into_bits(),
                                );
                                mangled = &mangled[1..];
                            }
                            Some(b'F') => {}
                            _ => anyhow::bail!("expected F or C/V/u qualifier"),
                        }

                        mangled = &mangled[1..];
                    }

                    if member || (!mangled.is_empty() && mangled[0] != b'_') {
                        let fn_state;
                        let fn_idx = cxxtype_stack.len();
                        ConsumeVal {
                            mangled,
                            value: fn_state,
                        } = self.demangle_nested_args(mangled, &mut decl)?;
                        cxxtype_stack.push(IncompleteCxxType::Function { fn_state });
                        last_fn_idx = Some(fn_idx);
                    }

                    debug_log_bytes(mangled, "mangled after demangle_nested_args");

                    if member && mangled.first() != Some(&b'_') {
                        anyhow::bail!("expected function return type");
                    }

                    mangled = &mangled[1..];

                    if self.opts.ansi() && type_quals.into_bits() != 0 {
                        append_blank(&mut decl);
                        decl.extend(type_quals.to_str().as_bytes());
                    }
                }
                b'G' => {
                    log::debug!("do type: ?");
                    mangled = &mangled[1..];
                }
                b'C' | b'V' | b'u' => {
                    log::debug!("do type: fundamental type qualifier");
                    if self.opts.ansi() {
                        if !decl.is_empty() {
                            decl.prepend(b" ");
                        }

                        decl.prepend(demangle_qualifier(mangled[0]));
                        self.type_quals = TypeQualifiers::from_bits(
                            self.type_quals.into_bits()
                                | TypeQualifiers::from_code(mangled[0]).into_bits(),
                        );
                    }
                    mangled = &mangled[1..];
                }
                _ => {
                    done = true;
                }
            }
        }

        if self.type_quals.into_bits() != 0 {
            if self.type_quals.r#const() && !is_tmpl {
                cxxtype_stack.insert(0, IncompleteCxxType::ConstModifier);
            }
            if self.type_quals.restrict() {
                cxxtype_stack.insert(0, IncompleteCxxType::RestrictModifier);
            }
            if self.type_quals.volatile() {
                cxxtype_stack.insert(0, IncompleteCxxType::VolatileModifier);
            }
        }
        self.type_quals.0 = 0;

        let inner_tys = match mangled[0] {
            b'Q' | b'K' => {
                log::debug!("do type: qualified type");
                let qual_name;
                ConsumeVal {
                    mangled,
                    value: qual_name,
                } = self.demangle_qualified(mangled, result, false, true)?;

                let btype_idx = self.btypes.register();
                self.btypes
                    .remember(
                        btype_idx,
                        qual_name.as_ref(),
                        BTypeKind::Class { templated: true },
                    )
                    .context("failed to remember qualified type as btype")?;
                vec![IncompleteCxxType::BType { index: btype_idx }]
            }
            b'B' => {
                log::debug!("do type: backref");
                let n;
                ConsumeVal { value: n, mangled } = get_count(&mangled[1..])?;

                if let Some(btype) = self.btypes.get(n) {
                    result.extend(&btype.name);
                    vec![IncompleteCxxType::BType { index: n }]
                } else {
                    log::error!("symbol has backref to uncaptured btype {n}");
                    anyhow::bail!("symbol has backref to uncaptured btype {n}");
                }
            }
            b'X' | b'Y' => {
                log::debug!("do type: template param");
                mangled = &mangled[1..];
                let idx;
                ConsumeVal {
                    value: idx,
                    mangled,
                } = consume_count_with_underscores(mangled)?;

                if idx >= self.tmpl_argvec.len() {
                    anyhow::bail!("unknown template param backref {idx}");
                }

                ConsumeVal { mangled, .. } = consume_count_with_underscores(mangled)?;

                let tmpl_name = if !self.tmpl_argvec.is_empty() {
                    Cow::Borrowed(&*self.tmpl_argvec[idx])
                } else {
                    let buf = format!("T{idx}").into_bytes();
                    buf.into()
                };
                result.extend(tmpl_name.iter());

                // TODO: should we really abuse btypes for this?
                let btype_idx = self.btypes.register();
                self.btypes
                    .remember(
                        btype_idx,
                        tmpl_name.as_ref(),
                        BTypeKind::Class { templated: true },
                    )
                    .context("failed to remember tmpl param as btype")?;
                vec![IncompleteCxxType::BType { index: btype_idx }]
            }
            _ => {
                let value;
                log::debug!("do type: fallthrough (assumed fundamental type)");
                ConsumeVal { value, mangled } = self.demangle_fund_type(mangled, result)?;
                value
            }
        };

        if let Some(idx) = last_fn_idx {
            match &mut cxxtype_stack[idx] {
                IncompleteCxxType::Function { fn_state } => {
                    let cxxtype = inner_tys.try_into()?;
                    fn_state.return_type = Some(cxxtype);
                }
                cxxtype => anyhow::bail!(
                    "do_type: expected last_fn_idx({idx}) to be function, but was {cxxtype:?}"
                ),
            }
        } else {
            cxxtype_stack.extend(inner_tys);
        }

        if !decl.is_empty() {
            result.push(b' ');
            result.extend(&decl);
        }

        if cxxtype_stack.is_empty() {
            log::debug!("do type: no type specified, assuming integral");
            // If unknown, assume integral
            cxxtype_stack.push(IncompleteCxxType::Int { signed: true });
        }

        log::debug!("do type: end");
        log::debug!("do type: good end");

        Ok(ConsumeVal {
            value: cxxtype_stack
                .try_into()
                .context("failed to assemble final type from IncompleteCxxType stack in do_type")?,
            mangled,
        })
    }

    #[must_use]
    fn demangle_fund_type<'a>(
        &mut self,
        mut mangled: &'a [u8],
        result: &'_ mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, Vec<IncompleteCxxType>>> {
        let mut cxxtype_stack = vec![];

        // Collect any applicable type qualifiers
        // TODO: refactor to collect qualifier info programmatically
        log::debug!("demangle fund type: start");
        loop {
            match mangled[0] {
                b'C' | b'V' | b'u' => {
                    log::debug!("demangle fund type: ansi qualifiers");
                    if self.opts.ansi() {
                        if !result.is_empty() {
                            result.prepend(b" ");
                        }
                        let qualifier = demangle_qualifier(mangled[0]);
                        result.prepend(qualifier);
                        let cty = match qualifier {
                            b"const" => IncompleteCxxType::ConstModifier,
                            b"volatile" => IncompleteCxxType::VolatileModifier,
                            b"__restrict" => IncompleteCxxType::RestrictModifier,
                            b"" => panic!("got no qualifier when one was expected"),
                            ty => unreachable!("unexpected qualifier string {ty:?}"),
                        };
                        cxxtype_stack.push(cty);
                    }
                }
                b'U' => {
                    log::debug!("demangle fund type: unsigned qualifier");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"unsigned");
                    cxxtype_stack.push(IncompleteCxxType::UnsignedModifier);
                }
                b'S' => {
                    log::debug!("demangle fund type: signed qualifier");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"signed");
                    cxxtype_stack.push(IncompleteCxxType::SignedModifier);
                }
                b'J' => {
                    log::debug!("demangle fund type: complex qualifier");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"__complex");
                    anyhow::bail!("TODO: add __complex modifier to IncompleteCxxType");
                }
                _ => break,
            }
        }

        // Actually demangle underlying type
        // TODO: refactor to collect type info programmatically
        log::debug!("demangle fund type: type");
        if mangled != b"" {
            match mangled[0] {
                b'_' => {}
                b'v' => {
                    log::debug!("demangle fund type: void");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"void");
                    cxxtype_stack.push(IncompleteCxxType::Void);
                }
                b'x' => {
                    log::debug!("demangle fund type: long long");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"long long");
                    cxxtype_stack.push(IncompleteCxxType::LongLong { signed: true });
                }
                b'l' => {
                    log::debug!("demangle fund type: long");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"long");
                    cxxtype_stack.push(IncompleteCxxType::Long { signed: true });
                }
                b'i' => {
                    log::debug!("demangle fund type: int");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"int");
                    cxxtype_stack.push(IncompleteCxxType::Int { signed: true });
                }
                b's' => {
                    log::debug!("demangle fund type: short");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"short");
                    cxxtype_stack.push(IncompleteCxxType::Short { signed: true });
                }
                b'b' => {
                    log::debug!("demangle fund type: bool");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"bool");
                    cxxtype_stack.push(IncompleteCxxType::Boolean);
                }
                b'c' => {
                    log::debug!("demangle fund type: char");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"char");
                    cxxtype_stack.push(IncompleteCxxType::Char { signed: None });
                }
                b'w' => {
                    log::debug!("demangle fund type: wchar_t");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"wchar_t");
                    cxxtype_stack.push(IncompleteCxxType::WideChar { signed: None });
                }
                b'r' => {
                    log::debug!("demangle fund type: long double");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"long double");
                    // ty_kind = TypeKind::Real;

                    cxxtype_stack.push(IncompleteCxxType::LongDouble);
                }
                b'd' => {
                    log::debug!("demangle fund type: double");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"double");
                    cxxtype_stack.push(IncompleteCxxType::Double);
                }
                b'f' => {
                    log::debug!("demangle fund type: float");
                    mangled = &mangled[1..];
                    append_blank(result);
                    result.extend(b"float");
                    cxxtype_stack.push(IncompleteCxxType::Float);
                }
                b'G' | b'I' => {
                    log::debug!("demangle fund type: stdint");
                    if mangled[0] == b'G' {
                        mangled = &mangled[1..];
                        if mangled.is_empty() || !mangled[0].is_ascii_digit() {
                            anyhow::bail!("missing count after G/I fundamental type");
                        }
                    }

                    mangled = &mangled[1..];
                    if mangled.is_empty() {
                        anyhow::bail!("missing symbol text for G/I fundamental type");
                    }
                    let buf = if mangled[0] == b'_' {
                        mangled = &mangled[1..];
                        let n = mangled.iter().take(9).take_while(|&&c| c != b'_').count();
                        let buf;
                        (buf, mangled) = mangled.split_at(n);
                        if mangled.is_empty() || mangled[0] != b'_' {
                            anyhow::bail!("missing trailing underscore");
                        }
                        buf
                    } else {
                        let buf;
                        (buf, mangled) = mangled.split_at(2);
                        buf
                    };
                    let buf_s =
                        std::str::from_utf8(buf).context("failed to parse hex count as utf8")?;
                    let dec = usize::from_str_radix(buf_s, 16).context("can't parse as hex")?;
                    if !(8..=64).contains(&dec) {
                        anyhow::bail!("count should have been 8-64, got: {dec}");
                    }
                    append_blank(result);
                    result.extend(format!("int{dec}_t").into_bytes());

                    cxxtype_stack.push(IncompleteCxxType::StdInt {
                        bitwidth: dec,
                        signed: true,
                    });
                }
                c if c.is_ascii_digit() => {
                    log::debug!("demangle fund type: explicit");
                    let bindex = self.btypes.register();
                    let mut btype = vec![];
                    ConsumeVal { mangled, .. } = self.demangle_class_name(mangled, &mut btype)?;
                    debug_log_bytes(mangled, "post-class mangled");
                    append_blank(result);
                    result.extend(&btype);
                    self.btypes
                        .remember(bindex, &btype, BTypeKind::Class { templated: false })
                        .context("failed to remember btype")?;

                    cxxtype_stack.push(IncompleteCxxType::BType { index: bindex });
                }
                b't' => {
                    log::debug!("demangle fund type: template");
                    let mut btype = vec![];
                    let bindex;
                    ConsumeVal {
                        mangled,
                        value: bindex,
                    } = self.demangle_template(mangled, &mut btype, None, true, true)?;
                    debug_log_bytes(&btype, "btype in demangle_fund_type template");
                    result.extend(&btype);

                    let bindex = bindex
                        .context("no btype index for template name when one was requested")?;

                    cxxtype_stack.push(IncompleteCxxType::BType { index: bindex });
                }
                c => {
                    let chr = char::from_u32(c as u32)
                        .map(|chr| chr.to_string())
                        .unwrap_or_else(|| format!("{c:x}"));
                    anyhow::bail!("unknown fundamental type tag {chr}");
                }
            }
        }

        log::debug!("demangle fund type: done");
        Ok(ConsumeVal {
            value: cxxtype_stack,
            mangled,
        })
    }

    #[must_use]
    fn demangle_class_name<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("demangle class name: start");

        let n;
        ConsumeVal { value: n, mangled } = consume_count(mangled)?;

        debug_log_bytes(mangled, "demangle class name: mangled");

        if mangled.len() >= n {
            ConsumeVal { mangled, .. } = self.demangle_arm_hp_template(mangled, n, declp)?;
            log::debug!("demangle class name: end (success=1)");
            Ok(ConsumeVal { value: (), mangled })
        } else {
            log::debug!("demangle class name: end (success=0)");
            anyhow::bail!("malformed class type slug");
        }
    }

    #[must_use]
    fn demangle_arm_hp_template<'a>(
        &mut self,
        mut mangled: &'a [u8],
        n: usize,
        declp: &'_ mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        let mut p = vec![];
        let mut args = vec![];
        log::debug!("demangle arm/hp template: start");

        if self.opts.style().hp() && mangled[n] == b'X' {
            log::debug!("demangle arm/hp template: hp acc");
            anyhow::bail!("TODO: implement hp cfront demangling");
        } else if self.arm_pt(mangled, n, &mut p, &mut args).is_ok() {
            log::debug!("demangle arm/hp template: arm/cfront");
            anyhow::bail!("TODO: implement arm_pt demangling");
        } else if n > 10
            && mangled.starts_with(b"_GLOBAL_")
            && mangled[9] == b'N'
            && mangled[8] == mangled[10]
            && CPLUS_MARKERS.contains(&mangled[8])
        {
            log::debug!("demangle arm/hp template: anonymous");

            declp.extend(b"{anonymous}");
        } else {
            log::debug!("demangle arm/hp template: fallthrough");
            // check that this is a non-recursive call
            if self.temp_start == -1 {
                // disable in recursive calls
                self.temp_start = 0;
            }
            declp.extend(&mangled[..n]);
        }

        log::debug!("demangle arm/hp template: done");

        mangled = &mangled[n..];
        Ok(ConsumeVal { value: (), mangled })
    }

    #[must_use]
    fn arm_pt<'a>(
        &'_ mut self,
        mut mangled: &'a [u8],
        n: usize,
        _anchor: &'_ mut Vec<u8>,
        args: &'_ mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        let style = self.opts.style();

        log::debug!("arm pt: start");

        if style.arm() || style.hp() {
            log::debug!("arm pt: arm/hp style");
            if let Some(anchor_pos) = memmem::find(mangled, b"__pt__") {
                let _anchor = &mangled[anchor_pos + 6..];
                let len;
                ConsumeVal {
                    value: len,
                    mangled,
                } = consume_count(mangled)?;
                if args[len..] == mangled[n..] && args[0] == b'_' {
                    args.splice(0..1, b"".iter().cloned());
                    log::debug!("arm pt: done (success=1)");
                    return Ok(ConsumeVal { value: (), mangled });
                }
            }
        }
        if style.auto() || style.edg() {
            anyhow::bail!("TODO: arm_pt: implement edg");
        }

        log::debug!("arm pt: done (success=0)");
        anyhow::bail!("arm_pt: unhandled case")
    }

    #[must_use]
    fn demangle_function_name<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
        scan: &'_ [u8],
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("demangle function name: start");

        let style = self.opts.style();
        let scan_idx = memmem::find(mangled, scan).context("scan not found in mangled")?;
        declp.extend(&mangled[..scan_idx]);

        // Consume the function name, including the "__" separating the name
        // from the signature.  We are guaranteed that SCAN points to the
        // separator.
        // RUST NOTE: using scan_idx here to maintain provenance from original mangled
        mangled = &mangled[(scan_idx + 2)..];

        // We may be looking at an instantiation of a template function:
        // foo__Xt1t2_Ft3t4, where t1, t2, ... are template arguments and a
        // following _F marks the start of the function arguments.  Handle
        // the template arguments first
        if style.hp() && mangled[0] == b'X' {
            log::debug!("demangle function name: hp style template");
            ConsumeVal { mangled, .. } = self.demangle_arm_hp_template(mangled, 0, declp)?;
            // mangled now refers to the 'F' marking the func args
        }

        if style.lucid() || style.arm() || style.hp() || style.edg() {
            // See if we have an ARM style constructor or destructor operator.
            // If so, then just record it, clear the decl, and return.
            // We can't build the actual constructor/destructor decl until later,
            // when we recover the class name from the signature.
            if *declp == b"__ct"[..] {
                self.constructor += 1;
                declp.clear();
                return Ok(ConsumeVal { mangled, value: () });
            } else if *declp == b"__dt"[..] {
                self.destructor += 1;
                declp.clear();
                return Ok(ConsumeVal { mangled, value: () });
            }
        }

        if declp.len() >= 3 && declp[0..2] == b"op"[..] && CPLUS_MARKERS.contains(&declp[2]) {
            // see if it's an assignment expression
            if declp.len() >= 10 && declp[3..10] == b"assign_"[..] {
                log::debug!("demangle function name: assignment operator");
                anyhow::bail!("TODO: implement operator= demangle");
            } else {
                log::debug!("demangle function name: other operator");
                anyhow::bail!("TODO: implement operator demangle");
            }
        } else if declp.len() >= 5 && declp[..4] == b"type"[..] && CPLUS_MARKERS.contains(&declp[4])
        {
            // type conversion operator
            log::debug!("demangle function name: type conversion operator");
            anyhow::bail!("TODO: implement type conversion operator demangle");
        } else if declp.len() >= 4 && declp[0..4] == b"__op"[..] {
            // ansi type conversion operator
            log::debug!("demangle function name: ansi type conversion operator");
            let tem = &declp[4..];
            let mut typ = Vec::new();
            ConsumeVal { .. } = self.do_type(tem, &mut typ, false)?;

            declp.clear();
            declp.extend_from_slice(b"operator ");
            declp.extend(typ);
        } else if declp.len() >= 4
            && declp[0..2] == b"__"[..]
            && declp[2].is_ascii_lowercase()
            && declp[3].is_ascii_lowercase()
        {
            log::debug!("demangle function name: operators");
            if declp.len() == 4 {
                // operator
                log::debug!("demangle function name: alt operator");

                let operator = OperatorKind::from_symbol_op(&declp[2..], self.opts)?;
                declp.clear();
                declp.extend(b"operator");
                declp.extend(operator.overload_name());
            } else if declp[2] == b'a' && declp.len() == 6 {
                // assignment
                log::debug!("demangle function name: alt assignment");
                anyhow::bail!("TODO: implement alt assignment demangle");
            }
        }

        log::debug!("demangle function name: end");

        Ok(ConsumeVal { mangled, value: () })
    }

    #[must_use]
    fn demangle_signature<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("demangle signature: start");

        let style = self.opts.style();
        let success = true;
        let mut expect_func = false;
        let mut expect_return_type = false;
        let mut func_done = false;
        let mut oldmangled = None;

        while success && !mangled.is_empty() {
            match mangled[0] {
                b'Q' => {
                    log::debug!("demangle signature: qualified");
                    oldmangled = Some(mangled);

                    ConsumeVal { mangled, .. } =
                        self.demangle_qualified(mangled, declp, true, false)?;
                    // self.types.push(value);
                    if style.auto() || style.gnu() {
                        expect_func = true;
                    }
                }
                b'K' => {
                    log::debug!("demangle signature: param K");
                    anyhow::bail!("TODO: implement demangle K");
                }
                b'S' => {
                    log::debug!("demangle signature: param S");
                    anyhow::bail!("TODO: implement demangle S");
                }
                b'C' | b'V' | b'u' => {
                    log::debug!("demangle signature: ansi qualifiers");
                    self.fn_state.type_quals = TypeQualifiers::from_bits(
                        self.fn_state.type_quals.into_bits()
                            | TypeQualifiers::from_code(mangled[0]).into_bits(),
                    );
                    log::debug!(
                        "demangle signature: new type quals = {:?}",
                        self.fn_state.type_quals
                    );

                    // A qualified member function
                    if oldmangled.is_none() {
                        oldmangled = Some(mangled);
                    }
                    mangled = &mangled[1..];
                }
                b'L' => {
                    log::debug!("demangle signature: local class name");
                    anyhow::bail!("TODO: implement demangle local class name");
                }
                c if c.is_ascii_digit() => {
                    log::debug!("demangle signature: param class name");
                    {
                        let oldmangled = if let Some(bs) = oldmangled {
                            bs
                        } else {
                            mangled
                        };
                        self.temp_start = -1; // Top of demangle_class
                        ConsumeVal { mangled, .. } = self.demangle_class(mangled, declp)?;
                        self.remember_type(oldmangled);

                        if (style.auto() || style.gnu() || style.edg())
                            && mangled.first() != Some(&b'F')
                        {
                            expect_func = true;
                        }
                    }
                    oldmangled = None;
                }
                b'B' => {
                    log::debug!("demangle signature: param B");
                    anyhow::bail!("TODO: implement demangle B");
                }
                b'F' => {
                    log::debug!("demangle signature: param function");
                    oldmangled = None;
                    func_done = true;
                    mangled = &mangled[1..];

                    if style.lucid() || style.arm() || style.hp() || style.edg() {
                        anyhow::bail!("TODO: implement forget_types");
                    }

                    ConsumeVal { mangled, .. } = self.demangle_args(mangled, declp)?;

                    if (style.auto() || style.edg()) && !mangled.is_empty() && mangled[0] == b'_' {
                        mangled = &mangled[1..];
                        // At this level, we don't care about the return type.
                        let mut tname = Vec::new();
                        ConsumeVal { mangled, .. } = self.do_type(mangled, &mut tname, false)?;
                        drop(tname);
                    }
                }
                b't' => {
                    log::debug!("demangle signature: param t");
                    let mut trawname: Vec<u8> = vec![];
                    let mut tname: Vec<u8> = vec![];
                    let oldmangled2 = if let Some(bs) = oldmangled {
                        bs
                    } else {
                        mangled
                    };

                    ConsumeVal { mangled, .. } = self.demangle_template(
                        mangled,
                        &mut tname,
                        Some(&mut trawname),
                        true,
                        true,
                    )?;

                    self.remember_type(&oldmangled2);

                    tname.extend(self.scope_str());
                    declp.prepend(&tname);

                    if (self.destructor & 1) > 0 {
                        trawname.prepend(b"~");
                        declp.extend(&trawname);
                        self.destructor -= 1;
                    }
                    // TODO: is this logic originally from the C demangler actually correct?
                    // it _feels_ incorrect
                    if (self.constructor & 1) > 0 || (self.destructor & 1) > 0 {
                        declp.extend(&trawname);
                        self.constructor -= 1;
                    }

                    oldmangled = None;
                    expect_func = true;
                }
                b'_' => {
                    log::debug!("demangle signature: param _");

                    if style.gnu() && expect_return_type {
                        log::debug!("demangle signature: gnu");
                        let mut return_type: Vec<u8> = vec![];
                        mangled = &mangled[1..];
                        ConsumeVal { mangled, .. } =
                            self.do_type(mangled, &mut return_type, false)?;
                        append_blank(&mut return_type);

                        declp.prepend(&return_type);
                    } else {
                        // At the outermost level, we cannot have a return type specified,
                        // so if we run into another '_' at this point we are dealing with
                        // a mangled name that is either bogus, or has been mangled by
                        // some algorithm we don't know how to deal with.  So just
                        // reject the entire demangling.
                        // However, "_nnn" is an expected suffix for alternate entry point
                        // numbered nnn for a function, with HP aCC, so skip over that
                        // without reporting failure. pai/1997-09-04
                        if style.hp() {
                            mangled = &mangled[1..];
                            while !mangled.is_empty() && mangled[0].is_ascii_digit() {
                                mangled = &mangled[1..];
                            }
                        } else {
                            log::error!("demangle_signature: param _: unknown case");
                            anyhow::bail!("param _: unknown case");
                        }
                    }
                }
                b'H' => {
                    log::debug!("demangle signature: param H");
                    if style.gnu() {
                        ConsumeVal { mangled, .. } =
                            self.demangle_template(mangled, declp, None, false, false)?;
                        if (self.constructor & 1) == 0 {
                            expect_return_type = true;
                        }
                        mangled = &mangled[1..];
                    }
                }
                _ => {
                    log::debug!("demangle signature: outermost function");
                    self.symbol_kind = StateSymbolKind::Function;
                    debug_log_bytes(declp, "demangle_signature declp pre-outermost");
                    if style.auto() || style.gnu() {
                        func_done = true;
                        ConsumeVal { mangled, .. } = self.demangle_args(mangled, declp)?;
                    } else {
                        // Non-GNU manglers use a specific token to mark the start
                        // of the outermost function argument tokens.  Typically 'F',
                        // for ARM/HP-demangling, for example.  So if we find something
                        // we are not prepared for, it must be an error.
                        anyhow::bail!("malformed function signature");
                    }
                }
            }

            if success && expect_func {
                func_done = true;
                self.decl_fn_qname_len = declp.len();
                if style.lucid() || style.arm() || style.edg() {
                    self.raw_types.clear();
                }
                ConsumeVal { mangled, .. } = self.demangle_args(mangled, declp)?;
                // Since template include the mangling of their return types,
                // we must set expect_func to 0 so that we don't try do
                // demangle more arguments the next time we get here.
                expect_func = false;
            }
        }

        // self.fn_state.type_quals = self.type_quals;

        if success && !func_done && (style.auto() || style.gnu()) {
            ConsumeVal { mangled, .. } = self.demangle_args(mangled, declp)?;
        }

        if success && self.opts.params() {
            if self.static_type {
                declp.extend(b" static");
            }
            if self.fn_state.type_quals.into_bits() != 0 {
                append_blank(declp);
                declp.extend(self.fn_state.type_quals.to_str().as_bytes())
            }
        }

        log::debug!("demangle signature: end (success=1)");

        Ok(ConsumeVal { mangled, value: () })
    }

    #[must_use]
    fn demangle_args<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("demangle args: start");
        let style = self.opts.style();
        let mut arg: Vec<u8> = vec![];
        let mut need_comma = false;
        let mut t;
        let mut r;
        let mut temptype: u8;

        if self.opts.params() {
            debug_log_bytes(mangled, "demangle args: remaining args mangled");
            declp.push(b'(');
            if mangled.is_empty() {
                declp.extend(b"void");
            }
        }

        while !mangled.is_empty() {
            let b = mangled[0];
            if (b == b'_' || b == b'e') && self.nrepeats <= 0 {
                break;
            }

            if b == b'N' || b == b'T' {
                log::debug!("demangle args: type parameter");
                temptype = *mangled
                    .first()
                    .context("missing character following arg prefix")?;
                mangled = &mangled[1..];

                if temptype == b'N' {
                    log::debug!("demangle args: N repeat");
                    ConsumeVal { mangled, value: r } = get_count(mangled).inspect_err(|_e| {
                        log::debug!("demangle args: fail (couldn't consume count - initial)");
                    })?;
                } else {
                    r = 1;
                }

                if style.hp() || style.arm() || style.edg() && self.raw_types.len() >= 10 {
                    // If we have 10 or more types we might have more than a 1 digit
                    // index so we'll have to consume the whole count here. This
                    // will lose if the next thing is a type name preceded by a
                    // count but it's impossible to demangle that case properly
                    // anyway. Eg if we already have 12 types is T12Pc "(..., type1,
                    // Pc, ...)"  or "(..., type12, char *, ...)"
                    ConsumeVal { mangled, value: t } =
                        consume_count(mangled).inspect_err(|_e| {
                            log::debug!(
                                "demangle args: fail (couldn't consume count - hp/arm/edg)"
                            );
                        })?;
                } else {
                    ConsumeVal { mangled, value: t } = get_count(mangled).inspect_err(|_e| {
                        log::debug!("demangle args: fail (couldn't consume count)");
                    })?;
                }
                if style.lucid() || style.arm() || style.hp() || style.edg() {
                    t -= 1;
                }
                // Validate the type index. Protect against illegal indices from
                // malformed type strings.
                if t >= self.raw_types.len() {
                    log::error!("demangle args: fail (illegal type index)");
                    anyhow::bail!("illegal type index {t} in type string");
                }
                while self.nrepeats > 0 || r > 0 {
                    r -= 1;
                    if need_comma && self.opts.params() {
                        declp.extend(b", ");
                    }

                    // Rust won't let us borrow a subfield while a mutable borrow occurs
                    // and we need `do_arg` to be generic about the source of the bytes
                    log::debug!("demangle args: demangle backref {t}");
                    for (i, ty) in self.raw_types.iter().enumerate() {
                        debug_log_bytes(&*ty, &format!("demangle args: typevec ent {i}"));
                    }
                    let tem = &*self.raw_types[t].to_owned();
                    let _ = self.do_arg(tem, &mut arg)?;

                    if self.opts.params() {
                        declp.extend(&arg);
                    }
                    arg.clear();
                    need_comma = true;
                }
            } else {
                log::debug!("demangle args: non-parameterised type");
                if need_comma && self.opts.params() {
                    declp.extend(b", ");
                }

                debug_log_bytes(mangled, "demangle args: mangled non-parameterised type");

                ConsumeVal { mangled, .. } = self
                    .do_arg(mangled, &mut arg)
                    .inspect_err(|_e| log::debug!("demangle args: fail (do_arg)"))?;

                if self.opts.params() {
                    declp.extend(&arg);
                }
                arg.clear();
                need_comma = true;
            }
        }

        // variable args
        if let Some(b'e') = mangled.first() {
            log::debug!("demangle args: varargs");
            mangled = &mangled[1..];

            if self.opts.params() {
                if need_comma {
                    declp.extend(b", ");
                }
                declp.extend(b"...");
                self.fn_state.has_varargs = true;
            }
        }

        if self.opts.params() {
            declp.push(b')');
        }

        debug_log_bytes(mangled, "mangled post demangle_args");
        log::debug!("demangle args: end (success)");

        Ok(ConsumeVal { mangled, value: () })
    }

    #[must_use]
    fn demangle_class<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &'_ mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        let mut class_name = vec![];
        ConsumeVal { mangled, .. } = self.demangle_class_name(mangled, &mut class_name)?;
        let bindex = self.btypes.register();
        let mut class_name_sliced = &class_name[..];
        if ((self.constructor & 1) == 1) || ((self.destructor & 1) == 1) {
            // Adjust so we don't include template args
            if self.temp_start > 0 {
                class_name_sliced = &class_name_sliced[..self.temp_start as usize];
            }
            declp.prepend(class_name_sliced);
            if (self.destructor & 1) == 1 {
                declp.prepend(b"~");
                self.destructor -= 1;
            } else {
                self.constructor -= 1;
            }
        }

        self.ktypes.push(class_name.clone());
        self.btypes
            .remember(bindex, &class_name, BTypeKind::Class { templated: false })?;
        declp.prepend(self.scope_str());
        declp.prepend(&class_name);

        Ok(ConsumeVal { mangled, value: () })
    }

    fn scope_str(&self) -> &'static [u8] {
        match self.opts.java() {
            true => b".",
            false => b"::",
        }
    }

    #[must_use]
    fn do_arg<'a>(
        &mut self,
        mut mangled: &'a [u8],
        result: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("do arg: start");
        let start = mangled;

        if self.nrepeats > 0 {
            log::debug!("do arg: repeated type (count: {})", self.nrepeats);
            self.nrepeats -= 1;

            if !self.previous_argument.is_empty() {
                // We want to reissue the previous type in this argument list.
                result.extend(&self.previous_argument);
                self.fn_state.arg_types.push(
                    self.previous_argument_type
                        .clone()
                        .context("missing previous argument type for previous argument")?,
                );
                return Ok(ConsumeVal { mangled, value: () });
            } else {
                anyhow::bail!("no previous argument to repeat");
            }
        }

        if mangled[0] == b'n' {
            log::debug!("do arg: squangling repeat");
            // A squangling-style repeat.
            let value;
            ConsumeVal { mangled, value } = consume_count(&mangled[1..])?;
            self.nrepeats = value as i32;

            if self.nrepeats <= 0 {
                // not a repeat after all.
                log::warn!("do_arg: got malformed repeat arg count {value}");
                anyhow::bail!("got malformed repeat arg count {value}");
            }

            if self.nrepeats > 9 {
                if mangled[0] != b'_' {
                    // multi char repeats should be followed with '_'
                    log::warn!(
                        "do_arg: got malformed repeat arg count (missing '_' after multi-char repeat)"
                    );
                    anyhow::bail!(
                        "got malformed repeat arg count (missing '_' after multi-char repeat)"
                    );
                } else {
                    mangled = &mangled[1..];
                }
            }

            // implement first repeat by recursively calling self
            return self.do_arg(mangled, result);
        }

        // Save the result in self.previous_argument so that we can find it
        // if it's repeated.  Note that saving START is not good enough: we
        // do not want to add additional types to the back-referenceable
        // type vector when processing a repeated type.
        self.previous_argument.clear();
        self.previous_argument_type = None;

        let mut prev_arg = vec![];
        let cxxtype;
        ConsumeVal {
            mangled,
            value: cxxtype,
        } = self
            .do_type(mangled, &mut prev_arg, false)
            .inspect_err(|_| {
                log::debug!("do arg: bail due to do_type fail");
            })?;
        self.previous_argument.extend(&prev_arg);
        self.previous_argument_type = Some(cxxtype.clone());
        result.extend(&self.previous_argument);
        self.fn_state.arg_types.push(cxxtype);

        let idx = memmem::find(start, mangled).context("failed to find arg start string")?;
        self.remember_type(&start[..idx]);

        log::debug!("do arg: end (success)");

        Ok(ConsumeVal { mangled, value: () })
    }

    #[must_use]
    fn demangle_template_value_parm<'a>(
        &mut self,
        mut mangled: &'a [u8],
        s: &mut Vec<u8>,
        cxxtype: &CxxType,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("debug template value parm: start {cxxtype:?}");

        if !mangled.is_empty() && mangled[0] == b'Y' {
            log::debug!("debug template value parm: template parameter");
            anyhow::bail!("TODO: implement demangle_template_value_parm for template");
        } else if cxxtype.is_integral_type() {
            ConsumeVal { mangled, .. } = self.demangle_integral_value(mangled, s)?;
        } else if let CxxType::Char { .. } = cxxtype {
            anyhow::bail!("TODO: implement demangle_template_value_parm for char");
        } else if let CxxType::Boolean = cxxtype {
            let value;
            ConsumeVal { mangled, value } = consume_count(mangled)?;
            let bool_val = match value {
                0 => &b"false"[..],
                1 => &b"true"[..],
                i => anyhow::bail!("invalid boolean literal value {i}"),
            };
            s.extend(bool_val);
        } else if cxxtype.is_realnum_type() {
            anyhow::bail!("TODO: implement demangle_template_value_parm for floats");
        } else if cxxtype.is_reference_type() {
            if mangled[0] == b'Q' {
                ConsumeVal { mangled, .. } = self.demangle_qualified(mangled, s, false, true)?;
            } else {
                anyhow::bail!("TODO: implement demangle_template_value_parm for unqualified types");
            }
        }

        log::debug!("debug template value parm: done");

        Ok(ConsumeVal { mangled, value: () })
    }

    #[must_use]
    fn demangle_integral_value<'a>(
        &mut self,
        mut mangled: &'a [u8],
        s: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("demangle integral value: begin");

        if mangled.is_empty() {
            log::error!("demangle_integral_value: end of mangled string");
            anyhow::bail!("end of mangled string");
        }

        if mangled[0] == b'E' {
            log::debug!("demangle integral value: E");
            let mut need_operator = false;
            s.push(b'(');
            mangled = &mangled[1..];

            while !mangled.is_empty() && mangled[0] != b'W' {
                if need_operator {
                    anyhow::bail!("TODO: implement demangle_integral_value operator");
                } else {
                    need_operator = true;
                }

                ConsumeVal { mangled, .. } =
                    self.demangle_template_value_parm(mangled, s, &CxxType::Int { signed: true })?;
            }

            if mangled.is_empty() || mangled[0] != b'W' {
                anyhow::bail!("malformed integral value");
            } else {
                s.push(b')');
                mangled = &mangled[1..];
            }
        } else if b"QK".contains(&mangled[0]) {
            ConsumeVal { mangled, .. } = self.demangle_qualified(mangled, s, false, true)?;
        } else {
            let mut have_digit = false;

            if mangled[0] == b'm' {
                s.push(b'-');
            }

            while !mangled.is_empty() && mangled[0].is_ascii_digit() {
                s.push(mangled[0]);
                mangled = &mangled[1..];
                have_digit = true;
            }

            if !have_digit {
                anyhow::bail!("malformed integral value, no digits");
            }
        }

        Ok(ConsumeVal { mangled, value: () })
    }

    #[must_use]
    fn demangle_nested_args<'a>(
        &'_ mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, FunctionState>> {
        log::debug!("demangle nested args: start");
        // The G++ name-mangling algorithm does not remember types on nested
        // argument lists, unless -fsquangling is used, and in that case the
        // type vector updated by remember_type is not used.  So, we turn
        // off remembering of types here.
        self.forgetting_types += 1;

        let saved_previous_argument = self.previous_argument.clone();
        let saved_previous_argument_type = self.previous_argument_type.clone();
        let saved_nrepeats = self.nrepeats;
        let saved_fnstate = self.fn_state.clone();

        self.previous_argument = vec![];
        self.previous_argument_type = None;
        self.nrepeats = 0;
        self.fn_state = FunctionState::default();

        // Actually demangle the args
        ConsumeVal { mangled, .. } = self.demangle_args(mangled, declp).inspect_err(|_e| {
            log::debug!("demangle nested args: done (success=0)");
        })?;

        let inner_fnstate = self.fn_state.clone();
        self.fn_state = saved_fnstate;

        // Restore the previous_argument field.
        self.previous_argument = saved_previous_argument;
        self.previous_argument_type = saved_previous_argument_type;
        self.forgetting_types -= 1;
        self.nrepeats = saved_nrepeats;

        log::debug!("demangle nested args: done (success=1)");

        Ok(ConsumeVal {
            mangled,
            value: inner_fnstate,
        })
    }

    fn remember_type(&mut self, raw_type: &[u8]) {
        if self.forgetting_types > 0 {
            log::debug!(
                "remember type: skipping as forgetting_types count is {}",
                self.forgetting_types
            );
            return;
        }

        let idx = self.raw_types.len();
        self.raw_types.push(raw_type.into());
        debug_log_bytes(
            raw_type,
            &format!("remember_type: remembering as type {idx}"),
        );
    }
}

const CPLUS_MARKERS: &[u8] = &[b'$', b'.', 0u8];

fn append_blank(v: &mut Vec<u8>) {
    if !v.is_empty() {
        v.push(b' ');
    }
}

fn demangle_qualifier(qualifier: u8) -> &'static [u8] {
    match qualifier {
        b'C' => b"const",
        b'V' => b"volatile",
        b'u' => b"__restrict",
        _ => b"",
    }
}

#[must_use]
fn consume_count(mangled: &[u8]) -> Result<ConsumeVal<'_, usize>> {
    let digit_count = mangled.iter().take_while(|&b| b.is_ascii_digit()).count();

    let (digits, mangled) = mangled.split_at(digit_count);
    let count = std::str::from_utf8(digits)
        .context("failed to parse digits: invalid utf8")?
        .parse()
        .context("failed to parse digits")?;

    Ok(ConsumeVal {
        value: count,
        mangled,
    })
}

#[must_use]
fn consume_count_with_underscores(mangled: &[u8]) -> Result<ConsumeVal<'_, usize>> {
    if mangled.starts_with(b"_") && mangled.ends_with(b"_") && mangled.len() > 1 {
        let end = 0.max(mangled.len() - 1);

        consume_count(&mangled[1..end])
    } else {
        if mangled.is_empty() || mangled[0] < b'0' || mangled[0] > b'9' {
            anyhow::bail!("could not find surrounding underscores or count");
        }

        Ok(ConsumeVal {
            mangled: &mangled[1..],
            value: (mangled[0] - b'0') as usize,
        })
    }
}

#[must_use]
fn get_count(mangled: &[u8]) -> Result<ConsumeVal<'_, usize>> {
    let digit = mangled[0];

    let ConsumeVal {
        value: count,
        mangled: mangled_post_count,
    } = consume_count(mangled)?;
    if !mangled_post_count.is_empty() && mangled_post_count[0] == b'_' {
        // Treat count like consume_count if followed by _
        Ok(ConsumeVal {
            value: count,
            mangled: mangled_post_count,
        })
    } else {
        // Only count first digit otherwise
        Ok(ConsumeVal {
            value: (digit - b'0') as usize,
            mangled: &mangled[1..],
        })
    }
}

fn strpbrk<'a>(s: &'a [u8], accept: &[u8]) -> Option<&'a [u8]> {
    let position = s.iter().position(|c| accept.contains(c))?;
    Some(&s[position..])
}

const ARM_VTABLE_STRING: &[u8] = b"__vtbl__";

#[must_use]
fn arm_special<'a>(mut mangled: &'a [u8], declp: &mut Vec<u8>) -> Result<ConsumeVal<'a, ()>> {
    let mut n = 0;

    log::debug!("arm_special");

    if mangled.starts_with(ARM_VTABLE_STRING) {
        // Found a ARM style virtual table, get past ARM_VTABLE_STRING
        // and create the decl.  Note that we consume the entire mangled
        // input string, which means that demangle_signature has no work
        // to do.

        let mut scan = &mangled[ARM_VTABLE_STRING.len()..];

        // Check if it can be demangled
        while !scan.is_empty() {
            ConsumeVal {
                value: n,
                mangled: scan,
            } = consume_count(scan)?;
            scan = &scan[n..];
            if scan[0..2] == b"__"[..] {
                scan = &scan[2..];
            }
        }
        mangled = &mangled[ARM_VTABLE_STRING.len()..];
        while !mangled.is_empty() {
            ConsumeVal { value: n, mangled } = consume_count(scan)?;
            if n > mangled.len() {
                anyhow::bail!("encountered end of string while consuming mangled vtable");
            }
            declp.prepend(&mangled[..n]);
            if mangled[0..2] == b"__"[..] {
                declp.prepend(b"::");
                mangled = &mangled[2..];
            }
        }
        declp.extend(b" virtual table");
        return Ok(ConsumeVal { mangled, value: () });
    }

    anyhow::bail!("vtable symbol missing vtable sentinel");
}
