use bitfield_struct::bitfield;
use memx::memmem;

#[bitfield(u32)]
pub struct DemangleOpts {
    /// Demangle function arguments as well as symbol name.
    params: bool,

    /// Include ANSI language features such as const, volatile, etc.
    ansi: bool,

    /// Demangle as Java instead of as C++.
    java: bool,

    /// Reserved space for future options.
    #[bits(5)]
    __0: u8,

    /// Which demangling style(s) to apply.
    /// If none are set, defaults are loaded from (X)
    #[bits(8)]
    style: DemangleStyle,

    /// Padding/reserved space.
    #[bits(16)]
    __1: u16,
}

#[bitfield(u8)]
pub struct DemangleStyle {
    /// Automatically detect the mangling style used by the mangled symbols.
    auto: bool,

    /// GNU-style symbol mangling.
    gnu: bool,

    /// Lucid compiler symbol mangling.
    lucid: bool,

    /// arm-gcc symbol mangling.
    arm: bool,

    /// HP aCC compiler symbol mangling.
    hp: bool,

    /// EDG compiler symbol mangling.
    edg: bool,

    /// Padding
    #[bits(2)]
    __: u8,
}

/// Types that can be encoded in the signatures of mangled functions.
#[derive(Debug)]
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
    pub fn from_symbol_op(sym: &str, opts: DemangleOpts) -> Option<Self> {
        let is_ansi = opts.ansi();
        Some(match sym {
            "nw" if is_ansi => Self::New,
            "dl" if is_ansi => Self::Delete,
            "new" => Self::New,
            "delete" => Self::Delete,
            "vn" if is_ansi => Self::ArrayNew,
            "vd" if is_ansi => Self::ArrayDelete,
            "as" if is_ansi => Self::Assignment,
            "ne" if is_ansi => Self::NonEquality,
            "eq" if is_ansi => Self::Equality,
            "ge" if is_ansi => Self::GreaterEqual,
            "gt" if is_ansi => Self::GreaterThan,
            "le" if is_ansi => Self::LessEqual,
            "lt" if is_ansi => Self::LessThan,
            "plus" => Self::Addition,
            "pl" if is_ansi => Self::Addition,
            "apl" if is_ansi => Self::AssigningAddition,
            "minus" => Self::Subtraction,
            "mi" if is_ansi => Self::Subtraction,
            "ami" if is_ansi => Self::AssigningSubtraction,
            "mult" => Self::Multiplication,
            "ml" if is_ansi => Self::Multiplication,
            "amu" if is_ansi => Self::AssigningMultiplication,
            "aml" if is_ansi => Self::AssigningMultiplication,
            "convert" => Self::UnaryPlus,
            "negate" => Self::Negate,
            "trunc_mod" => Self::Modulus,
            "md" if is_ansi => Self::Modulus,
            "amd" if is_ansi => Self::AssigningModulus,
            "trunc_div" => Self::Division,
            "dv" if is_ansi => Self::Division,
            "adv" if is_ansi => Self::AssigningDivision,
            "truth_andif" => Self::LogicalAnd,
            "aa" if is_ansi => Self::LogicalAnd,
            "truth_orif" => Self::LogicalOr,
            "oo" if is_ansi => Self::LogicalOr,
            "truth_not" => Self::LogicalNot,
            "nt" if is_ansi => Self::LogicalAnd,
            "postincrement" => Self::Postincrement,
            "pp" if is_ansi => Self::Postincrement,
            "postdecrement" => Self::Postdecrement,
            "mm" if is_ansi => Self::Postdecrement,
            "bit_ior" => Self::BitwiseOr,
            "or" if is_ansi => Self::BitwiseOr,
            "aor" if is_ansi => Self::AssigningBitwiseOr,
            "bit_xor" => Self::BitwiseXor,
            "er" if is_ansi => Self::BitwiseXor,
            "aer" if is_ansi => Self::AssigningBitwiseXor,
            "bit_and" => Self::BitwiseAnd,
            "ad" if is_ansi => Self::BitwiseAnd,
            "aad" if is_ansi => Self::AssigningBitwiseAnd,
            "bit_not" => Self::BitwiseNot,
            "co" if is_ansi => Self::BitwiseNot,
            "call" => Self::FunctionCall,
            "cl" => Self::FunctionCall,
            "alshift" => Self::ArithmeticLeftShift,
            "ls" if is_ansi => Self::ArithmeticLeftShift,
            "als" if is_ansi => Self::AssigningArithmeticLeftShift,
            "arshift" => Self::ArithmeticRightShift,
            "rs" if is_ansi => Self::ArithmeticRightShift,
            "ars" if is_ansi => Self::AssigningArithmeticRightShift,
            "component" => Self::IndirectMemberLookup,
            "pt" if is_ansi => Self::IndirectMemberLookup,
            "rf" if is_ansi => Self::IndirectMemberLookup,
            "indirect" => Self::Dereference,
            "method_call" => Self::MethodCall,
            "addr" => Self::AddressOf,
            "array" => Self::ArrayIndex,
            "vc" if is_ansi => Self::ArrayIndex,
            "compound" => Self::Compound,
            "cm" if is_ansi => Self::Compound,
            "cond" => Self::Conditional,
            "cn" if is_ansi => Self::Conditional,
            "max" => Self::Maximum,
            "mx" if is_ansi => Self::Maximum,
            "min" => Self::Minimum,
            "mn" if is_ansi => Self::Minimum,
            "nop" => Self::Nop,
            "rm" => Self::DereferenceIndirectMemberLookup,
            "sz" => Self::Sizeof,
            _ => return None,
        })
    }

    pub fn overload_name(&self) -> &'static str {
        match *self {
            OperatorKind::New => " new",
            OperatorKind::Delete => " delete",
            OperatorKind::ArrayNew => " new []",
            OperatorKind::ArrayDelete => " delete []",
            OperatorKind::Assignment => "=",
            OperatorKind::NonEquality => "!",
            OperatorKind::Equality => "==",
            OperatorKind::GreaterEqual => ">=",
            OperatorKind::GreaterThan => ">",
            OperatorKind::LessEqual => "<=",
            OperatorKind::LessThan => "<",
            OperatorKind::Addition => "+",
            OperatorKind::AssigningAddition => "+=",
            OperatorKind::Subtraction => "-",
            OperatorKind::AssigningSubtraction => "-=",
            OperatorKind::Multiplication => "*",
            OperatorKind::AssigningMultiplication => "*=",
            OperatorKind::UnaryPlus => "+",
            OperatorKind::Negate => "-",
            OperatorKind::Modulus => "%",
            OperatorKind::AssigningModulus => "%=",
            OperatorKind::Division => "/",
            OperatorKind::AssigningDivision => "/=",
            OperatorKind::LogicalAnd => "&&",
            OperatorKind::LogicalOr => "||",
            OperatorKind::LogicalNot => "!",
            OperatorKind::Postincrement => "++",
            OperatorKind::Postdecrement => "--",
            OperatorKind::BitwiseOr => "|",
            OperatorKind::AssigningBitwiseOr => "|=",
            OperatorKind::BitwiseXor => "^",
            OperatorKind::AssigningBitwiseXor => "^=",
            OperatorKind::BitwiseAnd => "&",
            OperatorKind::AssigningBitwiseAnd => "&=",
            OperatorKind::BitwiseNot => "~",
            OperatorKind::FunctionCall => "()",
            OperatorKind::ArithmeticLeftShift => "<<",
            OperatorKind::AssigningArithmeticLeftShift => "=<<",
            OperatorKind::ArithmeticRightShift => ">>",
            OperatorKind::AssigningArithmeticRightShift => "=>>",
            OperatorKind::IndirectMemberLookup => "->",
            OperatorKind::Dereference => "*",
            OperatorKind::MethodCall => "->()",
            OperatorKind::AddressOf => "&",
            OperatorKind::ArrayIndex => "[]",
            OperatorKind::Compound => ", ",
            OperatorKind::Conditional => "?:",
            OperatorKind::Maximum => ">?",
            OperatorKind::Minimum => "<?",
            OperatorKind::Nop => "",
            OperatorKind::DereferenceIndirectMemberLookup => "->*",
            OperatorKind::Sizeof => "sizeof ",
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
    const_: bool,

    /// Type is qualified with `volatile`.
    volatile: bool,

    /// Type is qualified with `restrict`/
    restrict: bool,

    #[bits(5)]
    __: u8,
}

impl TypeQualifiers {
    fn to_str(&self) -> &'static str {
        match (self.const_(), self.volatile(), self.restrict()) {
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
}

#[derive(Debug, Clone)]
pub enum DemangledType {
    Void,
}

#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum SymbolKind {
    VTable,
    Function {
        args: Vec<DemangledType>,
        return_type: DemangledType,
    },
    StaticMember,
    TypeInfo(TypeInfoKind),
}

#[non_exhaustive]
#[derive(Debug, Clone, Copy)]
pub enum TypeInfoKind {
    Node,
    Function,
}

#[derive(Debug, Clone)]
pub struct DemangledSymbol {
    pub qualified_name: String,
    pub kind: SymbolKind,
}

#[derive(Debug, thiserror::Error)]
pub enum DemangleError {
    #[error("failed to demangle symbol")]
    DemangleFailed,
}

pub type Result<T> = std::result::Result<T, DemangleError>;

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
}

#[derive(Default, Debug)]
struct DemanglerState {
    opts: DemangleOpts,
    typevec: Vec<Vec<u8>>,
    ktypevec: Vec<Vec<u8>>,
    btypevec: Vec<Vec<u8>>,
    numk: i32,
    numb: i32,
    ksize: i32,
    bsize: i32,
    ntypes: i32,
    typevec_size: i32,
    constructor: i32,
    destructor: i32,
    static_type: i32,
    temp_start: i32,
    dllimported: i32,
    tmpl_argvec: Vec<String>,
    ntmpl_args: i32,
    forgetting_types: i32,
    previous_argument: String,
    nrepeats: i32,
    symbol_kind: StateSymbolKind,
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

    let declp = internal_demangle(&mut state, mangled);

    let kind = extract_symbol_info_from_state(&state)?;

    Ok(DemangledSymbol {
        qualified_name: String::from_utf8(declp).map_err(|e| {
            log::error!("failed to decode declp: {e:?}");
            DemangleError::DemangleFailed
        })?,
        kind,
    })
}

fn extract_symbol_info_from_state(state: &DemanglerState) -> Result<SymbolKind> {
    match &state.symbol_kind {
        StateSymbolKind::Unknown => return Err(DemangleError::DemangleFailed),
        StateSymbolKind::VTable => Ok(SymbolKind::VTable),
        StateSymbolKind::StaticMember => Ok(SymbolKind::StaticMember),
        StateSymbolKind::TypeInfoNode => Ok(SymbolKind::TypeInfo(TypeInfoKind::Node)),
        StateSymbolKind::TypeInfoFunction => Ok(SymbolKind::TypeInfo(TypeInfoKind::Function)),
        sym => unimplemented!("output translation not implemented for symbol {sym:?}"),
    }
}

fn internal_demangle(state: &mut DemanglerState, mangled: &[u8]) -> Vec<u8> {
    let style = state.opts.style();

    let mut declp = vec![];
    if mangled == b"" {
        return declp;
    }

    let result = if style.auto() || style.gnu() {
        log::debug!("gnu demangle");
        gnu_special(state, mangled, &mut declp)
    } else {
        log::debug!("wrong style");
        None
    };

    let result = if let None = result {
        log::debug!("prefix demangle");
        todo!("implement demangle_prefix")
        // demangle_prefix(state, mangled, &mut declp)
    } else {
        result
    };

    declp
}

const CPLUS_MARKERS: &[u8] = &[b'$', b'.', 0u8];

#[derive(Debug)]
enum GnuMangleCase {
    Destructor,
    Vtable,
    StaticMember,
    VirtualThunk,
    TypeInfo,
}

fn gnu_special<'a, 'b>(
    state: &'a mut DemanglerState,
    mangled: &'b [u8],
    declp: &mut Vec<u8>,
) -> Option<&'b [u8]> {
    let (mangled, case) = match mangled {
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
            if rest.len() > 0
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
            if rest.len() > 0 && rest[0] == b'i' || rest[0] == b'f' =>
        {
            log::debug!("GNU demangler: typeinfo");

            (rest, GnuMangleCase::TypeInfo)
        }

        // other case
        _ => return None,
    };

    let mut success = true;
    let mangled = match case {
        GnuMangleCase::Destructor => {
            state.destructor += 1;
            mangled
        }
        GnuMangleCase::Vtable => {
            let mut mangled = mangled;
            while mangled != b"" {
                match mangled[0] {
                    b'Q' | b'K' => {
                        let mangled2 = demangle_qualified(state, mangled, declp, false, true)?;
                        mangled = mangled2;
                    }
                    b't' => {
                        let mangled2 = demangle_template(state, mangled, declp, false, true, true)?;
                        mangled = mangled2;
                    }
                    c => {
                        let mut is_count = true;
                        let n = if c.is_ascii_digit() {
                            let (n, mangled2) = consume_count(mangled)?;
                            mangled = mangled2;
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
                        declp.extend(b"::");
                        mangled = &mangled[1..];
                    }
                    _ => {
                        success = false;
                        break;
                    }
                }
            }

            if success {
                state.symbol_kind = StateSymbolKind::VTable;
                declp.extend(b" virtual table");
            }

            mangled
        }
        GnuMangleCase::StaticMember => {
            let mut mangled = &mangled[..];
            let p = strpbrk(mangled, CPLUS_MARKERS);

            match mangled[0] {
                b'Q' | b'K' => {
                    let mangled2 = demangle_qualified(state, mangled, declp, false, true)?;
                    mangled = mangled2;
                }
                b't' => {
                    let mangled2 = demangle_template(state, mangled, declp, false, true, true)?;
                    mangled = mangled2;
                }
                _ => {
                    let (n, mangled2) = consume_count(mangled)?;
                    mangled = mangled2;

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
                    state.symbol_kind = StateSymbolKind::StaticMember;
                    mangled = &mangled[1..];
                    declp.extend(b"::");
                    declp.extend(mangled);
                    mangled = &mangled[mangled.len()..];
                }
                _ => return None,
            }

            mangled
        }
        GnuMangleCase::VirtualThunk => todo!("implement general symbol demangling first"),
        GnuMangleCase::TypeInfo => {
            let (sym_k, p) = match mangled[0] {
                b'i' => (StateSymbolKind::TypeInfoNode, &b" type_info node"[..]),
                b'f' => (
                    StateSymbolKind::TypeInfoFunction,
                    &b" type_info function"[..],
                ),
                _ => return None,
            };
            let mut mangled = &mangled[1..];
            match mangled[0] {
                b'Q' | b'K' => {
                    log::debug!("typeinfo: qualified");
                    let mangled2 = demangle_qualified(state, mangled, declp, false, true)?;
                    mangled = mangled2;
                }
                b't' => {
                    log::debug!("typeinfo: template");
                    let mangled2 = demangle_template(state, mangled, declp, false, true, true)?;
                    mangled = mangled2;
                }
                _ => {
                    log::debug!("typeinfo: fundamental type");
                    let mangled2 = demangle_fund_type(state, mangled, declp)?;
                    if log::log_enabled!(log::Level::Debug) {
                        let declp_s =
                            std::str::from_utf8(&*declp).expect("failed to deserialize declp");
                        log::debug!("Declp after fund type: {declp_s}");
                    }

                    mangled = mangled2;
                }
            }

            if success && mangled != b"" {
                log::debug!("demangle failed");
                return None;
            } else {
                declp.extend(p);
            }

            state.symbol_kind = sym_k;

            mangled
        }

        _ => mangled,
    };

    Some(mangled)
}

fn demangle_qualified<'a>(
    state: &'_ mut DemanglerState,
    mangled: &'a [u8],
    result: &'_ mut Vec<u8>,
    isfuncname: bool,
    append: bool,
) -> Option<&'a [u8]> {
    todo!("implement demangle_qualified")
}

fn demangle_template<'a>(
    state: &'_ mut DemanglerState,
    mangled: &'a [u8],
    tname: &'_ mut Vec<u8>,
    trawname: bool,
    is_type: bool,
    remember: bool,
) -> Option<&'a [u8]> {
    log::debug!("demangle template");
    todo!("implement demangle_template")
}

fn append_blank(v: &mut Vec<u8>) {
    if !v.is_empty() {
        v.push(b' ');
    }
}

fn demangle_fund_type<'a>(
    state: &'_ mut DemanglerState,
    mangled: &'a [u8],
    result: &'_ mut Vec<u8>,
) -> Option<&'a [u8]> {
    let mut mangled = mangled;
    let mut ty_kind = TypeKind::Integral;

    // Collect any applicable type qualifiers
    // TODO: refactor to collect qualifier info programmatically
    log::debug!("fundamental type: modifiers");
    loop {
        log::debug!("{:?}", char::from_u32(mangled[0] as u32));
        match mangled[0] {
            b'C' | b'V' | b'u' => {
                log::debug!("fundamental type: ansi modifier");
                if state.opts.ansi() {
                    if !result.is_empty() {
                        result.splice(0..0, b" "[..].into_iter().cloned());
                    }
                    result.splice(0..0, demangle_qualifier(mangled[0]).into_iter().cloned());
                }
            }
            b'U' => {
                log::debug!("fundamental type: unsigned");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"unsigned");
            }
            b'S' => {
                log::debug!("fundamental type: signed");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"signed");
            }
            b'J' => {
                log::debug!("fundamental type: complex");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"__complex");
            }
            _ => break,
        }
    }

    // Actually demangle underlying type
    // TODO: refactor to collect type info programmatically
    log::debug!("fundamental type: type");
    if mangled != b"" {
        match mangled[0] {
            b'_' => {}
            b'v' => {
                log::debug!("fundamental type: type void");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"void");
            }
            b'x' => {
                log::debug!("fundamental type: long long");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"long long");
            }
            b'l' => {
                log::debug!("fundamental type: long");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"long");
            }
            b'i' => {
                log::debug!("fundamental type: int");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"int");
            }
            b's' => {
                log::debug!("fundamental type: short");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"short");
            }
            b'b' => {
                log::debug!("fundamental type: bool");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"bool");
                ty_kind = TypeKind::Bool;
            }
            b'c' => {
                log::debug!("fundamental type: char");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"char");
                ty_kind = TypeKind::Char;
            }
            b'w' => {
                log::debug!("fundamental type: wchar_t");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"wchar_t");
                ty_kind = TypeKind::Char;
            }
            b'r' => {
                log::debug!("fundamental type: long double");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"long double");
                ty_kind = TypeKind::Real;
            }
            b'd' => {
                log::debug!("fundamental type: double");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"double");
                ty_kind = TypeKind::Real;
            }
            b'f' => {
                log::debug!("fundamental type: float");
                mangled = &mangled[1..];
                append_blank(result);
                result.extend(b"float");
                ty_kind = TypeKind::Real;
            }
            b'G' | b'I' => {
                log::debug!("fundamental type: stdint");
                if mangled[0] == b'G' {
                    mangled = &mangled[1..];
                    if mangled.is_empty() || !mangled[0].is_ascii_digit() {
                        return None;
                    }
                }

                mangled = &mangled[1..];
                if mangled.is_empty() {
                    return None;
                }
                let buf = if mangled[0] == b'_' {
                    mangled = &mangled[1..];
                    let n = mangled.iter().take(9).take_while(|&&c| c != b'_').count();
                    let buf = {
                        let (buf, mangled2) = mangled.split_at(n);
                        mangled = mangled2;
                        buf
                    };
                    if mangled.is_empty() || mangled[0] != b'_' {
                        return None;
                    }
                    buf
                } else {
                    let (buf, mangled2) = mangled.split_at(2);
                    mangled = mangled2;
                    buf
                };
                let buf_s = std::str::from_utf8(buf).ok()?;
                let dec = usize::from_str_radix(buf_s, 16).ok()?;
                if dec > 64 || dec < 8 {
                    return None;
                }
                append_blank(result);
                result.extend(format!("int{dec}_t").into_bytes());
            }
            c if c.is_ascii_digit() => {
                log::debug!("fundamental type: class");
                let mut btype = vec![];
                if let Some(mangled2) = demangle_class_name(state, mangled, &mut btype) {
                    mangled = mangled2;
                    append_blank(result);
                    result.extend(&btype);
                    state.btypevec.push(btype);
                } else {
                    return None;
                }
            }
            b't' => {
                log::debug!("fundamental type: template");
                let mut btype = vec![];
                mangled = demangle_template(state, mangled, &mut btype, false, true, true)?;
                result.extend(&btype);
            }
            _ => return None,
        }
    }

    log::debug!("fundamental type demangled");
    Some(mangled)
}

fn demangle_qualifier(qualifier: u8) -> &'static [u8] {
    match qualifier {
        b'C' => b"const",
        b'V' => b"volatile",
        b'u' => b"__restrict",
        _ => b"",
    }
}

fn demangle_class_name<'a>(
    state: &'_ mut DemanglerState,
    mangled: &'a [u8],
    declp: &mut Vec<u8>,
) -> Option<&'a [u8]> {
    let mut mangled = mangled;
    log::debug!("demangle class type");

    let n = {
        let (n, mangled2) = consume_count(mangled)?;
        mangled = mangled2;
        n
    };

    if mangled.len() >= n {
        log::debug!("parse class name");
        mangled = demangle_arm_hp_template(state, mangled, n, declp)?;
        Some(mangled)
    } else {
        log::debug!("malformed class type slug");
        None
    }
}

fn demangle_arm_hp_template<'a>(
    state: &'_ mut DemanglerState,
    mangled: &'a [u8],
    n: usize,
    declp: &'_ mut Vec<u8>,
) -> Option<&'a [u8]> {
    let mut p = vec![];
    let mut args = vec![];
    let mut mangled = mangled;

    if state.opts.style().hp() && mangled[n] == b'X' {
        log::debug!("demangle template as HP cfront style");
        todo!("implement hp cfront demangling");
    } else if let Some(()) = arm_pt(state, mangled, n, &mut p, &mut args) {
        log::debug!("demangle template as arm/extended HP cfront style");
        todo!("implement arm_pt demangling");
    } else if n > 10
        && mangled.starts_with(b"_GLOBAL_")
        && mangled[9] == b'N'
        && mangled[8] == mangled[10]
        && CPLUS_MARKERS.contains(&mangled[8])
    {
        log::debug!("demangle template as anonymous namespace member");

        declp.extend(b"{anonymous}");
    } else {
        log::debug!("demangle class name");
        // check that this is a non-recursive call
        if state.temp_start == -1 {
            // disable in recursive calls
            state.temp_start = 0;
        }
        declp.extend(&mangled[..n]);
    }

    mangled = &mangled[n..];
    Some(mangled)
}

fn arm_pt(
    state: &mut DemanglerState,
    mangled: &[u8],
    n: usize,
    anchor: &mut Vec<u8>,
    args: &mut Vec<u8>,
) -> Option<()> {
    let style = state.opts.style();
    let mut mangled = mangled;

    log::debug!("arm_pt");

    if style.arm() || style.hp() {
        log::debug!("arm_pt: arm/hp style");
        if let Some(anchor_pos) = memmem(mangled, b"__pt__") {
            let anchor = &mangled[anchor_pos + 6..];
            let len = {
                let (len, mangled2) = consume_count(mangled)?;
                mangled = mangled2;
                len
            };
            if &args[len..] == &mangled[n..] && args[0] == b'_' {
                args.splice(0..1, b"".iter().cloned());
                return Some(());
            }
        }
    }
    if style.auto() || style.edg() {
        todo!("arm_pt: implement edg");
    }

    None
}

fn consume_count(mangled: &[u8]) -> Option<(usize, &[u8])> {
    let digit_count = mangled.iter().take_while(|&b| b.is_ascii_digit()).count();

    let (digits, mangled) = mangled.split_at(digit_count);
    let count = std::str::from_utf8(digits).ok()?.parse().ok()?;

    Some((count, mangled))
}

fn strpbrk<'a, 'b>(s: &'a [u8], accept: &'b [u8]) -> Option<&'a [u8]> {
    let position = s.iter().position(|c| accept.contains(c))?;
    Some(&s[position..])
}
