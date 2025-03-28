use bitfield_struct::bitfield;
use memchr::memmem;

/// Options for controlling demangling.
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

/// Options specifically concerning which demangling convention
/// should be used.
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
#[derive(Debug, PartialEq)]
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

/// What kind of symbol this is.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum SymbolKind {
    /// Symbol refers to the vtable of a specified class.
    VTable,
    /// Symbol refers to a function entry point.
    Function {
        args: Vec<DemangledType>,
        return_type: DemangledType,
    },
    /// Symbol refers to the static member of a container type.
    StaticMember,
    /// Symbol is type reflection information.
    TypeInfo(TypeInfoKind),
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
    /// The qualified name of the demangled symbol.
    /// Includes namespaces, and class names for member functions.
    pub qualified_name: String,

    /// Structured information on the demangled symbol.
    pub kind: SymbolKind,
}

#[derive(Debug, thiserror::Error)]
pub enum DemangleError {
    #[error("failed to demangle symbol")]
    DemangleFailed,
}

/// Result type for all demangle operations.
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
    tmpl_argvec: Vec<Vec<u8>>,
    ntmpl_args: i32,
    forgetting_types: i32,
    previous_argument: String,
    nrepeats: i32,
    symbol_kind: StateSymbolKind,
}

trait VecExt<T> {
    fn prepend<'a>(&mut self, prepend_with: &'a [T]);
}

impl<T: Clone> VecExt<T> for Vec<T> {
    fn prepend<'a>(&mut self, prepend_with: &'a [T]) {
        self.splice(0..0, prepend_with.into_iter().cloned());
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

    let declp = state.internal_demangle(mangled);

    let kind = state.extract_symbol_info()?;

    Ok(DemangledSymbol {
        qualified_name: String::from_utf8(declp).map_err(|e| {
            log::error!("failed to decode declp: {e:?}");
            DemangleError::DemangleFailed
        })?,
        kind,
    })
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
struct ConsumeVal<'a, Inner> {
    mangled: &'a [u8],
    value: Inner,
}

impl DemanglerState {
    fn extract_symbol_info(&self) -> Result<SymbolKind> {
        match &self.symbol_kind {
            StateSymbolKind::Unknown => return Err(DemangleError::DemangleFailed),
            StateSymbolKind::VTable => Ok(SymbolKind::VTable),
            StateSymbolKind::StaticMember => Ok(SymbolKind::StaticMember),
            StateSymbolKind::TypeInfoNode => Ok(SymbolKind::TypeInfo(TypeInfoKind::Node)),
            StateSymbolKind::TypeInfoFunction => Ok(SymbolKind::TypeInfo(TypeInfoKind::Function)),
            sym => unimplemented!("output translation not implemented for symbol {sym:?}"),
        }
    }

    fn internal_demangle(&mut self, mangled: &[u8]) -> Vec<u8> {
        let style = self.opts.style();

        let mut declp = vec![];
        if mangled == b"" {
            return declp;
        }

        let result = if style.auto() || style.gnu() {
            log::debug!("gnu demangle");
            self.gnu_special(mangled, &mut declp)
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

    fn gnu_special<'a, 'b>(
        &mut self,
        mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Option<ConsumeVal<'a, ()>> {
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
                self.destructor += 1;
                mangled
            }
            GnuMangleCase::Vtable => {
                let mut mangled = mangled;
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
                    self.symbol_kind = StateSymbolKind::VTable;
                    declp.extend(b" virtual table");
                }

                mangled
            }
            GnuMangleCase::StaticMember => {
                let mut mangled = &mangled[..];
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
                        if log::log_enabled!(log::Level::Debug) {
                            let declp_s =
                                std::str::from_utf8(&*declp).expect("failed to deserialize declp");
                            log::debug!("Declp after fund type: {declp_s}");
                        }
                    }
                }

                if log::log_enabled!(log::Level::Debug) {
                    let mangled_s =
                        std::str::from_utf8(&*mangled).expect("failed to deserialize mangled");
                    log::debug!("mangled after fund type: {mangled_s}");
                }

                if success && mangled != b"" {
                    log::debug!("demangle failed");
                    return None;
                } else {
                    declp.extend(p);
                }

                self.symbol_kind = sym_k;

                mangled
            }

            _ => mangled,
        };

        Some(ConsumeVal { value: (), mangled })
    }

    fn demangle_qualified<'a>(
        &mut self,
        mangled: &'a [u8],
        result: &'_ mut Vec<u8>,
        isfuncname: bool,
        append: bool,
    ) -> Option<ConsumeVal<'a, ()>> {
        todo!("implement demangle_qualified")
    }

    fn demangle_template<'a>(
        &mut self,
        mangled: &'a [u8],
        tname: &'_ mut Vec<u8>,
        trawname: Option<&'_ mut Vec<u8>>,
        is_type: bool,
        remember: bool,
    ) -> Option<ConsumeVal<'a, TypeKind>> {
        let mut mangled = &mangled[1..];
        let mut is_java_array = false;
        let mut need_comma = false;
        let mut ty_k = TypeKind::None;

        log::debug!("demangle template");

        if is_type {
            // Get template name
            if mangled[0] == b'z' {
                log::debug!("demangle template: is type, template param");
                mangled = &mangled[2..];

                let idx;
                ConsumeVal {
                    value: idx,
                    mangled,
                } = consume_count_with_underscores(mangled)?;

                todo!("implement demangle_template/z");
            } else {
                log::debug!("demangle template: is type, NOT template param");

                let r;
                ConsumeVal { value: r, mangled } = consume_count(mangled)?;

                if r > mangled.len() {
                    return None;
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

        log::debug!("{r} template param(s)");

        if !is_type {
            let mut v = vec![];
            v.resize_with(r, Vec::new);
            self.tmpl_argvec = v;
            self.ntmpl_args = r as i32;
        }

        if log::log_enabled!(log::Level::Debug) {
            let tname_s = std::str::from_utf8(&*tname).expect("failed to deserialize tname");
            log::debug!("tname: {tname_s}");
        }

        if log::log_enabled!(log::Level::Debug) {
            let mangled_s = std::str::from_utf8(&*mangled).expect("failed to deserialize mangled");
            log::debug!("mangled: {mangled_s}");
        }

        for i in 0..r {
            log::debug!("demangle template: param {i}");
            if need_comma {
                tname.extend(b", ");
            }
            if mangled[0] == b'Z' {
                let mut temp: Vec<u8> = vec![];
                log::debug!("demangle_template: type parameter");
                mangled = &mangled[1..];

                ConsumeVal {
                    value: ty_k,
                    mangled,
                } = self.do_type(mangled, &mut temp)?;

                tname.extend(&temp);

                if !is_type {
                    log::debug!("demangle_template: add to argvec");
                    self.tmpl_argvec.get_mut(i)?.extend(&temp);
                }
            } else if mangled[0] == b'z' {
                mangled = &mangled[1..];
                todo!("implement template parameter demangle");
            } else {
                // value parameter
                let mut temp: Vec<u8> = vec![];
                ConsumeVal {
                    value: ty_k,
                    mangled,
                } = self.do_type(mangled, &mut temp)?;

                todo!("implement value parameter demangle");
            }
            need_comma = true;
        }

        if is_java_array {
            tname.extend(b"[]");
        } else {
            tname.push(b'>');
        }

        if is_type && remember {
            self.btypevec.push(tname.clone());
        }

        log::debug!("demangle_template: done");

        Some(ConsumeVal {
            value: ty_k,
            mangled,
        })
    }

    fn do_type<'a>(
        &mut self,
        mangled: &'a [u8],
        result: &'_ mut Vec<u8>,
    ) -> Option<ConsumeVal<'a, TypeKind>> {
        let mut mangled = mangled;
        let mut done = false;
        let mut ty_k = TypeKind::None;
        let mut btype: Vec<u8> = vec![];
        let mut decl: Vec<u8> = vec![];
        result.clear();
        log::debug!("do_type: enter");

        while !done {
            match mangled[0] {
                // pointer types
                b'p' | b'P' => {
                    log::debug!("do_type: pointer");
                    mangled = &mangled[1..];
                    if !self.opts.java() {
                        decl.prepend(b"*");
                    }
                    if ty_k == TypeKind::None {
                        ty_k = TypeKind::Pointer;
                    }
                }
                b'R' => {
                    // reference types
                    log::debug!("do_type: reference");
                    mangled = &mangled[1..];
                    decl.prepend(b"&");
                    if ty_k == TypeKind::None {
                        ty_k = TypeKind::Reference;
                    }
                }
                b'A' => {
                    // array types
                    log::debug!("do_type: array");
                    mangled = &mangled[1..];
                    if !decl.is_empty() && (decl[0] == b'*' || decl[0] == b'&') {
                        decl.prepend(b"(");
                        decl.push(b')');
                    }
                    decl.push(b'[');
                    todo!("finish implementing array type");
                }
                b'T' => {
                    log::debug!("do_type: backref");
                    todo!("finish implementing backref type");
                }
                b'F' => {
                    log::debug!("do_type: function");
                    todo!("finish implementing function type");
                }
                b'O' => {
                    log::debug!("do_type: rvalue reference");
                    todo!("finish implementing rvalue type");
                }
                b'M' => {
                    log::debug!("do_type: member");
                    todo!("finish implementing member type");
                }
                b'G' => {
                    log::debug!("do_type: ?");
                    mangled = &mangled[1..];
                }
                b'C' | b'V' | b'u' => {
                    log::debug!("do_type: fundamental type qualifier");
                    if self.opts.ansi() {
                        if !decl.is_empty() {
                            decl.prepend(b" ");
                        }

                        decl.prepend(demangle_qualifier(mangled[0]));
                    }
                    mangled = &mangled[1..];
                }
                _ => {
                    done = true;
                }
            }
        }

        match mangled[0] {
            b'Q' | b'K' => {
                log::debug!("do_type: qualified type");
                self.demangle_qualified(mangled, result, false, true)?;
            }
            b'B' => {
                log::debug!("do_type: backref");
                let n;
                ConsumeVal { value: n, mangled } = get_count(&mangled[1..])?;

                if n >= self.btypevec.len() {
                    return None;
                }
                result.extend(&self.btypevec[n]);
            }
            b'X' | b'Y' => {
                log::debug!("do_type: template param");
                mangled = &mangled[1..];
                let idx;
                ConsumeVal {
                    value: idx,
                    mangled,
                } = consume_count_with_underscores(mangled)?;

                if idx >= self.tmpl_argvec.len() {
                    return None;
                }

                ConsumeVal { mangled, .. } = consume_count_with_underscores(mangled)?;

                if !self.tmpl_argvec.is_empty() {
                    result.extend(&self.tmpl_argvec[idx]);
                } else {
                    let buf = format!("T{idx}");
                    result.extend(buf.as_bytes());
                }
            }
            _ => {
                log::debug!("do_type: fallthrough (assumed fundamental type)");
                ConsumeVal {
                    value: ty_k,
                    mangled,
                } = self.demangle_fund_type(mangled, result)?;
            }
        }

        if !decl.is_empty() {
            result.push(b' ');
            result.extend(&decl);
        }

        if ty_k == TypeKind::None {
            log::debug!("do_type: no type sepcified, assuming integral");
            // If unknown, assume integral
            ty_k = TypeKind::Integral;
        }

        log::debug!("do_type: done");

        Some(ConsumeVal {
            value: ty_k,
            mangled,
        })
    }

    fn demangle_fund_type<'a>(
        &mut self,
        mangled: &'a [u8],
        result: &'_ mut Vec<u8>,
    ) -> Option<ConsumeVal<'a, TypeKind>> {
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
                    if self.opts.ansi() {
                        if !result.is_empty() {
                            result.prepend(b" ");
                        }
                        result.prepend(demangle_qualifier(mangled[0]));
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
                        let buf;
                        (buf, mangled) = mangled.split_at(n);
                        if mangled.is_empty() || mangled[0] != b'_' {
                            return None;
                        }
                        buf
                    } else {
                        let buf;
                        (buf, mangled) = mangled.split_at(2);
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
                    ConsumeVal { mangled, .. } = self.demangle_class_name(mangled, &mut btype)?;
                    append_blank(result);
                    result.extend(&btype);
                    self.btypevec.push(btype);
                }
                b't' => {
                    log::debug!("fundamental type: template");
                    let mut btype = vec![];
                    ConsumeVal { mangled, .. } =
                        self.demangle_template(mangled, &mut btype, None, true, true)?;
                    result.extend(&btype);
                }
                _ => return None,
            }
        }

        log::debug!("fundamental type demangled");
        Some(ConsumeVal {
            value: ty_kind,
            mangled,
        })
    }

    fn demangle_class_name<'a>(
        &mut self,
        mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Option<ConsumeVal<'a, ()>> {
        let mut mangled = mangled;
        log::debug!("demangle class type");

        let n;
        ConsumeVal { value: n, mangled } = consume_count(mangled)?;

        if mangled.len() >= n {
            log::debug!("parse class name");
            ConsumeVal { mangled, .. } = self.demangle_arm_hp_template(mangled, n, declp)?;
            Some(ConsumeVal { value: (), mangled })
        } else {
            log::debug!("malformed class type slug");
            None
        }
    }

    fn demangle_arm_hp_template<'a>(
        &mut self,
        mangled: &'a [u8],
        n: usize,
        declp: &'_ mut Vec<u8>,
    ) -> Option<ConsumeVal<'a, ()>> {
        let mut p = vec![];
        let mut args = vec![];
        let mut mangled = mangled;

        if self.opts.style().hp() && mangled[n] == b'X' {
            log::debug!("demangle template as HP cfront style");
            todo!("implement hp cfront demangling");
        } else if let Some(_) = self.arm_pt(mangled, n, &mut p, &mut args) {
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
            if self.temp_start == -1 {
                // disable in recursive calls
                self.temp_start = 0;
            }
            declp.extend(&mangled[..n]);
        }

        mangled = &mangled[n..];
        Some(ConsumeVal { value: (), mangled })
    }

    fn arm_pt<'a>(
        &'_ mut self,
        mangled: &'a [u8],
        n: usize,
        anchor: &'_ mut Vec<u8>,
        args: &'_ mut Vec<u8>,
    ) -> Option<ConsumeVal<'a, ()>> {
        let style = self.opts.style();
        let mut mangled = mangled;

        log::debug!("arm_pt");

        if style.arm() || style.hp() {
            log::debug!("arm_pt: arm/hp style");
            if let Some(anchor_pos) = memmem::find(mangled, b"__pt__") {
                let anchor = &mangled[anchor_pos + 6..];
                let len;
                ConsumeVal {
                    value: len,
                    mangled,
                } = consume_count(mangled)?;
                if &args[len..] == &mangled[n..] && args[0] == b'_' {
                    args.splice(0..1, b"".iter().cloned());
                    return Some(ConsumeVal { value: (), mangled });
                }
            }
        }
        if style.auto() || style.edg() {
            todo!("arm_pt: implement edg");
        }

        None
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

fn consume_count<'a>(mangled: &'a [u8]) -> Option<ConsumeVal<'a, usize>> {
    let digit_count = mangled.iter().take_while(|&b| b.is_ascii_digit()).count();

    let (digits, mangled) = mangled.split_at(digit_count);
    let count = std::str::from_utf8(digits).ok()?.parse().ok()?;

    Some(ConsumeVal {
        value: count,
        mangled,
    })
}

fn consume_count_with_underscores<'a>(mangled: &'a [u8]) -> Option<ConsumeVal<'a, usize>> {
    if mangled.starts_with(b"_") && mangled.ends_with(b"_") && mangled.len() > 1 {
        let end = 0.max(mangled.len() - 1);

        consume_count(&mangled[1..end])
    } else {
        None
    }
}

fn get_count<'a>(mangled: &'a [u8]) -> Option<ConsumeVal<'a, usize>> {
    let digit = mangled[0];

    let ConsumeVal {
        value: count,
        mangled: mangled_post_count,
    } = consume_count(mangled)?;
    if mangled_post_count.len() > 0 && mangled_post_count[0] == b'_' {
        // Treat count like consume_count if followed by _
        Some(ConsumeVal {
            value: count,
            mangled: mangled_post_count,
        })
    } else {
        // Only count first digit otherwise
        Some(ConsumeVal {
            value: (digit - b'0') as usize,
            mangled: &mangled[1..],
        })
    }
}

fn strpbrk<'a, 'b>(s: &'a [u8], accept: &'b [u8]) -> Option<&'a [u8]> {
    let position = s.iter().position(|c| accept.contains(c))?;
    Some(&s[position..])
}
