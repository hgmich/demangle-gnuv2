use anyhow::{Context, Result};
use bitfield_struct::bitfield;
use memchr::memmem;

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
            OperatorKind::NonEquality => b"!",
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
}

// TODO: remove and rename internal state fields as appropriate
#[derive(Default, Debug)]
struct DemanglerState {
    opts: DemangleOpts,
    btypes: BTypeStore,
    types: Vec<Vec<u8>>,
    ktypes: Vec<Vec<u8>>,
    constructor: i32,
    destructor: i32,
    static_type: bool,
    temp_start: i32,
    dllimported: bool,
    tmpl_argvec: Vec<Vec<u8>>,
    ntmpl_args: i32,
    forgetting_types: i32,
    previous_argument: Vec<u8>,
    nrepeats: i32,
    symbol_kind: StateSymbolKind,
    type_quals: TypeQualifiers,
}

#[derive(Debug)]
struct BTypeStore {
    next_idx: usize,
    storage: Vec<Option<Vec<u8>>>,
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

    fn remember(&mut self, idx: usize, btype: &[u8]) -> Result<()> {
        let cell = self
            .storage
            .get_mut(idx)
            .with_context(|| format!("failed to lookup btype {idx}"))?;
        *cell = Some(btype.to_owned());

        Ok(())
    }

    fn get(&self, idx: usize) -> Option<&[u8]> {
        self.storage.get(idx)?.as_deref()
    }
}

impl Default for BTypeStore {
    fn default() -> Self {
        Self::new()
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

    let kind = state.extract_symbol_info()?;

    Ok(DemangledSymbol {
        qualified_name: String::from_utf8(declp).map_err(|e| {
            log::error!("failed to decode declp: {e:?}");
            anyhow::anyhow!("failed to decode symbol from utf-8")
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
            StateSymbolKind::Unknown => anyhow::bail!("unknown symbol kind"),
            StateSymbolKind::VTable => Ok(SymbolKind::VTable),
            StateSymbolKind::StaticMember => Ok(SymbolKind::StaticMember),
            StateSymbolKind::TypeInfoNode => Ok(SymbolKind::TypeInfo(TypeInfoKind::Node)),
            StateSymbolKind::TypeInfoFunction => Ok(SymbolKind::TypeInfo(TypeInfoKind::Function)),
            StateSymbolKind::Function => self.extract_function_info(),
            sym => unimplemented!("output translation not implemented for symbol {sym:?}"),
        }
    }

    fn extract_function_info(&self) -> Result<SymbolKind> {
        // TODO: implement properly
        Ok(SymbolKind::Function {
            args: vec![],
            return_type: DemangledType::Void,
        })
    }

    fn internal_demangle(&mut self, mangled: &[u8]) -> Result<Vec<u8>> {
        let style = self.opts.style();

        let mut declp = vec![];
        if mangled == b"" {
            return Ok(declp);
        }

        let result = if style.auto() || style.gnu() {
            log::debug!("gnu demangle");
            self.gnu_special(mangled, &mut declp)
        } else {
            log::debug!("wrong style");
            Err(anyhow::anyhow!("wrong style"))
        };

        let result = if result.is_err() {
            log::debug!("prefix demangle");
            self.demangle_prefix(mangled, &mut declp)
        } else {
            result
        };

        match result {
            Ok(ConsumeVal { mangled, .. }) if !mangled.is_empty() => {
                log::debug!("signature demangle");
                self.demangle_signature(mangled, &mut declp)
            }
            _ => result,
        }?;

        Ok(declp)
    }

    fn demangle_prefix<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
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
            match (marker, mangled[10]) {
                (Some(&c), b'D') if c == mangled[10] => {
                    // Global destructor called at exit
                    mangled = &mangled[11..];
                    self.destructor = 2;
                    if let res @ Ok(_) = self.gnu_special(mangled, declp) {
                        return res;
                    }
                }
                (Some(&c), b'I') if c == mangled[10] => {
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
                // A GNU style constructor starts with __[0-9Qt].  But cfront uses
                // names like __Q2_3foo3bar for nested type names.  So don't accept
                // this style of constructor for cfront demangling.  A GNU
                // style member-template constructor starts with 'H'
                if style.lucid() || style.arm() || style.hp() || style.edg() {
                    self.constructor += 1;
                }
                mangled = &scan[2..];
            }
        } else if style.arm() && scan.len() > 3 && scan[2..4] == b"pt"[..] {
            log::debug!("demangle_prefix: cfront parameterized type");
            // Cfront style parameterised type
            ConsumeVal { mangled, .. } =
                self.demangle_arm_hp_template(mangled, mangled.len(), declp)?;
        } else if style.edg()
            && scan.len() > 3
            && ((scan[2..4] == b"pt"[..]) || (scan[2..4] == b"tm"[..]) || (scan[2..4] == b"ps"[..]))
        {
            log::debug!("demangle_prefix: edg parameterized type");
            // EDG-style parameterized type
            ConsumeVal { mangled, .. } =
                self.demangle_arm_hp_template(mangled, mangled.len(), declp)?;
        } else if scan_idx == 0 && scan.len() > 2 && !scan[2].is_ascii_digit() && scan[2] != b't' {
            log::debug!("demangle_prefix: arm name");
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
            log::debug!("demangle_prefix: global function name");
            ConsumeVal { mangled, .. } = self.demangle_function_name(mangled, declp, scan)?;
            self.symbol_kind = StateSymbolKind::Function;
        } else {
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

        Ok(ConsumeVal { mangled, value: () })
    }

    fn gnu_special<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
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
                mangled = &mangled[8..];
                ConsumeVal {
                    mangled,
                    value: delta,
                } = consume_count(mangled)?;

                mangled = &mangled[1..];
                let method = self.internal_demangle(mangled)?;

                if method.is_empty() {
                    anyhow::bail!("failed to get method name for virtual thunk");
                }

                declp.extend(format!("virtual function thunk (delta:{delta}) for ").as_bytes());
                declp.extend(&method);
                mangled = &mangled[mangled.len()..];

                mangled
            }
            GnuMangleCase::TypeInfo => {
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
                        if log::log_enabled!(log::Level::Debug) {
                            let declp_s =
                                std::str::from_utf8(&*declp).expect("failed to deserialize declp");
                            log::debug!("Declp after fund type: {declp_s}");
                        }
                    }
                }

                if log::log_enabled!(log::Level::Debug) {
                    let mangled_s =
                        std::str::from_utf8(mangled).expect("failed to deserialize mangled");
                    log::debug!("mangled after fund type: {mangled_s}");
                }

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

        if log::log_enabled!(log::Level::Debug) {
            let mangled_s = std::str::from_utf8(mangled).expect("failed to deserialize mangled");
            log::debug!("mangled after fund type: {mangled_s}");
        }

        Ok(ConsumeVal { value: (), mangled })
    }

    fn demangle_qualified<'a>(
        &mut self,
        mut mangled: &'a [u8],
        result: &'_ mut Vec<u8>,
        isfuncname: bool,
        append: bool,
    ) -> Result<ConsumeVal<'a, ()>> {
        let style = self.opts.style();
        let mut temp: Vec<u8> = vec![];
        let mut last_name: Vec<u8> = vec![];
        let mut qualifier_count = 0usize;

        let bindex = self.btypes.register();

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
                        todo!("Implement GNU mangled name with more than 9 classes");
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

        for i in (0..qualifier_count).into_iter().rev() {
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
                        todo!("implement EDG recursive demangling");
                    } else {
                        ConsumeVal { mangled, .. } = self.do_type(mangled, &mut last_name)?;
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

        self.btypes.remember(bindex, &temp)?;

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

        Ok(ConsumeVal { mangled, value: () })
    }

    fn demangle_template<'a>(
        &mut self,
        mangled: &'a [u8],
        tname: &'_ mut Vec<u8>,
        trawname: Option<&'_ mut Vec<u8>>,
        is_type: bool,
        remember: bool,
    ) -> Result<ConsumeVal<'a, TypeKind>> {
        let mut mangled = &mangled[1..];
        let mut is_java_array = false;
        let mut need_comma = false;
        let mut ty_k = TypeKind::None;
        let mut bindex = None;

        log::debug!("demangle template");

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

                todo!("implement demangle_template/z");
            } else {
                log::debug!("demangle template: is type, NOT template param");

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

        log::debug!("{r} template param(s)");

        if !is_type {
            let mut v = vec![];
            v.resize_with(r, Vec::new);
            self.tmpl_argvec = v;
            self.ntmpl_args = r as i32;
        }

        if log::log_enabled!(log::Level::Debug) {
            let tname_s = std::str::from_utf8(&*tname).context("failed to deserialize tname")?;
            log::debug!("tname: {tname_s}");
        }

        if log::log_enabled!(log::Level::Debug) {
            let mangled_s =
                std::str::from_utf8(mangled).context("failed to deserialize mangled")?;
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
                    self.tmpl_argvec
                        .get_mut(i)
                        .with_context(|| format!("missing Z template backref {i}"))?
                        .extend(&temp);
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
                log::debug!("is_type = {is_type}");
                // Change here is because we don't want to have to do a weird dance with Cell to reborrow
                // tname mutably during this scope.
                // Arguably there was an overgeneralization in the original C code anyway.
                if !is_type {
                    let mut s = Vec::new();
                    ConsumeVal { mangled, .. } =
                        self.demangle_template_value_parm(mangled, &mut s, ty_k)?;

                    self.tmpl_argvec.push(s.clone());
                    tname.extend(&*s);
                } else {
                    ConsumeVal { mangled, .. } =
                        self.demangle_template_value_parm(mangled, tname, ty_k)?;
                }

                if log::log_enabled!(log::Level::Debug) {
                    let tname_s = std::str::from_utf8(tname).expect("failed to deserialize tname");
                    log::debug!("tname = {tname_s}");
                }
            }
            need_comma = true;
        }

        tname.extend(if is_java_array { &b"[]"[..] } else { &b">"[..] });

        if is_type && remember {
            if let Some(idx) = bindex {
                if log::log_enabled!(log::Level::Debug) {
                    let tname_s = std::str::from_utf8(tname).expect("failed to deserialize tname");
                    log::debug!("demangle_template: remembering type {tname_s}");
                }
                self.btypes.remember(idx, tname);
            }
        }

        log::debug!("demangle_template: done");

        Ok(ConsumeVal {
            value: ty_k,
            mangled,
        })
    }

    fn do_type<'a>(
        &mut self,
        mut mangled: &'a [u8],
        result: &'_ mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, TypeKind>> {
        let mut done = false;
        let mut ty_k = TypeKind::None;
        let btype: Vec<u8> = vec![];
        let mut decl: Vec<u8> = vec![];
        let mut type_quals = TypeQualifiers::new();

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

                    mangled = &mangled[1..];
                    if !decl.is_empty() && [b'*', b'&'].contains(&decl[0]) {
                        decl.prepend(b"(");
                        decl.extend(b")");
                    }

                    ConsumeVal { mangled, .. } = self.demangle_nested_args(mangled, &mut decl)?;

                    if !mangled.is_empty() && mangled[0] != b'_' {
                        anyhow::bail!("malformed function type");
                    }

                    if !mangled.is_empty() && mangled[0] != b'_' {
                        mangled = &mangled[1..];
                    }
                }
                b'O' => {
                    log::debug!("do_type: rvalue reference");
                    todo!("finish implementing rvalue type");
                }
                b'M' => {
                    log::debug!("do_type: member");
                    type_quals = TypeQualifiers::new();
                    let member = !mangled.is_empty() && mangled[0] == b'M';
                    mangled = &mangled[1..];
                    decl.push(b')');
                    decl.prepend(self.scope_str());
                    match mangled.get(0) {
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
                            ConsumeVal { mangled, .. } = self.do_type(mangled, &mut temp)?;
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
                    decl.prepend(b"(");
                    if member {
                        match mangled.get(0) {
                            Some(c @ b'C') | Some(c @ b'V') | Some(c @ b'u') => {
                                type_quals = TypeQualifiers::from_bits(
                                    type_quals.into_bits()
                                        | TypeQualifiers::from_code(*c).into_bits(),
                                );
                                mangled = &mangled[1..];
                            }
                            Some(b'F') => anyhow::bail!("unexpected F, expected nothing or C/V/u"),
                            _ => {}
                        }

                        mangled = &mangled[1..];
                    }

                    if member {
                        ConsumeVal { mangled, .. } =
                            self.demangle_nested_args(mangled, &mut decl)?;
                    }

                    if mangled.get(0) != Some(&b'_') {
                        anyhow::bail!("expected to end with underscore");
                    }

                    if self.opts.ansi() && type_quals.into_bits() != 0 {
                        append_blank(&mut decl);
                        decl.extend(type_quals.to_str().as_bytes());
                    }
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
                ConsumeVal { mangled, .. } =
                    self.demangle_qualified(mangled, result, false, true)?;
            }
            b'B' => {
                log::debug!("do_type: backref");
                let n;
                ConsumeVal { value: n, mangled } = get_count(&mangled[1..])?;

                if let Some(btype) = self.btypes.get(n) {
                    result.extend(btype);
                } else {
                    log::error!("symbol has backref to uncaptured btype {n}");
                    anyhow::bail!("symbol has backref to uncaptured btype {n}");
                }
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
                    anyhow::bail!("unknown template param backref {idx}");
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

        Ok(ConsumeVal {
            value: ty_k,
            mangled,
        })
    }

    fn demangle_fund_type<'a>(
        &mut self,
        mut mangled: &'a [u8],
        result: &'_ mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, TypeKind>> {
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
                }
                c if c.is_ascii_digit() => {
                    log::debug!("fundamental type: class");
                    let bindex = self.btypes.register();
                    let mut btype = vec![];
                    ConsumeVal { mangled, .. } = self.demangle_class_name(mangled, &mut btype)?;
                    append_blank(result);
                    result.extend(&btype);
                    self.btypes
                        .remember(bindex, &btype)
                        .context("failed to remember btype")?;
                }
                b't' => {
                    log::debug!("fundamental type: template");
                    let mut btype = vec![];
                    ConsumeVal { mangled, .. } =
                        self.demangle_template(mangled, &mut btype, None, true, true)?;
                    if log::log_enabled!(log::Level::Debug) {
                        let btype_s =
                            std::str::from_utf8(&btype).expect("failed to deserialize btype");
                        log::debug!("btype after fund type: {btype_s}");
                    }
                    result.extend(&btype);
                }
                c => {
                    let chr = char::from_u32(c as u32)
                        .map(|chr| chr.to_string())
                        .unwrap_or_else(|| format!("{c:x}"));
                    anyhow::bail!("unknown fundamental type tag {chr}");
                }
            }
        }

        log::debug!("fundamental type demangled");
        Ok(ConsumeVal {
            value: ty_kind,
            mangled,
        })
    }

    fn demangle_class_name<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("demangle class type");

        let n;
        ConsumeVal { value: n, mangled } = consume_count(mangled)?;

        if mangled.len() >= n {
            log::debug!("parse class name");
            ConsumeVal { mangled, .. } = self.demangle_arm_hp_template(mangled, n, declp)?;
            Ok(ConsumeVal { value: (), mangled })
        } else {
            log::debug!("malformed class type slug");
            anyhow::bail!("malformed class type slug");
        }
    }

    fn demangle_arm_hp_template<'a>(
        &mut self,
        mut mangled: &'a [u8],
        n: usize,
        declp: &'_ mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        let mut p = vec![];
        let mut args = vec![];

        if self.opts.style().hp() && mangled[n] == b'X' {
            log::debug!("demangle template as HP cfront style");
            todo!("implement hp cfront demangling");
        } else if self.arm_pt(mangled, n, &mut p, &mut args).is_ok() {
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
        Ok(ConsumeVal { value: (), mangled })
    }

    fn arm_pt<'a>(
        &'_ mut self,
        mut mangled: &'a [u8],
        n: usize,
        anchor: &'_ mut Vec<u8>,
        args: &'_ mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        let style = self.opts.style();

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
                if args[len..] == mangled[n..] && args[0] == b'_' {
                    args.splice(0..1, b"".iter().cloned());
                    return Ok(ConsumeVal { value: (), mangled });
                }
            }
        }
        if style.auto() || style.edg() {
            todo!("arm_pt: implement edg");
        }

        anyhow::bail!("arm_pt: unhandled case")
    }

    fn demangle_function_name<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
        scan: &'_ [u8],
    ) -> Result<ConsumeVal<'a, ()>> {
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
            log::debug!("demangle_function_name: hp style template");
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
                log::debug!("demangle_function_name: assignment operator");
                todo!("implement operator= demangle");
            } else {
                log::debug!("demangle_function_name: other operator");
                todo!("implement operator demangle");
            }
        } else if declp.len() >= 5 && declp[..4] == b"type"[..] && CPLUS_MARKERS.contains(&declp[4])
        {
            // type conversion operator
            log::debug!("demangle_function_name: type conversion operator");
            todo!("implement type conversion operator demangle");
        } else if declp.len() >= 4 && declp[0..4] == b"__op"[..] {
            // ansi type conversion operator
            log::debug!("demangle_function_name: ansi type conversion operator");
            todo!("implement ansi type conversion operator demangle");
        } else if declp.len() >= 4
            && declp[0..2] == b"__"[..]
            && declp[2].is_ascii_lowercase()
            && declp[3].is_ascii_lowercase()
        {
            log::debug!("demangle_function_name: operators");
            if declp.len() == 4 {
                // operator
                log::debug!("demangle_function_name: alt operator");

                let operator = OperatorKind::from_symbol_op(&declp[2..], self.opts.clone())?;
                declp.clear();
                declp.extend(b"operator");
                declp.extend(operator.overload_name());
            } else if declp[2] == b'a' && declp.len() == 6 {
                // assignment
                log::debug!("demangle_function_name: alt assignment");
                todo!("implement alt assignment demangle");
            }
        }

        Ok(ConsumeVal { mangled, value: () })
    }

    fn demangle_signature<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        let style = self.opts.style();
        let success = true;
        let mut expect_func = false;
        let mut expect_return_type = false;
        let mut func_done = false;
        let mut oldmangled = None;

        while success && !mangled.is_empty() {
            match mangled[0] {
                b'Q' => {
                    oldmangled = Some(mangled);

                    self.demangle_qualified(mangled, declp, true, false)?;
                    // self.types.push(value);
                    if style.auto() || style.gnu() {
                        expect_func = true;
                    }
                }
                b'K' => {
                    log::debug!("demangle signature: param K");
                    todo!("implement demangle K");
                }
                b'S' => {
                    log::debug!("demangle signature: param S");
                    todo!("implement demangle S");
                }
                b'C' | b'V' | b'u' => {
                    log::debug!("demangle signature: ansi qualifiers");
                    self.type_quals = TypeQualifiers::from_bits(
                        self.type_quals.into_bits()
                            | TypeQualifiers::from_code(mangled[0]).into_bits(),
                    );

                    // A qualified member function
                    if oldmangled.is_none() {
                        oldmangled = Some(mangled);
                    }
                    mangled = &mangled[1..];
                }
                b'L' => {
                    log::debug!("demangle signature: local class name");
                    todo!("implement demangle local class name");
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
                        self.types.push(oldmangled.into());

                        if (style.auto() || style.gnu() || style.edg())
                            && mangled.get(0) == Some(&b'F')
                        {
                            expect_func = true;
                        }
                    }
                    oldmangled = None;
                }
                b'B' => {
                    log::debug!("demangle signature: param B");
                    todo!("implement demangle B");
                }
                b'F' => {
                    log::debug!("demangle signature: param function");
                    oldmangled = None;
                    func_done = true;
                    mangled = &mangled[1..];

                    if style.lucid() || style.arm() || style.hp() || style.edg() {
                        todo!("implement forget_types");
                    }

                    ConsumeVal { mangled, .. } = self.demangle_args(mangled, declp)?;

                    if (style.auto() || style.edg()) && !mangled.is_empty() && mangled[0] == b'_' {
                        mangled = &mangled[1..];
                        // At this level, we don't care about the return type.
                        let mut tname = Vec::new();
                        self.do_type(mangled, &mut tname)?;
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

                    self.types.push(oldmangled2.into());

                    tname.extend(self.scope_str());
                    declp.prepend(&*tname);

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
                        ConsumeVal { mangled, .. } = self.do_type(mangled, &mut return_type)?;
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
                if style.lucid() || style.arm() || style.edg() {
                    self.types.clear();
                }
                ConsumeVal { mangled, .. } = self.demangle_args(mangled, declp)?;
                // Since template include the mangling of their return types,
                // we must set expect_func to 0 so that we don't try do
                // demangle more arguments the next time we get here.
                expect_func = false;
            }
        }

        if success && !func_done && (style.auto() || style.gnu()) {
            ConsumeVal { mangled, .. } = self.demangle_args(mangled, declp)?;
        }

        if success && self.opts.params() {
            if self.static_type {
                declp.extend(b" static");
            }
            if self.type_quals.into_bits() != 0 {
                append_blank(declp);
                declp.extend(self.type_quals.to_str().as_bytes())
            }
        }

        Ok(ConsumeVal { mangled, value: () })
    }

    fn demangle_args<'a>(
        &mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("demangle args");
        let style = self.opts.style();
        let mut arg: Vec<u8> = vec![];
        let mut need_comma = false;
        let mut t;
        let mut r;
        let mut temptype: u8;

        if self.opts.params() {
            declp.push(b'(');
            if mangled.is_empty() {
                declp.extend(b"void");
            }
        }

        let premangled = mangled;
        while !mangled.is_empty() {
            let b = mangled[0];
            if (b == b'_' || b == b'e') && self.nrepeats <= 0 {
                break;
            }

            if b == b'N' || b == b'T' {
                mangled = &mangled[1..];
                log::debug!("demangle_args: type parameter");
                temptype = *premangled
                    .get(1)
                    .context("missing character following arg prefix")?;

                if temptype == b'N' {
                    ConsumeVal { mangled, value: r } = get_count(mangled)?;
                } else {
                    r = 1;
                }

                if style.hp() || style.arm() || style.edg() && self.types.len() >= 10 {
                    // If we have 10 or more types we might have more than a 1 digit
                    // index so we'll have to consume the whole count here. This
                    // will lose if the next thing is a type name preceded by a
                    // count but it's impossible to demangle that case properly
                    // anyway. Eg if we already have 12 types is T12Pc "(..., type1,
                    // Pc, ...)"  or "(..., type12, char *, ...)"
                    ConsumeVal { mangled, value: t } = consume_count(mangled)?;
                } else {
                    ConsumeVal { mangled, value: t } = get_count(mangled)?;
                }
                if style.lucid() || style.arm() || style.hp() || style.edg() {
                    t -= 1;
                }
                // Validate the type index. Protect against illegal indices from
                // malformed type strings.
                if t >= self.types.len() {
                    log::error!("illegal type index {t} in type string");
                    anyhow::bail!("illegal type index {t} in type string");
                }
                while self.nrepeats > 0 || r > 0 {
                    r -= 1;
                    if need_comma && self.opts.params() {
                        declp.extend(b", ");
                    }

                    // Rust won't let us borrow a subfield while a mutable borrow occurs
                    // and we need `do_arg` to be generic about the source of the bytes
                    let tem = &*self.types[t].to_owned();
                    let _ = self.do_arg(tem, &mut arg)?;

                    if self.opts.params() {
                        declp.extend(&arg);
                    }
                    arg.clear();
                    need_comma = true;
                }
            } else {
                log::debug!("demangle_args: non-parameterised type");
                if need_comma && self.opts.params() {
                    declp.extend(b", ");
                }

                if log::log_enabled!(log::Level::Debug) {
                    let mangled_s =
                        std::str::from_utf8(mangled).expect("failed to deserialize mangled");
                    log::debug!("mangled after fund type: {mangled_s}");
                }

                ConsumeVal { mangled, .. } = self.do_arg(mangled, &mut arg)?;

                if self.opts.params() {
                    declp.extend(&arg);
                }
                arg.clear();
                need_comma = true;
            }
        }

        // variable args
        if let Some(b'e') = mangled.first() {
            log::debug!("demangle_args: varargs");
            mangled = &mangled[1..];

            if self.opts.params() {
                if need_comma {
                    declp.extend(b", ");
                }
                declp.extend(b"...");
            }
        }

        if self.opts.params() {
            declp.push(b')');
        }

        Ok(ConsumeVal { mangled, value: () })
    }

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
        self.btypes.remember(bindex, &class_name);
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

    fn do_arg<'a>(
        &mut self,
        mut mangled: &'a [u8],
        result: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("do_arg");
        let start = mangled;

        if self.nrepeats > 0 {
            log::debug!("do_arg: repeated type (count: {})", self.nrepeats);
            self.nrepeats -= 1;

            if !self.previous_argument.is_empty() {
                // We want to reissue the previous type in this argument list.
                result.extend(&self.previous_argument);
                return Ok(ConsumeVal { mangled, value: () });
            } else {
                anyhow::bail!("no previous argument to repeat");
            }
        }

        if mangled[0] == b'n' {
            log::debug!("do_arg: squangling repeat");
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

        let mut prev_arg = vec![];
        ConsumeVal { mangled, .. } = self.do_type(mangled, &mut prev_arg)?;
        self.previous_argument.extend(&prev_arg);
        result.extend(&self.previous_argument);

        let idx = memmem::find(start, mangled).context("failed to find arg start string")?;
        self.types.push(start[..idx].into());

        Ok(ConsumeVal { mangled, value: () })
    }

    fn demangle_template_value_parm<'a>(
        &mut self,
        mut mangled: &'a [u8],
        s: &mut Vec<u8>,
        ty_k: TypeKind,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("debug_template_value_parm: start");

        if !mangled.is_empty() && mangled[0] == b'Y' {
            log::debug!("debug_template_value_parm: template parameter");
            todo!("implement demangle_template_value_parm for template");
        } else if ty_k == TypeKind::Integral {
            ConsumeVal { mangled, .. } = self.demangle_integral_value(mangled, s)?;
        } else if ty_k == TypeKind::Char {
            todo!("implement demangle_template_value_parm for char");
        } else if ty_k == TypeKind::Bool {
            let value;
            ConsumeVal { mangled, value } = consume_count(mangled)?;
            let bool_val = match value {
                0 => &b"false"[..],
                1 => &b"true"[..],
                i => anyhow::bail!("invalid boolean literal value {i}"),
            };
            s.extend(bool_val);
            if log::log_enabled!(log::Level::Debug) {
                let s_s = std::str::from_utf8(mangled).expect("failed to deserialize s");
                log::debug!("s after bool: {s_s}");
            }
        } else if ty_k == TypeKind::Real {
            todo!("implement demangle_template_value_parm for floats");
        } else if [TypeKind::Pointer, TypeKind::Reference].contains(&ty_k) {
            if mangled[0] == b'Q' {
                ConsumeVal { mangled, .. } = self.demangle_qualified(mangled, s, false, true)?;
            } else {
                todo!("implement demangle_template_value_parm for unqualified types");
            }
        }

        log::debug!("debug_template_value_parm: done");

        Ok(ConsumeVal { mangled, value: () })
    }

    fn demangle_integral_value<'a>(
        &mut self,
        mut mangled: &'a [u8],
        s: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        log::debug!("demangle_integral_value: begin");

        if mangled.is_empty() {
            log::error!("demangle_integral_value: end of mangled string");
            anyhow::bail!("end of mangled string");
        }

        if mangled[0] == b'E' {
            log::debug!("demangle_integral_value: E");
            let mut need_operator = false;
            s.push(b'(');
            mangled = &mangled[1..];

            while !mangled.is_empty() && mangled[0] != b'W' {
                if need_operator {
                    todo!("implement demangle_integral_value operator");
                } else {
                    need_operator = true;
                }

                ConsumeVal { mangled, .. } =
                    self.demangle_template_value_parm(mangled, s, TypeKind::Integral)?;
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

        return Ok(ConsumeVal { mangled, value: () });
    }

    fn demangle_nested_args<'a>(
        &'_ mut self,
        mut mangled: &'a [u8],
        declp: &mut Vec<u8>,
    ) -> Result<ConsumeVal<'a, ()>> {
        // The G++ name-mangling algorithm does not remember types on nested
        // argument lists, unless -fsquangling is used, and in that case the
        // type vector updated by remember_type is not used.  So, we turn
        // off remembering of types here.
        self.forgetting_types += 1;

        let saved_previous_argument = self.previous_argument.clone();
        let saved_nrepeats = self.nrepeats;

        self.previous_argument = vec![];
        self.nrepeats = 0;

        // Actually demangle the args
        self.demangle_args(mangled, declp)?;

        // Restore the previous_argument field.
        self.previous_argument = saved_previous_argument;
        self.forgetting_types -= 1;
        self.nrepeats = saved_nrepeats;

        return Ok(ConsumeVal { mangled, value: () });
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

fn consume_count_with_underscores(mangled: &[u8]) -> Result<ConsumeVal<'_, usize>> {
    if mangled.starts_with(b"_") && mangled.ends_with(b"_") && mangled.len() > 1 {
        let end = 0.max(mangled.len() - 1);

        consume_count(&mangled[1..end])
    } else {
        anyhow::bail!("could not find surrounding underscores");
    }
}

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
