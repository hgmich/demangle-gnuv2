import typing
from abc import ABCMeta

class TypeInfoType:
    Node: typing.ClassVar[TypeInfoType]
    Function: typing.ClassVar[TypeInfoType]

class DemangledType(metaclass=ABCMeta):
    Void: typing.ClassVar[type[DemangledType_Void]]
    Boolean: typing.ClassVar[type[DemangledType_Boolean]]
    Int: typing.ClassVar[type[DemangledType_Int]]
    Short: typing.ClassVar[type[DemangledType_Short]]
    Char: typing.ClassVar[type[DemangledType_Char]]
    WideChar: typing.ClassVar[type[DemangledType_WideChar]]
    Long: typing.ClassVar[type[DemangledType_Long]]
    LongLong: typing.ClassVar[type[DemangledType_LongLong]]
    StdInt: typing.ClassVar[type[DemangledType_StdInt]]
    Float: typing.ClassVar[type[DemangledType_Float]]
    Double: typing.ClassVar[type[DemangledType_Double]]
    LongDouble: typing.ClassVar[type[DemangledType_LongDouble]]
    Reference: typing.ClassVar[type[DemangledType_Reference]]
    Pointer: typing.ClassVar[type[DemangledType_Pointer]]
    Volatile: typing.ClassVar[type[DemangledType_Volatile]]
    ClassOrStruct: typing.ClassVar[type[DemangledType_ClassOrStruct]]
    Function: typing.ClassVar[type[DemangledType_Function]]

class DemangledType_Void(DemangledType):
    __match_args__ = ()

class DemangledType_Boolean(DemangledType):
    __match_args__ = ()

class DemangledType_Int(DemangledType):
    __match_args__ = ("signed",)

    signed: bool

class DemangledType_Short(DemangledType):
    __match_args__ = ("signed",)

    signed: bool

class DemangledType_Char(DemangledType):
    __match_args__ = ("signed",)

    signed: bool | None

class DemangledType_WideChar(DemangledType):
    __match_args__ = ("signed",)

    signed: bool | None

class DemangledType_Long(DemangledType):
    __match_args__ = ("signed",)

    signed: bool

class DemangledType_LongLong(DemangledType):
    __match_args__ = ("signed",)

    signed: bool

class DemangledType_StdInt(DemangledType):
    __match_args__ = ("bitwidth", "signed")

    bitwidth: int
    signed: bool

class DemangledType_Float(DemangledType):
    __match_args__ = ()

class DemangledType_Double(DemangledType):
    __match_args__ = ()

class DemangledType_LongDouble(DemangledType):
    __match_args__ = ()

class DemangledType_Reference(DemangledType):
    __match_args__ = ("const", "restrict", "inner")

    const: bool
    restrict: bool
    inner: DemangledType

class DemangledType_Pointer(DemangledType):
    __match_args__ = ("const", "restrict", "inner")

    const: bool
    restrict: bool
    inner: DemangledType

class DemangledType_Volatile(DemangledType):
    __match_args__ = ("inner",)

    inner: DemangledType

class DemangledType_ClassOrStruct(DemangledType):
    __match_args__ = ("name", "templated")

    name: str
    templated: bool

class DemangledType_Function(DemangledType):
    __match_args__ = ("args", "return_type", "const", "has_varargs")

    args: list[DemangledType]
    return_type: DemangledType | None
    const: bool
    has_varargs: bool

class SymbolType(metaclass=ABCMeta):
    VTable: typing.ClassVar[type[SymbolType_VTable]]
    Function: typing.ClassVar[type[SymbolType_Function]]
    StaticMember: typing.ClassVar[type[SymbolType_StaticMember]]
    TypeInfo: typing.ClassVar[type[SymbolType_TypeInfo]]
    GlobalConstructor: typing.ClassVar[type[SymbolType_GlobalConstructor]]
    GlobalDestructor: typing.ClassVar[type[SymbolType_GlobalDestructor]]
    DllImportStub: typing.ClassVar[type[SymbolType_DllImportStub]]

class SymbolType_VTable(SymbolType):
    __match_args__ = ()

class SymbolType_Function(SymbolType):
    __match_args__ = ("qualified_name", "args", "return_type", "const", "has_varargs")

    qualified_name: str
    args: list[DemangledType]
    return_type: DemangledType | None
    const: bool
    has_varargs: bool

class SymbolType_StaticMember(SymbolType):
    __match_args__ = ()

class SymbolType_TypeInfo(SymbolType):
    __match_args__ = ("type",)

    type: TypeInfoType

class SymbolType_GlobalConstructor(SymbolType):
    __match_args__ = ()

class SymbolType_GlobalDestructor(SymbolType):
    __match_args__ = ()

class SymbolType_DllImportStub(SymbolType):
    __match_args__ = ()

class DemangledSymbol:
    cxxdecl: str
    type: SymbolType

def cplus_demangle_v2(
    mangled: str, *, params: bool = True, ansi: bool = True
) -> DemangledSymbol: ...
