class DemangledSymbol:
    qualified_name: str

def cplus_demangle_v2(mangled: str, *, params: bool = True, ansi: bool = True) -> DemangledSymbol:
    pass
