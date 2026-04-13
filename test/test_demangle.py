import argparse
import json
import pathlib
import sys
from typing import Any

import demangle_gnuv2


class PathOrFileAction(argparse.Action):
    def __call__(self, parser, namespace, values, option_string=None):
        print('%r %r %r' % (namespace, values, option_string))
        setattr(namespace, self.dest, values)


class SymbolEncoder(json.JSONEncoder):
    def default(self, o: Any):
        if isinstance(o, demangle_gnuv2.DemangledSymbol):
            return self.encode_demangled_symbol(o)
        return super().default(o)

    def encode_demangled_symbol(self, sym: demangle_gnuv2.DemangledSymbol):
        return {
            "qualified_name": sym.qualified_name,
            "symbol_type": self.encode_symbol_type(sym.type)
        }

    def encode_symbol_type(self, type_: demangle_gnuv2.SymbolType):
        match type_:
            case demangle_gnuv2.SymbolType.VTable():
                return {"kind": "vtable"}
            case demangle_gnuv2.SymbolType.Function(args, return_type):
                # TODO: implement demangled_type
                return {
                    "kind": "function",
                    "args": list(map(lambda ty: self.encode_demangled_type(ty), args)),
                    "return_type": self.encode_demangled_type(return_type) if return_type is not None else None,
                }
            case demangle_gnuv2.SymbolType.StaticMember():
                return {"kind": "static_member"}
            case demangle_gnuv2.SymbolType.TypeInfo(type=inner):
                # TODO: implement demangled_type
                return {"kind": "type_info", "type": self.encode_type_info(inner)}
            case demangle_gnuv2.SymbolType.GlobalConstructor():
                return {"kind": "global_constructor"}
            case demangle_gnuv2.SymbolType.GlobalDestructor():
                return {"kind": "global_destructor"}
            case demangle_gnuv2.SymbolType.DllImportStub():
                return {"kind": "dllimport_stub"}
            case unknown:
                raise NotImplementedError(f"encode not implemented for SymbolType variant {type(unknown)}")

    def encode_type_info(self, inner: demangle_gnuv2.TypeInfoType):
        match inner:
            case demangle_gnuv2.TypeInfoType.Node:
                return {"type": "node"}
            case demangle_gnuv2.TypeInfoType.Function:
                return {"type": "function"}
            case unknown:
                raise NotImplementedError(f"encode not implemented for TypeInfoType variant {type(unknown)}")

    def encode_demangled_type(self, type_: demangle_gnuv2.DemangledType):
        match type_:
            case demangle_gnuv2.DemangledType.Void():
                return {"type": "void"}
            case demangle_gnuv2.DemangledType.Boolean():
                return {"type": "boolean"}
            case demangle_gnuv2.DemangledType.Int(signed):
                return {"type": "int", "signed": signed}
            case demangle_gnuv2.DemangledType.Short(signed):
                return {"type": "short", "signed": signed}
            case demangle_gnuv2.DemangledType.Char(signed):
                return {"type": "char", "signed": signed}
            case demangle_gnuv2.DemangledType.WideChar(signed):
                return {"type": "wchar", "signed": signed}
            case demangle_gnuv2.DemangledType.Long(signed):
                return {"type": "long", "signed": signed}
            case demangle_gnuv2.DemangledType.LongLong(signed):
                return {"type": "long_long", "signed": signed}
            case demangle_gnuv2.DemangledType.StdInt(bitwidth, signed):
                return {"type": "stdint", "bitwidth": bitwidth, "signed": signed}
            case demangle_gnuv2.DemangledType.Float():
                return {"type": "float"}
            case demangle_gnuv2.DemangledType.Double():
                return {"type": "double"}
            case demangle_gnuv2.DemangledType.LongDouble():
                return {"type": "long_double"}
            case demangle_gnuv2.DemangledType.Reference(const, restrict, inner):
                return {"type": "ref", "const": const, "restrict": restrict, "inner": self.encode_demangled_type(inner)}
            case demangle_gnuv2.DemangledType.Pointer(const, restrict, inner):
                return {"type": "ptr", "const": const, "restrict": restrict, "inner": self.encode_demangled_type(inner)}
            case demangle_gnuv2.DemangledType.Volatile(inner):
                return {"type": "volatile", "inner": self.encode_demangled_type(inner)}
            case demangle_gnuv2.DemangledType.ClassOrStruct(name, templated):
                return {"type": "class_or_struct", "name": name, "templated": templated}
            case demangle_gnuv2.DemangledType.Function(args, return_type):
                return {"type": "function", "args": list(map(lambda ty: self.encode_demangled_type(ty), args)), "return_type": self.encode_demangled_type(return_type) if return_type is not None else None}
            case demangle_gnuv2.DemangledType.VarArgs():
                return {"type": "var_args"}
            case unknown:
                 raise NotImplementedError(f"encode not implemented for DemangledType variant {type(unknown)}")

def main():
    script_path = pathlib.Path(sys.argv[0]).resolve()
    cur_dir = pathlib.Path(sys.argv[0]).resolve().parent
    test_fixtures_path = cur_dir / "c2e-syms.json"

    parser = argparse.ArgumentParser(
        prog=script_path.stem,
        description='Test the demangling against a set of fixtures')

    parser.add_argument('-i', '--input', type=argparse.FileType('r'), default=str(test_fixtures_path), help="file containing JSON test cases")
    parser.add_argument('-o', '--output', type=argparse.FileType('w+'), help="file to write detailed test suite info to")
    parser.add_argument('-j', '--json', default=False, action='store_true', help="output suite results in JSON format")
    parser.add_argument('-C', '--check', default=False, action='store_true', help="exit with error code if any tests fail")

    args = parser.parse_args()

    test_fixtures = json.load(args.input)["symbols"]

    results = []
    counts = {
        'success': 0,
        'mismatch': 0,
        'fail': 0,
        'panic': 0,
        'unknown': 0,
    }

    for test_case in test_fixtures:
        mangled = test_case['mangled']
        demangled = test_case['demangled']
        result = {"mangled": mangled, "expected": demangled}
        try:
            sym = demangle_gnuv2.cplus_demangle_v2(mangled)
            result["actual"] = sym.qualified_name
            result["success"] = result["expected"] == result["actual"]
            if result["success"]:
                counts["success"] += 1
            else:
                counts["mismatch"] += 1
                result["fail_reason"] = "MISMATCH"
            result["symbol_info"] = sym
        except:
            # PanicError isn't exposed from module so we can't catch it regularly
            exc, e1, e2 = sys.exc_info()
            result["actual"] = None
            result["success"] = False
            result["exc_info"] = str(e1)
            if isinstance(exc, TypeError) or exc is TypeError:
                counts["fail"] += 1
                result["fail_reason"] = "DEMANGLE_FAILED"
            elif exc.__module__ == "pyo3_runtime":
                counts["panic"] += 1
                result["fail_reason"] = "PANIC"
            else:
                counts["unknown"] += 1
                result["fail_reason"] = "UNKNOWN"

        if args.output:
            results.append(result)

    if args.output:
        json.dump({"results": results}, args.output, indent=2, cls=SymbolEncoder)

    all_failed = sum(counts.values()) - counts["success"]
    if args.json:
        json.dump(counts, sys.stdout)
    else:
        print(f"Results: {counts['success']} succeeded, {all_failed} failed")
        print("Failures:")
        print(f"\t{counts['mismatch']} mismatch(es)")
        print(f"\t{counts['fail']} demangle failure(s)")
        print(f"\t{counts['panic']} panic(s)")
        print(f"\t{counts['unknown']} unknown error(s)")
    if args.check and all_failed > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
