import json
import pathlib
import sys
import demangle_gnuv2
import argparse


class PathOrFileAction(argparse.Action):
    def __call__(self, parser, namespace, values, option_string=None):
        print('%r %r %r' % (namespace, values, option_string))
        setattr(namespace, self.dest, values)


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
        json.dump({"results": results}, args.output, indent=2)

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
