"""Vera command-line interface.

Usage:
    vera parse     <file.vera>              Parse a file and print the tree
    vera check     <file.vera>              Parse and type-check a file
    vera check     --json <file.vera>       Type-check and output JSON diagnostics
    vera typecheck <file.vera>              Same as check (explicit alias)
    vera verify    <file.vera>              Type-check and verify contracts
    vera verify    --json <file.vera>       Verify and output JSON diagnostics
    vera compile   <file.vera>              Compile to .wasm binary
    vera compile   --wat <file.vera>        Print WAT text to stdout
    vera compile   -o out.wasm <file.vera>  Specify output path
    vera run       <file.vera>              Compile and execute
    vera run       --fn name <file.vera>    Execute a specific function
    vera run       <file.vera> -- 5 10      Pass arguments to the function
    vera ast       <file.vera>              Parse and print the AST
    vera ast       --json <file.vera>       Parse and print the AST as JSON
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from vera.errors import VeraError
from vera.parser import parse_file
from vera.transform import transform


def _is_int_str(s: str) -> bool:
    """Return True if *s* can be parsed as a Python int literal."""
    try:
        int(s)
        return True
    except ValueError:
        return False


def cmd_parse(path: str) -> int:
    """Parse a .vera file and print the parse tree."""
    try:
        tree = parse_file(path)
        print(tree.pretty())
        return 0
    except FileNotFoundError:
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1


def cmd_check(path: str, as_json: bool = False) -> int:
    """Parse, transform, and type-check a .vera file."""
    from vera.checker import typecheck

    try:
        p = Path(path)
        source = p.read_text(encoding="utf-8")
        tree = parse_file(path)
        ast = transform(tree)
        diagnostics = typecheck(ast, source, file=str(p))

        errors = [d for d in diagnostics if d.severity == "error"]
        warnings = [d for d in diagnostics if d.severity == "warning"]

        if as_json:
            result = {
                "ok": len(errors) == 0,
                "file": path,
                "diagnostics": [e.to_dict() for e in errors],
                "warnings": [w.to_dict() for w in warnings],
            }
            print(json.dumps(result, indent=2))
            return 1 if errors else 0

        for w in warnings:
            print(f"warning: {w.format()}", file=sys.stderr)

        if errors:
            for e in errors:
                print(e.format(), file=sys.stderr)
            return 1

        print(f"OK: {path}")
        return 0
    except FileNotFoundError:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [{"severity": "error",
                                               "description": f"file not found: {path}",
                                               "location": {"line": 0, "column": 0}}],
                              "warnings": []}, indent=2))
            return 1
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [exc.diagnostic.to_dict()],
                              "warnings": []}, indent=2))
            return 1
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1


def cmd_verify(path: str, as_json: bool = False) -> int:
    """Parse, transform, type-check, and verify a .vera file."""
    from vera.checker import typecheck
    from vera.verifier import verify

    try:
        p = Path(path)
        source = p.read_text(encoding="utf-8")
        tree = parse_file(path)
        ast = transform(tree)

        # First type-check
        type_diags = typecheck(ast, source, file=str(p))
        type_errors = [d for d in type_diags if d.severity == "error"]
        type_warnings = [d for d in type_diags if d.severity == "warning"]

        if type_errors:
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in type_errors],
                    "warnings": [w.to_dict() for w in type_warnings],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            for e in type_errors:
                print(e.format(), file=sys.stderr)
            return 1

        # Then verify contracts
        result = verify(ast, source, file=str(p))

        errors = [d for d in result.diagnostics if d.severity == "error"]
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        all_warnings = type_warnings + warnings

        if as_json:
            s = result.summary
            result_dict = {
                "ok": len(errors) == 0,
                "file": path,
                "diagnostics": [e.to_dict() for e in errors],
                "warnings": [w.to_dict() for w in all_warnings],
                "verification": {
                    "tier1_verified": s.tier1_verified,
                    "tier3_runtime": s.tier3_runtime,
                    "total": s.total,
                },
            }
            print(json.dumps(result_dict, indent=2))
            return 1 if errors else 0

        for w in all_warnings:
            print(f"warning: {w.format()}", file=sys.stderr)

        if errors:
            for e in errors:
                print(e.format(), file=sys.stderr)
            return 1

        # Print success with summary
        s = result.summary
        parts = []
        if s.tier1_verified:
            parts.append(f"{s.tier1_verified} verified (Tier 1)")
        if s.tier3_runtime:
            parts.append(f"{s.tier3_runtime} runtime checks (Tier 3)")
        summary_str = ", ".join(parts) if parts else "no contracts"

        print(f"OK: {path}")
        print(f"Verification: {summary_str}")
        return 0
    except FileNotFoundError:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [{"severity": "error",
                                               "description": f"file not found: {path}",
                                               "location": {"line": 0, "column": 0}}],
                              "warnings": []}, indent=2))
            return 1
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [exc.diagnostic.to_dict()],
                              "warnings": []}, indent=2))
            return 1
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1


def cmd_compile(
    path: str,
    *,
    as_json: bool = False,
    wat: bool = False,
    output: str | None = None,
) -> int:
    """Parse, type-check, and compile a .vera file to WebAssembly."""
    from vera.checker import typecheck
    from vera.codegen import compile as codegen_compile

    try:
        p = Path(path)
        source = p.read_text(encoding="utf-8")
        tree = parse_file(path)
        ast = transform(tree)

        # Type-check first
        type_diags = typecheck(ast, source, file=str(p))
        type_errors = [d for d in type_diags if d.severity == "error"]
        type_warnings = [d for d in type_diags if d.severity == "warning"]

        if type_errors:
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in type_errors],
                    "warnings": [w.to_dict() for w in type_warnings],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            for e in type_errors:
                print(e.format(), file=sys.stderr)
            return 1

        # Compile
        result = codegen_compile(ast, source=source, file=str(p))

        errors = [d for d in result.diagnostics if d.severity == "error"]
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        all_warnings = type_warnings + warnings

        if errors:
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in errors],
                    "warnings": [w.to_dict() for w in all_warnings],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            for e in errors:
                print(e.format(), file=sys.stderr)
            return 1

        if as_json:
            result_dict = {
                "ok": True,
                "file": path,
                "exports": result.exports,
                "diagnostics": [],
                "warnings": [w.to_dict() for w in all_warnings],
            }
            print(json.dumps(result_dict, indent=2))
            return 0

        # Print warnings
        for w in all_warnings:
            print(f"warning: {w.format()}", file=sys.stderr)

        # Output mode: --wat prints WAT text, otherwise write .wasm binary
        if wat:
            print(result.wat)
            return 0

        # Write .wasm binary
        out_path = Path(output) if output else p.with_suffix(".wasm")
        out_path.write_bytes(result.wasm_bytes)
        n = len(result.exports)
        plural = "s" if n != 1 else ""
        print(f"Compiled: {out_path} ({n} function{plural} exported)")
        return 0

    except FileNotFoundError:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [{"severity": "error",
                                               "description": f"file not found: {path}",
                                               "location": {"line": 0, "column": 0}}],
                              "warnings": []}, indent=2))
            return 1
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [exc.diagnostic.to_dict()],
                              "warnings": []}, indent=2))
            return 1
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1


def cmd_run(
    path: str,
    *,
    as_json: bool = False,
    fn_name: str | None = None,
    fn_args: list[int] | None = None,
) -> int:
    """Parse, type-check, compile, and execute a .vera file."""
    from vera.checker import typecheck
    from vera.codegen import compile as codegen_compile, execute

    try:
        p = Path(path)
        source = p.read_text(encoding="utf-8")
        tree = parse_file(path)
        ast = transform(tree)

        # Type-check
        type_diags = typecheck(ast, source, file=str(p))
        type_errors = [d for d in type_diags if d.severity == "error"]

        if type_errors:
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in type_errors],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            for e in type_errors:
                print(e.format(), file=sys.stderr)
            return 1

        # Compile
        result = codegen_compile(ast, source=source, file=str(p))

        if not result.ok:
            errors = [d for d in result.diagnostics if d.severity == "error"]
            if as_json:
                result_dict = {
                    "ok": False,
                    "file": path,
                    "diagnostics": [e.to_dict() for e in errors],
                }
                print(json.dumps(result_dict, indent=2))
                return 1
            for e in errors:
                print(e.format(), file=sys.stderr)
            return 1

        # Execute
        exec_result = execute(result, fn_name=fn_name, args=fn_args)

        if as_json:
            result_dict = {
                "ok": True,
                "file": path,
                "function": fn_name or (
                    "main" if "main" in result.exports
                    else result.exports[0] if result.exports else None
                ),
                "value": exec_result.value,
                "stdout": exec_result.stdout,
            }
            print(json.dumps(result_dict, indent=2))
            return 0

        # Print stdout from IO.print calls
        if exec_result.stdout:
            sys.stdout.write(exec_result.stdout)
            # Add newline if stdout doesn't end with one
            if not exec_result.stdout.endswith("\n"):
                sys.stdout.write("\n")

        # Print return value if it's not None (non-Unit function)
        elif exec_result.value is not None:
            print(exec_result.value)

        return 0

    except FileNotFoundError:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [{"severity": "error",
                                               "description": f"file not found: {path}",
                                               "location": {"line": 0, "column": 0}}]}
                              , indent=2))
            return 1
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [exc.diagnostic.to_dict()]}
                              , indent=2))
            return 1
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1
    except RuntimeError as exc:
        if as_json:
            print(json.dumps({"ok": False, "file": path,
                              "diagnostics": [{"severity": "error",
                                               "description": str(exc),
                                               "location": {"line": 0, "column": 0}}]}
                              , indent=2))
            return 1
        print(f"Error: {exc}", file=sys.stderr)
        return 1
    except Exception as exc:
        # Catch WASM traps (wasmtime.Trap, wasmtime.WasmtimeError)
        # without importing wasmtime at module level.
        exc_name = type(exc).__name__
        if exc_name in ("Trap", "WasmtimeError"):
            msg = f"Runtime contract violation: {exc}"
            if as_json:
                print(json.dumps({"ok": False, "file": path,
                                  "diagnostics": [{"severity": "error",
                                                   "description": msg,
                                                   "location": {"line": 0, "column": 0}}]}
                                  , indent=2))
                return 1
            print(f"Error: {msg}", file=sys.stderr)
            return 1
        raise  # re-raise unexpected exceptions


def cmd_ast(path: str, as_json: bool = False) -> int:
    """Parse a .vera file and print the AST."""
    try:
        tree = parse_file(path)
        ast = transform(tree)
        if as_json:
            print(json.dumps(ast.to_dict(), indent=2))
        else:
            print(ast.pretty())
        return 0
    except FileNotFoundError:
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1


USAGE = """\
Usage: vera <command> [options] <file>

Commands:
    parse                Parse a .vera file and print the parse tree
    check [--json]       Parse and type-check a .vera file
    typecheck [--json]   Same as check (explicit alias)
    verify [--json]      Parse, type-check, and verify contracts
    compile [--wat]      Compile a .vera file to WebAssembly
    run [--fn name]      Compile and execute a .vera file
    ast [--json]         Parse a .vera file and print the AST

Options:
    --json               Output machine-readable JSON diagnostics
    --wat                Print WAT text instead of writing .wasm binary
    --fn <name>          Function to execute (default: main or first export)
    -o <path>            Output path for .wasm binary
    -- <args...>         Arguments to pass to the executed function
"""


def main() -> None:
    args = sys.argv[1:]

    if len(args) < 2:
        print(USAGE, file=sys.stderr)
        sys.exit(1)

    command = args[0]
    use_json = "--json" in args
    use_wat = "--wat" in args

    # Parse --fn <name> option
    fn_name: str | None = None
    if "--fn" in args:
        fn_idx = args.index("--fn")
        if fn_idx + 1 < len(args):
            fn_name = args[fn_idx + 1]

    # Parse -o <path> option
    output_path: str | None = None
    if "-o" in args:
        o_idx = args.index("-o")
        if o_idx + 1 < len(args):
            output_path = args[o_idx + 1]

    # Parse -- <args> for run command
    fn_args: list[int] | None = None
    if "--" in args:
        dash_idx = args.index("--")
        raw_args = args[dash_idx + 1:]
        if raw_args:
            try:
                fn_args = [int(a) for a in raw_args]
            except ValueError:
                bad = [a for a in raw_args if not _is_int_str(a)]
                msg = f"Invalid integer argument(s): {', '.join(bad)}"
                if use_json:
                    print(json.dumps({"ok": False, "file": "",
                                      "diagnostics": [{"severity": "error",
                                                       "description": msg}]},
                                     indent=2))
                else:
                    print(f"Error: {msg}", file=sys.stderr)
                sys.exit(1)

    # Remove flags from remaining args to find the filepath
    skip_flags = {"--json", "--wat"}
    skip_next = {"--fn", "-o"}
    remaining: list[str] = []
    i = 1  # skip command
    while i < len(args):
        if args[i] == "--":
            break  # everything after -- is function args
        if args[i] in skip_flags:
            i += 1
            continue
        if args[i] in skip_next:
            i += 2  # skip flag + value
            continue
        remaining.append(args[i])
        i += 1

    if not remaining:
        print(USAGE, file=sys.stderr)
        sys.exit(1)

    filepath = remaining[0]

    if command == "parse":
        sys.exit(cmd_parse(filepath))
    elif command in ("check", "typecheck"):
        sys.exit(cmd_check(filepath, as_json=use_json))
    elif command == "verify":
        sys.exit(cmd_verify(filepath, as_json=use_json))
    elif command == "compile":
        sys.exit(cmd_compile(
            filepath, as_json=use_json, wat=use_wat, output=output_path
        ))
    elif command == "run":
        sys.exit(cmd_run(
            filepath, as_json=use_json, fn_name=fn_name, fn_args=fn_args
        ))
    elif command == "ast":
        sys.exit(cmd_ast(filepath, as_json=use_json))
    else:
        print(f"Unknown command: {command}", file=sys.stderr)
        print(USAGE, file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
