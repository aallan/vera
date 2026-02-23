"""Vera command-line interface.

Usage:
    vera parse     <file.vera>              Parse a file and print the tree
    vera check     <file.vera>              Parse and type-check a file
    vera check     --json <file.vera>       Type-check and output JSON diagnostics
    vera typecheck <file.vera>              Same as check (explicit alias)
    vera verify    <file.vera>              Type-check and verify contracts
    vera verify    --json <file.vera>       Verify and output JSON diagnostics
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
    ast [--json]         Parse a .vera file and print the AST

Options:
    --json               Output machine-readable JSON diagnostics
"""


def main() -> None:
    args = sys.argv[1:]

    if len(args) < 2:
        print(USAGE, file=sys.stderr)
        sys.exit(1)

    command = args[0]
    use_json = "--json" in args
    remaining = [a for a in args[1:] if a != "--json"]

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
    elif command == "ast":
        sys.exit(cmd_ast(filepath, as_json=use_json))
    else:
        print(f"Unknown command: {command}", file=sys.stderr)
        print(USAGE, file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
