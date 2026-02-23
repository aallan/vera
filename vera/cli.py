"""Vera command-line interface.

Usage:
    vera parse     <file.vera>         Parse a file and print the tree
    vera check     <file.vera>         Parse and type-check a file
    vera typecheck <file.vera>         Same as check (explicit alias)
    vera ast       <file.vera>         Parse and print the AST
    vera ast       --json <file.vera>  Parse and print the AST as JSON
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


def cmd_check(path: str) -> int:
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

        for w in warnings:
            print(f"warning: {w.format()}", file=sys.stderr)

        if errors:
            for e in errors:
                print(e.format(), file=sys.stderr)
            return 1

        print(f"OK: {path}")
        return 0
    except FileNotFoundError:
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
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
    parse          Parse a .vera file and print the parse tree
    check          Parse and type-check a .vera file
    typecheck      Same as check (explicit alias)
    ast            Parse a .vera file and print the AST
    ast --json     Parse a .vera file and print the AST as JSON
"""


def main() -> None:
    args = sys.argv[1:]

    if len(args) < 2:
        print(USAGE, file=sys.stderr)
        sys.exit(1)

    command = args[0]

    if command == "parse":
        sys.exit(cmd_parse(args[1]))
    elif command in ("check", "typecheck"):
        sys.exit(cmd_check(args[1]))
    elif command == "ast":
        if "--json" in args:
            remaining = [a for a in args[1:] if a != "--json"]
            if not remaining:
                print(USAGE, file=sys.stderr)
                sys.exit(1)
            sys.exit(cmd_ast(remaining[0], as_json=True))
        else:
            sys.exit(cmd_ast(args[1]))
    else:
        print(f"Unknown command: {command}", file=sys.stderr)
        print(USAGE, file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
