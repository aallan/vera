"""Vera command-line interface.

Usage:
    vera parse <file.vera>         Parse a file and print the tree
    vera check <file.vera>         Parse and report any errors
"""

from __future__ import annotations

import sys
from pathlib import Path

from vera.errors import VeraError
from vera.parser import parse_file


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
    """Parse a .vera file and report errors (no output on success)."""
    try:
        parse_file(path)
        print(f"OK: {path}")
        return 0
    except FileNotFoundError:
        print(f"Error: file not found: {path}", file=sys.stderr)
        return 1
    except VeraError as exc:
        print(exc.diagnostic.format(), file=sys.stderr)
        return 1


USAGE = """\
Usage: vera <command> <file>

Commands:
    parse   Parse a .vera file and print the parse tree
    check   Parse a .vera file and report errors
"""


def main() -> None:
    args = sys.argv[1:]

    if len(args) < 2:
        print(USAGE, file=sys.stderr)
        sys.exit(1)

    command, path = args[0], args[1]

    if command == "parse":
        sys.exit(cmd_parse(path))
    elif command == "check":
        sys.exit(cmd_check(path))
    else:
        print(f"Unknown command: {command}", file=sys.stderr)
        print(USAGE, file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
