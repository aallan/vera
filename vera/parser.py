"""Vera parser — Lark LALR(1) frontend.

Parses .vera source into a Lark Tree, with LLM-oriented error diagnostics.
"""

from __future__ import annotations

from pathlib import Path
from typing import Optional

from lark import Lark, Tree
from lark.exceptions import LarkError

from vera.errors import ParseError, diagnose_lark_error

_GRAMMAR_PATH = Path(__file__).parent / "grammar.lark"

_parser: Optional[Lark] = None


def _get_parser() -> Lark:
    """Lazily construct the Lark parser (cached)."""
    global _parser
    if _parser is None:
        _parser = Lark(
            _GRAMMAR_PATH.read_text(),
            parser="lalr",
            start="start",
            propagate_positions=True,
        )
    return _parser


def parse(source: str, file: Optional[str] = None) -> Tree:
    """Parse Vera source code into a parse tree.

    Args:
        source: Vera source code as a string.
        file: Optional file path for error messages.

    Returns:
        A Lark Tree representing the parsed program.

    Raises:
        ParseError: If the source contains syntax errors.
            The error includes an LLM-oriented diagnostic with
            a description of the problem, the offending source line,
            a fix suggestion, and a spec reference.
    """
    parser = _get_parser()
    try:
        return parser.parse(source)
    except LarkError as exc:
        diagnostic = diagnose_lark_error(exc, source, file=file)
        raise ParseError(diagnostic) from exc


def parse_file(path: str | Path) -> Tree:
    """Parse a .vera file.

    Args:
        path: Path to the .vera file.

    Returns:
        A Lark Tree representing the parsed program.

    Raises:
        ParseError: If the file contains syntax errors.
        FileNotFoundError: If the file does not exist.
    """
    path = Path(path)
    source = path.read_text(encoding="utf-8")
    return parse(source, file=str(path))


def parse_to_ast(source: str, file: str | None = None):
    """Parse Vera source code directly to an AST.

    Args:
        source: Vera source code as a string.
        file: Optional file path for error messages.

    Returns:
        A Program AST node.

    Raises:
        ParseError: If the source contains syntax errors.
        TransformError: If the parse tree cannot be transformed.
    """
    from vera.transform import transform

    tree = parse(source, file=file)
    return transform(tree)
