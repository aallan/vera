"""Vera parser — Lark LALR(1) frontend.

Parses .vera source into a Lark Tree, with LLM-oriented error diagnostics.
"""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, Any, Optional

if TYPE_CHECKING:
    from vera.verifier import VerifyResult

from lark import Lark, Tree
from lark.exceptions import LarkError

from vera.errors import (
    Diagnostic,
    ParseError,
    diagnose_comment_problem,
    diagnose_lark_error,
)
from vera.lexical import (
    ANNOTATIONS_ATTR,
    annotation_labels,
    blank_block_comments,
    find_comment_problems,
)

_GRAMMAR_PATH = Path(__file__).parent / "grammar.lark"

_parser: Optional[Lark] = None


def _get_parser() -> Lark:
    """Lazily construct the Lark parser (cached)."""
    global _parser
    if _parser is None:
        # Explicit UTF-8 so users on Windows without PYTHONUTF8=1
        # in their shell still get correct grammar loading (the
        # default locale-encoded read would be cp1252 in en-US
        # Windows; harmless for the current pure-ASCII grammar
        # but defensive for future grammar additions).  See #641
        # for the broader cp1252 audit context.
        _parser = Lark(
            _GRAMMAR_PATH.read_text(encoding="utf-8"),
            parser="lalr",
            start="start",
            propagate_positions=True,
        )
    return _parser


def parse(source: str, file: Optional[str] = None) -> Tree[Any]:
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
    # Block comments nest (spec 1.3), which a regular expression cannot
    # express — so they are resolved before the grammar sees the source
    # (#1112).  Blanking preserves length and line structure exactly, so
    # `propagate_positions` offsets, every diagnostic's line/column, and
    # the formatter's span-based comment attachment all stay faithful.
    # A malformed comment is diagnosed here rather than left to the
    # grammar.  The grammar only ever sees the wreckage — an
    # unterminated `/*` reaches it as a stray `/` — so it blames the
    # wrong token, several lines from the delimiter that actually
    # caused the problem (E020/E021/E023).
    for problem in find_comment_problems(source):
        raise ParseError(diagnose_comment_problem(
            problem.kind, problem.line, problem.column, source, file=file,
        ))
    prepared, _ = blank_block_comments(source)
    try:
        tree = parser.parse(prepared)
    except LarkError as exc:
        # Diagnose against the ORIGINAL source: the blanked copy would
        # quote a line of spaces back at the user.
        diagnostic = diagnose_lark_error(exc, source, file=file)
        raise ParseError(diagnostic) from exc

    # Annotation comments are `%ignore`d, so they never reach the tree —
    # but spec 1.3 requires them in the AST.  Carrying them on the parse
    # result lets `transform()` attach them without taking a `source`
    # argument, which would mean updating every one of its call sites and
    # leaving a future caller free to omit it and silently lose labels on
    # that path.  `setattr` because the attribute belongs to Lark's Tree,
    # which we do not own; `transform()` reads it back by the same name.
    setattr(tree, ANNOTATIONS_ATTR, annotation_labels(source))
    return tree


def parse_file(path: str | Path) -> Tree[Any]:
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


def parse_to_ast(source: str, file: str | None = None) -> Any:
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


def verify_file(path: str | Path) -> "VerifyResult":
    """Parse, transform, type-check, and verify a .vera file.

    Args:
        path: Path to the .vera file.

    Returns:
        A VerifyResult with diagnostics and a verification summary.

    Raises:
        ParseError: If the file contains syntax errors.
        TransformError: If the parse tree cannot be transformed.
        FileNotFoundError: If the file does not exist.
    """
    from vera.checker import typecheck
    from vera.resolver import ModuleResolver
    from vera.transform import transform
    from vera.verifier import verify

    path = Path(path)
    source = path.read_text(encoding="utf-8")
    tree = parse(source, file=str(path))
    ast = transform(tree)
    # Resolve imports as `vera verify` does, so an imported name means the
    # declaration it names here too (#1513).
    resolved = ModuleResolver(_root=path.parent).resolve_imports(ast, path)
    # Type-check first (verify expects a valid AST)
    typecheck(ast, source, file=str(path), resolved_modules=resolved)
    return verify(ast, source, file=str(path), resolved_modules=resolved)


def typecheck_file(path: str | Path) -> list[Diagnostic]:
    """Parse, transform, and type-check a .vera file.

    Args:
        path: Path to the .vera file.

    Returns:
        A list of Diagnostic objects (empty if no issues found).

    Raises:
        ParseError: If the file contains syntax errors.
        TransformError: If the parse tree cannot be transformed.
        FileNotFoundError: If the file does not exist.
    """
    from vera.checker import typecheck
    from vera.resolver import ModuleResolver
    from vera.transform import transform

    path = Path(path)
    source = path.read_text(encoding="utf-8")
    tree = parse(source, file=str(path))
    ast = transform(tree)
    # Resolve imports as `vera check` does (#1513): an unresolved call is an
    # error, so a module-blind check would report every imported name.
    resolver = ModuleResolver(_root=path.parent)
    resolved = resolver.resolve_imports(ast, path)
    return resolver.errors + typecheck(
        ast, source, file=str(path), resolved_modules=resolved,
    )
