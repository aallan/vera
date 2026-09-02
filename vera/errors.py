"""Vera compiler diagnostics — LLM-oriented error reporting.

Every diagnostic is an instruction to the model that wrote the code.
See spec/00-introduction.md, Section 0.5 "Diagnostics as Instructions".
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from vera.lexical import CommentProblemKind


@dataclass
class SourceLocation:
    """A position in a Vera source file."""

    file: Optional[str] = None
    line: int = 0
    column: int = 0

    def __str__(self) -> str:
        parts = []
        if self.file:
            parts.append(self.file)
        parts.append(f"line {self.line}")
        parts.append(f"column {self.column}")
        return ", ".join(parts)

    def to_dict(self) -> dict[str, object]:
        """Machine-readable representation for JSON output."""
        d: dict[str, object] = {
            "line": self.line,
            "column": self.column,
        }
        if self.file:
            d["file"] = self.file
        return d


@dataclass
class Diagnostic:
    """A single compiler diagnostic.

    Every diagnostic includes:
      - description: what went wrong (plain English)
      - location: where in the source
      - source_line: the offending line of code
      - rationale: why this is an error (which language rule)
      - fix: concrete code showing the corrected form
      - spec_ref: specification chapter and section
    """

    description: str
    location: SourceLocation
    source_line: str = ""
    rationale: str = ""
    fix: str = ""
    spec_ref: str = ""
    severity: str = "error"
    error_code: str = ""
    # #222 Phase D: verification tier this diagnostic concerns, when
    # applicable.  3 on the Tier-3 fallback warnings (E520-E525, E532);
    # None elsewhere.  Surfaced in --json and the LSP diagnostic
    # payload so agents can rank edits by verification strength.
    tier: int | None = None

    def format(self) -> str:
        """Format as a natural language diagnostic for LLM consumption."""
        parts = []

        # Header with location
        loc = str(self.location)
        prefix = f"[{self.error_code}] " if self.error_code else ""
        parts.append(f"{prefix}{self.severity.title()} at {loc}:")

        # Source context with pointer
        if self.source_line:
            stripped = self.source_line.rstrip()
            parts.append("")
            parts.append(f"    {stripped}")
            if self.location.column > 0:
                pointer = " " * (self.location.column - 1 + 4) + "^"
                parts.append(pointer)

        # Description
        parts.append("")
        for line in self.description.splitlines():
            parts.append(f"  {line}")

        # Rationale
        if self.rationale:
            parts.append("")
            for line in self.rationale.splitlines():
                parts.append(f"  {line}")

        # Fix suggestion
        if self.fix:
            parts.append("")
            parts.append("  Fix:")
            parts.append("")
            for line in self.fix.splitlines():
                parts.append(f"    {line}")

        # Spec reference
        if self.spec_ref:
            parts.append("")
            parts.append(f"  See: {self.spec_ref}")

        return "\n".join(parts)

    def to_dict(self) -> dict[str, object]:
        """Machine-readable representation for JSON output."""
        d: dict[str, object] = {
            "severity": self.severity,
            "description": self.description,
            "location": self.location.to_dict(),
        }
        if self.source_line:
            d["source_line"] = self.source_line
        if self.rationale:
            d["rationale"] = self.rationale
        if self.fix:
            d["fix"] = self.fix
        if self.spec_ref:
            d["spec_ref"] = self.spec_ref
        if self.error_code:
            d["error_code"] = self.error_code
        if self.tier is not None:
            d["tier"] = self.tier
        return d


class VeraError(Exception):
    """Base exception for all Vera compiler errors."""

    def __init__(self, diagnostic: Diagnostic) -> None:
        self.diagnostic = diagnostic
        super().__init__(diagnostic.format())


class ParseError(VeraError):
    """A parse-phase error with LLM-oriented diagnostic."""

    pass


class TransformError(VeraError):
    """An error during Lark tree → AST transformation."""

    pass


class TypeError(VeraError):
    """A type-checking error."""

    pass


class VerifyError(VeraError):
    """A contract verification error."""

    pass


# =====================================================================
# Common parse error patterns
# =====================================================================

# Maps (expected_tokens, context) to error generators.
# Each generator receives the raw Lark exception info and returns
# a Diagnostic with a tailored message and fix suggestion.


def _get_source_line(source: str, line: int) -> str:
    """Extract a specific line from source text."""
    lines = source.splitlines()
    if 1 <= line <= len(lines):
        return lines[line - 1]
    return ""


def missing_contract_block(
    file: Optional[str], source: str, line: int, column: int
) -> Diagnostic:
    return Diagnostic(
        description=(
            "Function is missing its contract block. Every function in Vera "
            "must declare requires(), ensures(), and effects() clauses "
            "between the signature and the body."
        ),
        location=SourceLocation(file=file, line=line, column=column),
        source_line=_get_source_line(source, line),
        rationale=(
            "Vera requires all functions to have explicit contracts so that "
            "every function's behaviour is mechanically checkable."
        ),
        fix=(
            "Add a contract block after the signature:\n"
            "\n"
            "  private fn example(@Int -> @Int)\n"
            "    requires(true)\n"
            "    ensures(@Int.result >= 0)\n"
            "    effects(pure)\n"
            "  {\n"
            "    ...\n"
            "  }"
        ),
        spec_ref='Chapter 5, Section 5.2 "Function Declaration Syntax"',
        error_code="E001",
    )


# The illustrative E001 example shown in every doc mirror (README.md,
# docs/index.html, docs/index.md, spec/00-introduction.md) and used by
# tests/test_errors.py's TestErrorDisplaySync drift guard.  One example,
# one place: "which sample program illustrates E001" cannot fork across
# the docs because every mirror calls `render_e001_doc_example()` (or,
# for docs/index.html, `render_e001_doc_example_html()`) rather than
# hand-copying a rendering of it (#954).
E001_EXAMPLE_FILE = "main.vera"
E001_EXAMPLE_SOURCE = "private fn add(@Int, @Int -> @Int)\n{"
E001_EXAMPLE_LINE = 2
E001_EXAMPLE_COLUMN = 1


def e001_doc_example() -> Diagnostic:
    """The canonical E001 :class:`Diagnostic` every doc mirror renders."""
    return missing_contract_block(
        E001_EXAMPLE_FILE, E001_EXAMPLE_SOURCE, E001_EXAMPLE_LINE, E001_EXAMPLE_COLUMN
    )


def render_e001_doc_example() -> str:
    """Plain-text rendering of the canonical E001 example, byte-identical
    to what ``vera check`` prints for it (modulo trailing whitespace on
    otherwise-blank lines, stripped for the same reason a markdown
    fenced block shouldn't carry invisible trailing spaces).  Embedded
    verbatim in README.md, spec/00-introduction.md, and (via
    ``scripts/build_site.py``) docs/index.md."""
    text = e001_doc_example().format()
    return "\n".join(line.rstrip() for line in text.splitlines())


def render_e001_doc_example_html() -> str:
    """HTML rendering of the canonical E001 example for docs/index.html's
    ``<pre>`` sample block, wrapping each semantic piece of
    :meth:`Diagnostic.format` in the same ``err-*`` span classes the
    page's stylesheet already targets — the HTML mirror of
    :func:`render_e001_doc_example`, built from the same
    :class:`Diagnostic` rather than a hand-copied re-rendering of it.

    Mirrors :meth:`Diagnostic.format`'s own per-section indentation
    (a 2-space indent for the message, 4-space for the fix body) with
    one cosmetic difference: each span's OPENING line has its native
    indent moved to before the ``<span>`` tag rather than inside it —
    matching how the hand-written original was authored, with no
    rendered difference either way.
    """
    diag = e001_doc_example()
    parts: list[str] = [
        f'<span class="err-head">[{diag.error_code}] '
        f"Error at {diag.location}:</span>"
    ]
    if diag.source_line:
        stripped = diag.source_line.rstrip()
        parts.append("")
        parts.append(f'    <span class="err-code">{stripped}</span>')
        if diag.location.column > 0:
            pointer_indent = " " * (diag.location.column - 1 + 4)
            parts.append(f'{pointer_indent}<span class="err-caret">^</span>')

    msg_lines: list[str] = list(diag.description.splitlines())
    if diag.rationale:
        msg_lines.append("")
        msg_lines.extend(diag.rationale.splitlines())
    if msg_lines:
        parts.append("")
        first, *rest = msg_lines
        indented_rest = [f"  {line}" if line else "" for line in rest]
        content = "\n".join([first, *indented_rest])
        parts.append(f'  <span class="err-msg">{content}</span>')

    if diag.fix:
        parts.append("")
        fix_lines = ["Fix:", ""] + [
            f"    {line}" if line else "" for line in diag.fix.splitlines()
        ]
        parts.append(f'  <span class="err-fix">{chr(10).join(fix_lines)}</span>')

    if diag.spec_ref:
        parts.append("")
        parts.append(f'  <span class="err-ref">See: {diag.spec_ref}</span>')

    return "\n".join(parts)


def missing_effect_clause(
    file: Optional[str], source: str, line: int, column: int
) -> Diagnostic:
    return Diagnostic(
        description=(
            "Function is missing its effects() declaration. Every function "
            "in Vera must declare its effects explicitly."
        ),
        location=SourceLocation(file=file, line=line, column=column),
        source_line=_get_source_line(source, line),
        rationale=(
            "Vera is pure by default. All side effects must be declared in "
            "the function signature so the compiler can track them."
        ),
        fix=(
            "Add an effects clause after the contract block:\n"
            "\n"
            '  effects(pure)              -- for pure functions\n'
            '  effects(<IO>)              -- for functions with IO\n'
            '  effects(<State<Int>>)      -- for stateful functions\n'
            '  effects(<State<Int>, IO>)  -- for multiple effects'
        ),
        spec_ref='Chapter 5, Section 5.5 "Effect Declaration"',
        error_code="E002",
    )


def malformed_slot_reference(
    file: Optional[str], source: str, line: int, column: int, text: str
) -> Diagnostic:
    return Diagnostic(
        description=(
            f'Malformed slot reference "{text}". Slot references use the '
            "form @Type.index where Type starts with an uppercase letter "
            "and index is a non-negative integer."
        ),
        location=SourceLocation(file=file, line=line, column=column),
        source_line=_get_source_line(source, line),
        rationale=(
            "Vera uses typed De Bruijn indices (@T.n) instead of variable "
            "names. The type must match the binding site, and the index "
            "counts from the most recent binding of that type (0 = most recent)."
        ),
        fix=(
            "Use the correct slot reference form:\n"
            "\n"
            "  @Int.0     -- most recent Int binding\n"
            "  @Int.1     -- second most recent Int binding\n"
            "  @Bool.0    -- most recent Bool binding\n"
            "  @T.result  -- return value (in postconditions only)"
        ),
        spec_ref='Chapter 3, Section 3.1 "Overview"',
        error_code="E003",
    )


def unclosed_block(
    file: Optional[str], source: str, line: int, column: int
) -> Diagnostic:
    return Diagnostic(
        description=(
            'Expected closing brace "}". Every opening brace must have '
            "a matching closing brace."
        ),
        location=SourceLocation(file=file, line=line, column=column),
        source_line=_get_source_line(source, line),
        rationale=(
            "Vera requires mandatory braces on all blocks. There is no "
            "brace-optional syntax."
        ),
        fix=(
            'Add the missing "}" to close the block.'
        ),
        spec_ref='Chapter 10, Section 10.3.14 "Block Expressions"',
        error_code="E004",
    )


def module_call_dot_syntax(
    file: Optional[str],
    source: str,
    line: int,
    column: int,
) -> Diagnostic:
    """Diagnostic for old dot syntax in module-qualified calls."""
    return Diagnostic(
        description=(
            "Module-qualified calls use '::' between the module path "
            "and the function name, not '.'. "
            "Did you mean to use '::' syntax?"
        ),
        location=SourceLocation(file=file, line=line, column=column),
        source_line=_get_source_line(source, line),
        rationale=(
            "Vera uses '::' to separate the module path from the function "
            "name in module-qualified calls. The dot-separated module path "
            "is ambiguous with the function name in an LALR(1) grammar, so "
            "'::' provides an unambiguous delimiter."
        ),
        fix=(
            "Use '::' between the module path and the function name:\n"
            "\n"
            "  vera.math::abs(-5)\n"
            "  collections::sort([3, 1, 2])"
        ),
        spec_ref='Chapter 8, Section 8.5.3 "Module-Qualified Calls"',
        error_code="E008",
    )


def unexpected_token(
    file: Optional[str],
    source: str,
    line: int,
    column: int,
    token: str,
    expected: set[str],
) -> Diagnostic:
    """Fallback diagnostic for unexpected tokens not matching a known pattern."""
    expected_str = ", ".join(sorted(expected)[:8])
    if len(expected) > 8:
        expected_str += ", ..."

    return Diagnostic(
        description=(
            f'Unexpected "{token}" at this position. '
            f"Expected one of: {expected_str}"
        ),
        location=SourceLocation(file=file, line=line, column=column),
        source_line=_get_source_line(source, line),
        rationale=(
            "The parser reached this position expecting one of the listed "
            "tokens; the token found does not begin any construct valid here."
        ),
        fix=(
            "Replace the unexpected token with one of the expected tokens, "
            "or check for a missing delimiter (such as '}', ')', or ',') "
            "earlier in the construct."
        ),
        spec_ref='Chapter 10, "Formal Grammar"',
        error_code="E005",
    )


# `old` / `new` take an EFFECT reference (spec 7.9.2), so the grammar's
# `old_expr: "old" "(" effect_ref ")"` rejects an expression argument at
# parse time — several tokens to the right of the construct at fault.  A
# model reaching for Dafny's `old(<expr>)` got E005 "Unexpected @ ...
# Expected UPPER_IDENT" with the caret on its own argument (#1173,
# VeraBench VB-T5-009): nothing named `old`, and "expected UPPER_IDENT"
# described the parser's state rather than the misconception.
#
# Keyed by keyword; the value is (code, description, rationale, fix).
_CONTRACT_STATE_ARGS: dict[str, tuple[str, str, str, str]] = {
    "old": (
        "E030",
        "old() takes an effect reference, not an expression. Its only "
        "valid argument is the name of a stateful effect, as in "
        "old(State<Int>), and the call is only valid inside an ensures() "
        "clause.",
        "Vera has no mutable variables: a parameter slot or let binding "
        "holds one value for the whole call, so there is no separate "
        "before-value to ask for. Effect state is the only thing a call "
        "can change, which is why old() names an effect rather than "
        "wrapping an expression. The clause restriction follows from the "
        "same reasoning — requires() and decreases() are evaluated before "
        "the body runs, so every expression in them already observes the "
        "pre-state and old() would have nothing left to refer to.",
        "If you meant the value of a parameter, drop the wrapper — "
        "requires(@Int.0 > 0) says that directly, and the same slot "
        "reads identically in the postcondition. If you meant an "
        "effect's state before the call, name the effect inside an "
        "ensures() clause:\n"
        "\n"
        "  ensures(new(State<Int>) == old(State<Int>) + 1)",
    ),
    "new": (
        "E031",
        "new() takes an effect reference, not an expression. Its only "
        "valid argument is the name of a stateful effect, as in "
        "new(State<Int>), and the call is only valid inside an ensures() "
        "clause.",
        "Vera has no mutable variables: a parameter slot or let binding "
        "holds one value for the whole call, so there is no separate "
        "after-value to ask for. Effect state is the only thing a call "
        "can change, which is why new() names an effect rather than "
        "wrapping an expression. The clause restriction follows from the "
        "same reasoning — requires() and decreases() are evaluated before "
        "the body runs, so the after-state new() names does not exist "
        "yet at that point.",
        "If you meant the value of a parameter, drop the wrapper — "
        "ensures(@Int.result > @Int.0) relates the return value to the "
        "argument directly. If you meant an effect's state after the "
        "call, name the effect inside an ensures() clause:\n"
        "\n"
        "  ensures(new(State<Int>) == old(State<Int>) + 1)",
    ),
}

# Both keywords are three characters; the scan below relies on it.
_CONTRACT_STATE_KEYWORD_LEN = 3


def _line_column(source: str, offset: int) -> tuple[int, int]:
    """Convert a 0-based source offset to a 1-based (line, column)."""
    line = source.count("\n", 0, offset) + 1
    line_start = source.rfind("\n", 0, offset) + 1
    return line, offset - line_start + 1


def _contract_state_arg_at_fault(
    source: str, offset: int | None
) -> tuple[str, int] | None:
    """Is `offset` the first token of an `old(` / `new(` argument?

    Returns `(keyword, keyword_offset)`, or None when the failure is
    something else.  The scan is deliberately narrow: it fires only when
    nothing but whitespace separates the failing token from an `old(` /
    `new(` immediately to its left, which is exactly the position where
    the grammar demands an effect reference.  A failure anywhere later in
    the argument — `old(State<Int> > 0)`, whose real fault is the missing
    `)` — leaves a parsed token in between and falls through to the
    generic diagnostic rather than blaming the wrong construct.

    `source` is the original text while the offset comes from the
    comment-blanked copy `parse()` feeds the grammar. The two agree on
    every offset (blanking preserves length), and they differ in content
    only where a comment sits — so a comment wedged between `old` and its
    argument stops the scan here and falls through to E005. That is the
    conservative direction: a rarely written input keeps the old message
    instead of risking a wrong one.
    """
    if offset is None or not 0 <= offset <= len(source):
        return None
    i = offset - 1
    while i >= 0 and source[i] in " \t\r\n":
        i -= 1
    # A structural precondition, not a filter: everything below reads the
    # keyword as the token *before* `i`, which is only meaningful once `i`
    # is known to be the opening paren.  No input can prove it load-bearing
    # on its own — after the `old` keyword the grammar accepts nothing but
    # `(`, so the parser always fails on the very next token and `i` is
    # always either that paren or the keyword's own last character, and the
    # latter shifts the window off `old` anyway.  Keep it: dropping it would
    # leave the arithmetic below asserting something it never checked.
    if i < 0 or source[i] != "(":
        return None
    j = i - 1
    while j >= 0 and source[j] in " \t\r\n":
        j -= 1
    end = j + 1
    start = end - _CONTRACT_STATE_KEYWORD_LEN
    if start < 0:
        return None
    keyword = source[start:end]
    if keyword not in _CONTRACT_STATE_ARGS:
        return None
    # `keep_old(` ends in the same four characters but is a plain call.
    if start > 0 and (source[start - 1].isalnum() or source[start - 1] == "_"):
        return None
    return keyword, start


def contract_state_argument(
    file: Optional[str], source: str, keyword: str, keyword_offset: int
) -> Diagnostic:
    """Diagnostic for `old(<expr>)` / `new(<expr>)` (#1173)."""
    code, description, rationale, fix = _CONTRACT_STATE_ARGS[keyword]
    line, column = _line_column(source, keyword_offset)
    return Diagnostic(
        description=description,
        location=SourceLocation(file=file, line=line, column=column),
        source_line=_get_source_line(source, line),
        rationale=rationale,
        fix=fix,
        spec_ref='Chapter 7, Section 7.9.2 "State in Contracts"',
        error_code=code,
    )


_COMMENT_PROBLEMS = {
    "unterminated_block": (
        "E020",
        "Unterminated block comment. The `{-` opened here is never closed.",
        "Block comments nest, so each `{-` needs its own `-}`; this one's "
        "nesting never returns to depth zero, so the comment runs to the end "
        "of the file and swallows the code after it.",
        "Add a matching `-}` for this `{-`. A `{-` *inside* a block comment "
        "opens a nested comment that needs its own closer too. If you meant "
        "a block whose value is negative, separate the delimiters — write "
        "`{ -1 }`, because `{` immediately followed by `-` always opens a "
        "comment.",
    ),
    "unterminated_annotation": (
        "E021",
        "Unterminated annotation comment. The `/*` opened here has no "
        "closing `*/`.",
        "Annotation comments are delimited by `/*` and `*/`; without a "
        "closer the comment extends to the end of the file.",
        "Add a closing `*/`, or use `--` for a comment that runs to the end "
        "of the line.",
    ),
    "nested_annotation": (
        "E023",
        "Annotation comments do not nest. This `/*` sits inside an "
        "annotation comment that already closed at the first `*/`.",
        "Only block comments (`{- -}`) nest; an annotation comment ends at "
        "the first `*/`, so everything after it is parsed as code.",
        "Remove the inner `/*`, or use a block comment `{- ... {- ... -} "
        "... -}` if you need nesting.",
    ),
}


def diagnose_comment_problem(
    kind: CommentProblemKind,
    line: int,
    column: int,
    source: str,
    file: Optional[str] = None,
) -> Diagnostic:
    """Diagnostic for a malformed comment found during the pre-lex scan.

    Without these the grammar only sees the wreckage a malformed comment
    leaves behind and blames the wrong token — an unterminated `/*` is
    reported as an unexpected `/`.
    """
    code, description, rationale, fix = _COMMENT_PROBLEMS[kind]
    return Diagnostic(
        description=description,
        location=SourceLocation(file=file, line=line, column=column),
        source_line=_get_source_line(source, line),
        rationale=rationale,
        fix=fix,
        spec_ref='Chapter 1, Section 1.3 "Comments"',
        error_code=code,
    )


# =====================================================================
# Pattern matching for Lark exceptions
# =====================================================================


def diagnose_lark_error(
    exc: Exception,
    source: str,
    file: Optional[str] = None,
) -> Diagnostic:
    """Convert a Lark exception into an LLM-oriented Vera diagnostic.

    Attempts to match against known error patterns first, falling back
    to a generic diagnostic with the raw error info.
    """
    from lark.exceptions import UnexpectedCharacters, UnexpectedToken

    # Pattern: old(<expr>) / new(<expr>) — a contract state form applied
    # to an expression instead of an effect reference (#1173).  Checked
    # before the token-shaped patterns below because the argument can be
    # anything, including a character the lexer rejects outright
    # (`old($x)` raises UnexpectedCharacters, not UnexpectedToken).
    if isinstance(exc, (UnexpectedToken, UnexpectedCharacters)):
        at_fault = _contract_state_arg_at_fault(source, exc.pos_in_stream)
        if at_fault is not None:
            keyword, keyword_offset = at_fault
            return contract_state_argument(file, source, keyword, keyword_offset)

    if isinstance(exc, UnexpectedToken):
        line = exc.line
        column = exc.column
        token = str(exc.token)
        expected = set(exc.expected)

        # Pattern: missing contract block
        # After fn signature, parser expects "requires"/"ensures"/"decreases"
        # but got "{" (the body) or something else
        if token == "{" and expected & {"REQUIRES", "requires", "ENSURES", "ensures"}:  # noqa: S105
            return missing_contract_block(file, source, line, column)

        # Pattern: missing effects clause
        if expected & {"EFFECTS", "effects"}:
            return missing_effect_clause(file, source, line, column)

        # Pattern: old dot syntax for module-qualified calls
        # module_path consumed all idents including the fn name, parser
        # expects "::" (__ANON_9) but got "("
        if token == "(" and "__ANON_9" in expected:  # noqa: S105
            return module_call_dot_syntax(file, source, line, column)

        # Fallback
        return unexpected_token(file, source, line, column, token, expected)

    if isinstance(exc, UnexpectedCharacters):
        line = exc.line
        column = exc.column
        char = exc.char if hasattr(exc, "char") else "?"

        return Diagnostic(
            description=(
                f'Unexpected character "{char}". This character is not valid '
                "in Vera source code at this position."
            ),
            location=SourceLocation(file=file, line=line, column=column),
            source_line=_get_source_line(source, line),
            rationale=(
                "Vera's lexical grammar accepts only a fixed alphabet of "
                "characters; this character is not part of any token."
            ),
            fix=(
                "Remove the invalid character, or replace it with valid "
                "syntax (for example, use a string literal if the character "
                "was intended as text)."
            ),
            spec_ref='Chapter 1, "Lexical Structure"',
            error_code="E006",
        )

    # Unknown exception type — wrap it
    return Diagnostic(  # diag-fields-exempt: internal fallback for an unrecognised Lark exception; indicates a parser bug, not a user error, so no source-level fix or spec section applies.
        description=f"Internal parser error: {exc}",
        location=SourceLocation(file=file),
        error_code="E007",
    )


# =====================================================================
# Error code registry
# =====================================================================

ERROR_CODES: dict[str, str] = {
    # W0xx — Warnings
    "W001": "Typed hole",
    "W002": "Async argument evaluates eagerly",
    # E0xx — Parse & Transform
    "E001": "Missing contract block",
    "E002": "Missing effect clause",
    "E003": "Malformed slot reference",
    "E004": "Missing closing brace",
    "E005": "Unexpected token",
    "E006": "Unexpected character",
    "E007": "Internal parser error",
    "E008": "Module-qualified call uses dot instead of ::",
    "E009": "Invalid string escape sequence",
    "E010": "Unhandled grammar rule",
    # E01x — Module resolution
    "E011": "Circular import detected",
    "E012": "Cannot resolve import (no file found)",
    "E013": "Error parsing imported module",
    # E02x — Comments (lexical)
    "E020": "Unterminated block comment",
    "E021": "Unterminated annotation comment",
    "E023": "Annotation comments do not nest",
    # E03x — Contract constructs (parse)
    "E030": "old() argument is not an effect reference",
    "E031": "new() argument is not an effect reference",
    # E1xx — Type Checker: Core & Expressions
    "E120": "Data invariant not Bool",
    "E121": "Function body type mismatch",
    "E122": "Pure function performs effects",
    "E123": "Precondition predicate not Bool",
    "E124": "Postcondition predicate not Bool",
    "E125": "Call-site effect mismatch",
    "E126": "Refinement predicate not Bool",
    "E127": "Decreases measure not well-founded",
    "E128": "Quantifier bound not an integer",
    "E130": "Unresolved slot reference",
    "E131": "Result ref outside ensures",
    "E132": "Cyclic type alias",
    "E133": "Type alias arity mismatch",
    "E134": "Type does not take type arguments",
    "E135": "Array/Map/Set with a zero-size element, key, or value type",
    "E140": "Arithmetic requires numeric operands",
    "E141": "Arithmetic requires matching numeric types",
    "E142": "Cannot compare incompatible types",
    "E143": "Ordering requires orderable operands",
    "E144": "Logical operand not Bool (left)",
    "E145": "Logical operand not Bool (right)",
    "E146": "Unary not requires Bool",
    "E147": "Unary negate requires numeric",
    "E148": "Non-convertible type in string interpolation",
    "E149": "Integer literal out of range for its target type",
    "E150": "Cannot import private declaration",
    "E151": "Function redefines a built-in",
    "E152": "Effect redeclares a built-in effect",
    "E153": "Function name is reserved",
    "E154": "Name is reserved for the prelude",
    "E155": "Bare function name supplied by two imports",
    "E156": "Bare data type name supplied by two imports",
    "E157": "Bare constructor name supplied by two imports",
    "E160": "Array index must be Int or Nat",
    "E161": "Cannot index non-array type",
    "E170": "Let binding type mismatch",
    "E171": "Anonymous function body type mismatch",
    "E172": "Assert requires Bool",
    "E173": "Assume requires Bool",
    "E174": "old() outside ensures",
    "E175": "new() outside ensures",
    "E176": "Unknown expression type",
    "E178": "Bare call to a where-helper from outside its parent",
    "E180": "Unknown ability in constraint",
    "E181": "Constraint references undeclared type variable",
    "E182": "Slot reference to a zero-size type",
    "E183": "Let binding of a zero-size type",
    # E2xx — Type Checker: Calls
    "E200": "Unresolved function",
    "E201": "Wrong argument count",
    "E202": "Argument type mismatch",
    "E203": "Effect operation wrong argument count",
    "E204": "Effect operation argument type mismatch",
    "E205": "Conflicting type argument inference",
    "E206": "Generic type parameter instantiated at Unit",
    "E207": "Non-literal SQL argument",
    "E208": "SQL placeholder count mismatch",
    "E209": "Unsupported SQL placeholder syntax",
    "E210": "Unknown constructor",
    "E211": "Constructor is nullary",
    "E212": "Constructor wrong field count",
    "E213": "Constructor field type mismatch",
    "E214": "Unknown nullary constructor",
    "E215": "Constructor requires arguments",
    "E216": "Empty tuple type",
    "E217": "Bare effect operation must be qualified or handled",
    "E220": "Unresolved qualified call",
    "E230": "Module not found",
    "E231": "Function not imported from module",
    "E232": "Function is private in module",
    "E233": "Function not found in module",
    "E240": "Ability operation wrong argument count",
    "E241": "Ability operation argument type mismatch",
    "E242": "Ord ability operation on non-orderable type",
    "E243": "Eq ability operation on non-Eq-derivable type",
    # E3xx — Type Checker: Control Flow
    "E300": "If condition not Bool",
    "E301": "If branches incompatible types",
    "E302": "Match arm type mismatch",
    "E310": "Unreachable match arm",
    "E311": "Non-exhaustive match (ADT)",
    "E312": "Non-exhaustive match (Bool)",
    "E313": "Non-exhaustive match (infinite type)",
    "E314": "Pattern cannot match the scrutinee's type",
    "E320": "Unknown constructor in pattern",
    "E321": "Pattern constructor wrong arity",
    "E322": "Unknown nullary constructor in pattern",
    "E323": "Empty tuple pattern",
    "E330": "Unknown effect in handler",
    "E331": "Handler state type mismatch",
    "E332": "Effect has no such operation",
    "E333": "Handler with-state but no state declaration",
    "E334": "State update type name mismatch",
    "E335": "State update expression type mismatch",
    "E336": "Handler state diverges from the State<T> cell type",
    "E337": "Builtin effect handler type-argument arity",
    # E5xx — Verification
    "E500": "Postcondition verified false",
    "E501": "Call-site precondition violation",
    "E502": "@Nat subtraction underflow obligation not discharged",
    "E503": "@Nat binding-site narrowing may be negative",
    "E504": "@Nat narrowing unverified and not runtime-guarded",
    "E505": "Refinement predicate may be violated at narrowing site",
    "E506": "Refinement narrowing not statically verified (Tier-3)",
    "E507": "Assertion verified false",
    "E520": "Cannot verify contract (generic function with no concrete instantiation)",
    "E521": "Cannot verify precondition (undecidable)",
    "E522": "Cannot verify postcondition (body undecidable)",
    "E523": "Cannot verify postcondition (expression undecidable)",
    "E524": "Cannot verify postcondition (timeout)",
    "E525": "Cannot verify termination metric",
    "E526": "Division or modulo by zero",
    "E527": "Array index out of bounds",
    "E528": "Arithmetic overflow",
    "E529": "float_to_int domain (NaN, infinity, or out of i64 range)",
    "E530": "Nat-to-Int widening out of i64 range",
    "E531": "Nat-to-Int widening unverified and not runtime-guarded",
    "E532": "Cannot verify call-site precondition (undecidable)",
    "E533": "Instantiated handler state diverges from the State<T> cell type",
    # E6xx — Codegen
    "E600": "Unsupported parameter type",
    "E601": "Unsupported return type",
    "E602": "Unsupported body expression type",
    "E603": "Unsupported closure",
    "E604": "Unsupported state effect type",
    "E605": "Unsupported state type parameter",
    "E606": "State without proper effect declaration",
    "E607": "State with unsupported operations",
    "E608": "Name collision: function",
    "E609": "Name collision: ADT type",
    "E610": "Name collision: constructor",
    "E611": "Exn without type argument",
    "E612": "Exn with unsupported type",
    "E613": "Type does not satisfy ability constraint",
    "E614": "Program contains typed holes",
    "E615": "Cannot interpolate value of unknown type",
    "E616": "Cannot infer closure return type for call_indirect",
    "E617": "Refinement predicate not compilable to runtime guard",
    "E618": "Nested refinement base unsupported",
    "E619": "Cannot infer type argument for ability-constrained parameter",
    "E620": "Function dropped: skipped callee or no function table",
    "E621": "Name collision: module ADT contends with a prelude data type",
    "E622": "Cannot infer a generic call's type argument",
    "E699": "Internal compiler error",
    # E7xx — Testing
    "E700": "Contract violation during testing",
    "E701": "Cannot generate test inputs",
    "E702": "Test execution error",
}
