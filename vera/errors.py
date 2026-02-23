"""Vera compiler diagnostics — LLM-oriented error reporting.

Every diagnostic is an instruction to the model that wrote the code.
See spec/00-introduction.md, Section 0.5 "Diagnostics as Instructions".
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


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

    def format(self) -> str:
        """Format as a natural language diagnostic for LLM consumption."""
        parts = []

        # Header with location
        loc = str(self.location)
        parts.append(f"{self.severity.title()} at {loc}:")

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


class VeraError(Exception):
    """Base exception for all Vera compiler errors."""

    def __init__(self, diagnostic: Diagnostic) -> None:
        self.diagnostic = diagnostic
        super().__init__(diagnostic.format())


class ParseError(VeraError):
    """A parse-phase error with LLM-oriented diagnostic."""

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
            "  fn example(@Int -> @Int)\n"
            "    requires(true)\n"
            "    ensures(@Int.result >= 0)\n"
            "    effects(pure)\n"
            "  {\n"
            "    ...\n"
            "  }"
        ),
        spec_ref='Chapter 5, Section 5.1 "Function Structure"',
    )


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
        spec_ref='Chapter 7, Section 7.1 "Effect Declarations"',
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
        spec_ref='Chapter 3, Section 3.1 "Slot Reference Syntax"',
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
        spec_ref='Chapter 1, Section 1.6 "Canonical Formatting"',
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

    if isinstance(exc, UnexpectedToken):
        line = exc.line
        column = exc.column
        token = str(exc.token)
        expected = set(exc.expected)

        # Pattern: missing contract block
        # After fn signature, parser expects "requires"/"ensures"/"decreases"
        # but got "{" (the body) or something else
        if token == "{" and expected & {"REQUIRES", "requires", "ENSURES", "ensures"}:
            return missing_contract_block(file, source, line, column)

        # Pattern: missing effects clause
        if expected & {"EFFECTS", "effects"}:
            return missing_effect_clause(file, source, line, column)

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
        )

    # Unknown exception type — wrap it
    return Diagnostic(
        description=f"Internal parser error: {exc}",
        location=SourceLocation(file=file),
    )
