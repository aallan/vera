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
        spec_ref='Chapter 5, Section 5.1 "Function Structure"',
        error_code="E001",
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
        spec_ref='Chapter 3, Section 3.1 "Slot Reference Syntax"',
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
        spec_ref='Chapter 1, Section 1.6 "Canonical Formatting"',
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
        error_code="E005",
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

        # Pattern: old dot syntax for module-qualified calls
        # module_path consumed all idents including the fn name, parser
        # expects "::" (__ANON_9) but got "("
        if token == "(" and "__ANON_9" in expected:
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
            error_code="E006",
        )

    # Unknown exception type — wrap it
    return Diagnostic(
        description=f"Internal parser error: {exc}",
        location=SourceLocation(file=file),
        error_code="E007",
    )


# =====================================================================
# Error code registry
# =====================================================================

ERROR_CODES: dict[str, str] = {
    # E0xx — Parse & Transform
    "E001": "Missing contract block",
    "E002": "Missing effect clause",
    "E003": "Malformed slot reference",
    "E004": "Missing closing brace",
    "E005": "Unexpected token",
    "E006": "Unexpected character",
    "E007": "Internal parser error",
    "E008": "Module-qualified call uses dot instead of ::",
    "E010": "Unhandled grammar rule",
    # E1xx — Type Checker: Core & Expressions
    "E120": "Data invariant not Bool",
    "E121": "Function body type mismatch",
    "E122": "Pure function performs effects",
    "E123": "Precondition predicate not Bool",
    "E124": "Postcondition predicate not Bool",
    "E130": "Unresolved slot reference",
    "E131": "Result ref outside ensures",
    "E140": "Arithmetic requires numeric operands",
    "E141": "Arithmetic requires matching numeric types",
    "E142": "Cannot compare incompatible types",
    "E143": "Ordering requires orderable operands",
    "E144": "Logical operand not Bool (left)",
    "E145": "Logical operand not Bool (right)",
    "E146": "Unary not requires Bool",
    "E147": "Unary negate requires numeric",
    "E160": "Array index must be Int or Nat",
    "E161": "Cannot index non-array type",
    "E170": "Let binding type mismatch",
    "E171": "Anonymous function body type mismatch",
    "E172": "Assert requires Bool",
    "E173": "Assume requires Bool",
    "E174": "old() outside ensures",
    "E175": "new() outside ensures",
    "E176": "Unknown expression type",
    # E2xx — Type Checker: Calls
    "E200": "Unresolved function",
    "E201": "Wrong argument count",
    "E202": "Argument type mismatch",
    "E203": "Effect operation wrong argument count",
    "E204": "Effect operation argument type mismatch",
    "E210": "Unknown constructor",
    "E211": "Constructor is nullary",
    "E212": "Constructor wrong field count",
    "E213": "Constructor field type mismatch",
    "E214": "Unknown nullary constructor",
    "E215": "Constructor requires arguments",
    "E220": "Unresolved qualified call",
    "E230": "Module not found",
    "E231": "Function not imported from module",
    "E232": "Function is private in module",
    "E233": "Function not found in module",
    # E3xx — Type Checker: Control Flow
    "E300": "If condition not Bool",
    "E301": "If branches incompatible types",
    "E302": "Match arm type mismatch",
    "E310": "Unreachable match arm",
    "E311": "Non-exhaustive match (ADT)",
    "E312": "Non-exhaustive match (Bool)",
    "E313": "Non-exhaustive match (infinite type)",
    "E320": "Unknown constructor in pattern",
    "E321": "Pattern constructor wrong arity",
    "E322": "Unknown nullary constructor in pattern",
    "E330": "Unknown effect in handler",
    "E331": "Handler state type mismatch",
    "E332": "Effect has no such operation",
    "E333": "Handler with-state but no state declaration",
    "E334": "State update type name mismatch",
    "E335": "State update expression type mismatch",
    # E5xx — Verification
    "E500": "Postcondition verified false",
    "E501": "Call-site precondition violation",
    "E520": "Cannot verify contract (generic function)",
    "E521": "Cannot verify precondition (undecidable)",
    "E522": "Cannot verify postcondition (body undecidable)",
    "E523": "Cannot verify postcondition (expression undecidable)",
    "E524": "Cannot verify postcondition (timeout)",
    "E525": "Cannot verify termination metric",
    # E6xx — Codegen
    "E600": "Unsupported parameter type",
    "E601": "Unsupported return type",
    "E602": "Unsupported body expression type",
    "E603": "Unsupported closure",
    "E604": "Unsupported state effect type",
    "E605": "Unsupported state type parameter",
    "E606": "State without proper effect declaration",
    "E607": "State with unsupported operations",
}
