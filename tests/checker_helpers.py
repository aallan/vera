"""Shared helpers and fixtures for the ``test_checker_*.py`` type-checker suite.

Split out of ``tests/test_checker.py`` (#420) so the eight phase-focused
``test_checker_*.py`` files can share the ``_check*`` assertion helpers and the
example-corpus constants.
"""

from __future__ import annotations

from pathlib import Path

from vera.checker import typecheck
from vera.errors import Diagnostic
from vera.parser import parse_to_ast

# =====================================================================
# Helpers
# =====================================================================

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"
EXAMPLE_FILES = sorted(f.name for f in EXAMPLES_DIR.glob("*.vera"))

# Self-contained examples (no unresolved external references)
CLEAN_EXAMPLES = [
    "absolute_value.vera",
    "closures.vera",
    "effect_handler.vera",
    "factorial.vera",
    "generics.vera",
    "increment.vera",
    "list_ops.vera",
    "modules.vera",
    "mutual_recursion.vera",
    "pattern_matching.vera",
    "quantifiers.vera",
    "refinement_types.vera",
    "safe_divide.vera",
]

# The former WARN_EXAMPLES list ("unresolved external references,
# warnings expected") was removed with #854: closures.vera was its sole
# entry, and apply_fn is now checker-registered, so no example warns.


def _check(source: str) -> list[Diagnostic]:
    """Parse and type-check, return diagnostics."""
    prog = parse_to_ast(source)
    return typecheck(prog, source=source)


def _errors(source: str) -> list[Diagnostic]:
    """Parse and type-check, return only errors (not warnings)."""
    return [d for d in _check(source) if d.severity == "error"]


def _warnings(source: str) -> list[Diagnostic]:
    """Parse and type-check, return only warnings."""
    return [d for d in _check(source) if d.severity != "error"]


def _check_ok(source: str) -> None:
    """Assert the source type-checks with no errors."""
    errs = _errors(source)
    assert errs == [], \
        f"Expected no errors, got: {[e.description for e in errs]}"


def _check_clean(source: str) -> None:
    """Assert the source type-checks with no errors AND no warnings."""
    diags = _check(source)
    assert diags == [], \
        f"Expected no diagnostics, got: {[d.description for d in diags]}"


def _check_err(source: str, match: str) -> list[Diagnostic]:
    """Assert the source has at least one error matching the substring."""
    errs = _errors(source)
    assert any(match.lower() in e.description.lower() for e in errs), \
        f"Expected error matching '{match}', got: " \
        f"{[e.description for e in errs]}"
    return errs
