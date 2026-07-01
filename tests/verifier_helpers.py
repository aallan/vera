"""Shared helpers for the test_verifier_*.py suite (split from tests/test_verifier.py, #839).

The established pattern:
    _verify(source) -> VerifyResult
    _verify_ok(source) -> assert no verification errors
    _verify_err(source, match) -> assert at least one matching error
    _verify_warn(source, match) -> assert at least one matching warning
    _nat_sub_status(source) -> per-obligation nat_sub statuses
plus the EXAMPLES_DIR / ALL_EXAMPLES corpus constants and the _MK
source template.
"""
from __future__ import annotations

from pathlib import Path

from vera.parser import parse_to_ast
from vera.checker import typecheck_with_artifacts
from vera.verifier import VerifyResult, verify


EXAMPLES_DIR = Path(__file__).parent.parent / "examples"


# Examples that verify with no errors (may have Tier 3 warnings)
ALL_EXAMPLES = sorted(f.name for f in EXAMPLES_DIR.glob("*.vera"))


# =====================================================================
# Helpers
# =====================================================================

def _verify(source: str) -> VerifyResult:
    """Parse, type-check, and verify a source string.

    Mirrors the CLI verify path (``cmd_verify``): collects the #747
    semantic-type side-tables during type-check and threads them into
    ``verify()``, so the projection / generic-instantiation @Nat
    narrowing obligations fire here exactly as for ``vera verify``.
    """
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast, source)
    return verify(
        ast, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


def _verify_ok(source: str) -> None:
    """Assert source verifies with no errors."""
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors == [], f"Expected no errors, got: {[e.description for e in errors]}"


def _verify_err(source: str, match: str) -> list:
    """Assert source produces at least one verification error matching *match*."""
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors, "Expected at least one error, got none"
    matched = [e for e in errors if match.lower() in e.description.lower()]
    assert matched, (
        f"No error matched '{match}'. Errors: {[e.description for e in errors]}"
    )
    return matched


def _verify_warn(source: str, match: str) -> list:
    """Assert source produces at least one verification warning matching *match*."""
    result = _verify(source)
    warnings = [d for d in result.diagnostics if d.severity == "warning"]
    assert warnings, "Expected at least one warning, got none"
    matched = [w for w in warnings if match.lower() in w.description.lower()]
    assert matched, (
        f"No warning matched '{match}'. Warnings: {[w.description for w in warnings]}"
    )
    return matched


def _nat_sub_status(source: str) -> list[str]:
    """Statuses of the `nat_sub` (#520/E502) obligations for *source*.

    Helper for the shadow/projection audit battery
    (:class:`TestShadowAuditSubtraction680`): returns one status string per
    recorded `@Nat`-subtraction site so a test can assert the tier directly.
    """
    result = _verify(source)
    return [o.status for o in result.obligations if o.kind == "nat_sub"]


# A non-literal `@Tuple<Nat, Nat>` source (a call) for the subtraction audit
# battery: destructuring it yields two OPAQUE `@Nat` shadows, so a downstream
# subtraction over them exercises the tracked-shadow / `_contains_opaque_shadow`
# path (see :class:`TestShadowAuditSubtraction680`).
_MK = """
private fn mk(@Nat -> @Tuple<Nat, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Nat.0, @Nat.0) }
"""
