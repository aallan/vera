"""Shared helpers for the test_verifier_*.py suite (split from tests/test_verifier.py, #839).

The established pattern:
    _verify(source) -> VerifyResult
    _verify_ok(source) -> assert no verification errors
    _verify_err(source, match) -> assert at least one matching error
    _verify_warn(source, match) -> assert at least one matching warning
    _nat_sub_status(source) -> per-obligation nat_sub statuses
plus the EXAMPLES_DIR / ALL_EXAMPLES corpus constants and the _MK
source template.  ``_verify`` drives the verifier through
``tests/pipeline.py``'s ``verify``.
"""
from __future__ import annotations

from pathlib import Path

from tests import pipeline
from vera.verifier import VerifyResult


EXAMPLES_DIR = Path(__file__).parent.parent / "examples"


# Examples that verify with no errors (may have Tier 3 warnings)
ALL_EXAMPLES = sorted(f.name for f in EXAMPLES_DIR.glob("*.vera"))


# =====================================================================
# Helpers
# =====================================================================

def _verify(source: str) -> VerifyResult:
    """Parse, type-check, and verify a source string.

    Through ``tests/pipeline.py``'s ``verify``, the CLI verify path
    (``cmd_verify``): the #747 semantic-type side-tables collected during
    the type check are threaded into ``verify()``, so the projection /
    generic-instantiation @Nat narrowing obligations fire here exactly as
    for ``vera verify``.  A parse or transform error is raised.
    """
    verified = pipeline.verify(source)
    _ = verified.checked.program  # raises the parse or transform error, if any
    # Check-clean is every verifier test's premise: verification
    # semantics on an ill-typed program are meaningless, and discarding
    # the checker diagnostics here let a fixture with a dangling slot
    # ref (E130) pass its `errors == []` assertion trivially — the same
    # fake-green class the differential harness's gate closed (PR #1202
    # review rounds, twice).
    check_errors = verified.checked.errors
    assert not check_errors, (
        "verifier-test fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:70]) for d in check_errors]}"
    )
    return verified.result


def _verify_user_effect(source: str) -> VerifyResult:
    """Verify a fixture whose subject needs a user-declared effect's
    operation, past the check.

    A row naming a user-declared effect is refused at check since #1681
    (E340), so ``vera verify`` never reaches the operation, and the
    verifier's treatment of it is measured on the tables the check
    collected.  The premise `_verify` holds stays, narrowed by exactly that
    refusal: the program is well typed, and the check's errors are the
    rows' E340s and nothing else.
    """
    verified = pipeline.verify(source, past_check=True)
    _ = verified.checked.program  # raises the parse or transform error, if any
    check_errors = verified.checked.errors
    assert check_errors and all(
        d.error_code == "E340" for d in check_errors), (
        "a user-effect verifier fixture is refused at its rows (E340) and "
        "nowhere else, got: "
        f"{[(d.error_code, d.description[:70]) for d in check_errors]}"
    )
    return verified.result


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


def _nat_sub_status(source: str, *, past_check: bool = False) -> list[str]:
    """Statuses of the `nat_sub` (#520/E502) obligations for *source*.

    Helper for the shadow/projection audit battery
    (:class:`TestShadowAuditSubtraction680`): returns one status string per
    recorded `@Nat`-subtraction site so a test can assert the tier directly.
    """
    result = (_verify_user_effect(source) if past_check
              else _verify(source))
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
