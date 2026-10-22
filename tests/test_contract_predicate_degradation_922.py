"""Regression tests for #922 — a non-Eq composite ``==`` / ``hash`` / ``show``
in a CONTRACT-PREDICATE position must degrade to a clean diagnostic (E613 for a
non-derivable ``==``, E602 for an unsupported ``hash`` / ``show``), NEVER escape
as an uncaught Python traceback at compile.

The bug (a `check`-green program crashes `vera compile` / `run` / `test`):

The #912 fix wired the ``AdtEqNotDerivableError`` / ``CodegenSkip`` graceful
degradation (emit a clean E613 / E602, drop the function) at the body, lifted-
closure, and *postcondition* contract sites — but three sibling contract-
predicate sites were left unguarded:

  1. ``requires`` (precondition): ``_compile_preconditions`` translates the
     predicate with NO surrounding try/except, so a non-Eq composite ``==`` in a
     ``requires(...)`` raised an uncaught ``AdtEqNotDerivableError``.

  2. Refinement-type parameter guard: ``_emit_refinement_check`` translated the
     refinement predicate under a ``try/except CodegenSkip`` that did NOT cover
     ``AdtEqNotDerivableError``, so a non-Eq composite ``==`` in a ``{ @T | P }``
     guard escaped uncaught.

  3. ``ensures`` (postcondition) catch too narrow: the ``_compile_postconditions``
     backstop caught only ``AdtEqNotDerivableError``, NOT ``CodegenSkip`` — so
     ``ensures(hash(unsupportedType) == 0)`` (or ``show``) escaped as an uncaught
     ``CodegenSkip``.

Fix: every contract-predicate ``translate_expr`` call site is guarded by the
SAME ``(AdtEqNotDerivableError, CodegenSkip)`` degradation the postcondition path
uses — an ``AdtEqNotDerivableError`` becomes a clean E613, a ``CodegenSkip``
becomes a clean E602, and the enclosing function is dropped.  A user program can
NEVER surface a Python traceback from a contract predicate (contract §516 / §522
/ §589).

Written test-first: each RED test below crashed with an uncaught traceback on the
pre-fix compiler (``_compile`` re-raises), and produces a clean diagnostic after.
The regression tests pin that VALID contracts (primitive ``==``, derivable-ADT
``==``, refinements over primitives) still compile and run unchanged, and that
the #912 postcondition backstop still degrades a concrete composite ``==`` to a
clean E613.
"""

from __future__ import annotations


from tests import pipeline
from tests.codegen_helpers import _compile, _run


# ---------------------------------------------------------------------
# Helpers (mirror tests/test_composite_postcondition_eq_912.py)
# ---------------------------------------------------------------------


def _diag_codes(source: str) -> list[str]:
    """ALL diagnostic codes (error + warning) from a compile.

    The ``hash`` / ``show`` ``CodegenSkip`` path degrades to an E602 *warning*
    (matching the function-body convention), so a warning-inclusive accessor is
    needed to assert it — ``_error_codes`` would miss it.
    """
    result = _compile(source)
    return [d.error_code for d in result.diagnostics]


def _refused_e243(source: str) -> None:
    """A `Tuple` `==` in a contract is refused at check (E243, `Tuple` is not
    Eq-derivable, #1654), so code generation never translates it."""
    compiled = pipeline.compile(source)
    codes = {d.error_code for d in compiled.checked.errors}
    assert codes == {"E243"}, [
        (d.error_code, d.description[:70]) for d in compiled.checked.errors]
    assert compiled.generator is None


# Program bodies -------------------------------------------------------

# ``hash`` is not supported for ``Decimal`` (a host-handle type) in codegen, so a
# ``hash(@Decimal.0)`` in a contract predicate raises ``CodegenSkip`` (the #912
# postcondition backstop caught only ``AdtEqNotDerivableError``, so it escaped).
#
# (This was originally a directly-recursive ADT (`List<Int>`), but #924 made
# recursive-ADT ``hash`` / ``show`` SUPPORTED via a generated recursive helper —
# so a still-unsupported operand is needed to keep exercising the ``CodegenSkip``
# contract-predicate degradation.  Any type without a codegen ``hash`` works;
# ``Decimal`` is the smallest.)
_HASH_SKIP = """
private fn h(@Decimal -> @Int)
  requires({requires})
  ensures({ensures})
  effects(pure)
{{
  0
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  h(decimal_from_int(1))
}}
"""


# =====================================================================
# RED: a non-Eq composite in a CONTRACT PREDICATE degrades cleanly.
# Each `_compile` here crashed with an uncaught traceback on the pre-fix
# compiler; after the fix it returns a CompileResult with a clean E613/E602.
# =====================================================================

class TestContractPredicateDegradation922:
    def test_precondition_tuple_eq_is_refused_at_check(self) -> None:
        # Site 1 — `requires`: a `Tuple<Int, Int> == Tuple<Int, Int>` in a
        # precondition.  `Tuple` is intentionally non-Eq (spec §9.8), so this
        # reached the structural-Eq dispatch and raised `AdtEqNotDerivableError`.
        # Pre-fix `_compile_preconditions` had no try/except → uncaught
        # traceback; then a clean E613.  Now refused at check (E243).
        src = (
            "private fn f(@Int -> @Int) "
            "requires(Tuple(@Int.0, @Int.0) == Tuple(@Int.0, @Int.0)) "
            "ensures(true) effects(pure) { @Int.0 }\n"
            "public fn main(@Unit -> @Int) "
            "requires(true) ensures(true) effects(pure) { 0 }\n"
        )
        _refused_e243(src)

    def test_refinement_guard_tuple_eq_is_refused_at_check(self) -> None:
        # Site 2 — refinement-type param guard: a `Tuple == Tuple` inside a
        # `{ @Int | P }` refinement predicate.  Pre-fix `_emit_refinement_check`
        # caught only `CodegenSkip`, so `AdtEqNotDerivableError` escaped; then
        # a clean E613.  Now refused at check (E243).
        src = (
            "type Weird = { @Int | Tuple(@Int.0, @Int.0) == Tuple(@Int.0, @Int.0) };\n"
            "private fn g(@Weird -> @Int) "
            "requires(true) ensures(true) effects(pure) { @Weird.0 }\n"
            "public fn main(@Unit -> @Int) "
            "requires(true) ensures(true) effects(pure) { 0 }\n"
        )
        _refused_e243(src)

    def test_postcondition_hash_unsupported_is_clean_e602(self) -> None:
        # Site 3 — `ensures` with a `CodegenSkip` (not `AdtEqNotDerivableError`):
        # `hash(@Decimal.0)` is unsupported in codegen and raises `CodegenSkip`.
        # Pre-fix the postcondition backstop caught only `AdtEqNotDerivableError`,
        # so this escaped as an uncaught `CodegenSkip`.  Now: a clean E602.
        src = _HASH_SKIP.format(requires="true", ensures="hash(@Decimal.0) == 0")
        codes = _diag_codes(src)
        assert "E602" in codes, f"expected E602 (no traceback), got {codes}"

    def test_precondition_hash_unsupported_is_clean_e602(self) -> None:
        # Site 1 with the `CodegenSkip` flavour (not just `AdtEqNotDerivableError`)
        # — `hash(@Decimal.0)` in a `requires`.  Confirms the broadened
        # precondition catch covers `CodegenSkip`, not only the ADT-eq error.
        # Pre-fix: uncaught `CodegenSkip` traceback.
        src = _HASH_SKIP.format(requires="hash(@Decimal.0) == 0", ensures="true")
        codes = _diag_codes(src)
        assert "E602" in codes, f"expected E602 (no traceback), got {codes}"


# =====================================================================
# REGRESSION: VALID contracts must compile and run unchanged.  A too-broad
# catch that swallowed a real translate_expr result would break these.
# =====================================================================

class TestValidContractsUnaffected922:
    def test_primitive_precondition_runs(self) -> None:
        # A primitive `requires(@Int.0 > 0)` still compiles and runs — the new
        # guard must not perturb the common valid case.
        src = (
            "private fn f(@Int -> @Int) "
            "requires(@Int.0 > 0) ensures(true) effects(pure) { @Int.0 }\n"
            "public fn main(@Unit -> @Int) "
            "requires(true) ensures(true) effects(pure) { f(7) }\n"
        )
        assert _run(src, fn="main") == 7

    def test_derivable_adt_precondition_runs(self) -> None:
        # An Eq-DERIVABLE ADT `==` (`Box<Int>`, all-Eq fields) in a precondition
        # must still lower structurally and run — the degradation must fire ONLY
        # for non-derivable operands, never for a valid derivable `==`.
        src = (
            "private data Box { MkBox(Int) }\n"
            "private fn f(@Box -> @Int) "
            "requires(@Box.0 == MkBox(7)) ensures(true) effects(pure) { 0 }\n"
            "public fn main(@Unit -> @Int) "
            "requires(true) ensures(true) effects(pure) { f(MkBox(7)) }\n"
        )
        assert _run(src, fn="main") == 0

    def test_primitive_refinement_param_runs(self) -> None:
        # A refinement over a PRIMITIVE (`{ @Int | @Int.0 > 0 }`) still emits a
        # valid runtime guard and runs — the broadened refinement catch must not
        # disturb the valid path.
        src = (
            "type PosInt = { @Int | @Int.0 > 0 };\n"
            "private fn f(@PosInt -> @Int) "
            "requires(true) ensures(true) effects(pure) { @PosInt.0 }\n"
            "public fn main(@Unit -> @Int) "
            "requires(true) ensures(true) effects(pure) { f(7) }\n"
        )
        assert _run(src, fn="main") == 7

    def test_primitive_postcondition_runs(self) -> None:
        # A primitive `ensures(@Int.result == @Int.0)` still compiles and runs —
        # the broadened postcondition catch (now `CodegenSkip` too) must not
        # swallow a valid postcondition.
        src = (
            "private fn f(@Int -> @Int) "
            "requires(true) ensures(@Int.result == @Int.0) effects(pure) { @Int.0 }\n"
            "public fn main(@Unit -> @Int) "
            "requires(true) ensures(true) effects(pure) { f(7) }\n"
        )
        assert _run(src, fn="main") == 7


# =====================================================================
# CROSS-CHECK: the #912 postcondition backstop still degrades a concrete
# composite `==` in `ensures` to a clean E613 (the broadened catch must not
# regress the exact case #912 fixed).
# =====================================================================

class TestPostcondition912StillDegrades922:
    def test_tuple_postcondition_is_refused_at_check(self) -> None:
        src = (
            "private fn mk(@Int -> @Tuple<Int, Int>) "
            "requires(true) "
            "ensures(@Tuple<Int, Int>.result == Tuple(@Int.0, @Int.0)) "
            "effects(pure) { Tuple(@Int.0, @Int.0) }\n"
        )
        _refused_e243(src)
