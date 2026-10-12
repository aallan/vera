"""Regression tests for #874 — the ``eq`` / ``compare`` ability operations in
contract position (``requires`` / ``ensures``) must lower to their canonical
operator form, so a contract that ``vera check`` accepts also *compiles*,
*runs*, and *verifies at Tier 1*.

The bug: codegen's Pass 1.6 (``_rewrite_ability_ops``) rewrites ``eq(a, b)`` to
``BinaryExpr(a, EQ, b)`` and ``compare(a, b)`` to the ``Ordering`` if-chain, but
only over function *bodies* and ``where`` helpers — never over the FnDecl's
contract clauses.  A contract predicate written with the ability op
(``ensures(eq(@Int.result, 3))``) therefore reached the WASM backend as a bare
``FnCall(name='eq')`` whose target is not a registered function, tripping the
``_translate_call`` guard-rail with an *uncaught* ``CodegenSkip`` — a hard
traceback for ``vera compile`` / ``vera run`` (the contract path is lowered
OUTSIDE the ``_compile_fn`` try/except that would otherwise demote a body skip
to an E602 warning + silent function drop).

The verifier had the parallel gap: ``smt._translate_call`` recognised none of
the ability ops, so ``eq`` in an ``ensures`` returned ``None`` → the whole
postcondition demoted to Tier 3 (E523) instead of being *proved* at Tier 1.
A contract that compiles but is never statically checked is a second, quieter
silent failure.

One-canonical-form fix (#815 / DESIGN.md §0.2.3): ``eq(a, b)`` and ``a == b``
are semantically identical, so they share one internal representation
(``BinaryExpr(_, EQ, _)``).  Codegen rewrites contract clauses through the same
Pass 1.6 it already runs on bodies; the verifier desugars the ability-op call
to the same canonical ``BinaryExpr`` and translates it via its existing,
FP-correct ``==`` path.  Checker (already resolves the op → ``Bool``), codegen,
and verifier then agree.

Written test-first: each RED test below FAILS on the pre-fix compiler
(``CodegenSkip`` traceback for the codegen tests; a Tier-3 count for the
verify tests).
"""

from __future__ import annotations


import pytest

from vera.codegen import execute
from vera.codegen.api import WasmTrapError
from tests.codegen_helpers import _compile, _run
from tests.verifier_helpers import _verify


# ---------------------------------------------------------------------
# Codegen helpers (mirror tests/test_codegen_structural_eq.py)
# ---------------------------------------------------------------------


def _skip_warnings(source: str) -> list[str]:
    """E602 skip warnings — the marker that a function was dropped."""
    result = _compile(source)
    return [
        d.error_code
        for d in result.diagnostics
        if d.severity == "warning" and d.error_code == "E602"
    ]


# ---------------------------------------------------------------------
# Verify helpers (mirror tests/verifier_helpers.py)
# ---------------------------------------------------------------------


# =====================================================================
# Codegen: eq / compare in contract position must compile + run
# =====================================================================

class TestEqContractCodegen874:
    def test_eq_in_ensures_compiles_and_runs(self) -> None:
        # RED: pre-fix this raised an uncaught CodegenSkip at
        # _compile_postconditions.  The ensures holds (3 == 3), so the
        # guarded function returns its value normally.
        src = """
public fn three(@Unit -> @Int)
  requires(true)
  ensures(eq(@Int.result, 3))
  effects(pure)
{
  3
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  three(())
}
"""
        assert _run(src, fn="main") == 3
        # And no function was silently dropped behind an E602 skip.
        assert _skip_warnings(src) == []

    def test_eq_in_requires_compiles_and_runs(self) -> None:
        # RED: eq() in a precondition tripped the same guard-rail.
        src = """
public fn echo(@Int -> @Int)
  requires(eq(@Int.0, 3))
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  echo(3)
}
"""
        assert _run(src, fn="main") == 3
        assert _skip_warnings(src) == []

    def test_compare_in_ensures_compiles_and_runs(self) -> None:
        # RED: the sibling Ord op `compare` shared the gap.  compare(3, 5)
        # is Less; the body returns 1 (an Int witness) so we can observe a
        # concrete run value while the ensures references compare().
        src = """
public fn cmp_lt(@Int -> @Int)
  requires(true)
  ensures(compare(@Int.0, 5) == Less)
  effects(pure)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  cmp_lt(3)
}
"""
        assert _run(src, fn="main") == 3
        assert _skip_warnings(src) == []

    def test_eq_ensures_violation_traps_at_runtime(self) -> None:
        # The lowered contract must actually ENFORCE: an eq-ensures that is
        # false at runtime must trap, not pass through.  (Distinguishes a
        # working contract from one that compiles to a no-op.)
        src = """
public fn wrong(@Unit -> @Int)
  requires(true)
  ensures(eq(@Int.result, 3))
  effects(pure)
{
  4
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrong(())
}
"""
        result = _compile(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, f"Unexpected compile errors: {errors}"
        # Pin the SPECIFIC contract-violation trap, not merely *some* trap: an
        # unrelated codegen regression trapping for a different reason (OOB
        # index, unreachable, …) would satisfy a bare `raises(WasmTrapError)`.
        # The message additionally shows the canonical operator form the `eq`
        # lowered to (`ensures(@Int.result == 3) failed`), so it also witnesses
        # that the contract compiled *as* `==` and enforced.
        with pytest.raises(WasmTrapError, match="Postcondition violation") as exc:
            execute(result, fn_name="main")
        assert exc.value.kind == "contract_violation"
        assert "@Int.result == 3" in str(exc.value)

    def test_eq_in_where_fn_contract_compiles_and_runs(self) -> None:
        # RED: the ability-op rewrite must reach a *where*-helper's OWN
        # contract too.  `_rewrite_where_fns` rewrote only `wfn.body`, not
        # `wfn.contracts`, so a where-fn whose `ensures` used `eq` tripped the
        # same uncaught CodegenSkip that the top-level path did.  The helper's
        # ensures holds (result == input), so `caller(())` returns 3.
        src = """
public fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  helper(3)
}
where {
  fn helper(@Int -> @Int)
    requires(true)
    ensures(eq(@Int.result, @Int.0))
    effects(pure)
  {
    @Int.0
  }
}
"""
        assert _run(src, fn="caller") == 3
        assert _skip_warnings(src) == []

    def test_compare_in_where_fn_contract_compiles_and_runs(self) -> None:
        # RED: the sibling `compare` op shares the where-fn-contract gap.  The
        # helper's ensures compares result to input (Equal since result ==
        # input), so it holds and `caller(())` returns 3.
        src = """
public fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  helper(3)
}
where {
  fn helper(@Int -> @Int)
    requires(true)
    ensures(compare(@Int.result, @Int.0) == Equal)
    effects(pure)
  {
    @Int.0
  }
}
"""
        assert _run(src, fn="caller") == 3
        assert _skip_warnings(src) == []

    def test_eq_in_forall_contract_compiles_and_runs(self) -> None:
        # RED: a `forall` in a contract is runtime-lowered by
        # `_translate_quantifier`, which compiles the predicate `AnonFn` body.
        # `_rewrite_ops_in_expr` fell through `ForallExpr`/`ExistsExpr` to the
        # leaf return, so an `eq` inside the predicate reached codegen as a bare
        # unregistered call — the same uncaught `CodegenSkip` as #874's original
        # top-level case (PR #887 review).  The ensures holds ([0,0,0] all == 0),
        # so `all_zero(())` returns 1 (true).
        src = """
private fn all_zero(@Array<Int> -> @Bool)
  requires(true)
  ensures(forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { eq(@Array<Int>.0[@Int.0], 0) }))
  effects(pure)
{
  true
}

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  all_zero([0, 0, 0])
}
"""
        assert _run(src) == 1
        assert _skip_warnings(src) == []

    def test_compare_in_exists_contract_compiles_and_runs(self) -> None:
        # RED: the sibling `exists` quantifier + `compare` op share the gap.
        # The ensures holds (9 > 5, so some element compares Greater), so
        # `any_big(())` returns 1 (true).
        src = """
private fn any_big(@Array<Int> -> @Bool)
  requires(true)
  ensures(exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { compare(@Array<Int>.0[@Int.0], 5) == Greater }))
  effects(pure)
{
  true
}

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  any_big([1, 9, 2])
}
"""
        assert _run(src) == 1
        assert _skip_warnings(src) == []


# =====================================================================
# Verify: eq in ensures must be proved at Tier 1, not deferred to Tier 3
# =====================================================================

class TestEqContractVerify874:
    def test_eq_ensures_verified_tier1(self) -> None:
        # RED: smt._translate_call did not recognise `eq`, so the ensures
        # returned None → the postcondition demoted to Tier 3 (E523).  After
        # the fix it desugars to `@Int.result == 3` and proves at Tier 1.
        result = _verify("""
public fn three(@Unit -> @Int)
  requires(true)
  ensures(eq(@Int.result, 3))
  effects(pure)
{
  3
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Unexpected verify errors: {errors}"
        assert result.summary.tier1_verified >= 1
        assert result.summary.tier3_runtime == 0, (
            "eq-ensures must be proved at Tier 1, not deferred to Tier 3"
        )

    def test_eq_ensures_false_is_a_counterexample(self) -> None:
        # An eq-ensures that is FALSE must be caught statically (a real
        # Tier-1 obligation), not silently deferred to a runtime check.
        result = _verify("""
public fn wrong(@Unit -> @Int)
  requires(true)
  ensures(eq(@Int.result, 3))
  effects(pure)
{
  4
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, (
            "A false eq-ensures must fail Tier-1 verification with a "
            "counterexample, not pass as a Tier-3 deferral"
        )

    def test_compare_ensures_verified_tier1(self) -> None:
        # The sibling Ord op `compare` must also verify at Tier 1: the verifier
        # desugars `compare(a, b)` to the same canonical Ordering if-chain
        # codegen emits.  compare(3, 5) is Less, and the ensures references it.
        result = _verify("""
public fn lt5(@Unit -> @Int)
  requires(true)
  ensures(compare(@Int.result, 5) == Less)
  effects(pure)
{
  3
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Unexpected verify errors: {errors}"
        assert result.summary.tier1_verified >= 1
        assert result.summary.tier3_runtime == 0, (
            "compare-ensures must be proved at Tier 1, not deferred to Tier 3"
        )

    def test_compare_ensures_false_is_a_counterexample(self) -> None:
        # A false compare-ensures must be a static counterexample, not a
        # silent Tier-3 deferral.  compare(3, 5) is Less, not Greater.
        result = _verify("""
public fn wrong(@Unit -> @Int)
  requires(true)
  ensures(compare(@Int.result, 5) == Greater)
  effects(pure)
{
  3
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, (
            "A false compare-ensures must fail Tier-1 verification with a "
            "counterexample, not pass as a Tier-3 deferral"
        )

    def test_user_where_fn_eq_shadows_builtin_desugar(self) -> None:
        # The `_is_user_fn` guard (mirroring codegen's `not in self._fn_sigs`)
        # must route a contract `eq(...)` to a user `where`-helper of that
        # name, NOT the built-in `==` desugar.  Here the user `eq(a, b)` means
        # `a > b` (via its `ensures`), so `caller`'s postcondition
        # `eq(@Int.result, @Int.0)` reduces to `@Int.result > @Int.0`, which is
        # FALSE for `caller` returning its own input — a Tier-1 counterexample.
        # If the guard were absent, the desugar would hijack `eq` to
        # `@Int.result == @Int.0`, which is TRUE, and the function would
        # verify — the observable difference this test pins (and the mutation
        # kill: disable `_is_user_fn` → this program verifies clean).
        result = _verify("""
public fn caller(@Int -> @Int)
  requires(true)
  ensures(eq(@Int.result, @Int.0))
  effects(pure)
{
  @Int.0
}
where {
  fn eq(@Int, @Int -> @Bool)
    requires(true)
    ensures(@Bool.result == (@Int.1 > @Int.0))
    effects(pure)
  {
    @Int.1 > @Int.0
  }
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, (
            "The user where-fn `eq` (result > input) must route through the "
            "user semantics, yielding a counterexample — not be hijacked by "
            "the built-in `==` desugar (which would verify)"
        )
