"""Tests for vera.codegen — refinements (assert/assume, forall/exists quantifiers, refinement type aliases and runtime guards).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re

import pytest

from vera.codegen import (
    execute,
)

from tests.codegen_helpers import (
    _compile,
    _compile_ok,
    _run,
    _run_float,
    _run_refine_trap,
    _run_trap,
)


# =====================================================================
# C6l: Assert and assume
# =====================================================================


class TestAssertAssume:
    def test_assert_true(self) -> None:
        """assert(true) should not trap."""
        assert _run("""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  assert(true);
  42
}
""") == 42

    def test_assert_false(self) -> None:
        """assert(false) should trap."""
        _run_trap("""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  assert(false);
  42
}
""")

    def test_assert_with_expression(self) -> None:
        """assert with a computed expression."""
        assert _run("""
public fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  assert(@Int.0 > 0);
  @Int.0 + 1
}
""", args=[5]) == 6

    def test_assert_expression_false_traps(self) -> None:
        """assert with expression that evaluates to false."""
        _run_trap("""
public fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  assert(@Int.0 > 0);
  @Int.0
}
""", args=[0])

    def test_assert_in_sequence(self) -> None:
        """assert followed by computation."""
        assert _run("""
public fn f(@Int, @Int -> @Int) requires(true) ensures(true) effects(pure) {
  assert(@Int.1 > 0);
  let @Int = @Int.1 + @Int.0;
  assert(@Int.0 > 0);
  @Int.0
}
""", args=[3, 5]) == 8

    def test_assume_is_noop(self) -> None:
        """assume should be a no-op at runtime."""
        assert _run("""
public fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  assume(@Int.0 > 0);
  @Int.0 * 2
}
""", args=[5]) == 10

    def test_assert_wat_contains_unreachable(self) -> None:
        """WAT should contain unreachable for assert."""
        result = _compile_ok("""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  assert(true);
  1
}
""")
        assert "unreachable" in result.wat


# =====================================================================
# C6l: Forall quantifier
# =====================================================================


class TestForall:
    def test_forall_all_positive(self) -> None:
        """forall over array where all elements satisfy predicate."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 1

    def test_forall_not_all_positive(self) -> None:
        """forall over array where one element fails predicate."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, -2, 3];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 0

    def test_forall_empty_domain(self) -> None:
        """forall with empty domain should be vacuously true."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  forall(@Int, 0, fn(@Int -> @Bool) effects(pure) {
    false
  })
}
""") == 1

    def test_forall_single_element_true(self) -> None:
        """forall with single element, predicate true."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [42];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 1

    def test_forall_single_element_false(self) -> None:
        """forall with single element, predicate false."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [-1];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 0

    def test_forall_all_equal(self) -> None:
        """forall checking all elements equal a value."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [7, 7, 7];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 7
  })
}
""") == 1


# =====================================================================
# C6l: Exists quantifier
# =====================================================================


class TestExists:
    def test_exists_has_zero(self) -> None:
        """exists with one matching element."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 0, 3];
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 1

    def test_exists_no_match(self) -> None:
        """exists with no matching element."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 0

    def test_exists_empty_domain(self) -> None:
        """exists with empty domain should be false."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  exists(@Int, 0, fn(@Int -> @Bool) effects(pure) {
    true
  })
}
""") == 0

    def test_exists_single_element_true(self) -> None:
        """exists with single matching element."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [0];
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 1

    def test_exists_single_element_false(self) -> None:
        """exists with single non-matching element."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [5];
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 0


# =====================================================================
# C6l: Quantifier WAT inspection
# =====================================================================


class TestQuantifierWat:
    def test_forall_wat_has_loop(self) -> None:
        """WAT for forall should contain loop and block."""
        result = _compile_ok("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""")
        assert "loop" in result.wat
        assert "block" in result.wat
        assert "br_if" in result.wat

    def test_exists_wat_has_loop(self) -> None:
        """WAT for exists should contain loop and block."""
        result = _compile_ok("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""")
        assert "loop" in result.wat
        assert "block" in result.wat


# =====================================================================
# Refinement type alias compilation
# =====================================================================


class TestRefinementTypeAlias:
    """Refined type aliases (e.g. PosInt, Percentage) resolve to their
    base WASM type for params, returns, and let bindings."""

    _PREAMBLE = """
type PosInt = { @Int | @Int.0 > 0 };
type Nat = { @Int | @Int.0 >= 0 };
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 };
"""

    def test_safe_divide_basic(self) -> None:
        val = _run(self._PREAMBLE + """
public fn safe_divide(@Int, @PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 / @PosInt.0 }
""", fn="safe_divide", args=[10, 2])
        assert val == 5

    def test_safe_divide_integer_division(self) -> None:
        val = _run(self._PREAMBLE + """
public fn safe_divide(@Int, @PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 / @PosInt.0 }
""", fn="safe_divide", args=[7, 3])
        assert val == 2

    def test_to_percentage_clamp_low(self) -> None:
        val = _run(self._PREAMBLE + """
public fn to_percentage(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""", fn="to_percentage", args=[-5])
        assert val == 0

    def test_to_percentage_passthrough(self) -> None:
        val = _run(self._PREAMBLE + """
public fn to_percentage(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""", fn="to_percentage", args=[50])
        assert val == 50

    def test_to_percentage_clamp_high(self) -> None:
        val = _run(self._PREAMBLE + """
public fn to_percentage(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""", fn="to_percentage", args=[150])
        assert val == 100

    def test_refined_type_let_binding(self) -> None:
        """Let binding to a refined type alias resolves correctly."""
        val = _run(self._PREAMBLE + """
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @PosInt = @Int.0;
  @PosInt.0 + 1
}
""", fn="f", args=[10])
        assert val == 11

    def test_refined_return_in_expr(self) -> None:
        """Function returning a refined type works in expressions."""
        val = _run(self._PREAMBLE + """
public fn clamp(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  clamp(200) + clamp(50)
}
""")
        assert val == 150

    def test_refined_type_exports_in_wat(self) -> None:
        """WAT should contain function exports for refined-type fns."""
        result = _compile_ok(self._PREAMBLE + """
public fn safe_divide(@Int, @PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 / @PosInt.0 }

public fn to_percentage(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""")
        assert '(export "safe_divide"' in result.wat
        assert '(export "to_percentage"' in result.wat


class TestRefinementRuntimeGuards:
    """#746: refined params/returns carry a runtime predicate guard, so an
    unverified compile traps (via ``$vera.contract_fail``) on a violating
    value rather than silently storing it.  The function boundary (param entry
    + return exit) is where the refinement invariant is relied upon; call
    arguments are covered transitively by the callee's param guard."""

    _PRE = "type PosInt = { @Int | @Int.0 > 0 };\n"

    def test_refined_param_guard_traps_on_negative(self) -> None:
        src = self._PRE + """
public fn use_it(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
"""
        _run_refine_trap(src, fn="use_it", args=[-5])
        assert _run(src, fn="use_it", args=[7]) == 7

    def test_refined_param_guard_traps_on_zero(self) -> None:
        src = self._PRE + """
public fn use_it(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
"""
        _run_refine_trap(src, fn="use_it", args=[0])

    def test_refined_return_guard_traps(self) -> None:
        src = self._PRE + """
public fn mk(@Int -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        _run_refine_trap(src, fn="mk", args=[-5])
        assert _run(src, fn="mk", args=[7]) == 7

    def test_call_argument_guarded_transitively(self) -> None:
        """A violating call argument traps via the callee's param guard — no
        separate call-site guard is needed."""
        src = self._PRE + """
public fn use_it(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }

public fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ use_it(@Int.0) }
"""
        _run_refine_trap(src, fn="caller", args=[-3])
        assert _run(src, fn="caller", args=[9]) == 9

    def test_valid_value_passes_param_and_return_guards(self) -> None:
        """A satisfying value flows through both the entry and exit guards."""
        src = self._PRE + """
public fn id_pos(@PosInt -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
"""
        assert _run(src, fn="id_pos", args=[42]) == 42
        _run_refine_trap(src, fn="id_pos", args=[-1])

    def test_refined_string_param_guard_traps(self) -> None:
        src = """
type NonEmpty = { @String | string_length(@String.0) > 0 };
public fn use_s(@NonEmpty -> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(@NonEmpty.0) }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ use_s("") }
"""
        _run_refine_trap(src, fn="entry")

    def test_refined_string_return_guard_traps(self) -> None:
        src = """
type NonEmpty = { @String | string_length(@String.0) > 0 };
public fn mk(@String -> @NonEmpty)
  requires(true) ensures(true) effects(pure)
{ @String.0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(mk("")) }
"""
        _run_refine_trap(src, fn="entry")

    def test_generic_refined_return_guarded_after_monomorphization(self) -> None:
        """A generic function with a *concrete* refined return is runtime-guarded
        on its monomorphised instance (the static obligation is skipped for
        generics — #555 — but codegen monomorphises and the return guard
        fires)."""
        src = self._PRE + """
public forall<T> fn coerce(@T -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ 0 - 1 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ coerce(5) }
"""
        _run_refine_trap(src, fn="entry")

    _ARR = (
        "type NonEmptyArray = "
        "{ @Array<Int> | array_length(@Array<Int>.0) > 0 };\n"
    )

    def test_array_param_guard_traps_on_empty(self) -> None:
        """A refinement over a non-primitive (`Array`) base is runtime-guarded
        too — the predicate is compiled to WASM directly (Z3 cannot decide
        `array_length`, but codegen can), so an empty array into a
        `@NonEmptyArray` parameter traps.

        The body returns ``array_length(...)`` rather than indexing
        ``[0]``: absent the guard, an empty array would return 0 normally
        instead of trapping on an out-of-bounds index, so the trap on
        ``count([])`` isolates the *guard* as the sole cause."""
        src = self._ARR + """
public fn count(@NonEmptyArray -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(@NonEmptyArray.0) }
public fn empty(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ count([]) }
public fn nonempty(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ count([42, 7]) }
"""
        _run_refine_trap(src, fn="empty")
        assert _run(src, fn="nonempty") == 2

    def test_array_return_guard_traps_on_empty(self) -> None:
        """A refined `@NonEmptyArray` return is runtime-guarded at exit."""
        src = self._ARR + """
public fn mk(@Array<Int> -> @NonEmptyArray)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @NonEmptyArray = mk([]); 0 }
"""
        _run_refine_trap(src, fn="entry")

    def test_tuple_component_param_guard_traps_on_negative(self) -> None:
        """A `Tuple<PosInt, Int>` parameter carries no *top-level* refinement,
        but its refined *components* are guarded at the boundary (the
        PR-review-found FFI gap): an external caller passing `Tuple(-5, 3)`
        traps on the violating component, while `Tuple(7, 3)` flows through.
        Calling the public fn with a Vera-constructed tuple models the FFI
        boundary — the construction site is value-position (statically
        obligated, no runtime guard), so only the callee's entry decomposition
        protects the boundary against an unverified / external caller."""
        src = self._PRE + """
public fn first(@Tuple<PosInt, Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn entry_bad(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ first(Tuple(0 - 5, 3)) }
public fn entry_ok(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ first(Tuple(7, 3)) }
"""
        _run_refine_trap(src, fn="entry_bad")
        assert _run(src, fn="entry_ok") == 0

    def test_tuple_component_return_guard_traps(self) -> None:
        """Symmetric exit guard: a `fn -> Tuple<PosInt, Int>` whose body yields
        a refinement-violating component traps at the boundary rather than
        handing back a Tier-1-violating tuple.  Exercises the
        `_has_guardable_tuple_components` early-return fix — the return has no
        top-level refinement and trivial ensures, yet must not short-circuit."""
        src = self._PRE + """
public fn mk(@Int -> @Tuple<PosInt, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(@Int.0, 3) }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<PosInt, Int> = mk(0 - 9); 0 }
"""
        _run_refine_trap(src, fn="entry")

    def test_nested_tuple_component_guard_traps(self) -> None:
        """Component decomposition recurses into nested tuples: a violating
        `PosInt` deep in `Tuple<Tuple<PosInt, Int>, Int>` traps at the
        boundary."""
        src = self._PRE + """
public fn nest(@Tuple<Tuple<PosInt, Int>, Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ nest(Tuple(Tuple(0 - 1, 2), 3)) }
"""
        _run_refine_trap(src, fn="entry")

    def test_nat_tuple_component_guard_traps(self) -> None:
        """A bare `@Nat` tuple component is guarded with the synthesised
        implicit `>= 0` (the message proves the base invariant is what fired),
        so a negative component into `Tuple<Nat, Int>` traps at the boundary."""
        src = """
public fn natc(@Tuple<Nat, Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ natc(Tuple(0 - 4, 3)) }
"""
        result = _compile_ok(src)
        with pytest.raises(RuntimeError, match=r"@Nat\.0 >= 0"):
            execute(result, fn_name="entry")

    def test_valid_tuple_components_pass_both_guards(self) -> None:
        """A satisfying tuple flows through both the exit (mk's return) and
        entry (first's param) component guards without a false trap."""
        src = self._PRE + """
public fn mk(@Int -> @Tuple<PosInt, Int>)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ Tuple(@Int.0, 3) }
public fn first(@Tuple<PosInt, Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ first(mk(5)) }
"""
        assert _run(src, fn="entry") == 0

    def test_generic_tuple_alias_component_guard_traps(self) -> None:
        """A GENERIC tuple alias (`type Box<T> = Tuple<T, Int>`) substitutes its
        type argument when resolving the component types, so `Box<PosInt>`
        guards its first component — `Box(Tuple(-5, 3))` traps at the boundary
        instead of the `PosInt` substitution being silently dropped (which left
        the component unguarded — CR PR-review)."""
        src = self._PRE + """
type Box<T> = Tuple<T, Int>;
public fn f(@Box<PosInt> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn entry_bad(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ f(Tuple(0 - 5, 3)) }
public fn entry_ok(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ f(Tuple(7, 3)) }
"""
        _run_refine_trap(src, fn="entry_bad")
        assert _run(src, fn="entry_ok") == 0

    def test_infinite_tuple_alias_fails_closed_with_e617(self) -> None:
        """A mutually-recursive (infinite) tuple alias would recurse forever
        through the component-guard decomposition; the depth limit FAILS CLOSED
        with a loud E617 rather than silently emitting partial guards (or
        hanging) — never a silent `return []` that drops deep components (CR
        PR-review)."""
        src = """
type A = Tuple<B, Int>;
type B = Tuple<A, Int>;
public fn f(@A -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
"""
        result = _compile(src)
        errs = [d for d in result.diagnostics
                if d.severity == "error" and d.error_code == "E617"]
        assert errs, (
            f"expected a fail-closed E617 for the infinite tuple alias; "
            f"diagnostics: {result.diagnostics}"
        )

    def test_refinement_over_tuple_component_guard_traps(self) -> None:
        """A refinement OVER a tuple (`type Pair = { @Tuple<PosInt, Int> | true
        }`) carries no top-level Tuple shape, so its refined *components* would
        cross the boundary unguarded behind the refinement.  `_resolve_tuple_
        type` unwraps the refinement, so `use_pair(Tuple(-5, 3))` traps on the
        `PosInt` component while `Tuple(7, 3)` flows through (CR PR-review)."""
        src = self._PRE + """
type Pair = { @Tuple<PosInt, Int> | true };
public fn use_pair(@Pair -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn entry_bad(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ use_pair(Tuple(0 - 5, 3)) }
public fn entry_ok(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ use_pair(Tuple(7, 3)) }
"""
        _run_refine_trap(src, fn="entry_bad")
        assert _run(src, fn="entry_ok") == 0

    def test_nested_refinement_over_tuple_guard_traps(self) -> None:
        """Component decomposition recurses through a refinement-over-tuple
        component too: a violating `PosInt` in `Tuple<Pair, Int>` (where `Pair =
        { @Tuple<PosInt, Int> | true }`) traps at the boundary (CR PR-review)."""
        src = self._PRE + """
type Pair = { @Tuple<PosInt, Int> | true };
public fn use_np(@Tuple<Pair, Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn entry_bad(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ use_np(Tuple(Tuple(0 - 5, 3), 9)) }
public fn entry_ok(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ use_np(Tuple(Tuple(7, 3), 9)) }
"""
        _run_refine_trap(src, fn="entry_bad")
        # Happy path: a valid nested value must flow through without the
        # component recursion over-trapping (CR PR-review).
        assert _run(src, fn="entry_ok") == 0

    def test_param_guard_fires_before_precondition(self) -> None:
        """The refined-parameter guard runs *before* explicit preconditions:
        a `requires` that itself depends on the refined param must not trap
        first.  Passing `0` to a `@NonZero` parameter reports the refinement
        violation (a contract-fail ``RuntimeError``) rather than the
        precondition's `10 / 0` integer-divide-by-zero WASM trap (CR
        re-review of 100f938)."""
        src = """
type NonZero = { @Int | @Int.0 != 0 };
public fn risky(@NonZero -> @Int)
  requires(10 / @NonZero.0 > 0) ensures(true) effects(pure)
{ @NonZero.0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ risky(0) }
"""
        result = _compile_ok(src)
        # The contract-fail channel raises RuntimeError carrying the
        # refinement message; a div-by-zero (i.e. precondition-first) would
        # instead surface as a bare wasmtime trap, failing this match.
        with pytest.raises(RuntimeError, match="Refinement violation"):
            execute(result, fn_name="entry")

    def test_return_guard_fires_before_ensures(self) -> None:
        """The refined-return guard runs *before* explicit ensures (symmetric
        with the param ordering): an `ensures(...)` that divides by the result
        must not trap first.  `coerce(0)` narrowing `0` into a `@NonZero`
        return reports the refinement violation, not the ensures' `100 / 0`
        integer-divide-by-zero (CR full-review of a48cd2c).  The ensures is a
        tautology (`x == x`) so it verifies, yet still emits the dividing
        expression at run time."""
        src = """
type NonZero = { @Int | @Int.0 != 0 };
public fn coerce(@Int -> @NonZero)
  requires(true)
  ensures(100 / @NonZero.result == 100 / @NonZero.result) effects(pure)
{ @Int.0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ coerce(0) }
"""
        # Guard-first -> "Refinement violation"; ensures-first -> a bare
        # div-by-zero trap that would fail this match.
        _run_refine_trap(src, fn="entry")

    def test_nat_base_param_guard_enforces_ge_zero(self) -> None:
        """A `{ @Nat | P }` parameter guard conjoins the implicit `>= 0` base
        invariant, so a negative value satisfying P (e.g. `-1` for `@Nat.0 <
        10`) is rejected at the boundary — not just P (CR f1f2a26).  Calling
        the public fn directly models an untrusted / FFI caller that bypasses
        any Vera call-site nat-narrowing guard, so only the entry guard
        protects the boundary."""
        src = """
type Small = { @Nat | @Nat.0 < 10 };
public fn f(@Small -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Small.0 }
"""
        result = _compile_ok(src)
        # -1 satisfies `< 10` but not `>= 0`: the guard message proves the
        # base invariant is conjoined into the lowered check.
        with pytest.raises(RuntimeError, match=r"@Nat\.0 >= 0"):
            execute(result, fn_name="f", args=[-1])
        assert _run(src, fn="f", args=[7]) == 7

    def test_aliased_nat_base_param_guard_enforces_ge_zero(self) -> None:
        """The `@Nat` `>= 0` conjoin follows the base's ALIAS chain: `type Age
        = Nat; type SmallAge = { @Age | @Age.0 < 10 }` is guarded too, so a
        negative value satisfying P (`-1 < 10`) is rejected at an FFI boundary
        — not only refinements written directly over `@Nat` (CR db24433).  The
        synthetic `>= 0` ref uses the binder key `@Age.0` (not `@Nat.0`) so it
        resolves against the pushed slot."""
        src = """
type Age = Nat;
type SmallAge = { @Age | @Age.0 < 10 };
public fn f(@SmallAge -> @Age)
  requires(true) ensures(true) effects(pure)
{ @SmallAge.0 }
"""
        result = _compile_ok(src)
        with pytest.raises(RuntimeError, match=r"@Age\.0 >= 0"):
            execute(result, fn_name="f", args=[-1])
        assert _run(src, fn="f", args=[7]) == 7

    def test_bool_base_param_guard_traps_on_false(self) -> None:
        """A `{ @Bool | P }` parameter guard fires at the boundary: passing the
        violating value (`false` for `@Bool.0`) traps via the refinement
        channel, while the satisfying value (`true`) flows through.  Bool args
        cross the WASM boundary as i32 0/1."""
        src = """
type TrueOnly = { @Bool | @Bool.0 };
public fn f(@TrueOnly -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @TrueOnly.0 }
"""
        _run_refine_trap(src, fn="f", args=[0])  # false violates `@Bool.0`
        assert _run(src, fn="f", args=[1]) == 1  # true satisfies it

    def test_float64_base_param_guard_traps_on_violation(self) -> None:
        """A `{ @Float64 | P }` parameter guard fires at the boundary: a value
        on the wrong side of the predicate (`-1.5` for `@Float64.0 > 0.0`)
        traps, while a satisfying value (`2.5`) passes.  Float64 args cross the
        boundary as Python floats."""
        src = """
type PosF = { @Float64 | @Float64.0 > 0.0 };
public fn f(@PosF -> @Float64)
  requires(true) ensures(true) effects(pure)
{ @PosF.0 }
"""
        _run_refine_trap(src, fn="f", args=[-1.5])
        assert _run_float(src, fn="f", args=[2.5]) == 2.5

    def test_nested_refinement_base_rejected_e600(self) -> None:
        """A refinement whose base resolves to ANOTHER refinement —
        `type Tiny = { @Pos | @Pos.0 < 10 }` over `type Pos = { @Int | @Int.0 >
        0 }` — is rejected at codegen with a clean E600, NOT a partial guard
        that checks only `< 10` and silently drops the inner `> 0` (which would
        wrongly accept `-1`).  The 'reject before codegen' choice (CR
        e6f17b7)."""
        src = """
type Pos = { @Int | @Int.0 > 0 };
type Tiny = { @Pos | @Pos.0 < 10 };
public fn f(@Tiny -> @Int) requires(true) ensures(true) effects(pure) { 0 }
"""
        result = _compile(src)
        errs = [d for d in result.diagnostics
                if d.severity == "error" and d.error_code == "E618"]
        assert errs, (
            f"expected E618 rejecting the nested refinement base; "
            f"diagnostics: {result.diagnostics}"
        )
        assert "resolves to another refinement" in errs[0].description

    def test_generic_call_in_refinement_predicate_rejected_e617(self) -> None:
        """A refinement predicate that calls a GENERIC function can't be
        lowered to a boundary runtime guard (the monomorphised instance isn't
        registered in the guard's context), so `_emit_refinement_check` catches
        the `CodegenSkip` and emits a clean E617 — NOT a raw traceback (the
        guard sites sit outside the body's CodegenSkip handler), and NOT a
        silent `return None` that would drop the guard the verifier recorded as
        runtime-checked (PR-review)."""
        src = """
private forall<T> fn always_true(@T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ true }
type Checked = { @Int | always_true(@Int.0) };
public fn f(@Checked -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Checked.0 }
"""
        result = _compile(src)
        errs = [d for d in result.diagnostics
                if d.severity == "error" and d.error_code == "E617"]
        assert errs, (
            f"expected E617 for the un-lowerable generic predicate; "
            f"diagnostics: {result.diagnostics}"
        )


class TestHeadOverRefinement655ShapeB:
    """`#655` Shape B — array indexing through a refinement-of-Array
    alias now compiles and runs cleanly.

    Pre-fix: `type NonEmptyArray = { @Array<Int> | predicate }` plus
    a function `head(@NonEmptyArray -> @Int) { @NonEmptyArray.0[0] }`
    parsed and type-checked OK, but codegen's
    `_infer_index_element_type` returned None — the
    `_alias_array_element` helper in `vera/wasm/inference.py` only
    followed `isinstance(target, ast.NamedType)` chains, so
    `RefinementType.base_type` was never unwrapped.  The `head`
    function got dropped via [E602] ("body contains unsupported
    expressions"), and any call site referenced a non-existent
    `$head` → `unknown func: $head` at WASM validation.

    Post-fix (v0.0.146): the alias-target lookup peels any
    `RefinementType` layers before checking whether the base is a
    `NamedType` pointing at `Array<T>`.  Refinement-of-Array
    aliases now resolve their element type the same as a bare
    `Array<T>`.

    This test pins both the compile contract (no [E602] for `head`,
    function gets exported) and the runtime contract
    (`head([1, 2, 3])` returns 1).
    """

    _HEAD_SRC = """
type NonEmptyArray = { @Array<Int> | array_length(@Array<Int>.0) > 0 };

private fn head(@NonEmptyArray -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @NonEmptyArray.0[0]
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  head([1, 2, 3])
}
"""

    def test_head_over_refinement_compiles_and_runs(self) -> None:
        """`head([1, 2, 3])` returns 1 — the function compiles and the
        call resolves to a real `$head` clone in WASM."""
        result = _compile_ok(self._HEAD_SRC)
        # `$head` must appear as a defined function in the WAT (not
        # dropped via [E602]).
        wat = result.wat or ""
        assert re.search(r"\(func \$head\b", wat), (
            f"Expected `(func $head ...)` definition in WAT after "
            f"#655 Shape B fix.  Pre-fix `head` was dropped via "
            f"[E602] and the call site referenced an absent "
            f"`$head`.  WAT excerpt: "
            f"{[line.strip() for line in wat.splitlines() if 'head' in line.lower()][:5]}"
        )
        # Runtime pin — `head([1, 2, 3]) == 1`.
        exec_result = execute(result, fn_name="main")
        assert exec_result.value == 1, (
            f"Expected head([1, 2, 3]) == 1; got {exec_result.value!r}"
        )

    def test_head_emits_no_e602_for_refinement_alias(self) -> None:
        """Compiling the head/NonEmptyArray fixture emits no
        `[E602]` warning for `head` — the function isn't dropped.

        Pre-fix the diagnostic stream contained
        `Function 'head' body contains unsupported expressions —
        skipped.` for every compile of this shape.  Post-fix that
        warning is absent.
        """
        result = _compile_ok(self._HEAD_SRC)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        head_e602 = [
            d for d in warnings
            if d.error_code == "E602"
            and d.description.startswith("Function 'head' ")
        ]
        assert not head_e602, (
            f"Expected no [E602] for `head`; got: "
            f"{[d.description for d in head_e602]}"
        )
