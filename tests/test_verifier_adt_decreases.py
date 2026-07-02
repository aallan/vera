"""Tests for vera.verifier — adt_decreases (match/ADT verification, decreases measures, mutual recursion).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations

import pytest

from vera.parser import parse_to_ast
from vera.checker import typecheck
from vera.verifier import verify

from tests.verifier_helpers import (
    EXAMPLES_DIR,
    _verify,
    _verify_err,
    _verify_ok,
)


# =====================================================================
# Phase A: Match + ADT verification tests
# =====================================================================

class TestMatchAndAdtVerification:
    """Tests for match expression and ADT constructor Z3 translation."""

    # -- Simple match on ADT -----------------------------------------------

    def test_match_trivial_nat_result(self) -> None:
        """Match on ADT with Nat result verifies postcondition."""
        source = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private fn length(@List<Int> -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}
"""
        result = _verify(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Unexpected errors: {[e.description for e in errors]}"
        # The ensures should be Tier 1 verified (not T3 fallback)
        warns_e522 = [d for d in result.diagnostics
                      if d.error_code == "E522"]
        assert warns_e522 == [], "Match body should be translatable (no E522)"

    def test_match_simple_int_result(self) -> None:
        """Match returning a simple int value is verifiable."""
        source = """\
private data Color {
  Red,
  Green,
  Blue
}

private fn color_value(@Color -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Color.0 {
    Red -> 1,
    Green -> 2,
    Blue -> 3
  }
}
"""
        _verify_ok(source)

    def test_match_two_arm_postcondition(self) -> None:
        """Match with two arms can verify a specific postcondition."""
        source = """\
private data Bit {
  Zero,
  One
}

private fn bit_value(@Bit -> @Int)
  requires(true)
  ensures(@Int.result >= 0 && @Int.result <= 1)
  effects(pure)
{
  match @Bit.0 {
    Zero -> 0,
    One -> 1
  }
}
"""
        _verify_ok(source)

    def test_match_postcondition_violation(self) -> None:
        """Match with a wrong postcondition is caught."""
        source = """\
private data Bit {
  Zero,
  One
}

private fn bit_value(@Bit -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Bit.0 {
    Zero -> 0,
    One -> 1
  }
}
"""
        _verify_err(source, "does not hold")

    # -- Constructor translation -------------------------------------------

    def test_nullary_constructor_in_body(self) -> None:
        """Nullary constructors in function bodies are translatable."""
        source = """\
private data Maybe {
  Nothing,
  Just(Int)
}

private fn always_nothing(@Int -> @Maybe)
  requires(true)
  ensures(true)
  effects(pure)
{ Nothing }
"""
        _verify_ok(source)

    def test_constructor_call_in_body(self) -> None:
        """Constructor calls with args in function bodies are translatable."""
        source = """\
private data Maybe {
  Nothing,
  Just(Int)
}

private fn wrap(@Int -> @Maybe)
  requires(true)
  ensures(true)
  effects(pure)
{ Just(@Int.0) }
"""
        _verify_ok(source)

    # -- ADT parameter declarations ----------------------------------------

    def test_adt_param_declaration(self) -> None:
        """Functions with ADT parameters should declare proper Z3 vars."""
        source = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private fn is_nil(@List<Int> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> true,
    Cons(@Int, @List<Int>) -> false
  }
}
"""
        _verify_ok(source)

    # -- The list_ops.vera example -----------------------------------------

    def test_list_ops_length_no_e522(self) -> None:
        """Ensure list_ops.vera length() no longer gets E522."""
        source = EXAMPLES_DIR / "list_ops.vera"
        if not source.exists():
            pytest.skip("list_ops.vera not found")
        text = source.read_text(encoding="utf-8")
        ast = parse_to_ast(text)
        typecheck(ast, text)
        result = verify(ast, text, file=str(source))
        e522 = [d for d in result.diagnostics if d.error_code == "E522"]
        assert e522 == [], (
            f"list_ops.vera should not have E522 warnings: "
            f"{[d.description for d in e522]}"
        )


# =====================================================================
# Phase B: Decreases verification tests
# =====================================================================

class TestDecreasesVerification:
    """Tests for termination metric verification."""

    def test_simple_nat_decreases(self) -> None:
        """Simple Nat decreases on factorial is Tier 1."""
        source = """\
private fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 1 }
  else { @Nat.0 * factorial(@Nat.0 - 1) }
}
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], "Nat decreases should be verified (no E525)"
        assert result.summary.tier1_verified >= 3  # requires + ensures + decreases

    def test_nat_decreases_sum(self) -> None:
        """Nat decreases on a summation function is Tier 1."""
        source = """\
private fn sum_to(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 }
  else { @Nat.0 + sum_to(@Nat.0 - 1) }
}
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], "Nat decreases should be verified (no E525)"

    def test_mutual_recursion_verified(self) -> None:
        """Mutual recursion decreases are now verified via where-block groups."""
        source = EXAMPLES_DIR / "mutual_recursion.vera"
        if not source.exists():
            pytest.skip("mutual_recursion.vera not found")
        text = source.read_text(encoding="utf-8")
        ast = parse_to_ast(text)
        typecheck(ast, text)
        result = verify(ast, text, file=str(source))
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], "Mutual recursion decreases should be verified"
        assert result.summary.tier3_runtime == 0

    def test_factorial_example_all_t1(self) -> None:
        """factorial.vera: one Tier-3 contract (the #798 overflow guard)."""
        source = EXAMPLES_DIR / "factorial.vera"
        if not source.exists():
            pytest.skip("factorial.vera not found")
        text = source.read_text(encoding="utf-8")
        ast = parse_to_ast(text)
        typecheck(ast, text)
        result = verify(ast, text, file=str(source))
        # #798: the `@Nat.0 * factorial(@Nat.0 - 1)` multiply emits an
        # int_overflow obligation; operands are unbounded so it falls to
        # Tier 3 (runtime overflow trap).  All other contracts stay Tier 1.
        assert result.summary.tier3_runtime == 1, (
            f"factorial.vera should have 1 T3, got {result.summary.tier3_runtime}"
        )


# =====================================================================
# Phase C: ADT decreases verification tests
# =====================================================================

class TestAdtDecreasesVerification:
    """Tests for ADT structural ordering in decreases clauses."""

    def test_list_length_decreases(self) -> None:
        """List length with structural decreases is Tier 1."""
        source = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private fn length(@List<Int> -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@List<Int>.0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], "ADT decreases should be verified (no E525)"
        # #798: the `1 + length(...)` add emits an int_overflow obligation;
        # operands are unbounded so it falls to Tier 3 (runtime overflow trap).
        assert result.summary.tier3_runtime == 1

    def test_list_sum_decreases(self) -> None:
        """List sum with structural decreases is Tier 1."""
        source = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private fn sum(@List<Int> -> @Int)
  requires(true)
  ensures(true)
  decreases(@List<Int>.0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> @Int.0 + sum(@List<Int>.0)
  }
}
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], "ADT decreases should be verified (no E525)"

    def test_list_ops_all_tier1(self) -> None:
        """list_ops.vera: two Tier-3 contracts (the #798 overflow guards)."""
        source = EXAMPLES_DIR / "list_ops.vera"
        if not source.exists():
            pytest.skip("list_ops.vera not found")
        text = source.read_text(encoding="utf-8")
        ast = parse_to_ast(text)
        typecheck(ast, text)
        result = verify(ast, text, file=str(source))
        # #798: the `1 + length(...)` and `@Int.0 + sum(...)` adds each emit an
        # int_overflow obligation; operands are unbounded so both fall to Tier 3
        # (runtime overflow trap).  The Tier-1 count is unchanged.
        assert result.summary.tier3_runtime == 2, (
            f"list_ops.vera should have 2 T3, got {result.summary.tier3_runtime}"
        )
        assert result.summary.tier1_verified == 8

    def test_overall_tier_counts(self) -> None:
        """All examples together: 277 T1 / 92 T3 / 369 total (current).

        Counts move when examples are added or their contracts become
        more / less verifiable.  Trajectory:

        * 184/23/207 baseline including `array_utilities.vera` (v0.0.117).
        * 213/26/239 after `string_utilities.vera` (#470 + #471 phase 1)
          contributed 29 T1 + 3 T3 + 32 contracts.
        * 219/26/245 after `nested_closures.vera` (#514, v0.0.121)
          contributed 6 T1 + 6 contracts.
        * 222/26/248 after #520 added @Nat subtraction underflow
          obligations.  factorial.vera (+1) and mutual_recursion.vera
          (+2) each have @Nat.0 - 1 sites that the verifier now
          discharges from path conditions.
        * 254/26/280 after `life.vera` (Stage 12 launch) contributed
          32 T1 + 32 contracts including the formal Conway B3/S23
          rule on `next_cell`.
        * 252/26/278 after v0.0.145 — `examples/closures.vera` shed
          the private `option_map` workaround (#604 fix); the removed
          shadow had a `requires(true) ensures(true)` pair
          contributing 2 T1 + 2 contracts that no longer appear.
        * 253/25/278 after v0.0.153 — #667 (SMT translator coverage
          for FloatLit / IndexExpr / ArrayLit).  The shift comes
          entirely from `examples/json.vera::main`'s contract
          relaxation: pre-#667 the body translation failed (FloatLit
          returned None), so the postcondition `ensures(@Int.result
          == 0)` dropped to Tier 3 with an E522 warning ("Cannot
          statically verify postcondition…") — counted in the 26
          T3.  Post-#667 the body translates fully and the verifier
          reaches the contradiction (helpers have `ensures(true)`,
          so `@Int.result == 0` isn't provable); the contract was
          honestly relaxed to `ensures(true)`, which trivially
          verifies T1.  Net: -1 T3 (was a T3-with-warning) + 1 T1
          (the relaxed `ensures(true)`) = +1 T1, -1 T3, total
          unchanged at 278.  No other example contract changed
          tier under #667.
        * 255/25/280 after `examples/read_char.vera` (#618 terminal
          implementation) added 2 T1 + 2 contracts — the trivial
          `requires(true) ensures(true)` on `main`.  Net: +2 T1,
          +2 total.
        * 256/28/284 after #552 generalised the @Nat `>= 0` invariant
          to all binding sites.  `json.vera` gains 1 T1 (a
          provably-safe @Int→@Nat narrowing).  `string_utilities.vera`
          gains 3 T3: each `nat_to_int(array_length(...))` narrows
          array_length's @Int result into nat_to_int's @Nat param, and
          array_length is untranslatable to Z3 so the `>= 0` obligation
          drops to a Tier-3 runtime guard.  Net: +1 T1, +3 T3, +4 total.
        * 256/25/281 after the #552 review round.  `string_utilities.vera`'s
          three `nat_to_int(array_length(...))` narrowings were treated as
          non-`let` sites with no codegen runtime guard, so each was surfaced
          as an E504 `tier3_unguarded` warning and excluded from the totals
          rather than counted as a runtime check: -3 T3, -3 total,
          +3 tier3_unguarded.
        * 256/28/284 after #747 (PR #756) extended codegen's runtime guard to
          the concrete @Nat *call-argument* site (`vera/wasm/calls.py`).  The
          three `nat_to_int(array_length(...))` narrowings pass an opaque @Int
          into nat_to_int's CONCRETE @Nat formal, which codegen now traps on
          `< 0` at run time — so each is correctly a codegen-guarded
          `tier3_runtime` again, not an E504: +3 T3, +3 total,
          -3 tier3_unguarded.  Only genuinely-unguarded sites (effect-op
          arguments, generic-instantiated fields/args whose @Nat erases to
          i64 — #754) still warn, and no example exercises one: +0
          tier3_unguarded.
        * 258/29/287/0 after #746 generalised the @Nat discharge to arbitrary
          refinement predicates and added a codegen runtime guard.
          `refinement_types.vera` gains 2 T1 — the `safe_divide(10, 3)`
          argument now discharges `3 > 0` into its `@PosInt` formal, and
          `to_percentage`'s body now discharges its `@Percentage` return
          predicate (`>= 0 && <= 100`) — and 1 T3: `head([42, 1, 2])` narrows
          into `@NonEmptyArray`, whose `array_length(...) > 0` predicate is over
          a non-primitive (`Array`) base Z3 cannot decide, so it is a
          runtime-checked Tier-3 (an informational E506; codegen emits the
          predicate guard at the function boundary).  Net: +2 T1, +1 T3,
          +3 total, +0 tier3_unguarded.
        * 260/27/287/0 after #732 verified instantiated generics per
          monomorphization.  `generics.vera`'s `identity` and `const` are
          instantiated at concrete types (`identity<Int>`, `const<Int, Bool>`),
          so their `ensures(@T.result == @T.0)` / `ensures(@A.result == @A.0)`
          postconditions are now discharged statically instead of bailing to
          Tier 3 (E520): +2 T1, -2 T3, +0 total (the two contracts change tier;
          the total is unchanged).
        * 263/32/295/0 after #680 auto-synthesised obligations for integer
          division/modulo (`b != 0`, E526) and array indexing
          (`0 <= i < array_length`, E527).  The corpus gains 3 T1 from guarded
          divisions discharged at Tier 1 — effect_handler's path-guarded
          `@Int.0 / @Int.1`, refinement_types' `@PosInt` divisor, and
          safe_divide's `requires(@Int.1 != 0)` — and 5 T3: json's opaque
          divisor (1) plus opaque / dynamic array indices in json (1),
          life (2, deeply-nested match+if guards beyond Tier 1), and
          refinement_types' `@NonEmptyArray` (1, an Array-base refinement Z3
          cannot decide at Tier 1 — #427).  No example indexes provably out of
          bounds, so none is a loud E527.  Net: +3 T1, +5 T3, +8 total, +0 t3u.
        * 263/31/294/0 after the #680-review Float64-divisor fix: json's `/`
          divisor resolves to `@Float64`, so it is now exempt up front
          (`f64.div` by zero is inf/NaN, not a trap) instead of recording a
          bogus Tier-3 `div_zero` — it was the corpus's only tier3 div_zero.
          -1 T3, -1 total.

        #801 + #800: contract-position divisions now carry the same div_zero
        obligation as body divisions, and body `assert(P)` predicates now carry
        a Tier-1 proof obligation.  One safe (guarded) contract division and
        one provable body assert in the corpus each discharge to Tier 1
        (+2 T1, +2 total over the pre-fix baseline of 263 / 294).

        #798: every @Int/@Nat `+`/`-`/`*` (in bodies AND contract clauses;
        @Nat subtraction is excluded — that's the existing nat_sub underflow
        obligation) now carries an int_overflow obligation.  The corpus gains
        55 such obligations: 8 discharge at Tier 1 (all in life.vera, where
        the cell-coordinate operands are provably bounded into i64 range) and
        47 fall to Tier 3 (unbounded operands → runtime overflow trap).  Net:
        +8 T1, +47 T3, +55 total, +0 tier3_unguarded — verified by
        reconstructing the prior 265/31/296/0 baseline with int_overflow
        obligations excluded.

        #802: string_length on a non-literal argument now defers to Tier 3
        (Z3's Length counts code points, Vera counts UTF-8 bytes), so two
        example contracts over a slot-arg string_length move T1 -> T3.  Net:
        -2 T1, +2 T3, +0 total (the obligations persist, only their tier
        changes): 273/78/351 -> 271/80/351.

        #807: float_to_int(x) now carries a domain obligation (NaN / Inf /
        out-of-i64-range, E529) at every site.  `json.vera` has one SYMBOLIC
        site — `float_to_int(@Float64.0 * 10.0)` — which defers to Tier 3 (Z3's
        FP<->Real reasoning is unreliable, so symbolic float_to_int is concrete-
        gated to Tier 3, guarded by the codegen trunc trap).  No example has a
        concrete float_to_int site, so no T1 is added.  Net: +1 T3, +1 total:
        271/80/351 -> 271/81/352.

        #815: `examples/modules.vera` renamed its built-in calls
        (`abs(max(...))` -> `magnitude(larger(...))`, `vera.math::abs` ->
        `vera.math::magnitude`) to avoid the new E151 built-in-redefinition
        error.  The built-in `abs` carried a Tier-1-known `result >= 0`
        postcondition the verifier discharged statically; the user-defined
        `magnitude`/`larger` shed it, so one obligation moves T1 -> T3.  Net:
        -1 T1, +1 T3, +0 total: 271/81/352 -> 270/82/352.
        """
        t1 = t3 = total = t3u = 0
        for f in sorted(EXAMPLES_DIR.glob("*.vera")):
            text = f.read_text(encoding="utf-8")
            prog = parse_to_ast(text)
            typecheck(prog, text)
            result = verify(prog, text, file=str(f))
            t1 += result.summary.tier1_verified
            t3 += result.summary.tier3_runtime
            total += result.summary.total
            t3u += sum(1 for o in result.obligations
                       if o.status == "tier3_unguarded")
        # #813: the @Nat -> @Int widening obligation (nat_to_int_coerce) fires at
        # every genuine widening across the corpus — each a @Nat value flowing
        # into an @Int slot that can exceed i64.MAX, so honest Tier-3
        # (runtime-guarded) unless the value is provably bounded.
        #   Stage 2a (return position): `array_utilities.vera::count_above_cutoff`
        #   (a @Nat fold result) and `::lowest_grade`, `html.vera::text_length`
        #   (string_length is @Nat), `nested_closures.vera::grid_sum` — +4 T3:
        #   270/82/352 -> 270/86/356.
        #   Stage 2b (binding sites): `generics.vera::test_generics`
        #   (`let @Int = identity(42)`, identity<Nat>) +1 T3; `string_ops.vera::main`
        #   (`let @Int = string_length("hello")` — verified, literal length) +1 T1
        #   and (`to_string(@Nat.0)` call-arg from a parse_nat result) +1 T3:
        #   270/86/356 -> 271/88/359.
        #
        # #813 follow-up site 1 (the explicit `nat_to_int` built-in): its declared
        # @Int return previously masked the @Nat source, so `nat_to_int(@Nat.x)`
        # widenings went unobligated.  Now obligated like an implicit widening —
        # `json.vera::average`, `life.vera::initial_cell` (x2), `life.vera::make_grid`
        # each call `nat_to_int(@Nat.x)` on an unbounded @Nat: +4 T3, +4 total:
        # 271/88/359 -> 271/92/363.  (Site 2a — a literal-arm heterogeneous
        # if/match — adds no corpus obligation: no example has that shape.)
        #
        # #305 (v0.0.193): examples/http_server.vera joins the corpus —
        # its status_of range postcondition and the trivial handler /
        # body_for contracts all discharge statically: +6 T1, +6 total:
        # 271/92/363 -> 277/92/369.
        assert t1 == 277, f"Expected 277 T1, got {t1}"
        assert t3 == 92, f"Expected 92 T3, got {t3}"
        assert total == 369, f"Expected 369 total, got {total}"
        assert t3u == 0, f"Expected 0 tier3_unguarded, got {t3u}"


# =====================================================================
# Mutual recursion decreases verification tests
# =====================================================================

class TestMutualRecursionDecreases:
    """Verify decreases clauses for mutually recursive where-block functions."""

    def test_mutual_recursion_decreases_verified(self) -> None:
        """is_even/is_odd with matching decreases(@Nat.0) both verify."""
        source = """\
public fn is_even(@Nat -> @Bool)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { true } else { is_odd(@Nat.0 - 1) }
}
  where {
    fn is_odd(@Nat -> @Bool)
      requires(true)
      ensures(true)
      decreases(@Nat.0)
      effects(pure)
    {
      if @Nat.0 == 0 then { false } else { is_even(@Nat.0 - 1) }
    }
  }
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], f"Expected no E525, got {e525}"
        assert result.summary.tier3_runtime == 0

    def test_sibling_without_decreases_stays_tier3(self) -> None:
        """If a sibling has no decreases clause, caller stays Tier 3."""
        source = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { g(@Nat.0 - 1) }
}
  where {
    fn g(@Nat -> @Nat)
      requires(true)
      ensures(true)
      effects(pure)
    {
      if @Nat.0 == 0 then { 0 } else { f(@Nat.0 - 1) }
    }
  }
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert len(e525) == 1, "f's decreases should be Tier 3 (sibling has none)"

    def test_where_block_contracts_verified(self) -> None:
        """Where-block functions have their own contracts verified."""
        source = """\
public fn outer(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  effects(pure)
{
  helper(@Nat.0)
}
  where {
    fn helper(@Nat -> @Nat)
      requires(true)
      ensures(@Nat.result >= 0)
      effects(pure)
    {
      @Nat.0
    }
  }
"""
        result = _verify(source)
        # Both outer and helper have requires + ensures = 4 contracts
        assert result.summary.tier1_verified == 4
        assert result.summary.tier3_runtime == 0

    def test_mutual_recursion_example_all_t1(self) -> None:
        """mutual_recursion.vera should have zero Tier 3 contracts."""
        source = EXAMPLES_DIR / "mutual_recursion.vera"
        if not source.exists():
            pytest.skip("mutual_recursion.vera not found")
        text = source.read_text(encoding="utf-8")
        prog = parse_to_ast(text)
        typecheck(prog, text)
        result = verify(prog, text, file=str(source))
        assert result.summary.tier3_runtime == 0
        # 8 contract obligations + 2 @Nat.0 - 1 underflow obligations
        # (#520) — both discharged from `if @Nat.0 == 0` path condition.
        assert result.summary.tier1_verified == 10
