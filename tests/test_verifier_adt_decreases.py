"""Tests for vera.verifier — adt_decreases (match/ADT verification, decreases measures, mutual recursion).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations

import pytest

from vera.parser import parse_to_ast
from vera.checker import typecheck, typecheck_with_artifacts
from vera.resolver import ModuleResolver
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
        """All examples together: 411 T1 / 122 T3 / 533 total (current).

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
        * 411/122/533 after `ephemeris.vera` (#143) contributed 47 T1 +
          2 T3 + 49 contracts.  The two T3s are the `ensures` clauses of
        * 411/119/530 after #1362 stopped three `string_utilities.vera`
          `nat_to_int` arguments claiming a runtime guard that does not
          exist; they are disclosed (`tier3_unguarded`/E504) instead, and
          `tier3_unguarded` is counted in neither tier by design.
          `vec_norm` and `declination`, each standing on the far side of a
          `sqrt` or an `asin` — float builtins are opaque to the solver by
          design, so the claims are runtime-guarded rather than proved, and
          no solver budget reaches them.  Net: +47 T1, +2 T3, +49 total,
          +0 t3u.
        """
        # The DEFAULT budget is the premise: `conftest.py`'s autouse
        # `_default_z3_budget` scrubs an inherited VERA_Z3_TIMEOUT_MS so this
        # loop measures what TESTING.md publishes.
        t1 = t3 = total = t3u = 0
        for f in sorted(EXAMPLES_DIR.glob("*.vera")):
            text = f.read_text(encoding="utf-8")
            prog = parse_to_ast(text)
            # CLI parity (cmd_verify): resolve imports AND thread the #747
            # semantic-type side-tables into verify().  Without the resolver,
            # modules.vera's two imported-function obligations demote to
            # Tier-3; without the artifacts, target-type-dependent
            # obligations do — either way this pin would measure a pipeline
            # no user runs (PR #983 review).
            resolver = ModuleResolver(_root=f.parent)
            resolved = resolver.resolve_imports(prog, f)
            _diags, artifacts = typecheck_with_artifacts(
                prog, text, file=str(f), resolved_modules=resolved,
            )
            # The DEFAULT budget, deliberately.  This pin briefly carried an
            # explicit 60 s because `ephemeris.vera` had an obligation proving
            # in ~9-11 s against the 10 s default, which made the count a
            # property of host speed.  That obligation is gone — the example
            # bounds its eccentricity at construction now, rather than deriving
            # it through a division chain — so every obligation in the corpus
            # sits far from any plausible budget and the pin measures the
            # programs rather than the machine.  Verified flip-free across
            # [500 ms, 20 s], warm and cold (#1350).
            result = verify(prog, text, file=str(f),
                            resolved_modules=resolved,
                            expr_types=artifacts.expr_semantic_types,
                            expr_target_types=artifacts.expr_target_types)
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
        #
        # v0.0.196 doc sweep: examples/async_http_fanout.vera (the #841
        # concurrent-async showcase) joins the corpus — summarise's 0..3
        # range postcondition proves statically (+4 T1) while fetch_both's
        # effectful postcondition falls to runtime (+2 T3), +6 total:
        # 277/92/369 -> 281/94/375.
        #
        # #882: a call-site precondition over an argument (or a precondition)
        # outside the decidable fragment previously produced NO obligation —
        # a silent static-coverage gap.  It now demotes LOUDLY to a Tier-3
        # call_pre obligation (E532).  Three example call sites — `http::main`
        # -> fetch_title, `inference::main` -> classify_sentiment, and
        # `async_http_fanout::main` -> fetch_both — each call a helper whose
        # `requires(string_length(...) > 0)` is undecidable, so each gains one
        # demoted call_pre: +3 T3.
        #
        # #967: a demoted call_pre is a Tier-3 obligation, so it counts toward
        # `total` like any other runtime-checked obligation.  The pre-fix
        # hand-counted path bumped `tier3_runtime` but forgot the matching
        # `total`, leaving total short by three (one per demotion).  Deriving
        # the summary from the obligation stream closes it:
        # 281/94/375 -> 281/97/378.
        #
        # #758: the @Int -> @Nat narrowing obligation (nat_bind) now fires at
        # the RETURN position too (the dual of #813's 7c widen-return).  Two
        # corpus returns narrow into @Nat: `absolute_value.vera::absolute_value`
        # (`if @Int.0 >= 0 then @Int.0 else -@Int.0`) proves `>= 0` per-arm at
        # Tier 1 (+1 T1), and `nested_closures.vera::three_d_count`
        # (`array_length(...)` over an opaque let-bound array — array_length
        # returns @Int) is an honest Tier-3 runtime-guarded narrowing (+1 T3).
        #
        # Method correction (PR #983 review): every trajectory entry above
        # was measured through a bare `verify(prog, text)` call WITHOUT the
        # #747 semantic-type side-tables and WITHOUT resolved modules — both
        # of which the CLI always passes.  modules.vera's two
        # imported-function obligations therefore read Tier-3 here while
        # `vera verify` proves them Tier-1 (the bare-call figures were
        # 281/97/378 pre-#758).  The loop now resolves imports and threads
        # CLI parity ends at 284/96/380; #379's Inference + JSON example adds
        # six Tier-1 obligations, producing 290/96/386.
        #
        # #1094: examples/scoreboard.vera joins the corpus — build_board's
        # `map_size(...) == 4` postcondition and the two callers' non-empty-map
        # preconditions discharge statically (+8 T1) while the top_score /
        # roster_size / summary bodies fall to runtime (+3 T3), +11 total:
        # 290/96/386 -> 298/99/397.
        #
        # examples/maximum_syntax.vera (syntax-breadth showcase) joins the
        # corpus — its many trivial `requires(true)`/`ensures(true)` pairs
        # discharge statically (+39 T1), while `increment_and_return`'s
        # `old(State<Int>)`/`new(State<Int>)` postcondition (undecidable, plus
        # the two `int_overflow` sub-obligations it and its body carry) and
        # `roundtrip`'s `<Async>` postcondition fall to runtime (+4 T3),
        # +43 total: 298/99/397 -> 337/103/440.
        #
        # A later pass added the generic custom-effect demo (`effect
        # Logger<T>` + `log_twice`, showing `<Logger<Int>>` row
        # instantiation) to the same example — its trivial
        # `requires(true)`/`ensures(true)` pair discharges statically, same
        # shape as `count_to_three`'s: +2 T1, +0 T3, +2 total:
        # 337/103/440 -> 339/103/442.
        #
        # `to_percentage`'s `Percentage` refinement was rebased from Int
        # (0..100) to Float64 (0..1), converting through `int_to_float(...)
        # / 100.0`. Both of the function's own obligations that previously
        # discharged at Tier 1 -- its `==>` postcondition and the return
        # value's `refine_bind` into `@Percentage` -- now involve a float
        # division Z3 can't decide, so both drop to Tier 3: -2 T1, +2 T3,
        # +0 total (same two obligations, different tier): 339/103/442 ->
        # 337/105/442.
        #
        # A further pass filled in the remaining syntax gaps found by
        # comparing the example against grammar.lark / spec: a plain enum
        # `data Color` + wildcard match (`is_green`), `Tuple<A, B>`
        # construction/destructuring (`swap`), and a `Nat`-typed mutual
        # recursion pair declared via a trailing `where` block (`is_even`/
        # `is_odd`). All four are simple `requires(true)`/`ensures(true)`
        # pairs (`is_even`/`is_odd` also each add one `decreases`
        # obligation) that discharge statically, same shape as
        # `count_to_three`'s: +12 T1, +0 T3, +12 total: 337/105/442 ->
        # 349/105/454.
        #
        # #229: `examples/database.vera` (the `<DB>` effect demo) adds two
        # functions -- `insert_user` and `main` -- each carrying a trivial
        # `requires(true)`/`ensures(true)` pair (2 requires + 2 ensures) that
        # all discharge statically at Tier 1: +4 T1, +0 T3, +4 total:
        # 349/105/454 -> 353/105/458.
        #
        # #229: `examples/sqlitedb.vera` (the on-disk `<DB>` demo) likewise
        # adds two functions -- `format_row` and `main` -- with trivial
        # `requires(true)`/`ensures(true)` pairs (2 requires + 2 ensures), all
        # Tier 1: +4 T1, +0 T3, +4 total: 353/105/458 -> 357/105/462.
        #
        # #1172: `examples/gc_pressure.vera` declared its ACCUMULATOR as the
        # decreases measure (it grows every hop) -- caught by the new runtime
        # termination guard, which trapped the example at run.  Corrected to
        # the counter (`@Int.1`), which the verifier discharges at Tier 1
        # where the accumulator measure was Tier 3: +1 T1, -1 T3, +0 total:
        # 357/105/462 -> 358/104/462.
        #
        # #764: the tuple pseudo-constructor now translates in expression
        # position and `_translate_block` models a destructure, so the
        # syntax-tour `swap` (`Tuple<A, B>` construction + destructuring)
        # discharges an obligation at Tier 1 that the truncated body left
        # at Tier 3: +1 T1, -1 T3, +0 total: 358/104/462 -> 359/103/462.
        #
        # #779: the obligation walkers now descend into fresh-scope bodies
        # (closure bodies, quantifier predicates, handler clauses) and the
        # enclosing-scope handler bodies / quantifier domains, so primitive
        # ops and binding sites there are REPORTED instead of omitted.  All
        # 22 new corpus obligations are honest Tier-3 (fresh slots are
        # unconstrained by design) and Tier 1 is UNCHANGED — the empty
        # fresh-scope env can neither prove a false Tier-1 nor lose an
        # existing proof: +0 T1, +22 T3, +22 total: 359/103/462 ->
        # 359/125/484.
        #
        # #1214: a zero-size call argument no longer collapses the call
        # summary, so a call spelled `f(())` is modelled exactly as `f(1)`
        # already was.  Five obligations that could only be runtime-checked
        # while such a call was opaque now discharge statically — in
        # `collections.vera` (one) and `array_utilities.vera` (four, once its
        # helpers state the values their caller's `ensures` had been asserting
        # about them).  The obligation SET is unchanged, only the tier:
        # +5 T1, -5 T3, +0 total: 359/125/484 -> 364/120/484.
        #
        # #143: `ephemeris.vera`, the first floating-point example, adds
        # 47 T1 + 2 T3: 364/120/484 -> 411/122/533.
        #
        # #1362 then disclosed three of `string_utilities.vera`'s
        # `nat_to_int` arguments — 411/119/530 with 3 tier3_unguarded, the
        # three leaving `tier3_runtime` without joining any other count —
        # and PLANTING the missing guard put them back: `nat_to_int` now
        # emits the same narrowing guard every other `@Nat` entry point
        # does, so the obligations are runtime-guarded in fact and `tier3`
        # is true of them again.  Same three obligations, three statuses
        # across the two changes: a claimed guard that did not exist, an
        # honest disclosure, then a guard that does.  Only the last is both
        # true and quiet, which is why the corpus carries NO unguarded
        # narrowing: 411/119/530/3 -> 411/122/533/0.
        assert t1 == 411, f"Expected 411 T1, got {t1}"
        assert t3 == 122, f"Expected 122 T3, got {t3}"
        assert total == 533, f"Expected 533 total, got {total}"
        # Zero is the load-bearing value, not a vacuous one: every corpus
        # narrowing is now covered by an emitted guard, so any reappearance
        # is a REGRESSION in guard coverage rather than a new example.  The
        # disclosure path itself is exercised synthetically, in
        # `test_verifier_truth_consult_status.py`.
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


class TestWalkerBlindSpots1179:
    """PR #1179 adversarial review F1: `_walk_for_calls` skipped
    HandleExpr clauses and AnonFn bodies, so a measure-violating
    recursive call hidden there did not block a Tier-1 proof — a
    `verify`-green program then trapped at `run` on a terminating
    execution.  These pin the obligations as NOT verified."""

    @staticmethod
    def _decreases_statuses(source: str):
        import os
        import tempfile
        from vera.parser import parse_file
        from vera.transform import transform
        from vera.verifier import verify

        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8"
        ) as f:
            f.write(source)
            path = f.name
        try:
            prog = transform(parse_file(path))
        finally:
            os.unlink(path)
        vr = verify(prog, source=source, file=path)
        return [ob.status for ob in vr.obligations if ob.kind == "decreases"]

    def test_handler_clause_recursive_call_not_verified(self) -> None:
        statuses = self._decreases_statuses('-- P11: a handler clause re-enters the guarded function with a LARGER\n-- argument while an activation is live (terminating via the flag).\n-- Dynamic re-entry semantics say trap; the program terminates.\nprivate fn f(@Int, @Int -> @Int)\n  requires(@Int.1 >= 0)\n  ensures(true)\n  decreases(@Int.1)\n  effects(pure)\n{\n  if @Int.1 == 0 then {\n    0\n  } else {\n    if @Int.0 == 1 && @Int.1 == 2 then {\n      handle[State<Int>](@Int = 0) {\n        get(@Unit) -> { resume(f(9, 0) + @Int.0) },\n        put(@Int) -> { resume(()) }\n      } in {\n        get(())\n      }\n    } else {\n      f(@Int.1 - 1, @Int.0) + 1\n    }\n  }\n}\n\npublic fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n  effects(pure)\n{\n  f(3, 1)\n}\n')
        assert statuses and all(s != "verified" for s in statuses), (
            f"a recursive call inside a handle clause must block the "
            f"Tier-1 proof, got {statuses}"
        )

    def test_closure_body_recursive_call_not_verified(self) -> None:
        statuses = self._decreases_statuses('-- P16: recursive call hidden inside a closure body -- invisible to\n-- _walk_for_calls, so the decreases obligation verifies Tier 1, but the\n-- runtime guard sees the dynamic re-entry and traps.  Terminating.\nprivate fn f(@Int -> @Int)\n  requires(@Int.0 >= 0)\n  ensures(true)\n  decreases(@Int.0)\n  effects(pure)\n{\n  if @Int.0 == 0 then {\n    0\n  } else {\n    if @Int.0 >= 3 then {\n      7\n    } else {\n      if @Int.0 == 2 then {\n        f(@Int.0 - 1) + 10\n      } else {\n        nat_to_int(array_length(array_map([1], fn(@Int -> @Int) effects(pure) { f(@Int.0 + 3) }))) + 100\n      }\n    }\n  }\n}\n\npublic fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n  effects(pure)\n{\n  f(2)\n}\n')
        assert statuses and all(s != "verified" for s in statuses), (
            f"a recursive call inside a closure body must block the "
            f"Tier-1 proof, got {statuses}"
        )
