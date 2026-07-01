"""Tests for vera.verifier — primitive_ops (division/modulo-by-zero (E526) and array/string index-bounds (E527) obligations (#680)).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations


from tests.verifier_helpers import (
    _verify,
    _verify_err,
    _verify_ok,
)


class TestPrimitiveDivisionObligation680:
    """`a / b` and `a % b` (Int/Nat) carry a Tier-1 `b != 0` obligation (#680).

    Integer division and modulo by zero trap at runtime (`i64.div_s` /
    `i64.rem_s`).  The divisor lives in the Tier-1 decidable fragment
    (concrete integer arithmetic), so the obligation mirrors `@Nat`
    subtraction (#520): discharged from a precondition, path condition, or
    refinement type at Tier 1; a counterexample (`b = 0`) is a loud E526.

    Two exemptions: float division (`@Float64 / @Float64`) is Real-sorted
    and produces inf/NaN rather than trapping, so it is not obligated; and
    a non-zero integer literal divisor (`x / 5`) is trivially safe, mirroring
    #520's pure-literal exemption.
    """

    def test_unguarded_int_division_fails(self) -> None:
        """Bare `@Int.0 / @Int.1` without a guarding `requires` → E526.

        Counterexample: @Int.1 = 0.  This is silent/clean pre-#680.
        """
        _verify_err("""
private fn unsafe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""", "by zero")

    def test_unguarded_int_modulo_fails(self) -> None:
        """Bare `@Int.0 % @Int.1` carries the same `@Int.1 != 0` obligation."""
        _verify_err("""
private fn unsafe_mod(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 % @Int.1 }
""", "by zero")

    def test_unguarded_nat_division_fails(self) -> None:
        """`@Nat.0 / @Nat.1` — a @Nat divisor can still be 0 → E526."""
        _verify_err("""
private fn unsafe_nat_div(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 / @Nat.1 }
""", "by zero")

    def test_requires_nonzero_divisor_discharges(self) -> None:
        """`requires(@Int.1 != 0)` discharges the obligation at Tier 1."""
        _verify_ok("""
private fn safe_div(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""")

    def test_requires_nonzero_divisor_discharges_modulo(self) -> None:
        """`requires(@Int.1 != 0)` discharges a modulo obligation too."""
        _verify_ok("""
private fn safe_mod(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 % @Int.1 }
""")

    def test_if_guard_divisor_discharges(self) -> None:
        """Path condition `@Int.1 != 0` (else branch of `if @Int.1 == 0`)
        discharges `@Int.0 / @Int.1`.  This is the `checked_div` shape used
        in examples/effect_handler.vera."""
        _verify_ok("""
private fn guarded_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.1 == 0 then {
    0
  } else {
    @Int.0 / @Int.1
  }
}
""")

    def test_posint_refinement_divisor_discharges(self) -> None:
        """A `@PosInt = {@Int | @Int.0 > 0}` divisor discharges `> 0 ⟹ != 0`."""
        _verify_ok("""
type PosInt = { @Int | @Int.0 > 0 };

private fn refined_div(@Int, @PosInt -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 / @PosInt.0 }
""")

    def test_nonzero_literal_divisor_not_flagged(self) -> None:
        """`@Int.0 / 5` — a non-zero literal divisor is trivially safe and
        exempt (mirrors #520's pure-literal exemption); no obligation, so a
        bare `requires(true)` still verifies."""
        _verify_ok("""
private fn div_by_five(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 / 5 }
""")

    def test_float_division_not_obligated(self) -> None:
        """`@Float64.0 / @Float64.1` produces inf/NaN, not a trap — float
        division (Real-sorted divisor) carries no by-zero obligation."""
        _verify_ok("""
private fn float_div(@Float64, @Float64 -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
{ @Float64.0 / @Float64.1 }
""")

    def test_float64_shadow_divisor_records_no_obligation(self) -> None:
        """A `@Float64` divisor that is opaque (a non-literal destructure
        shadow, so `translate_expr`/the shadow path fires before the Real-sort
        check) must record NO `div_zero` obligation — float division is exempt
        regardless of translatability (`f64.div` by zero is inf/NaN, not a
        trap).  The float exemption keys on the divisor's resolved TYPE up
        front, before the None/shadow recordings (PR #778 review)."""
        result = _verify("""
private fn mk(@Float64 -> @Tuple<Float64, Float64>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Float64.0, @Float64.0) }

private fn fdiv(@Float64 -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Float64, @Float64> = mk(@Float64.0); @Float64.0 / @Float64.1 }
""")
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert divs == [], [(o.kind, o.status) for o in divs]

    def test_partial_requires_does_not_discharge(self) -> None:
        """`requires(@Int.0 != 0)` constrains the numerator, not the divisor
        `@Int.1` — the obligation still fires."""
        _verify_err("""
private fn wrong_guard(@Int, @Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""", "by zero")

    def test_division_obligation_recorded_div_zero_kind(self) -> None:
        """A guarded division records exactly one `div_zero` obligation,
        discharged (verified)."""
        result = _verify("""
private fn safe_div(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""")
        div = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(div) == 1, f"expected one div_zero obligation, got {len(div)}"
        assert div[0].status == "verified"

    def test_division_inside_array_literal_fires(self) -> None:
        """An unguarded division in an array-literal element is obligated
        (E526) — the walker recurses into `ArrayLit` elements, so the
        compile-error promise holds outside direct position too (#680 review)."""
        _verify_err("""
private fn arr_div(@Int, @Int -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ [@Int.0 / @Int.1, 99] }
""", "by zero")

    def test_division_inside_assert_fires(self) -> None:
        """An unguarded division in an `assert` condition is obligated (E526)
        — the walker recurses into Assert/Assume conditions (#680 review)."""
        _verify_err("""
private fn assert_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ assert(@Int.0 / @Int.1 > 0); @Int.0 }
""", "by zero")

    def test_safe_destructured_divisor_not_flagged(self) -> None:
        """A destructured non-zero divisor (`Tuple(10, 5)`) must NOT be a false
        E526.  The destructured slots are not rebound to fresh unconstrained
        vars — a fresh `@Int` has no `!= 0` invariant (unlike a `@Nat`'s
        `>= 0`), so rebinding would make the safe `5` divisor look like a
        possible zero.  (Regression guard for the #680 review's destructure
        walk.)"""
        _verify_ok("""
private fn ld_safe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Int, @Int> = Tuple(10, 5); @Int.0 / @Int.1 }
""")

    def test_division_inside_letdestruct_value_fires(self) -> None:
        """An unguarded division in a `let`-destructure value
        (`let Tuple<...> = Tuple(@Int.0 / @Int.1, ...)`) is obligated (E526) —
        the block walker walks the destructured value (#680 review)."""
        _verify_err("""
private fn ld_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Int, @Int> = Tuple(@Int.0 / @Int.1, 5); @Int.0 }
""", "by zero")

    def test_untranslatable_let_divisor_not_falsely_discharged(self) -> None:
        """An untranslatable scalar `let` (a `random_int` effect result the SMT
        layer doesn't model) that shadows a constrained outer must NOT let the
        outer's `requires(@Int.0 != 0)` falsely discharge a division by it.
        `requires(@Int.0 != 0); let @Int = random_int(0, 10); 1 / @Int.0` —
        random_int can be 0, so the division is unsafe and must be honest Tier-3
        (the shadowed value is unknown), not a false Tier-1 (#680 review).  This
        is the silent-failure differential: before the shadow fix it verified
        clean (Tier-1) yet trapped at runtime."""
        result = _verify("""
public fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"expected no error, got: {[e.description for e in errors]}"
        div = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(div) == 1 and div[0].status == "tier3", (
            "divisor must be honest Tier-3 (the shadowed let value is unknown), "
            f"got {[(o.kind, o.status) for o in div]}"
        )

    def test_division_inside_interpolated_string_fires(self) -> None:
        r"""An unguarded division in an interpolated-string expression
        (`"x: \(@Int.0 / @Int.1)"`) is obligated (E526) — the walker recurses
        into InterpolatedString parts, mirroring the @Nat-binding walker
        (#680 review)."""
        _verify_err(
            'private fn interp_div(@Int, @Int -> @String)\n'
            '  requires(true)\n'
            '  ensures(true)\n'
            '  effects(pure)\n'
            '{ "x: \\(@Int.0 / @Int.1)" }\n',
            "by zero",
        )

    def test_div_by_zero_fix_hint_renders_actual_divisor(self) -> None:
        """The E526 fix hint names the *actual* divisor, not a fixed slot.

        For `@Int.1 / @Int.0` the divisor is `@Int.0` (De Bruijn: most
        recent binding).  The pre-review hint hard-coded `@Int.1 != 0`,
        which points at the wrong parameter here; `format_expr(expr.right)`
        renders the real operand (PR #778 review, `verifier.py` E526 hint).
        """
        matched = _verify_err("""
private fn wrong_slot_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.1 / @Int.0 }
""", "by zero")
        fix = matched[0].fix
        assert "@Int.0 != 0" in fix, fix
        assert "@Int.1" not in fix, fix

    def test_literal_destructure_divisor_discharges_at_tier1(self) -> None:
        """A divisor projected from a literal-constructor destructure is
        Tier-1, not Tier-3.  `let Tuple<@Int, @Int> = Tuple(10, 6);
        @Int.0 / @Int.1` discharges `10 != 0` — the divisor `@Int.1` is the
        literal first component — rather than shadowing it to an opaque
        Tier-3 value (PR #778 review: rebind translatable components to
        their projected terms, mirroring the @Nat-binding walker)."""
        result = _verify("""
private fn lit_destr_div(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Int, @Int> = Tuple(10, 6); @Int.0 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [
            (o.kind, o.status) for o in divs
        ]

    def test_nonliteral_destructure_divisor_stays_tier3(self) -> None:
        """A divisor from a NON-literal destructure source (a call) can't be
        projected, so each component stays a tracked opaque shadow → Tier-3,
        never a false E526.  Guards the 77d90fb regression: a bare fresh
        `@Int` slot var carries no `!= 0` invariant and false-fired E526."""
        result = _verify("""
private fn mk(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Int.0, @Int.0) }

private fn nonlit_destr_div(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Int, @Int> = mk(@Int.0); @Int.0 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_untranslatable_destructure_component_keeps_debruijn(self) -> None:
        """An untranslatable destructured component with NO stale outer must
        still push a tracked placeholder, so same-type De Bruijn positions
        don't collapse.  `let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10));
        1 / @Int.0` must be Tier-3: `@Int.0` is the *opaque second component*,
        not the literal `10` it would shift onto if the component were skipped
        (PR #778 review, `verifier.py` De Bruijn collapse).  A skip here is a
        silent false-discharge — the worst #680 failure class."""
        result = _verify("""
private fn debruijn_keep(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10)); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_compound_shadow_divisor_is_tier3_not_e526(self) -> None:
        """A divisor that *contains* an opaque shadow (`shadow + 1`), not just
        one that IS a shadow, must fall to Tier-3 — Z3 must not pick
        `shadow = -1` and emit a false E526.  `let @Int = random_int(0, 10);
        1 / (@Int.0 + 1)` shadows the outer `@Int.0`, so the compound divisor
        is opaque (PR #778 review, `verifier.py` `_contains_opaque_shadow`)."""
        result = _verify("""
private fn compound_shadow(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / (@Int.0 + 1) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_opaque_match_scrutinee_shadows_arm_bindings(self) -> None:
        """A match arm binding over an UNTRANSLATABLE scrutinee (an effect op)
        must shadow its pattern slots, so a primitive op in the arm falls to
        Tier-3 — never discharged against a stale same-name outer slot.
        Without it, `match Source.next(()) { Some(@Int) -> 1 / @Int.0 }` under
        `requires(@Int.0 != 0)` silently verifies `1 / @Int.0` against the
        *outer* param's `!= 0` while the matched field can be 0 — a silent
        false-discharge (PR #778 review, outside-diff; the match-arm analogue
        of the untranslatable-`let` shadow, mirroring `_fresh_pattern_env`)."""
        result = _verify("""
effect Source {
  op next(Unit -> Option<Int>);
}

private fn opaque_match(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Source>)
{
  match Source.next(()) {
    Some(@Int) -> 1 / @Int.0,
    None -> 1
  }
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]


class TestPrimitiveIndexObligation680:
    """`arr[i]` carries a `0 <= i < array_length(arr)` obligation (#680).

    Array indexing traps at runtime (codegen emits a bounds check +
    `unreachable`).  Unlike division, the array length is an *uninterpreted*
    SMT function — spec §6.4.3 documents array bounds as needing reasoning
    beyond the Tier-1 decidable fragment (#427).  So the verifier uses a
    two-check: provably in bounds (a literal/refinement/precondition pins
    the length) → Tier 1; provably *out* of bounds (statically-known length
    the index exceeds, e.g. `[1,2,3][5]`) → loud E527; otherwise (opaque /
    dynamic length) → honest Tier 3, guarded by the runtime trap.  An
    unguarded dynamic index is therefore NOT an error — it degrades
    gracefully, never silently.

    String indexing is a type error (E161 "Cannot index String"), so there
    is no string-index obligation — `IndexExpr` is array-only.

    Index sites inside closure / quantifier bodies are intentionally not
    walked (the captured length is beyond Tier 1 without #427); they remain
    runtime-guarded.  `test_index_inside_closure_not_obligated` pins that.
    """

    def test_literal_in_bounds_index_discharges(self) -> None:
        """`[10, 20, 30][1]` — literal length 3, index 1 < 3 → Tier 1, no error."""
        _verify_ok("""
private fn second(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [10, 20, 30][1] }
""")

    def test_literal_out_of_bounds_index_fails(self) -> None:
        """`[1, 2, 3][5]` — provably out of bounds (5 >= 3) → loud E527."""
        _verify_err("""
private fn oob(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [1, 2, 3][5] }
""", "out of bounds")

    def test_requires_guarded_index_discharges(self) -> None:
        """`requires(@Nat.0 < array_length(@Array<Int>.0))` discharges the
        bounds obligation at Tier 1."""
        _verify_ok("""
private fn at(@Array<Int>, @Nat -> @Int)
  requires(@Nat.0 < array_length(@Array<Int>.0))
  ensures(true)
  effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")

    def test_if_guard_index_discharges(self) -> None:
        """`if @Nat.0 < array_length(arr) then arr[@Nat.0] else 0` — the
        then-branch path condition discharges the bounds obligation at Tier 1.
        The complementary `>= ... then 0 else arr[...]` shape (used in
        examples/life.vera) discharges via the negated else-branch condition."""
        _verify_ok("""
private fn at(@Array<Int>, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ if @Nat.0 < array_length(@Array<Int>.0) then { @Array<Int>.0[@Nat.0] } else { 0 } }
""")

    def test_refinement_nonempty_array_index_is_tier3(self) -> None:
        """A `@NonEmptyArray` refinement index is honest Tier 3, not an error.

        The `array_length(@Array<Int>.0) > 0` predicate is over a non-primitive
        (Array) base that Z3 cannot decide at Tier 1 (the same reason the
        refinement narrowing itself is a Tier-3 E506; see
        examples/refinement_types.vera and TestAdtDecreasesVerification's tier
        ledger).  So the `[0]` access degrades to a runtime-guarded Tier 3 —
        no error, never silent.  Lifting this to Tier 1 is #427 (Tier-2 array
        reasoning)."""
        result = _verify("""
type NonEmptyArray = { @Array<Int> | array_length(@Array<Int>.0) > 0 };

private fn head(@NonEmptyArray -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @NonEmptyArray.0[0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"expected no error, got: {[e.description for e in errors]}"
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3"

    def test_opaque_unguarded_index_is_tier3(self) -> None:
        """An unguarded index into a dynamic-length array is NOT an error —
        the length is opaque (beyond Tier 1), so it degrades to Tier 3,
        guarded by the runtime trap.  This is the honest-tiering differential:
        the obligation is RECORDED as tier3, not silently dropped.  (A wrong
        fix that emitted nothing would pass the no-error check but fail the
        obligation-recorded assertion.)"""
        result = _verify("""
private fn at(@Array<Int>, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"expected no error (Tier-3), got: {[e.description for e in errors]}"
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1, f"expected one index_bounds obligation, got {len(idx)}"
        assert idx[0].status == "tier3"

    def test_index_inside_closure_not_obligated(self) -> None:
        """An index inside an `array_map` closure body (a captured array) is
        NOT obligated — the walker does not recurse into closure bodies, where
        the captured length is beyond Tier 1 (#427).  Pinned via a differential:
        the closure body records ZERO index_bounds obligations.  A `_verify_ok`
        alone would NOT catch a walker that started recursing into AnonFn —
        the captured index degrades to honest Tier 3 (no error) — so we assert
        the obligation count directly.  (Mirrors ch05_capture_array_index.)"""
        result = _verify("""
private fn step_flat(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Array<Int>.0[0] }) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"expected no error, got: {[e.description for e in errors]}"
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert idx == [], f"closure-body index must not be obligated, got {len(idx)}"

    def test_index_obligation_recorded_index_bounds_kind(self) -> None:
        """A guarded index records exactly one `index_bounds` obligation,
        discharged (verified)."""
        result = _verify("""
private fn at(@Array<Int>, @Nat -> @Int)
  requires(@Nat.0 < array_length(@Array<Int>.0))
  ensures(true)
  effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1, f"expected one index_bounds obligation, got {len(idx)}"
        assert idx[0].status == "verified"

    def test_literal_index_equal_length_fails(self) -> None:
        """`[1, 2, 3][3]` — index exactly equal to the length is out of bounds
        → E527.  Pins the strict `<` in `i < length` (an off-by-one `<=` would
        let `[1,2,3][3]` through)."""
        _verify_err("""
private fn at_len(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [1, 2, 3][3] }
""", "out of bounds")

    def test_provably_negative_index_fails(self) -> None:
        """`[1, 2, 3][0 - 1]` — a provably-negative index is out of bounds
        regardless of length → E527.  Pins the lower-bound (`i >= 0`)
        conjunct."""
        _verify_err("""
private fn at_neg(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [1, 2, 3][0 - 1] }
""", "out of bounds")

    def test_int_index_upper_bound_only_guard_is_tier3(self) -> None:
        """A signed `@Int` index guarded ONLY on the upper bound
        (`requires(@Int.0 < array_length(...))`, no `>= 0`) is NOT proven —
        the index could be negative, so it stays honest Tier 3, not a false
        Tier-1.  If the obligation's `i >= 0` conjunct were dropped this would
        wrongly verify; the differential pins it."""
        result = _verify("""
private fn at_int(@Array<Int>, @Int -> @Int)
  requires(@Int.0 < array_length(@Array<Int>.0))
  ensures(true)
  effects(pure)
{ @Array<Int>.0[@Int.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"expected no error (Tier-3), got: {[e.description for e in errors]}"
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3"

    def test_op_inside_index_is_walked(self) -> None:
        """An unguarded division in the index sub-expression is obligated
        (E526) — the walker recurses into `expr.index` before checking the
        bound, so a trap buried in the index isn't silently lost."""
        _verify_err("""
private fn idx_div(@Array<Int>, @Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Array<Int>.0[@Int.0 / @Int.1] }
""", "by zero")

    def test_untranslatable_array_let_shadows_stale_outer(self) -> None:
        """An untranslatable array `let` (`array_append`, unmodelled by the SMT
        layer) must shadow a stale same-type outer array, so a later index does
        not resolve to the stale length and false-E527.  `let a = [1,2,3]; let a
        = array_append(a, 99); a[3]` is valid (the appended array has length 4),
        so it must NOT be E527 — the stale outer is replaced by a fresh
        (opaque) array, making the index honest Tier-3 (#680 review)."""
        _verify_ok("""
private fn append_index(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let @Array<Int> = [1, 2, 3]; let @Array<Int> = array_append(@Array<Int>.0, 99); @Array<Int>.0[3] }
""")

    def test_untranslatable_destructure_array_shadows_stale_outer(self) -> None:
        """A destructured array slot from an untranslatable destructure must
        also shadow a stale same-type outer array (#680 review) — `let a =
        [1,2,3]; let Tuple<@Array<Int>, @Int> = mk(...); a[5]` must be Tier-3,
        not a false E527 against the stale length 3."""
        _verify_ok("""
private fn mk(@Array<Int> -> @Tuple<Array<Int>, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Array<Int>.0, 0) }

private fn destructure_shadow(@Array<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let @Array<Int> = [1, 2, 3]; let Tuple<@Array<Int>, @Int> = mk(@Array<Int>.0); @Array<Int>.0[5] }
""")

    def test_index_oob_fix_hint_renders_operands_and_both_bounds(self) -> None:
        """The E527 fix hint names the actual collection and index, and
        covers BOTH bounds (`0 <= i && i < array_length(...)`) — not a
        fixed slot or an upper-bound-only guard (PR #778 review,
        `verifier.py` E527 hint).  `[10, 20, 30][5]` exercises the
        `ArrayLit` render path in `format_expr`."""
        matched = _verify_err("""
private fn oob_hint(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [10, 20, 30][5] }
""", "out of bounds")
        fix = matched[0].fix
        assert "0 <= 5 && 5 < array_length([10, 20, 30])" in fix, fix
