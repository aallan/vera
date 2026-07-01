"""Tests for vera.codegen — nat_guards (@Nat subtraction-underflow and binding-site narrowing runtime guards).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re

import pytest
import wasmtime

from vera.codegen import (
    compile,
    execute,
)

from tests.codegen_helpers import (
    _compile_ok,
    _run,
)


# =====================================================================
# @Nat subtraction underflow runtime guard (#520)
# =====================================================================

class TestNatSubtractionRuntimeGuard520:
    """Codegen emits a runtime underflow guard for `@Nat - @Nat`.

    The verifier (vera/verifier.py, #520 commit b446cac) emits a
    Tier-1 proof obligation `lhs >= rhs` at every @Nat-Nat
    subtraction site.  The codegen mirrors that detection (same
    helpers — _is_static_nat_typed + _has_nat_origin_codegen) and
    emits a runtime guard that traps on underflow.

    The guard exists because `vera compile` doesn't run the verifier
    — programs that skip `vera verify` would otherwise produce
    silent negative @Nat values.  When verification has run and
    discharged the obligation statically, the runtime guard is
    redundant but cheap (one i64 compare + branch); a Tier-1
    skip-channel is a future optimization.
    """

    # Body uses `@Nat.1 - @Nat.0` (first param minus second param)
    # rather than `@Nat.0 - @Nat.1` so the call-site argument order
    # reads naturally — De Bruijn `@T.0` is the most recent (last)
    # binding, so `unsafe(a, b)` with body `@Nat.0 - @Nat.1` would be
    # `b - a` and easy to misread.  See CLAUDE.md / DE_BRUIJN.md.
    _GUARDED_SUB = """
private fn unsafe(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.1 - @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  unsafe(0, 1)
}
"""

    _SAFE_SUB = """
private fn safe(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.1 - @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  safe(5, 3)
}
"""

    def test_underflow_traps_at_runtime(self) -> None:
        """unsafe(0, 1) traps via the runtime guard.

        Without the guard, `i64.sub` would produce -1 silently and
        store it in a @Nat slot, violating the type invariant. With
        the guard, the function traps cleanly before the bad value
        propagates.
        """
        result = _compile_ok(self._GUARDED_SUB)
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
            execute(result, fn_name="main", args=[])

    def test_safe_subtraction_returns_correct_result(self) -> None:
        """safe(5, 3) returns 2 — guard passes through cleanly.

        The guard is `if (i64.lt_s lhs rhs) then unreachable end`, so
        when lhs >= rhs the branch is not taken and the subtraction
        proceeds normally.  Confirms the guard doesn't introduce a
        regression on the happy path.
        """
        assert _run(self._SAFE_SUB) == 2

    def test_guard_emitted_in_wat_for_nat_sub(self) -> None:
        """The guarded WAT contains `i64.lt_s` and `unreachable`.

        Structural assertion that the codegen actually inserted the
        guard sequence rather than emitting a bare `i64.sub`.  The
        unguarded WAT (e.g. for `@Int - @Int`) would contain
        `i64.sub` but no `i64.lt_s` paired with `unreachable`.
        """
        result = _compile_ok(self._GUARDED_SUB)
        wat = result.wat
        # Both the comparison and the trap must appear inside `unsafe`
        # (the function with the @Nat-Nat subtraction).
        unsafe_idx = wat.find("(func $unsafe")
        assert unsafe_idx >= 0, "unsafe function not found in WAT"
        # Slice out the `unsafe` body up to the next top-level paren.
        body_end = wat.find("\n  (func ", unsafe_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[unsafe_idx:body_end]
        assert "i64.lt_s" in body, (
            f"Expected `i64.lt_s` in unsafe body for underflow guard, "
            f"got: {body!r}"
        )
        assert "unreachable" in body, (
            f"Expected `unreachable` in unsafe body for underflow guard, "
            f"got: {body!r}"
        )

    def test_int_subtract_emits_no_nat_underflow_guard(self) -> None:
        """`@Int - @Int` does not get the #520 *nat-sub underflow* guard.

        Sister to the structural test above: the #520 nat-sub guard fires only
        on sites where the result is statically @Nat AND at least one operand
        has @Nat origin.  @Int - @Int is not such a site (Int can be negative),
        so it must NOT carry the nat-sub guard — which would wrongly trap on a
        legitimate negative result like ``5 - 10``.

        Note (#798): @Int - @Int now DOES carry the *overflow* guard, a
        distinct mechanism — the two-XOR signed-overflow test
        ``((a^b) & (a^r)) < 0`` followed by ``unreachable``.  That guard does
        not fire on ``5 - 10`` (in range), so the runtime behaviour this test
        cares about (no spurious trap on a negative Int result) is unchanged.
        The discriminator below is therefore the *shape*: the #520 guard
        compares the two operands directly (``i64.lt_s`` on lhs/rhs straight
        after loading them, no ``i64.xor``), whereas the #798 overflow guard
        is XOR-based.  We assert the overflow-guard shape is present and the
        nat-sub shape (an ``i64.lt_s`` not preceded by the XOR sign-test) is
        not the mechanism, by pinning runtime behaviour: ``5 - 10 = -5`` must
        return cleanly, never trap.
        """
        src = """
private fn int_sub(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.1 - @Int.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  int_sub(5, 10)
}
"""
        result = _compile_ok(src)
        wat = result.wat
        int_sub_idx = wat.find("(func $int_sub")
        assert int_sub_idx >= 0
        body_end = wat.find("\n  (func ", int_sub_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[int_sub_idx:body_end]
        # i64.sub must be present (it's the actual subtraction).
        assert "i64.sub" in body
        # The #798 overflow guard IS present — and is XOR-based (the signed
        # overflow test), distinguishing it from the #520 nat-sub guard which
        # never uses i64.xor.
        assert "i64.xor" in body, (
            f"Expected the #798 overflow guard's i64.xor sign-test in "
            f"int_sub body. Body:\n{body}"
        )
        # The #520 nat-sub underflow guard would trap on a legitimate negative
        # result; pin that it does NOT — main() computes int_sub(5, 10) = 5-10
        # = -5 and must return it cleanly, never trap.
        assert _run(src) == -5, (
            "Int subtraction of 5 - 10 must return -5, not trap — the #520 "
            "nat-sub underflow guard must not apply to @Int - @Int."
        )

    def test_pure_literal_subtract_emits_no_guard(self) -> None:
        """`0 - 1` (pure-literal idiom) emits no guard — Path-A scope.

        The codegen guard fires only when at least one operand has
        @Nat *provenance* (slot ref or @Nat-returning function),
        matching the verifier's _has_nat_origin filter.  This keeps
        the corpus's `Err(_) -> 0 - 1` and `throw(0 - 1)` idioms
        unaffected — they consume the result at @Int positions where
        the upcast is well-defined.
        """
        # ensures(true) avoids confounding `i64.lt_s` from the
        # postcondition-check codegen (which compiles `< 0` to
        # `i64.lt_s; i32.eqz; if; ...; call $vera.contract_fail`).
        # We're isolating whether the underflow guard fires, not the
        # postcondition check.
        src = """
public fn neg_sentinel(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0 - 1
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  neg_sentinel()
}
"""
        result = _compile_ok(src)
        wat = result.wat
        sentinel_idx = wat.find("(func $neg_sentinel")
        assert sentinel_idx >= 0
        body_end = wat.find("\n  (func ", sentinel_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[sentinel_idx:body_end]
        # Bare i64.sub, no guard — even though both operands are
        # non-negative IntLits and thus statically @Nat per checker.
        # The provenance filter excludes pure-literal subtractions.
        # As with test_int_subtract_emits_no_guard, banning both
        # `i64.lt_s` / `i64.lt_u` and any `unreachable` defends
        # against future codegen variants that switch comparator or
        # trap mechanism.
        assert "i64.sub" in body
        assert not re.search(r"\bi64\.lt_[su]\b", body), (
            f"Pure-literal `0 - 1` should not get a guard at Path-A "
            f"scope. Body:\n{body}"
        )
        assert "unreachable" not in body, (
            f"Pure-literal `0 - 1` should not emit a trap guard at "
            f"Path-A scope. Body:\n{body}"
        )

    def test_recursion_with_path_guard_runs_clean(self) -> None:
        """`if @Nat.0 == 0 then 0 else f(@Nat.0 - 1)` runs at deep depth.

        The verifier discharges the underflow obligation from the
        path condition (the else-branch implies @Nat.0 != 0, hence
        @Nat.0 >= 1).  The codegen still emits the runtime guard
        (no Tier-1 skip-channel currently), but `lhs >= rhs` always
        holds at runtime so the branch is never taken — confirming
        the guard doesn't fire spuriously on path-discharged sites.
        """
        src = """
private fn countdown(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    countdown(@Nat.0 - 1)
  }
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  countdown(100)
}
"""
        # countdown(100) → 99 → ... → 0; guard never fires.
        assert _run(src) == 0

        # Structural assertion: the guard IS emitted on the
        # path-discharged @Nat.0 - 1 site.  Pure behavioural assertion
        # (countdown(100) == 0) would pass even if the guard were
        # accidentally elided, because the path condition keeps
        # @Nat.0 >= 1 in the recursive arm so underflow can never
        # fire — making the test silently coverage-blind.  Pinning
        # the WAT shape catches a future regression where the codegen
        # detector skips path-discharged sites (that's a Tier-1
        # skip-channel optimisation; until it lands, every @Nat-Nat
        # site with provenance gets the guard regardless of static
        # discharge status).
        result = _compile_ok(src)
        wat = result.wat
        countdown_idx = wat.find("(func $countdown")
        assert countdown_idx >= 0, "countdown not found in WAT"
        body_end = wat.find("\n  (func ", countdown_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[countdown_idx:body_end]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"Expected the @Nat.0 - 1 underflow guard "
            f"(i64.lt_s + unreachable) inside countdown body, got: "
            f"{body!r}"
        )

    def test_modulecall_provenance_emits_guard_and_traps(self) -> None:
        """ModuleCall with @Nat return type carries provenance.

        `vera.math::abs(...)` returns `@Nat` per spec/09 §9.x, so
        `vera.math::abs(a) - vera.math::abs(b)` is a `@Nat - @Nat`
        site where both operands have @Nat provenance via
        ast.ModuleCall (not ast.FnCall).  The CodeRabbit review on
        PR #554 (round 1) identified that the original codegen
        helpers `_is_static_nat_typed` and `_has_nat_origin_codegen`
        only handled ast.FnCall — module-qualified callees with
        @Nat return types would have slipped past the guard.

        This test exercises the fix by:
          (1) confirming the guard is emitted in the WAT for the
              ModuleCall case, and
          (2) confirming the guard actually fires at runtime when
              the subtraction would underflow (`abs(0) - abs(5)`
              produces -5 without the guard, traps with it).
        """
        unsafe_src = """
import vera.math(abs);

private fn unsafe_modcall(@Int, @Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  vera.math::abs(@Int.1) - vera.math::abs(@Int.0)
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  -- @Int.1 is the first param (older / De Bruijn = 1), @Int.0 is the
  -- second / most-recent.  Body computes `abs(@Int.1) - abs(@Int.0)`,
  -- so `unsafe_modcall(0, 5)` evaluates as `abs(0) - abs(5) = 0 - 5`
  -- → underflow.
  unsafe_modcall(0, 5)
}
"""
        # Structural assertion: guard emitted in unsafe_modcall body.
        result = _compile_ok(unsafe_src)
        wat = result.wat
        fn_idx = wat.find("(func $unsafe_modcall")
        assert fn_idx >= 0, "unsafe_modcall not found in WAT"
        body_end = wat.find("\n  (func ", fn_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[fn_idx:body_end]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"Expected the underflow guard for ModuleCall-provenance "
            f"@Nat - @Nat inside unsafe_modcall body, got: {body!r}"
        )

        # Behavioural assertion: unsafe_modcall(0, 5) produces
        # abs(@Int.1) - abs(@Int.0) = abs(0) - abs(5) = 0 - 5 = underflow → trap.
        # @Int.1 is the first parameter (older / De Bruijn = 1) and @Int.0 the
        # second (most-recent), so call order is preserved in the body via
        # the swapped subscripts.
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
            execute(result, fn_name="main", args=[])

        # Safe case: passing args where lhs >= rhs runs cleanly.
        safe_src = """
import vera.math(abs);

private fn safe_modcall(@Int, @Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  vera.math::abs(@Int.1) - vera.math::abs(@Int.0)
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  -- safe_modcall(5, 3): @Int.1=5, @Int.0=3 → abs(5) - abs(3) = 2.
  safe_modcall(5, 3)
}
"""
        # safe_modcall(5, 3): abs(@Int.1) - abs(@Int.0) = abs(5) - abs(3) = 2.
        assert _run(safe_src) == 2

    def test_rhs_only_provenance_emits_guard_and_traps(self) -> None:
        """`0 - @Nat.0` carries provenance via the RHS slot only.

        The codegen detector requires `_has_nat_origin_codegen(left)
        OR _has_nat_origin_codegen(right)` — symmetric in both
        operands.  Existing positive tests pin the left-has-provenance
        case (`@Nat.1 - @Nat.0`, `@Nat.0 - 1`) and the both-provenance
        ModuleCall case, but not the right-only-provenance case.
        Without that coverage a future refactor that accidentally
        ignored `expr.right` (or changed `or` to `and`) would still
        pass every existing test while silently re-opening the
        underflow hole on the right-only shape.

        Body: `0 - @Nat.0` (a non-negative IntLit on the left, a
        @Nat slot on the right).  Both operands are statically @Nat
        per the checker, but only the slot has @Nat provenance —
        the literal is exempt at Path-A scope.  The guard must
        still fire because the right operand provides provenance.
        """
        src = """
private fn lit_minus_slot(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  0 - @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  -- @Nat.0 = 1 → `0 - 1` underflows.
  lit_minus_slot(1)
}
"""
        # Structural assertion: guard emitted in lit_minus_slot body
        # despite the LHS being a literal.
        result = _compile_ok(src)
        wat = result.wat
        fn_idx = wat.find("(func $lit_minus_slot")
        assert fn_idx >= 0, "lit_minus_slot not found in WAT"
        body_end = wat.find("\n  (func ", fn_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[fn_idx:body_end]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"Expected the underflow guard for rhs-only-provenance "
            f"`0 - @Nat.0` inside lit_minus_slot body, got:\n{body}"
        )

        # Behavioural assertion: lit_minus_slot(1) → 0 - 1 → trap.
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
            execute(result, fn_name="main", args=[])

        # Safe case: lit_minus_slot(0) → 0 - 0 = 0 (no underflow).
        safe_src = """
private fn lit_minus_slot(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  0 - @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  lit_minus_slot(0)
}
"""
        assert _run(safe_src) == 0


# =====================================================================
# @Nat binding-site narrowing runtime guard (#552)
# =====================================================================

class TestNatBindingRuntimeGuard552:
    """Codegen emits a runtime `value >= 0` guard at `let @Nat = <Int>`
    narrowing sites (#552), the binding-site generalisation of the #520
    subtraction guard.

    The verifier emits a Tier-1 `value >= 0` obligation; codegen mirrors
    the detection (_narrows_into_nat, sharing _is_static_nat_typed +
    _has_nat_origin_codegen) and traps if a negative value would reach a
    @Nat slot.  Like the #520 guard, it protects programs compiled
    without `vera verify`.

    #552 guarded the canonical `let` site; #747 extends the runtime guard
    to the tuple-destructure, top-level match-bind, ADT sub-pattern,
    concrete constructor-field, and call-argument sites (see
    `TestNatBindingRuntimeGuard747`).  The effect-op-argument site and a
    dedicated trap kind remain a follow-up.
    """

    _GUARDED_LET = """
private fn narrow(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  narrow(0 - 1)
}
"""

    _SAFE_LET = """
private fn narrow(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  narrow(7)
}
"""

    def test_negative_narrowing_traps_at_runtime(self) -> None:
        """narrow(0 - 1) feeds -1 into `let @Nat`, tripping the guard.

        Without the guard, `local.set` would store -1 silently in a
        @Nat slot.  With it, the function traps before the bad value
        propagates.
        """
        result = _compile_ok(self._GUARDED_LET)
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_nonnegative_narrowing_returns_value(self) -> None:
        """narrow(7) passes the guard and returns 7 — no spurious trap."""
        assert _run(self._SAFE_LET) == 7

    def test_guard_emitted_in_wat_for_let_narrowing(self) -> None:
        """The `narrow` body contains the `i64.lt_s` + `unreachable` guard."""
        result = _compile_ok(self._GUARDED_LET)
        wat = result.wat
        idx = wat.find("(func $narrow")
        assert idx >= 0, "narrow function not found in WAT"
        body_end = wat.find("\n  (func ", idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[idx:body_end]
        assert "i64.lt_s" in body, (
            f"Expected `i64.lt_s` in narrow body for the @Nat guard. "
            f"Body:\n{body}"
        )
        assert "unreachable" in body, (
            f"Expected `unreachable` in narrow body for the @Nat guard. "
            f"Body:\n{body}"
        )

    def test_guard_emitted_for_untranslatable_let_narrowing(self) -> None:
        """The let-site guard fires even when the narrowed value is
        untranslatable to Z3 (a Tier-3 narrowing — the case the guard
        primarily exists for).  Codegen keys on static @Nat-typing, not
        Z3-translatability, so `let @Nat = array_length(...)` is guarded
        like any other @Int->@Nat let (#748 review)."""
        src = """
private fn narrow_len(@Array<Int> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = array_length(@Array<Int>.0);
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  narrow_len([1, 2, 3])
}
"""
        result = _compile_ok(src)
        wat = result.wat
        idx = wat.find("(func $narrow_len")
        assert idx >= 0, "narrow_len function not found in WAT"
        body_end = wat.find("\n  (func ", idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[idx:body_end]
        assert "i64.lt_s" in body, (
            f"Expected `i64.lt_s` @Nat guard for an untranslatable let "
            f"narrowing. Body:\n{body}"
        )
        assert "unreachable" in body

    def test_already_nat_let_emits_no_guard(self) -> None:
        """`let @Nat = @Nat.0` is not a narrowing — no guard emitted.

        Sister to the structural test above: the guard fires only when
        the bound value is not already statically @Nat (or is a
        pure-literal subtraction), so a @Nat -> @Nat let must emit no
        `i64.lt_[su]`.
        """
        src = """
private fn passthru(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Nat.0;
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  passthru(5)
}
"""
        result = _compile_ok(src)
        wat = result.wat
        idx = wat.find("(func $passthru")
        assert idx >= 0
        body_end = wat.find("\n  (func ", idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[idx:body_end]
        assert not re.search(r"\bi64\.lt_[su]\b", body), (
            f"`let @Nat = @Nat.0` is not a narrowing and must not get a "
            f"guard. Body:\n{body}"
        )

    def test_wrapped_subtraction_traps_at_runtime(self) -> None:
        """`let @Nat = { 0 - 1 }` — a pure-literal underflow wrapped in a
        block — now gets the guard and traps, matching the verifier.  The
        top-level-only check missed this; the guard descends to the
        value-producing leaf (#552 review)."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Nat = { 0 - 1 };
  @Nat.0
}
"""
        result = _compile_ok(src)
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])


class TestNatBindingRuntimeGuard747:
    """#747: the runtime `value >= 0` guard now fires at the @Nat binding
    sites beyond `let` — tuple destructure, top-level match bind, ADT
    sub-pattern bind, concrete constructor field, and call argument.  Each
    emits the `i64.lt_s; if; unreachable` net so an unverified compile traps
    on a negative @Nat rather than silently storing it; a non-narrowing
    target (an @Int field/formal) emits none.
    """

    @staticmethod
    def _body(wat: str, fn: str) -> str:
        """Slice out function ``fn``'s WAT body.

        The guard-presence tests assert ``i64.lt_s`` appears in this slice;
        that uniquely identifies the @Nat guard *only because* their
        fixtures contain no other `i64.lt_s` emitter (comparison, string /
        array / math builtins all emit one).  Keep these fixtures to plain
        arithmetic / ctor / match bodies — the negative-traps tests below
        pin the guard's runtime *semantics* independently.
        """
        # Boundary-safe so `$gcall` does not match `$gcall_helper` — a plain
        # substring `find` would slice the wrong body (CR #756).
        m = re.search(rf"\(func \${re.escape(fn)}(?![A-Za-z0-9_$.])", wat)
        assert m is not None, f"{fn} not found in WAT"
        idx = m.start()
        end = wat.find("\n  (func ", idx + 1)
        return wat[idx:end if end >= 0 else len(wat)]

    def _assert_guarded(self, wat: str, fn: str) -> None:
        """Assert ``fn``'s body emits the full @Nat guard shape — both the
        `i64.lt_s` comparison and the `unreachable` trap edge — so a
        regression emitting the compare without the trap is caught (CR #756).
        The fixtures are plain arithmetic / ctor / match bodies, so neither
        token appears except in the guard."""
        body = self._body(wat, fn)
        assert "i64.lt_s" in body, f"{fn}: missing i64.lt_s guard compare"
        assert "unreachable" in body, f"{fn}: missing unreachable trap edge"

    def test_param_destructure_nat_components_guarded(self) -> None:
        """`let Tuple<@Nat, @Nat> = @Tuple<Int, Int>.0` guards each
        narrowed component."""
        result = _compile_ok("""
public fn gdestr(@Tuple<Int, Int> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = @Tuple<Int, Int>.0; @Nat.0 }
""")
        self._assert_guarded(result.wat, "gdestr")

    def test_subpattern_nat_bind_guarded(self) -> None:
        """`match opt { Some(@Nat) -> }` on `Option<Int>` guards the
        projected @Int payload bound as @Nat."""
        result = _compile_ok("""
public fn gsub(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        self._assert_guarded(result.wat, "gsub")

    def test_toplevel_match_nat_bind_guarded(self) -> None:
        """`match <Int> { @Nat -> }` guards the scrutinee bound as @Nat."""
        result = _compile_ok("""
public fn gmatch(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Int.0 { @Nat -> @Nat.0 } }
""")
        self._assert_guarded(result.wat, "gmatch")

    def test_concrete_nat_ctor_field_guarded(self) -> None:
        """A concrete @Nat constructor field guards its @Int argument."""
        result = _compile_ok("""
public data NatBox { WrapN(Nat) }
public fn gctor(@Int -> @NatBox)
  requires(true) ensures(true) effects(pure)
{ WrapN(@Int.0) }
""")
        self._assert_guarded(result.wat, "gctor")

    def test_concrete_nat_call_arg_guarded(self) -> None:
        """A concrete @Nat call formal guards its @Int argument."""
        result = _compile_ok("""
public fn takesNat(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
public fn gcall(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ takesNat(@Int.0) }
""")
        self._assert_guarded(result.wat, "gcall")

    def test_nat_alias_let_bind_guarded(self) -> None:
        """A `type Age = Nat` alias target is guarded at the let-bind site —
        `_resolve_base_type_name` resolves the alias so the runtime guard is
        not skipped by the bare `type_name == "Nat"` check (CR #756)."""
        result = _compile_ok("""
type Age = Nat;
public fn galias(@Int -> @Age)
  requires(true) ensures(true) effects(pure)
{ let @Age = @Int.0; @Age.0 }
""")
        self._assert_guarded(result.wat, "galias")

    def test_generic_nat_alias_ctor_field_guarded(self) -> None:
        """A generic alias instantiated to @Nat (`type Id<T> = T` used as
        `Id<Nat>`) resolves to Nat via type-argument substitution, so the
        constructor-field narrowing is still guarded (CR #756)."""
        result = _compile_ok("""
type Id<T> = T;
public data GBox { GWrap(Id<Nat>) }
public fn ggen(@Int -> @GBox)
  requires(true) ensures(true) effects(pure)
{ GWrap(@Int.0) }
""")
        self._assert_guarded(result.wat, "ggen")

    def test_generic_instantiated_call_arg_guarded(self) -> None:
        """A generic function formal fixed to @Nat at the call site is guarded
        on the *monomorphised* callee.  The guard keys on the resolved call
        target (`pick$Nat`, concrete @Nat flags), not the generic `pick`
        (erased flags) — so `pick<Nat>(@Nat.0, @Int.0)` traps a negative
        narrowing just like a concrete @Nat call (CR #756)."""
        result = _compile_ok("""
private forall<T>
fn pick(@T, @T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }
public fn gcall(@Nat, @Int -> @Nat)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ pick(@Nat.0, @Int.0) }
""")
        self._assert_guarded(result.wat, "gcall")

    def test_builtin_mdheading_nat_field_guarded(self) -> None:
        """The built-in `MdHeading` constructor's concrete @Nat level field is
        guarded.  Manual built-in layouts bypass `_compute_constructor_layout`
        (the only other `nat_fields` populator), so the flag must be set on the
        layout explicitly; MdHeading is the sole built-in ctor with a @Nat
        field (CR #756)."""
        result = _compile_ok("""
public fn mkheading(@Int -> @MdBlock)
  requires(true) ensures(true) effects(pure)
{ MdHeading(@Int.0, [MdText("x")]) }
""")
        self._assert_guarded(result.wat, "mkheading")

    def test_int_ctor_field_emits_no_guard(self) -> None:
        """A concrete @Int constructor field is not a narrowing target —
        no guard, mirroring the @Int-field/@Int-formal exemption."""
        result = _compile_ok("""
public data IntBox { WrapI(Int) }
public fn gint(@Int -> @IntBox)
  requires(true) ensures(true) effects(pure)
{ WrapI(@Int.0) }
""")
        assert not re.search(
            r"\bi64\.lt_[su]\b", self._body(result.wat, "gint"))

    def test_call_arg_negative_traps_at_runtime(self) -> None:
        """An unverified compile passing -5 into a @Nat formal traps at
        runtime — the guard's safety-net role beyond the `let` site."""
        result = _compile_ok("""
public fn takesNat(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ takesNat(0 - 5) }
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_destructure_negative_traps_at_runtime(self) -> None:
        """A tuple-destructure binding a negative component into a @Nat slot
        traps at runtime — proves the destructure guard's *semantics*, not
        just its emission (the offset/accessor load logic is the most
        regression-prone of the five sites)."""
        result = _compile_ok("""
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = Tuple(0 - 5, 1); @Nat.0 }
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_subpattern_negative_traps_at_runtime(self) -> None:
        """An ADT sub-pattern binding a negative payload as @Nat traps at
        runtime — the sub-pattern guard's semantics."""
        result = _compile_ok("""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match Some(0 - 5) { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_toplevel_match_negative_traps_at_runtime(self) -> None:
        """A top-level `match <Int> { @Nat -> }` binding a negative scrutinee
        as @Nat traps at runtime — pins the match-bind guard's semantics, not
        only its WAT emission (CR #756)."""
        result = _compile_ok("""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match 0 - 5 { @Nat -> @Nat.0 } }
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    @staticmethod
    def _boxes_module() -> object:
        """A resolved `boxes` module declaring `data NatBox { WrapN(Nat) }`
        for the cross-module imported-constructor guard tests (#747 site 4)."""
        from pathlib import Path

        from vera.parser import parse_to_ast
        from vera.resolver import ResolvedModule

        src = "public data NatBox {\n  WrapN(Nat)\n}\n"
        return ResolvedModule(
            path=("boxes",), file_path=Path("/fake/boxes.vera"),
            program=parse_to_ast(src), source=src)

    def test_imported_concrete_nat_ctor_field_guarded(self) -> None:
        """An imported concrete-@Nat constructor field emits the runtime
        guard (#747 site 4) — the cross-module codegen path the local-ctor
        tests don't exercise."""
        from vera.parser import parse_to_ast

        src = """import boxes(WrapN, NatBox);
public fn gimp(@Int -> @NatBox)
  requires(true) ensures(true) effects(pure)
{ WrapN(@Int.0) }
"""
        result = compile(
            parse_to_ast(src), source=src,
            resolved_modules=[self._boxes_module()])
        assert not [d for d in result.diagnostics if d.severity == "error"]
        self._assert_guarded(result.wat, "gimp")

    def test_imported_ctor_negative_traps_at_runtime(self) -> None:
        """The imported concrete-@Nat ctor guard traps on a negative arg —
        the cross-module runtime safety net."""
        from vera.parser import parse_to_ast

        src = """import boxes(WrapN, NatBox);
public fn main(@Unit -> @NatBox)
  requires(true) ensures(true) effects(pure)
{ WrapN(0 - 5) }
"""
        result = compile(
            parse_to_ast(src), source=src,
            resolved_modules=[self._boxes_module()])
        assert not [d for d in result.diagnostics if d.severity == "error"]
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    @staticmethod
    def _nat_fn_module() -> object:
        """A resolved `natfns` module with a function taking a concrete @Nat
        formal, for the cross-module imported-function guard test (CR #756 —
        `_register_modules` must harvest the module's `_fn_nat_params`)."""
        from pathlib import Path

        from vera.parser import parse_to_ast
        from vera.resolver import ResolvedModule

        src = ("public fn boxNat(@Nat -> @Nat)\n"
               "  requires(true) ensures(true) effects(pure)\n"
               "{ @Nat.0 }\n")
        return ResolvedModule(
            path=("natfns",), file_path=Path("/fake/natfns.vera"),
            program=parse_to_ast(src), source=src)

    def test_imported_fn_nat_param_guarded(self) -> None:
        """A cross-module call into an imported function's concrete @Nat formal
        emits the runtime guard.  `_register_modules` must harvest the imported
        module's `_fn_nat_params`, or the guard metadata is lost and the
        narrowing stored unchecked (CR #756)."""
        from vera.parser import parse_to_ast

        src = """import natfns(boxNat);
public fn gimpfn(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ boxNat(@Int.0) }
"""
        result = compile(
            parse_to_ast(src), source=src,
            resolved_modules=[self._nat_fn_module()])
        assert not [d for d in result.diagnostics if d.severity == "error"]
        self._assert_guarded(result.wat, "gimpfn")

    def test_imported_fn_negative_traps_at_runtime(self) -> None:
        """The imported-function @Nat guard traps on a negative argument at
        run time, not only in the WAT — proves the harvested `_fn_nat_params`
        is enforced end-to-end across the module boundary (CR #756)."""
        from vera.parser import parse_to_ast

        src = """import natfns(boxNat);
public fn gimpfn(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ boxNat(@Int.0) }
"""
        result = compile(
            parse_to_ast(src), source=src,
            resolved_modules=[self._nat_fn_module()])
        assert not [d for d in result.diagnostics if d.severity == "error"]
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="gimpfn", args=[-1])

    @pytest.mark.parametrize("body", [
        'string_repeat("ab", 0 - 5)',
        'string_from_char_code(0 - 5)',
        'string_pad_start("ab", 0 - 5, "x")',
        'string_pad_end("ab", 0 - 5, "x")',
    ])
    def test_builtin_nat_param_negative_traps_at_runtime(self, body) -> None:
        """A negative @Int narrowed into a builtin's @Nat parameter traps at
        runtime (#757 fold-in).  Builtin translators bypass `_fn_nat_params`,
        so each guards its @Nat arg directly; an unverified compile of a
        negative argument traps rather than overallocating or passing a
        negative to a host import (CR #756)."""
        result = _compile_ok(f"""
public fn main(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{{ {body} }}
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_builtin_nat_param_valid_does_not_trap(self) -> None:
        """A non-negative builtin @Nat argument runs without trapping — the
        guard fires only on a genuine narrowing of a negative value (#757)."""
        result = _compile_ok("""
public fn main(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ string_repeat("ab", 3) }
""")
        execute(result, fn_name="main", args=[])

    def test_builtin_md_has_heading_negative_level_traps_at_runtime(self) -> None:
        """`md_has_heading` is the markup builtin in the guarded set — its @Nat
        `level` parameter is covered by the same `_narrows_into_nat` guard as the
        string builtins, but its `@MdBlock`/`@Bool` signature keeps it out of the
        `@String`-returning parametrized trap test above.  A negative @Int
        narrowed into `level` traps rather than passing a negative to the host
        import (review of #756; round-14 #757 fold-in)."""
        result = _compile_ok("""
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Title");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Bool = md_has_heading(@MdBlock.0, 0 - 5);
      if @Bool.0 then { IO.print("yes") } else { IO.print("no") }
    },
    Err(_) -> IO.print("err")
  }
}
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_generic_ctor_field_negative_does_not_trap_today(self) -> None:
        """The generic-instantiated constructor field is the one #747 narrowing
        site with NO runtime guard: constructor layouts carry no per-field @Nat
        mono metadata, so a generic field instantiated to @Nat erases to i64
        (#757).  `Some(0 - 5)` building an `Option<Nat>` therefore compiles and
        runs *without* trapping today — it stores -5 silently.  This pins the
        deferral so it can't regress to a *silent* loss of the obligation: when
        #757 lands and emits the guard, this test flips to a trap and becomes the
        regression anchor, symmetric with the #754 effect-op pin
        (`test_non_let_tier3_narrowing_warns_unguarded`).  The verifier still
        obligates the narrowing statically (E503), so a verified program is
        unaffected — this is purely the codegen runtime backstop (review of
        #756, #760)."""
        result = _compile_ok("""
public fn f(@Unit -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{ Some(0 - 5) }
""")
        # No pytest.raises: the deferred-guard state means this MUST NOT trap.
        # If #757 adds the guard, replace this with a pytest.raises(...) block.
        execute(result, fn_name="f", args=[])
