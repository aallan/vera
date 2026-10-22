"""Tests for vera.codegen — nat_guards (@Nat subtraction-underflow and binding-site narrowing runtime guards).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re

import pytest

from vera.codegen.api import WasmTrapError

from vera.codegen import (
    compile,
    execute,
)

from tests.codegen_helpers import (
    _compile_ok,
    _run,
)
from tests.module_fixture_helpers import fake_resolved_module
from tests import pipeline
from tests.pipeline import checks


# =====================================================================
# @Nat subtraction underflow runtime guard (#520)
# =====================================================================

class TestNatSubtractionRuntimeGuard520:
    """Codegen emits a runtime underflow guard for `@Nat - @Nat`.

    The verifier (vera/verifier.py, #520 commit b446cac) emits a
    Tier-1 proof obligation `lhs >= rhs` at every @Nat-Nat
    subtraction site.  The codegen mirrors that detection (one rule,
    `vera.narrowing.is_guarded_nat_subtraction`: both operands `@Nat`) and
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
        with pytest.raises(WasmTrapError):
            execute(result, fn_name="main", args=[])

    def test_safe_subtraction_returns_correct_result(self) -> None:
        """safe(5, 3) returns 2 — guard passes through cleanly.

        The guard is `if (i64.lt_s lhs rhs) then <signal> unreachable end`, so
        when lhs >= rhs the branch is not taken and the subtraction
        proceeds normally.  Confirms the guard doesn't introduce a
        regression on the happy path.
        """
        assert _run(self._SAFE_SUB) == 2

    def test_guard_emitted_in_wat_for_nat_sub(self) -> None:
        """The guarded WAT contains `i64.lt_s` and `unreachable`.

        Structural assertion that the codegen actually inserted the
        guard sequence rather than emitting a bare `i64.sub`.  Signed: a
        `@Nat` holds `0 .. i64.MAX`, over which the signed compare is exact
        (spec §2.2; on the u64 `Nat` it compared unsigned, #1479).
        """
        result = _compile_ok(self._GUARDED_SUB)
        wat = result.wat
        # Both the comparison and the trap must appear inside `unsafe`
        # (the function with the @Nat-Nat subtraction).
        unsafe_idx = wat.find("(func $:unsafe")
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
        assert checks(result, kind="nat_underflow", function="unsafe"), body
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
        nat-sub shape is not the mechanism, by pinning runtime behaviour:
        ``5 - 10 = -5`` must return cleanly, never trap.
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
        int_sub_idx = wat.find("(func $:int_sub")
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

    def test_pure_literal_subtract_emits_no_underflow_guard(self) -> None:
        """`0 - 1` is an `@Int` subtraction (spec §4.2): it carries the #798
        overflow guard every `@Int` subtraction does, and no `@Nat`
        underflow guard.  The corpus's `Err(_) -> 0 - 1` and `throw(0 - 1)`
        idioms consume the result at `@Int` positions, where it is -1.  (On
        the u64 `Nat` both literals were `Nat`, and a provenance filter kept
        the underflow guard off the pure-literal idiom.)
        """
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
  neg_sentinel(())
}
"""
        result = _compile_ok(src)
        assert checks(result, kind="nat_underflow", function="neg_sentinel") == ()
        assert checks(result, kind="overflow", function="neg_sentinel")
        assert _run(src) == -1

    def test_recursion_with_path_guard_runs_clean(self) -> None:
        """`if @Nat.0 == 0 then 0 else f(@Nat.0 - 1)` runs at deep depth.

        `@Nat.0 - 1` is an `@Int` subtraction narrowed into `countdown`'s
        `@Nat` parameter (spec §4.4).  The verifier discharges the
        narrowing from the path condition (the else-branch implies @Nat.0
        != 0, hence @Nat.0 >= 1).  The codegen still emits the narrowing
        guard (no Tier-1 skip-channel currently), but the value is never
        negative at runtime so the branch is never taken — confirming the
        guard doesn't fire spuriously on path-discharged sites.
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
        # @Nat.0 >= 1 in the recursive arm so the value can never be
        # negative — making the test silently coverage-blind.  Pinning
        # the module's record catches a future regression where the codegen
        # skips path-discharged sites (that's a Tier-1 skip-channel
        # optimisation; until it lands, every narrowing gets the guard
        # regardless of static discharge status).
        result = _compile_ok(src)
        wat = result.wat
        countdown_idx = wat.find("(func $:countdown")
        assert countdown_idx >= 0, "countdown not found in WAT"
        body_end = wat.find("\n  (func ", countdown_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[countdown_idx:body_end]
        # The guard's own check, in the module's record (#1479): not tokens
        # another check in the body could supply.  The subtraction carries
        # the `@Int` overflow guard and no `@Nat` underflow guard.
        assert checks(result, kind="nat_guard", function="countdown"), (
            f"Expected the @Nat.0 - 1 narrowing guard's nat_guard check "
            f"in countdown, got: {body!r}"
        )
        assert checks(result, kind="overflow", function="countdown"), body
        assert checks(result, kind="nat_underflow", function="countdown") == ()

    def test_modulecall_provenance_emits_guard_and_traps(self) -> None:
        """A module-qualified call with a @Nat return type carries provenance.

        `nm::absn(...)` returns `@Nat`, so `nm::absn(a) - nm::absn(b)` is a
        `@Nat - @Nat` site where both operands have @Nat provenance through
        a qualified call.  The CodeRabbit review on PR #554 (round 1)
        identified that the original codegen helpers `_is_static_nat_typed`
        and `_has_nat_origin_codegen` only handled ast.FnCall — module-
        qualified callees with @Nat return types would have slipped past the
        guard.  The link step (#1694) makes the qualified call the plain call
        of its target's link name, whose declared return carries the
        provenance.

        This test exercises the fix by:
          (1) confirming the guard is emitted in the WAT for the
              ModuleCall case, and
          (2) confirming the guard actually fires at runtime when
              the subtraction would underflow (`abs(0) - abs(5)`
              produces -5 without the guard, traps with it).
        """
        unsafe_src = """
module nm;

private fn absn(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  abs(@Int.0)
}

private fn unsafe_modcall(@Int, @Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  nm::absn(@Int.1) - nm::absn(@Int.0)
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
        fn_idx = wat.find("(func $:unsafe_modcall")
        assert fn_idx >= 0, "unsafe_modcall not found in WAT"
        body_end = wat.find("\n  (func ", fn_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[fn_idx:body_end]
        assert "i64.lt_s" in body, (
            f"Expected the underflow guard's i64.lt_s for ModuleCall-provenance "
            f"@Nat - @Nat inside unsafe_modcall body, got: {body!r}"
        )
        assert checks(result, kind="nat_underflow", function="unsafe_modcall"), (
            f"Expected the underflow guard's nat_underflow check for "
            f"ModuleCall-provenance @Nat - @Nat in unsafe_modcall, got: {body!r}"
        )

        # Behavioural assertion: unsafe_modcall(0, 5) produces
        # abs(@Int.1) - abs(@Int.0) = abs(0) - abs(5) = 0 - 5 = underflow → trap.
        # @Int.1 is the first parameter (older / De Bruijn = 1) and @Int.0 the
        # second (most-recent), so call order is preserved in the body via
        # the swapped subscripts.
        with pytest.raises(WasmTrapError):
            execute(result, fn_name="main", args=[])

        # Safe case: passing args where lhs >= rhs runs cleanly.
        safe_src = """
module nm;

private fn absn(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  abs(@Int.0)
}

private fn safe_modcall(@Int, @Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  nm::absn(@Int.1) - nm::absn(@Int.0)
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

    def test_a_literal_minus_a_nat_is_narrowed_at_the_return(self) -> None:
        """`0 - @Nat.0` is an `@Int` subtraction (the literal is an `Int`,
        spec §4.2), so into a `@Nat` return it is a narrowing: guarded at
        the return, with no `@Nat` underflow guard at the subtraction.  On
        the u64 `Nat` it was a `@Nat - @Nat` whose underflow guard the
        right operand's provenance alone had to trigger.
        """
        src = """
private fn lit_minus_slot(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  0 - @Nat.0
}

public fn main(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  lit_minus_slot(@Nat.0)
}
"""
        result = _compile_ok(src)
        assert checks(result, kind="nat_guard", function="lit_minus_slot")
        assert checks(result, kind="nat_underflow",
                      function="lit_minus_slot") == ()
        # @Nat.0 = 1 → `0 - 1` is -1, which the return narrowing stops.
        with pytest.raises(WasmTrapError) as trapped:
            execute(result, fn_name="main", args=[1])
        assert trapped.value.kind == "nat_guard"
        assert execute(result, fn_name="main", args=[0]).value == 0


# =====================================================================
# @Nat binding-site narrowing runtime guard (#552)
# =====================================================================

class TestNatBindingRuntimeGuard552:
    """Codegen emits a runtime `value >= 0` guard at `let @Nat = <Int>`
    narrowing sites (#552), the binding-site generalisation of the #520
    subtraction guard.

    The verifier emits a Tier-1 `value >= 0` obligation; codegen mirrors
    the detection (_narrows_into_nat, the shared rule
    `vera.narrowing.narrows_into_nat`) and traps if a negative value would
    reach a @Nat slot.  Like the #520 guard, it protects programs compiled
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
            WasmTrapError
        ):
            execute(result, fn_name="main", args=[])

    def test_nonnegative_narrowing_returns_value(self) -> None:
        """narrow(7) passes the guard and returns 7 — no spurious trap."""
        assert _run(self._SAFE_LET) == 7

    def test_guard_emitted_in_wat_for_let_narrowing(self) -> None:
        """The `narrow` body contains the `i64.lt_s` + `unreachable` guard."""
        result = _compile_ok(self._GUARDED_LET)
        wat = result.wat
        idx = wat.find("(func $:narrow")
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
        idx = wat.find("(func $:narrow_len")
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
        idx = wat.find("(func $:passthru")
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
            WasmTrapError
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
        m = re.search(rf"\(func \$:?{re.escape(fn)}(?![A-Za-z0-9_$.])", wat)
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
            WasmTrapError
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
            WasmTrapError
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
            WasmTrapError
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
            WasmTrapError
        ):
            execute(result, fn_name="main", args=[])

    @staticmethod
    def _boxes_module() -> object:
        """A resolved `boxes` module declaring `data NatBox { WrapN(Nat) }`
        for the cross-module imported-constructor guard tests (#747 site 4)."""
        return fake_resolved_module(
            ("boxes",), "public data NatBox {\n  WrapN(Nat)\n}\n")

    def test_imported_concrete_nat_ctor_field_guarded(self) -> None:
        """An imported concrete-@Nat constructor field emits the runtime
        guard (#747 site 4) — the cross-module codegen path the local-ctor
        tests don't exercise."""

        src = """import boxes(WrapN, NatBox);
public fn gimp(@Int -> @NatBox)
  requires(true) ensures(true) effects(pure)
{ WrapN(@Int.0) }
"""
        result = compile(
            pipeline.typed(src, modules=[self._boxes_module()]), source=src)
        assert not [d for d in result.diagnostics if d.severity == "error"]
        self._assert_guarded(result.wat, "gimp")

    def test_imported_ctor_negative_traps_at_runtime(self) -> None:
        """The imported concrete-@Nat ctor guard traps on a negative arg —
        the cross-module runtime safety net."""

        src = """import boxes(WrapN, NatBox);
public fn main(@Unit -> @NatBox)
  requires(true) ensures(true) effects(pure)
{ WrapN(0 - 5) }
"""
        result = compile(
            pipeline.typed(src, modules=[self._boxes_module()]), source=src)
        assert not [d for d in result.diagnostics if d.severity == "error"]
        with pytest.raises(
            WasmTrapError
        ):
            execute(result, fn_name="main", args=[])

    @staticmethod
    def _nat_fn_module() -> object:
        """A resolved `natfns` module with a function taking a concrete @Nat
        formal, for the cross-module imported-function guard test (CR #756 —
        `_register_modules` must harvest the module's `_fn_nat_params`)."""
        return fake_resolved_module(("natfns",), (
            "public fn boxNat(@Nat -> @Nat)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Nat.0 }\n"))

    def test_imported_fn_nat_param_guarded(self) -> None:
        """A cross-module call into an imported function's concrete @Nat formal
        emits the runtime guard.  `_register_modules` must harvest the imported
        module's `_fn_nat_params`, or the guard metadata is lost and the
        narrowing stored unchecked (CR #756)."""

        src = """import natfns(boxNat);
public fn gimpfn(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ boxNat(@Int.0) }
"""
        result = compile(
            pipeline.typed(src, modules=[self._nat_fn_module()]), source=src)
        assert not [d for d in result.diagnostics if d.severity == "error"]
        self._assert_guarded(result.wat, "gimpfn")

    def test_imported_fn_negative_traps_at_runtime(self) -> None:
        """The imported-function @Nat guard traps on a negative argument at
        run time, not only in the WAT — proves the harvested `_fn_nat_params`
        is enforced end-to-end across the module boundary (CR #756)."""

        src = """import natfns(boxNat);
public fn gimpfn(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ boxNat(@Int.0) }
"""
        result = compile(
            pipeline.typed(src, modules=[self._nat_fn_module()]), source=src)
        assert not [d for d in result.diagnostics if d.severity == "error"]
        with pytest.raises(
            WasmTrapError
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
            WasmTrapError
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
            WasmTrapError
        ):
            execute(result, fn_name="main", args=[])

    def test_generic_ctor_field_negative_traps(self) -> None:
        """The generic-instantiated constructor field, which #757 closed.

        This pinned the DEFERRAL: constructor layouts carry no per-field
        `@Nat` metadata, so a generic field instantiated to `@Nat` erased to
        i64 and `Some(0 - 5)` building an `Option<Nat>` stored `-5` in
        silence.  The cell said it would flip to a trap when #757 landed.

        #757 landed and it did not flip, because it was not measuring the
        guard.  `_compile_ok` runs a bare `transform -> compile` with no
        checker artifacts, so `_expr_target_types` is empty; #757's guard
        reads a generic field's instantiation from exactly that table, and
        with the table absent it declines and emits nothing.  The cell went
        on passing for a reason unrelated to its subject — the same shape
        run through `vera run`, which threads the artifacts, traps.

        So it compiles the way the real pipeline does and asserts the trap.
        The kind is `nat_guard`: this is the SIGN direction (#757), not the
        §2.6.5 predicate at a construction position (#1426), which
        `Option<Nat>` has no refinement to carry.  Found in the #1426
        release audit.
        """

        src = """\
public fn f(@Unit -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{ Some(0 - 5) }
"""
        result = compile(pipeline.typed(src), source=src)
        with pytest.raises(WasmTrapError) as caught:
            execute(result, fn_name="f", args=[])
        assert caught.value.kind == "nat_guard", caught.value.kind

        # The control the file pairs with every trap case: a guard that lost
        # its `_narrows_into_nat` gate and fired unconditionally would
        # satisfy the assertions above just as well (CR PR-review).
        ok_src = """
public fn f(@Unit -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{ Some(5) }
"""
        execute(compile(pipeline.typed(ok_src), source=ok_src),
                fn_name="f", args=[])


class TestNatReturnRuntimeGuard758:
    """Codegen emits the `@Int -> @Nat` narrowing guard at the RETURN
    position (#758) — the dual of the #813 `@Nat -> @Int` widen-return
    guard.  An `@Int` body narrowing into a `@Nat` return can be negative
    (`to_nat(0 - 5)` = -5), so the function must trap rather than store a
    negative in the `@Nat` slot.

    Pre-fix the return slot carried no guard: `to_nat(0 - 5)` silently
    returned -5.  Mirrors `TestNatBindingRuntimeGuard552` for the let site.
    """

    _BARE_SLOT = """
public fn to_nat(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""

    _ABS_IF = """
public fn f(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 >= 0 then { @Int.0 } else { 0 - @Int.0 } }
"""

    def test_negative_return_narrowing_traps_at_runtime(self) -> None:
        """to_nat(-5) trips the return guard and traps before returning -5
        through the @Nat slot."""
        result = _compile_ok(self._BARE_SLOT)
        with pytest.raises(
            WasmTrapError
        ):
            execute(result, fn_name="to_nat", args=[-5])

    def test_nonnegative_return_narrowing_returns_value(self) -> None:
        """to_nat(7) passes the guard and returns 7 — no spurious trap."""
        assert _run(self._BARE_SLOT, fn="to_nat", args=[7]) == 7

    def test_guard_emitted_in_wat_for_return_narrowing(self) -> None:
        """The `to_nat` body carries the `i64.lt_s` + `unreachable` guard."""
        result = _compile_ok(self._BARE_SLOT)
        wat = result.wat
        idx = wat.find("(func $:to_nat ")
        assert idx >= 0, "to_nat function not found in WAT"
        body_end = wat.find("\n  (func ", idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[idx:body_end]
        assert "i64.lt_s" in body, f"Expected `i64.lt_s` in to_nat body:\n{body}"
        assert "unreachable" in body, (
            f"Expected `unreachable` in to_nat body:\n{body}"
        )

    def test_provable_abs_return_does_not_trap(self) -> None:
        """The absolute-value shape's guard is DEAD — the value is always
        non-negative, so run(-5) returns 5, never trips the trap.  Pins that
        a Tier-1-provable narrowing pays only dead instructions."""
        assert _run(self._ABS_IF, fn="f", args=[-5]) == 5
        assert _run(self._ABS_IF, fn="f", args=[7]) == 7

    def test_int_return_emits_no_narrowing_guard(self) -> None:
        """Control: an `@Int -> @Int` return is not a narrowing, so it must
        NOT carry the guard — a negative Int result returns cleanly."""
        result = _compile_ok("""
public fn ident(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        exec_result = execute(result, fn_name="ident", args=[-5])
        assert exec_result.value == -5, (
            "an @Int->@Int identity must return -5, not trap"
        )

    def test_guard_emitted_for_builtin_return_narrowing(self) -> None:
        """The return guard fires for a builtin-@Int-returning call narrowed
        into a `@Nat` return.  `array_length(...)` returns `@Int` (registry),
        so returning it into a `@Nat` slot is guarded like any other @Int->@Nat
        narrowing — the codegen mirror of the verifier's nat_bind obligation,
        keeping the two site sets in agreement."""
        result = _compile_ok("""
public fn f(@Array<Int> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ array_length(@Array<Int>.0) }
""")
        wat = result.wat
        idx = wat.find("(func $:f ")
        assert idx >= 0, "f function not found in WAT"
        body_end = wat.find("\n  (func ", idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[idx:body_end]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"Expected the @Nat narrowing guard in f body:\n{body}"
        )
        # The guard is DEAD (array_length is never negative) — a valid array
        # returns its length, never traps.
        assert _run("""
public fn f(@Array<Int> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ array_length(@Array<Int>.0) }

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ f([1, 2, 3]) }
""", fn="main") == 3


def _fn_body(wat: str, fn: str) -> str:
    """Slice out function ``fn``'s WAT body (boundary-safe so ``$f`` does not
    match ``$f_helper``).  The guard-presence tests assert ``i64.lt_s`` appears
    in this slice; that uniquely identifies the @Nat guard only because the
    fixtures contain no other ``i64.lt_s`` emitter — keep them to plain
    arithmetic / slot / call bodies."""
    m = re.search(rf"\(func \$:?{re.escape(fn)}(?![A-Za-z0-9_$.])", wat)
    assert m is not None, f"{fn} not found in WAT"
    idx = m.start()
    end = wat.find("\n  (func ", idx + 1)
    return wat[idx:end if end >= 0 else len(wat)]


class TestNatAliasReturnGuard983:
    """#983 review — the @Int->@Nat return narrowing guard (and its @Nat->@Int
    widen dual) resolve type ALIASES and stay off the refinement-boundary path.

    Pre-fix the codegen gates keyed on the RAW alias name
    (``_type_expr_to_slot_name(return_type) == "Nat"`` / ``"Int"``), so a
    ``type Count = Nat`` / ``type MyInt = Int`` return slipped past the guard
    while the verifier's alias-resolving 7d/7c gates still obligated it
    (``nat_bind`` / ``nat_to_int_coerce``) — an unsound silent negative
    (``run(-5)`` returned -5 through the @Nat slot).  The fix resolves the alias
    via ``_resolve_base_type_name`` (the resolver the let-bind guard already
    uses) and excludes an alias-to-refinement via ``_refinement_guard_parts`` so
    it keeps its single 7b boundary guard.
    """

    _ALIAS_WITNESSABLE = """
type Count = Nat;
public fn f(@Int -> @Count)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""

    def test_alias_nat_return_guard_emitted_in_wat(self) -> None:
        """A ``type Count = Nat`` return carries the ``i64.lt_s``/``unreachable``
        narrowing guard — pre-fix the alias name masked the bare @Nat and no
        guard was emitted (the alias-blind gate)."""
        result = _compile_ok(self._ALIAS_WITNESSABLE)
        body = _fn_body(result.wat, "f")
        assert "i64.lt_s" in body, f"missing alias narrowing guard:\n{body}"
        assert "unreachable" in body, f"missing trap edge:\n{body}"

    def test_alias_nat_return_negative_traps_at_runtime(self) -> None:
        """``f(-5)`` through the ``@Count`` alias TRAPS rather than silently
        returning -5 (the pre-fix soundness gap)."""
        result = _compile_ok(self._ALIAS_WITNESSABLE)
        with pytest.raises(
            WasmTrapError
        ):
            execute(result, fn_name="f", args=[-5])

    def test_alias_nat_return_nonnegative_returns_value(self) -> None:
        """A non-negative input passes the alias guard unchanged."""
        assert _run(self._ALIAS_WITNESSABLE, fn="f", args=[7]) == 7

    _ALIAS_OPAQUE = """
type Count = Nat;
public fn f(@Array<Int> -> @Count)
  requires(true) ensures(true) effects(pure)
{ array_length(@Array<Int>.0) }
"""

    def test_alias_opaque_tier3_narrowing_guard_emitted(self) -> None:
        """An opaque ``array_length`` narrowing into a ``type Count = Nat``
        return still carries the guard.  The verifier obligates this ``tier3``
        (promising a runtime guard); pre-fix codegen emitted none through the
        alias — the exact silent-guard-promise soundness gap.  The guard is dead
        here (``array_length`` is never negative), so a valid array never
        traps."""
        result = _compile_ok(self._ALIAS_OPAQUE)
        body = _fn_body(result.wat, "f")
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"missing alias tier3 narrowing guard:\n{body}"
        )
        assert _run(self._ALIAS_OPAQUE + """
public fn main(@Unit -> @Count)
  requires(true) ensures(true) effects(pure)
{ f([1, 2, 3]) }
""", fn="main") == 3

    _ALIAS_WIDEN = """
type MyInt = Int;
public fn g(@Nat -> @MyInt)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
"""

    def test_alias_int_return_of_a_nat_has_nothing_to_check(self) -> None:
        """A ``type MyInt = Int`` return with a @Nat body is a widening, which
        is a no-op at the value level (spec §2.2): no check, and i64.MAX
        comes back as itself.  (On the u64 `Nat` it carried a widening guard,
        which the alias name once masked.)"""
        result = _compile_ok(self._ALIAS_WIDEN)
        assert checks(result, function="g") == (), _fn_body(result.wat, "g")
        assert _run(self._ALIAS_WIDEN, fn="g", args=[2**63 - 1]) == 2**63 - 1

    _ALIAS_TO_REFINEMENT = """
type Pos = { @Nat | @Nat.0 > 0 };
public fn f(@Int -> @Pos)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
"""

    def test_alias_to_refinement_return_single_guard_not_double(self) -> None:
        """An alias-to-refinement (``type Pos = { @Nat | ... }``) return stays
        on the 7b refinement-boundary path — guarded ONCE by the boundary
        predicate (``vera.contract_fail``), NOT additionally by the bare-@Nat
        nat-bind narrowing guard.  The predicate uses ``>`` (``i64.gt_s``), so
        the ABSENCE of ``i64.lt_s`` (the nat-bind guard's signature) pins that
        the narrow gate did not co-fire — a double guard.  The
        ``_refinement_guard_parts`` exclusion is what prevents the alias
        resolution from double-guarding; dropping it reintroduces ``i64.lt_s``
        (the item-1c mutation)."""
        result = _compile_ok(self._ALIAS_TO_REFINEMENT)
        body = _fn_body(result.wat, "f")
        assert checks(result, kind="contract_violation", function="f"), (
            f"expected the refinement boundary guard:\n{body}"
        )
        assert "i64.lt_s" not in body, (
            f"the nat-bind narrow guard must NOT co-fire with the refinement "
            f"boundary guard (double guard):\n{body}"
        )


class TestParameterisedAliasReturnGuard1256:
    """#1256 — the same two gates resolve a PARAMETERISED alias APPLICATION.

    `_resolve_base_type_name` chases an alias by NAME and drops the type
    arguments, so `type Ident<T> = T; type Count = Ident<Nat>;` resolved to
    the bare head `Ident` — in neither gate's set — and a `@Count` return got
    no guard at all while the plain `type Count = Nat` spelling got both.
    Same silent-negative soundness gap #983 closed for the unparameterised
    alias, reached one spelling over: measured `run(-5)` returning -5 through
    the `@Nat` slot.

    Both gates now ask `WasmContext._boundary_base`, which substitutes the
    application because it resolves the type EXPRESSION rather than chasing
    its head — the derivation the throw payload and the `apply_fn` signature
    already share.  Each case carries its unparameterised twin as the oracle:
    the claim is that the two spellings compile to the same guard, and a
    bare "guard present" assertion would not notice if the twin lost its.
    """

    _PARAM_ALIAS = "type Ident<T> = T;\n"

    _NARROW = _PARAM_ALIAS + """
type Count = Ident<Nat>;
public fn f(@Int -> @Count)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""

    _NARROW_TWIN = """
type Count = Nat;
public fn f(@Int -> @Count)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""

    _WIDEN = _PARAM_ALIAS + """
type MyInt = Ident<Int>;
public fn g(@Nat -> @MyInt)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
"""

    _WIDEN_TWIN = """
type MyInt = Int;
public fn g(@Nat -> @MyInt)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
"""

    @pytest.mark.parametrize(
        ("source", "fn"),
        [
            pytest.param(_NARROW, "f", id="narrow"),
            pytest.param(_NARROW_TWIN, "f", id="narrow_unparameterised_twin"),
        ],
    )
    def test_the_guard_is_emitted_through_the_application(
        self, source: str, fn: str,
    ) -> None:
        """Pre-fix the parameterised case emitted no guard at all."""
        body = _fn_body(_compile_ok(source).wat, fn)
        assert "i64.lt_s" in body and "unreachable" in body, body

    @pytest.mark.parametrize(
        ("source", "fn"),
        [
            pytest.param(_WIDEN, "g", id="widen"),
            pytest.param(_WIDEN_TWIN, "g", id="widen_unparameterised_twin"),
        ],
    )
    def test_a_widening_through_the_application_checks_nothing(
        self, source: str, fn: str,
    ) -> None:
        """A `@Nat` into an `Ident<Int>` return is a widening, a no-op at the
        value level, on both spellings.  (On the u64 `Nat` both carried the
        widening guard, which the parameterised spelling once lost.)"""
        result = _compile_ok(source)
        assert checks(result, function=fn) == (), _fn_body(result.wat, fn)

    def test_a_negative_through_the_application_traps(self) -> None:
        """The soundness statement: -5 no longer reaches the `@Nat` slot.

        Pre-fix this returned **-5** — the value, not a trap — which is the
        same silent negative #983 closed for `type Count = Nat`.
        """
        result = _compile_ok(self._NARROW)
        with pytest.raises(WasmTrapError):
            execute(result, fn_name="f", args=[-5])

    def test_a_satisfying_value_through_the_application_passes(self) -> None:
        """The gained guard fires on violations only — 7 still returns 7."""
        assert _run(self._NARROW, fn="f", args=[7]) == 7

    # The parameter is `@Int`, NOT `@Nat`: the body must actually NARROW for
    # the exclusion to have anything to exclude.  A `@Nat` body into a
    # `@Nat`-based return is no narrowing leaf at all, so
    # `_collect_narrowing_return_leaves` returns nothing and the absence of
    # `i64.lt_s` below holds whether or not the conjunct is there —
    # measured, and the reason this fixture is spelled the harder way.
    _REFINED_OVER_APPLICATION = _PARAM_ALIAS + """
type Grown = { @Ident<Nat> | @Ident<Nat>.0 >= 18 };
public fn f(@Int -> @Grown)
  requires(@Int.0 >= 18) ensures(true) effects(pure)
{ @Int.0 }
"""

    def test_a_refinement_over_an_application_is_not_double_guarded(
        self,
    ) -> None:
        """The exclusion the swap must NOT disturb.

        `_boundary_base` strips refinement wrappers, so a refined return now
        answers `Nat` where the old spelling answered the alias head — which
        would double-guard were the narrow gate keyed on the base ALONE.  It
        is not: the `_refinement_guard_parts` conjunct beside it is what
        keeps a refined return on its single 7b boundary guard, and this is
        the shape that proves the swap left that conjunct doing its job.
        The return type is
        `tests/conformance/ch02_refinement_base_param_alias.vera`'s — the one
        corpus program whose base spelling the swap moves (`T` to `Nat`),
        inert there for exactly this reason.

        Mutation-measured over the whole suite, dropping the conjunct:
        `i64.lt_s` appears and this goes red, together with #983's
        unparameterised twin `test_alias_to_refinement_return_single_guard_
        not_double` — those two and nothing else, which is what says the
        exclusion is tested at both spellings and by nothing incidental.
        That measurement is also why the parameter is `@Int`: with the
        conformance program's own `@Nat` parameter the body narrows nothing,
        the leaf collector returns empty, and the assertion held with the
        conjunct gone.  A control that cannot go red is not a control.
        """
        result = _compile_ok(self._REFINED_OVER_APPLICATION)
        body = _fn_body(result.wat, "f")
        assert checks(result, kind="contract_violation", function="f"), body
        assert "i64.lt_s" not in body, body


class TestNatReturnPerLeafTCO983:
    """#983 review — the @Int->@Nat return narrowing guard is emitted PER
    NARROWING LEAF, not as a whole-body wrap, so a non-narrowing @Nat->@Nat
    recursive tail call keeps its ``return_call`` and runs constant-stack.

    Pre-fix the guard wrapped the whole body and the ``narrow_guarded`` flag
    reverted EVERY ``return_call`` to plain ``call``, so ``drain`` (a mixed-arm
    function: one narrowing leaf ``@Int.0``, one @Nat->@Nat recursive tail call)
    lost TCO and stack-exhausted at ~35k depth.  Post-fix only the narrowing
    leaf is guarded inline; the recursive tail call's ``return_call`` survives.
    """

    _DRAIN = """
public fn drain(@Int -> @Nat)
  requires(@Int.0 >= 0) ensures(true) decreases(@Int.0) effects(pure)
{ if @Int.0 == 0 then { @Int.0 } else { drain(@Int.0 - 1) } }
"""

    def test_recursive_tail_call_keeps_return_call(self) -> None:
        """The @Nat->@Nat recursive tail call keeps ``return_call $:drain`` — TCO
        is no longer reverted by the sibling narrowing arm's guard."""
        result = _compile_ok(self._DRAIN)
        body = _fn_body(result.wat, "drain")
        assert "return_call $:drain" in body, (
            f"recursive tail call lost TCO (reverted to plain call):\n{body}"
        )

    def test_narrowing_leaf_still_guarded(self) -> None:
        """The narrowing ``@Int.0`` leaf still carries its inline guard — the
        per-leaf emission guards the genuine narrowing without touching the
        recursive tail call."""
        result = _compile_ok(self._DRAIN)
        body = _fn_body(result.wat, "drain")
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"narrowing leaf lost its guard:\n{body}"
        )

    def test_runs_constant_stack_at_200k(self) -> None:
        """``drain(200000)`` returns 0 — constant-stack via the preserved
        ``return_call``.  Pre-fix this stack-exhausted at ~35k depth."""
        assert _run(self._DRAIN, fn="drain", args=[200000]) == 0
