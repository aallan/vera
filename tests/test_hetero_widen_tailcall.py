"""Verifier<->codegen desync tests for the #820 heterogeneous per-arm @Nat->@Int
widen guard: three fixes found by review on PR #986.

FIX 1 — the per-arm widen guard is DEAD CODE under a tail call.  A hetero
@Int-join arm that is a @Nat-returning tail call lowers to ``return_call``; the
guard is appended AFTER the terminator, so ``run(u64.MAX)`` returns the
bit-reinterpreted negative @Int with NO trap while the verifier claims the
``nat_to_int_coerce`` obligation is ``tier3`` (runtime-guarded).  The fix mirrors
the #983 leaf machinery: collect the calls under each guarded @Nat arm and
subtract them from ``tail_sites`` so they lower to a plain ``call`` the guard can
follow.

FIX 4 — the per-arm widen gate is TARGET-BLIND.  Codegen guarded any i64 hetero
join, never consulting the join's TARGET type (unlike the verifier's
``_is_hetero_int_widen_join``, which additionally requires ``_is_int_type`` of the
target).  A hetero i64 join in a @Nat-RETURNING function (the @Int arm narrows in
via the #983 nat_bind machinery) had its legal @Nat arm falsely wrapped in the
widen guard, trapping a verify-clean Tier-1 program on a value like 2^63.

FIX 3 — a user ``data Tuple<A, B>`` fools the ``expr.name == "Tuple"`` gate: the
construction takes the builtin-Tuple target-table path and emits a widen guard
(``run`` traps) while the verifier routes the user construction through the
generic-ctor-field path and emits NO obligation (opposite-direction desync).
Its discrimination is RETRACTED as of #1397 — the name is reserved in the data
namespace (E158), so there is no second Tuple to tell apart — and the class
that pinned it now measures the refusal plus the genuine carrier's guard.

Constants:
    I64_MAX  = 9223372036854775807   ( 2^63 - 1 )  -- sign bit clear, in-range
    TWO_63   = 9223372036854775808   ( 2^63     )  -- sign bit set, a legal @Nat
    U64_MAX  = 18446744073709551615  ( 2^64 - 1 )
"""

from __future__ import annotations

import tempfile
from pathlib import Path

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import WasmTrapError
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.verifier import verify

I64_MAX = 9223372036854775807
TWO_63 = 9223372036854775808
U64_MAX = 18446744073709551615
_MASK64 = (1 << 64) - 1
_KIND = "nat_to_int_coerce"


def _compile_with_types(source: str):
    """Compile via the artifact-threaded path (mirrors cmd_run): the widening
    classifier consults the checker's resolved- and target-type tables."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        path = f.name
    try:
        program = parse_to_ast(source)
        resolver = ModuleResolver(_root=Path(path).parent)
        resolved = resolver.resolve_imports(program, Path(path))
        diags, arts = typecheck_with_artifacts(
            program, source, file=path, resolved_modules=resolved,
        )
        errors = [d for d in diags if d.severity == "error"]
        assert not errors, f"typecheck errors: {[d.description for d in errors]}"
        result = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        errs = [d for d in result.diagnostics if d.severity == "error"]
        assert not errs, f"codegen errors: {[d.description for d in errs]}"
        return result
    finally:
        Path(path).unlink(missing_ok=True)


def _run(source: str, fn: str, args: list[int]) -> int:
    result = _compile_with_types(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None
    return exec_result.value


def _assert_traps(
    source: str, fn: str, args: list[int], kind: str = "widen_guard",
) -> None:
    """Assert the guard at THIS site fires, by its own trap kind.

    Two guards live in this file's fixtures and they report different kinds:
    the `@Int` -> `@Nat` narrowing guard carries `nat_guard` (#754), and the
    `@Nat` -> `@Int` widen guard carries `widen_guard` (#1438, which signals
    `vera.widen_trap` before the `unreachable` on #754's pattern — until then
    the widen side tripped the bare `unreachable` net, indistinguishable from
    a non-exhaustive match).  A union of the two would accept either at every
    site, so a narrowing guard regressing to the bare net — the exact
    condition #754 fixed — would leave every cell here green (PR review).
    Since #1438 the same argument runs in the other direction too: a widen
    guard losing its signal now fails here instead of quietly passing as
    `unreachable`.  The default is the widen kind because most sites here are
    widening; a narrowing site passes its own.
    """
    result = _compile_with_types(source)
    with pytest.raises(WasmTrapError) as exc_info:
        execute(result, fn_name=fn, args=args)
    assert exc_info.value.kind == kind, (
        f"expected the {kind!r} guard at this site, got "
        f"{exc_info.value.kind!r}"
    )


def _assert_no_trap(source: str, fn: str, args: list[int], expect: int) -> None:
    assert _run(source, fn, args) & _MASK64 == expect & _MASK64


def _coerce_statuses(source: str) -> list[str]:
    program = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(program, source)
    result = verify(
        program, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    return [o.status for o in result.obligations if o.kind == _KIND]


# =====================================================================
# FIX 1 — per-arm widen guard dead under a tail call
# =====================================================================

# The @Nat `_` arm is a tail call to a @Nat helper; the `0 ->` arm is a genuine
# @Int slot, so the match is a hetero @Int join and the `_` arm is widen-guarded.
# The join is the return-position expr of an @Int fn, so it TARGETS @Int.
_FIX1_MATCH = """
private fn helper(@Nat -> @Nat) requires(true) ensures(true) effects(pure) { @Nat.0 }
public fn f(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{ let @Int = 0 - 1; match @Nat.0 { 0 -> @Int.0, _ -> helper(@Nat.0) } }
"""

# The if-form: the else arm is the @Nat tail call, the then arm a genuine @Int.
_FIX1_IF = """
private fn helper(@Nat -> @Nat) requires(true) ensures(true) effects(pure) { @Nat.0 }
public fn f(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{ let @Int = 0 - 1; if @Nat.0 == 0 then { @Int.0 } else { helper(@Nat.0) } }
"""

# TCO preservation: a hetero match whose GENUINE @Int arm is a *recursive* tail
# call (returns @Int, so NOT widen-guarded and NOT collected).  The @Nat `0 ->`
# arm is a bare slot (widen-guarded per-arm, but reachable — not a call).  The
# recursive @Int arm must keep its `return_call $f` so a deep run is
# constant-stack.
_FIX1_TCO = """
public fn f(@Nat, @Int -> @Int) requires(true) ensures(true) effects(pure)
{ match @Int.0 { 0 -> @Nat.0, _ -> f(@Nat.0, @Int.0 - 1) } }
"""


class TestFix1DeadGuardUnderTailCall:
    def test_match_tailcall_arm_verifier_tier3(self) -> None:
        statuses = _coerce_statuses(_FIX1_MATCH)
        assert statuses, "no nat_to_int_coerce obligation emitted"
        assert all(s == "tier3" for s in statuses), statuses

    def test_match_tailcall_arm_run_traps(self) -> None:
        # BUG at head: the `_` arm compiled to `return_call $helper` and the
        # widen guard appended after it is DEAD — run(u64.MAX) returned -1.
        _assert_traps(_FIX1_MATCH, "f", [U64_MAX])

    def test_match_tailcall_arm_in_range(self) -> None:
        _assert_no_trap(_FIX1_MATCH, "f", [42], 42)

    def test_if_tailcall_arm_run_traps(self) -> None:
        _assert_traps(_FIX1_IF, "f", [U64_MAX])

    def test_if_tailcall_arm_in_range(self) -> None:
        _assert_no_trap(_FIX1_IF, "f", [42], 42)

    def test_match_tailcall_arm_wat_plain_call_then_live_guard(self) -> None:
        # After the fix the @Nat arm's call must be a PLAIN `call $helper`
        # (not `return_call`) followed by the live widen guard, so the sign
        # check runs.  This is the structural proof the guard is reachable.
        wat = _compile_with_types(_FIX1_MATCH).wat
        assert "call $helper" in wat
        assert "return_call $helper" not in wat, (
            "the @Nat widen-guarded arm's call must be reverted to a plain "
            "call so the appended guard is reached"
        )
        # ...and the live guard (sign check + trap) follows it.  Since #1438 the
        # widen guard's trap is `call $vera.widen_trap` then `unreachable`, so
        # pin the signal: a bare `unreachable` appears elsewhere in every module
        # (GC shadow-stack overflow, array bounds), and asserting only that word
        # would keep this cell green with no widen guard emitted at all.
        assert "i64.lt_s" in wat and "call $vera.widen_trap" in wat

    def test_tco_recursive_int_arm_return_call_survives(self) -> None:
        # The GENUINE @Int recursive arm is NOT widen-guarded, so its
        # `return_call $f` must survive — the collector over-collects only
        # inside guarded @Nat arms.
        wat = _compile_with_types(_FIX1_TCO).wat
        assert "return_call $f" in wat, (
            "the recursive @Int tail arm must keep its return_call (TCO); the "
            "hetero-arm collector must not strip a non-@Nat arm's tail call"
        )

    def test_tco_recursive_int_arm_constant_stack(self) -> None:
        # 100k-depth recursion returns constant-stack iff the return_call
        # survived; a reverted plain-call chain stack-exhausts.  @Nat.0 = 0 so
        # the base-case widen guard does not trap.
        assert _run(_FIX1_TCO, "f", [0, 100_000]) == 0


# =====================================================================
# FIX 4 — target-blind per-arm gate false-traps a legal @Nat
# =====================================================================

# A hetero i64 join in a @Nat-RETURNING fn.  The @Int arm narrows into the @Nat
# return (handled by the #983 nat_bind machinery); the @Nat arm is a LEGAL @Nat.
# The join TARGETS @Nat, so the verifier emits NO per-arm nat_to_int_coerce and
# codegen must NOT widen-guard the @Nat arm.
_FIX4_IF = """
public fn pick_if(@Nat, @Int, @Bool -> @Nat)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ if @Bool.0 then { @Nat.0 } else { @Int.0 } }
"""

_FIX4_MATCH = """
public fn pick_match(@Nat, @Int -> @Nat)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ match @Int.0 { 0 -> @Nat.0, _ -> @Int.0 } }
"""

# FIX 4 (b): the @Int arm of a @Nat-returning hetero join still narrows into the
# @Nat return and must keep its #983 nat_bind guard (negative -> trap).  No
# `requires(@Int.0 >= 0)` so a negative @Int can reach the arm.
_FIX4_NARROW = """
public fn pnarrow(@Nat, @Int, @Bool -> @Nat)
  requires(true) ensures(true) effects(pure)
{ if @Bool.0 then { @Nat.0 } else { @Int.0 } }
"""

# FIX 4 (d): a hetero join in a LET whose binding is @Int genuinely TARGETS @Int,
# so the @Nat arm must STILL be widen-guarded (the target-aware gate fires).
_FIX4_LET_INT = """
public fn f(@Nat, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Int = if @Int.0 == 0 then { @Nat.0 } else { @Int.0 }; @Int.0 }
"""


class TestFix4TargetBlindGate:
    def test_if_nat_return_verifies_tier1_no_coerce(self) -> None:
        # The verifier is correct: a @Nat-target hetero join emits no
        # nat_to_int_coerce (only the @Int arm's nat_bind).
        assert _coerce_statuses(_FIX4_IF) == []

    def test_if_nat_arm_legal_nat_no_trap(self) -> None:
        # BUG at head: 2^63 (a legal @Nat) traps because the @Nat arm was
        # falsely widen-guarded even though the join targets @Nat.
        _assert_no_trap(_FIX4_IF, "pick_if", [TWO_63, 0, 1], TWO_63)
        _assert_no_trap(_FIX4_IF, "pick_if", [U64_MAX, 0, 1], U64_MAX)

    def test_if_nat_arm_in_range_control(self) -> None:
        # i64.MAX has the sign bit clear, so it never tripped the guard — a
        # constant control that isolates the false-trap regression.
        _assert_no_trap(_FIX4_IF, "pick_if", [I64_MAX, 0, 1], I64_MAX)

    def test_match_nat_return_verifies_tier1_no_coerce(self) -> None:
        assert _coerce_statuses(_FIX4_MATCH) == []

    def test_match_nat_arm_legal_nat_no_trap(self) -> None:
        _assert_no_trap(_FIX4_MATCH, "pick_match", [TWO_63, 0], TWO_63)
        _assert_no_trap(_FIX4_MATCH, "pick_match", [U64_MAX, 0], U64_MAX)

    def test_int_arm_narrow_guard_intact(self) -> None:
        # Regression companion: FIX 4 must NOT disable the @Int arm's #983
        # narrow guard — a negative @Int into the @Nat return still traps.
        _assert_traps(_FIX4_NARROW, "pnarrow", [0, -5, 0], "nat_guard")

    def test_let_int_target_still_guards_nat_arm(self) -> None:
        # Control: when the hetero join genuinely TARGETS @Int (a `let @Int`),
        # the target-aware gate still fires and the @Nat arm is widen-guarded.
        _assert_traps(_FIX4_LET_INT, "f", [U64_MAX, 0])

    def test_let_int_target_in_range(self) -> None:
        _assert_no_trap(_FIX4_LET_INT, "f", [42, 0], 42)


# =====================================================================
# FIX 3 — the user `data Tuple<A, B>` that fooled the builtin-Tuple gate
# is refused at check (#1397)
# =====================================================================

# A user ADT named Tuple.  The desync FIX 3 guarded against no longer has a
# program to happen in: #1397 reserves the name in the data namespace, so the
# checker refuses this declaration with E158 and neither the verifier's
# generic-ctor-field routing nor codegen's target-table path can be reached
# with a second Tuple in scope.
_FIX3_USER_TUPLE = """
private data Tuple<A, B> { Tuple(A, B) }
public fn f(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = Tuple(@Nat.0, @Nat.0); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 } }
"""

# Control: the REAL builtin Tuple carrier — its @Nat->@Int component widening
# MUST still trap (do not break the actual #820 site).
_FIX3_BUILTIN_TUPLE = """
public fn tc(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = Tuple(@Nat.0, 0); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 } }
"""


class TestFix3UserTupleIsRefused:
    """#1397 — the collision FIX 3 discriminated is now refused at check.

    FIX 3 taught codegen to tell the builtin variadic carrier (empty
    ``field_offsets``) from a user ``data Tuple<A, B>`` (a fixed layout), so
    only the carrier took the target-table widen-guard path.  That
    discrimination is retracted: `Tuple` is reserved in the data namespace
    (E158) on the rule that reserves built-in function names (E151) and
    built-in effect names (E152), because the same name collision ALSO made
    ``show`` under a user ``data Tuple`` drop the constructor name, and the
    carrier cannot be told apart at render time.

    What the class still measures is the half that must not move: the
    genuine carrier's #820 widen guard is intact, so the retraction is not a
    quiet withdrawal of the guard it was narrowing.
    """

    def test_user_tuple_declaration_is_refused_at_check(self) -> None:
        # The declaration FIX 3 existed to accommodate no longer type-checks,
        # so codegen never sees a second Tuple and the desync it guarded
        # against (a widen guard the verifier never obligated, trapping a
        # legal @Nat at u64.MAX) is unreachable rather than discriminated.
        program = parse_to_ast(_FIX3_USER_TUPLE)
        diags, _arts = typecheck_with_artifacts(program, _FIX3_USER_TUPLE)
        codes = [d.error_code for d in diags if d.severity == "error"]
        assert "E158" in codes, codes

    def test_builtin_tuple_still_traps(self) -> None:
        # Control: the genuine builtin Tuple carrier's widen guard is intact.
        _assert_traps(_FIX3_BUILTIN_TUPLE, "tc", [U64_MAX])

    def test_builtin_tuple_in_range(self) -> None:
        _assert_no_trap(_FIX3_BUILTIN_TUPLE, "tc", [42], 42)

    def test_a_user_tuple_CONSTRUCTOR_cannot_disarm_the_carrier_guard(
        self,
    ) -> None:
        """The constructor-namespace twin, found in PR #1404 review.

        `ctor_layouts` is flattened by CONSTRUCTOR name, so a user ADT with
        a constructor called `Tuple` won the built-in carrier's flat slot
        with its own FIXED layout.  At `release/v0.2.0` the FIX-3 clause
        then read that layout, concluded "user ADT", and skipped the widen
        guard on a GENUINE built-in tuple construction elsewhere in the same
        program: `tc(u64.MAX)` returned a reinterpreted negative `@Int` with
        NO trap, on a program the verifier had nothing to say about.

        A `Bool` payload is load-bearing: with an `Int` one the clobbered
        layout's `int_fields` coincidentally re-guards the same component,
        which is why the hole is invisible to the obvious repro.

        #1397 closes it at the source — the constructor name is reserved
        (E158) — so the program is refused before either layout exists.
        """
        poisoned = """
private data ZzBox { Tuple(Bool) }
""" + _FIX3_BUILTIN_TUPLE
        program = parse_to_ast(poisoned)
        diags, _arts = typecheck_with_artifacts(program, poisoned)
        codes = [d.error_code for d in diags if d.severity == "error"]
        assert "E158" in codes, codes

    def test_builtin_tuple_coerce_is_still_runtime_guarded(self) -> None:
        # And the verifier still OBLIGATES it — the half `_coerce_statuses`
        # used to check on the user side.  Retracting the discrimination must
        # not leave codegen guarding a site the verifier stopped obligating,
        # which is the desync in the other direction.
        assert "tier3" in _coerce_statuses(_FIX3_BUILTIN_TUPLE)
