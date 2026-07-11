"""Runtime @Nat -> @Int widening-trap codegen tests for #813 (stage 3).

The verifier (stages 2a/2b) emits a ``nat_to_int_coerce`` obligation at every
@Nat -> @Int coercion site (return, call argument, let binding) that the value
is ``<= i64.MAX``.  This file makes the codegen emit the matching runtime guard,
so ``vera run`` / ``vera compile`` programs **trap** when a @Nat above i64.MAX
would otherwise reinterpret to a negative @Int — instead of silently returning
the wrong value.

A @Nat is stored as an i64; its unsigned value exceeds i64.MAX exactly when its
sign bit is set, i.e. when the i64 reads as negative.  So the guard traps when
``(i64 value) < 0`` — the same WAT as the #552 nat-bind guard, a bare
``unreachable`` (kind="unreachable"); a precise trap kind is a follow-up.

Written test-first: ``*_traps`` FAILS on the pre-stage-3 codegen (the widen is a
no-op, so ``widen(u64.MAX)`` returns -1, no trap), and ``*_no_trap`` passes both
before and after (a safe/bounded widen is unchanged).

Constants:
    I64_MAX = 9223372036854775807   ( 2^63 - 1 )
    U64_MAX = 18446744073709551615  ( 2^64 - 1 )
"""

from __future__ import annotations

import tempfile
from pathlib import Path

import pytest
import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver

I64_MAX = 9223372036854775807
U64_MAX = 18446744073709551615
_MASK64 = (1 << 64) - 1


def _compile_with_types(source: str):
    """Compile via the artifact-threaded path (mirrors cmd_run); the widening
    classifier consults the checker's resolved-type table, so codegen must be
    handed it."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        path = f.name
    try:
        ast = parse_to_ast(source)
        resolver = ModuleResolver(_root=Path(path).parent)
        resolved = resolver.resolve_imports(ast, Path(path))
        diags, arts = typecheck_with_artifacts(
            ast, source, file=path, resolved_modules=resolved,
        )
        errors = [d for d in diags if d.severity == "error"]
        assert not errors, f"typecheck errors: {[d.description for d in errors]}"
        result = codegen_compile(
            ast, source=source, file=path,
            resolved_modules=resolved,
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


def _assert_traps(source: str, fn: str, args: list[int]) -> None:
    result = _compile_with_types(source)
    with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
        execute(result, fn_name=fn, args=args)


def _assert_no_trap(source: str, fn: str, args: list[int], expect: int) -> None:
    assert _run(source, fn, args) & _MASK64 == expect & _MASK64


# `ensures(true)` deliberately: a postcondition like `ensures(@Int.result >= 0)`
# would make the *runtime postcondition* guard trap on the -1 result, masking
# whether the coercion guard itself fires.  With no catching postcondition, a
# pre-stage-3 `widen(u64.MAX)` returns -1 *silently* — the exact soundness hole.
_WIDEN_RETURN = """
public fn widen(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
"""

_WIDEN_CALL_ARG = """
public fn takes_int(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

public fn caller(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ takes_int(@Nat.0) }
"""

_WIDEN_LET = """
public fn f(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Int = @Nat.0; @Int.0 }
"""

# #813 stage 2c — @Nat into a concrete @Int constructor field, found by the
# completeness audit.  Codegen guards the concrete @Int field via the layout
# `int_fields` bitmap (the dual of `nat_fields`); without the guard the stored
# bits reinterpret to a negative @Int when extracted (u64.MAX -> -1).
_WIDEN_CTOR_FIELD = """
private data WrapInt { WrapInt(Int) }
public fn ctor_field(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @WrapInt = WrapInt(@Nat.0); match @WrapInt.0 { WrapInt(@Int) -> @Int.0 } }
"""

# #813 stage 2c — extracting a concrete @Nat *field* into an @Int sub-pattern
# slot (`match @Box.0 { Box(@Int) -> }` on a `Box(Nat)`).  Codegen guards the
# extraction only when the source field is @Nat (`layout.nat_fields[i]`), never
# a genuine @Int field — a widen guard would otherwise wrongly trap a
# legitimately-negative @Int.
_WIDEN_ADT_SUBPATTERN = """
private data Box { Box(Nat) }
public fn box_extract(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Box = Box(@Nat.0); match @Box.0 { Box(@Int) -> @Int.0 } }
"""

# #813 stage 2c — `match @Nat.0 { @Int -> }` binds a @Nat scrutinee into an @Int
# slot.  Codegen guards the bind only when the scrutinee is @Nat
# (`_result_is_nat`), never a genuine @Int scrutinee (which can be negative).
_WIDEN_MATCH_BIND = """
public fn mb(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Nat.0 { @Int -> @Int.0 } }
"""

# Control: a @Int scrutinee match-bind must NOT trap on a negative value —
# proves the widen guard keys on the SOURCE being @Nat, not the target slot.
_MATCH_BIND_INT_SOURCE = """
public fn mbint(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Int.0 { @Int -> @Int.0 } }
"""

# #813 review (C1): a @Nat-returning CALL widened at the return position.  This
# is the case the original corpus missed — codegen's _result_is_nat must resolve
# make's @Nat return via the side-table, and the return guard must survive
# tail-call lowering (the call is in tail position).  Pre-fix: returned -1.
_WIDEN_RETURN_CALL = """
private fn make(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }

public fn f(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ make(@Nat.0) }
"""

# I2 controls: a genuine @Int source at a widening-target slot must NOT trap on
# a negative value (the guard keys on a @Nat source, not the @Int target).
_RETURN_INT_SOURCE = """
public fn ret_int(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
_LET_INT_SOURCE = """
public fn let_int(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Int = @Int.0; @Int.0 }
"""

# S5: pipe arg `@Nat.0 |> identity()` desugars to identity(@Nat.0); codegen
# guards it at the call-argument site, so u64.MAX must trap.
_WIDEN_PIPE = """
private fn identity(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

public fn pipe_widen(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 |> identity() }
"""

# #813 follow-up (audit site 1): the explicit `nat_to_int` built-in widens its
# @Nat argument to @Int.  Its declared return is @Int, so the resolved-type
# side-table reports "Int" and the plain `_result_is_nat` FnCall branch misses
# that the *value* carries an unbounded @Nat forward — leaving it unguarded
# (silent -1 on u64.MAX).  Both `_result_is_nat` helpers special-case it.
_WIDEN_NAT_TO_INT = """
public fn ntoi(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(@Nat.0) }
"""

# #813 follow-up (audit site 2a): an if-expr with a real @Nat arm and a
# NON-NEGATIVE LITERAL arm.  A literal is always <= i64.MAX, so it is @Nat-
# compatible: `_result_is_nat` keeps the whole if @Nat (`_arm_nat_compatible`),
# and the single boundary guard fires on the real @Nat arm.  `if true` forces
# the @Nat then-arm; `else { 0 }` is the literal arm (never out-of-range).
# (Site 2b — a genuine @Int *slot* sibling arm — is guarded per-arm since #820;
# see `_WIDEN_HETERO_IF_SLOT` below.)
_WIDEN_HETERO_IF = """
public fn hif(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ if true then { @Nat.0 } else { 0 } }
"""

# #813 follow-up (audit site 2a): the same literal-arm shape via `match`.  The
# `0 -> 0` arm is a literal (@Nat-compatible), the `_ -> @Nat.0` wildcard arm
# returns the @Nat scrutinee (the real @Nat arm) with no match-bind — so the
# whole match is @Nat and the boundary guard fires.  u64.MAX falls to `_`.
_WIDEN_HETERO_MATCH = """
public fn hmatch(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Nat.0 { 0 -> 0, _ -> @Nat.0 } }
"""

# Control: the genuine @Int *slot* arm of a heterogeneous if must NOT trap on a
# negative value — the per-arm guard fires only on the @Nat arm, never the @Int
# arm (which can be legitimately negative).  `if false` forces the @Int else-arm.
_HETERO_IF_INT_ARM_CONTROL = """
public fn hctrl(@Nat, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if false then { @Nat.0 } else { @Int.0 } }
"""

# #820 site 2b: a heterogeneous if whose alternative is a genuine @Int *slot*
# (not the #813 non-negative literal).  The join is genuinely @Int, so the
# boundary guard cannot fire — the @Nat then-arm is guarded PER-ARM.  `if true`
# forces the @Nat arm; u64.MAX must trap.
_WIDEN_HETERO_IF_SLOT = """
public fn hif(@Nat, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if true then { @Nat.0 } else { @Int.0 } }
"""

# #820 site 2b (match form): the `_ -> @Nat.0` arm is guarded per-arm because the
# `0 -> @Int.0` arm makes the join genuinely @Int.  u64.MAX falls to `_`.
_WIDEN_HETERO_MATCH_SLOT = """
public fn hmatch(@Nat, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Nat.0 { 0 -> @Int.0, _ -> @Nat.0 } }
"""

# #820: a @Nat element widening into an @Array<Int> literal.  Codegen recovers
# the target element type (`Array<Int>`) and guards the element store.
_WIDEN_ARRAY_ELEM = """
public fn ae(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [@Nat.0]; @Array<Int>.0[0] }
"""

# #820: a @Nat component widening into an @Int tuple slot at construction.  The
# Tuple carrier's target component types (`Tuple<Int, Int>`) supply the guard.
_WIDEN_TUPLE_CONSTRUCT = """
public fn tc(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = Tuple(@Nat.0, 0); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 } }
"""

# #820: the destructure form — the field load is guarded at the destructure read.
_WIDEN_TUPLE_DESTR = """
public fn td(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(@Nat.0, @Nat.0); @Int.0 }
"""

# #820: `apply_fn(closure, @Nat.0)` widens a @Nat into the closure's @Int formal.
# The formal type is recovered from the closure's function-type; the
# call_indirect argument is guarded.
_WIDEN_CLOSURE_ARG = """
type IntToInt = fn(Int -> Int) effects(pure);
public fn f(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 }; apply_fn(@IntToInt.0, @Nat.0) }
"""

# Control: a @Nat argument into a closure whose formal is genuinely @Nat is NOT
# a widening — the closure body may legitimately receive u64.MAX, so no trap.
_CLOSURE_NAT_FORMAL_CONTROL = """
type NatToNat = fn(Nat -> Nat) effects(pure);
public fn f(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @NatToNat = fn(@Nat -> @Nat) effects(pure) { @Nat.0 }; apply_fn(@NatToNat.0, @Nat.0) }
"""

# #820: a @Nat closure body widening into the closure's @Int RETURN — the
# definition-side dual of the closure argument.  Guarded in
# _compile_lifted_closure; obligated shallow-syntactically (tier3).
_WIDEN_CLOSURE_RETURN = """
type NatToInt = fn(Nat -> Int) effects(pure);
public fn f(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @NatToInt = fn(@Nat -> @Int) effects(pure) { @Nat.0 }; apply_fn(@NatToInt.0, @Nat.0) }
"""

# #820: a CAPTURED @Nat used as the closure's @Int return — same body-return
# guard (the captured @Nat.0 is the body's trailing value).  `@Unit` arg so the
# only widening is the return.
_WIDEN_CLOSURE_CAPTURE = """
type UnitToInt = fn(Unit -> Int) effects(pure);
public fn f(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @UnitToInt = fn(@Unit -> @Int) effects(pure) { @Nat.0 }; apply_fn(@UnitToInt.0, ()) }
"""

# Control: a genuinely @Int closure body/return must NOT trap on a negative
# value — the closure-return guard fires only on a @Nat body.
_CLOSURE_INT_BODY_CONTROL = """
type IntToInt = fn(Int -> Int) effects(pure);
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 }; apply_fn(@IntToInt.0, @Int.0) }
"""


class TestNatToIntWideningTrap813:
    def test_return_widening_traps_above_i64_max(self) -> None:
        # u64.MAX widened to @Int reinterprets to -1; the guard must trap rather
        # than return it.  Pre-stage-3: no guard, execute returns -1 (no trap).
        _assert_traps(_WIDEN_RETURN, "widen", [U64_MAX])

    def test_return_widening_no_trap_when_in_range(self) -> None:
        # A @Nat that fits in i64 widens exactly — no trap, value preserved.
        _assert_no_trap(_WIDEN_RETURN, "widen", [42], 42)

    def test_return_widening_no_trap_at_i64_max(self) -> None:
        # The boundary value i64.MAX is in range (sign bit clear) — no trap.
        _assert_no_trap(_WIDEN_RETURN, "widen", [I64_MAX], I64_MAX)

    def test_call_argument_widening_traps(self) -> None:
        _assert_traps(_WIDEN_CALL_ARG, "caller", [U64_MAX])

    def test_call_argument_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_CALL_ARG, "caller", [7], 7)

    def test_let_widening_traps(self) -> None:
        _assert_traps(_WIDEN_LET, "f", [U64_MAX])

    def test_let_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_LET, "f", [9], 9)

    def test_ctor_field_widening_traps(self) -> None:
        _assert_traps(_WIDEN_CTOR_FIELD, "ctor_field", [U64_MAX])

    def test_ctor_field_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_CTOR_FIELD, "ctor_field", [42], 42)

    def test_adt_subpattern_widening_traps(self) -> None:
        _assert_traps(_WIDEN_ADT_SUBPATTERN, "box_extract", [U64_MAX])

    def test_adt_subpattern_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_ADT_SUBPATTERN, "box_extract", [42], 42)

    def test_match_bind_widening_traps(self) -> None:
        _assert_traps(_WIDEN_MATCH_BIND, "mb", [U64_MAX])

    def test_match_bind_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_MATCH_BIND, "mb", [42], 42)

    def test_match_bind_int_source_no_trap_on_negative(self) -> None:
        # A genuine @Int scrutinee bound by `@Int ->` must NOT trap on a
        # negative value — the widen guard fires only on a @Nat source.
        _assert_no_trap(_MATCH_BIND_INT_SOURCE, "mbint", [-5], -5)

    def test_return_call_result_widening_traps(self) -> None:
        # #813 review C1: a @Nat-returning call widened at return must trap —
        # codegen must resolve the call's @Nat return AND the guard must survive
        # tail-call lowering.  Pre-fix this silently returned -1.
        _assert_traps(_WIDEN_RETURN_CALL, "f", [U64_MAX])

    def test_return_call_result_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_RETURN_CALL, "f", [7], 7)

    def test_return_int_source_no_trap_on_negative(self) -> None:
        _assert_no_trap(_RETURN_INT_SOURCE, "ret_int", [-5], -5)

    def test_let_int_source_no_trap_on_negative(self) -> None:
        _assert_no_trap(_LET_INT_SOURCE, "let_int", [-5], -5)

    def test_pipe_widening_traps(self) -> None:
        _assert_traps(_WIDEN_PIPE, "pipe_widen", [U64_MAX])

    def test_pipe_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_PIPE, "pipe_widen", [42], 42)

    def test_nat_to_int_widening_traps(self) -> None:
        # #813 follow-up site 1: `nat_to_int(@Nat.0)` widened to @Int must trap
        # on u64.MAX.  Pre-fix the built-in's declared @Int return masked the
        # @Nat source and it silently returned -1.
        _assert_traps(_WIDEN_NAT_TO_INT, "ntoi", [U64_MAX])

    def test_nat_to_int_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_NAT_TO_INT, "ntoi", [42], 42)

    def test_hetero_if_nat_arm_widening_traps(self) -> None:
        # #813 follow-up site 2: the @Nat then-arm of a heterogeneous if must
        # trap on u64.MAX even though the if's join type is @Int.
        _assert_traps(_WIDEN_HETERO_IF, "hif", [U64_MAX])

    def test_hetero_if_nat_arm_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_HETERO_IF, "hif", [42], 42)

    def test_hetero_match_nat_arm_widening_traps(self) -> None:
        # u64.MAX falls to the `_` arm returning the @Nat scrutinee; the literal
        # `0 -> 0` arm keeps the match @Nat-classified, so the boundary guard
        # fires — must trap.
        _assert_traps(_WIDEN_HETERO_MATCH, "hmatch", [U64_MAX])

    def test_hetero_match_nat_arm_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_HETERO_MATCH, "hmatch", [42], 42)

    def test_hetero_if_int_arm_no_trap_on_negative(self) -> None:
        # Control: the genuine @Int arm of a heterogeneous if must NOT trap on a
        # negative value — the per-arm guard fires only on the @Nat arm.
        _assert_no_trap(_HETERO_IF_INT_ARM_CONTROL, "hctrl", [0, -5], -5)

    # ---- #820 sites: per-component target-type widening guards ----

    def test_hetero_if_slot_nat_arm_traps(self) -> None:
        # #820 site 2b: the @Nat then-arm of a heterogeneous @Int-slot-join if
        # must trap on u64.MAX (the boundary guard can't fire — the @Int else arm
        # can be negative).  Pre-#820 this silently returned -1.
        _assert_traps(_WIDEN_HETERO_IF_SLOT, "hif", [U64_MAX, 0])

    def test_hetero_if_slot_nat_arm_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_HETERO_IF_SLOT, "hif", [42, 0], 42)

    def test_hetero_if_slot_int_arm_no_trap_on_negative(self) -> None:
        # The genuine @Int else-arm must round-trip a negative value (`if false`
        # forces it) — the per-arm guard never touches the @Int arm.
        _WIDEN_HETERO_IF_SLOT_ELSE = _WIDEN_HETERO_IF_SLOT.replace(
            "if true", "if false")
        _assert_no_trap(_WIDEN_HETERO_IF_SLOT_ELSE, "hif", [0, -5], -5)

    def test_hetero_match_slot_nat_arm_traps(self) -> None:
        # #820 site 2b (match): u64.MAX falls to `_ -> @Nat.0`, guarded per-arm.
        _assert_traps(_WIDEN_HETERO_MATCH_SLOT, "hmatch", [U64_MAX, 0])

    def test_hetero_match_slot_nat_arm_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_HETERO_MATCH_SLOT, "hmatch", [42, 0], 42)

    def test_array_elem_widening_traps(self) -> None:
        # #820: a @Nat element widened into an @Array<Int> literal must trap.
        _assert_traps(_WIDEN_ARRAY_ELEM, "ae", [U64_MAX])

    def test_array_elem_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_ARRAY_ELEM, "ae", [42], 42)

    def test_tuple_construct_widening_traps(self) -> None:
        # #820: a @Nat component widened into an @Int tuple slot at construction.
        _assert_traps(_WIDEN_TUPLE_CONSTRUCT, "tc", [U64_MAX])

    def test_tuple_construct_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_TUPLE_CONSTRUCT, "tc", [42], 42)

    def test_tuple_destr_widening_traps(self) -> None:
        # #820: the destructure form guards the field load at the read.
        _assert_traps(_WIDEN_TUPLE_DESTR, "td", [U64_MAX])

    def test_tuple_destr_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_TUPLE_DESTR, "td", [42], 42)

    def test_closure_arg_widening_traps(self) -> None:
        # #820: a @Nat argument widened into an @Int closure formal must trap at
        # the call_indirect boundary.  Pre-#820 this silently returned -1.
        _assert_traps(_WIDEN_CLOSURE_ARG, "f", [U64_MAX])

    def test_closure_arg_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_CLOSURE_ARG, "f", [42], 42)

    def test_closure_nat_formal_no_trap(self) -> None:
        # Control: a @Nat argument into a genuinely @Nat closure formal is not a
        # widening — u64.MAX must round-trip, never trap.
        _assert_no_trap(_CLOSURE_NAT_FORMAL_CONTROL, "f", [U64_MAX], U64_MAX)

    def test_closure_return_widening_traps(self) -> None:
        # #820: a @Nat closure body widened into the closure's @Int return must
        # trap on u64.MAX (guarded in _compile_lifted_closure).  Pre-#820 silent.
        _assert_traps(_WIDEN_CLOSURE_RETURN, "f", [U64_MAX])

    def test_closure_return_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_CLOSURE_RETURN, "f", [42], 42)

    def test_closure_capture_widening_traps(self) -> None:
        # #820: a captured @Nat used as the closure's @Int return — same guard.
        _assert_traps(_WIDEN_CLOSURE_CAPTURE, "f", [U64_MAX])

    def test_closure_capture_widening_no_trap_in_range(self) -> None:
        _assert_no_trap(_WIDEN_CLOSURE_CAPTURE, "f", [42], 42)

    def test_closure_int_body_no_trap_on_negative(self) -> None:
        # Control: a genuinely @Int closure body must round-trip a negative value
        # — the closure-return guard fires only on a @Nat body.
        _assert_no_trap(_CLOSURE_INT_BODY_CONTROL, "f", [-5], -5)
