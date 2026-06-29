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
