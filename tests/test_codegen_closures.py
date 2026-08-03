"""Tests for vera.codegen — Closures.

Covers anonymous functions, captures, apply_fn, function tables,
and call_indirect compilation.
"""

from __future__ import annotations

import os
import re
from unittest import mock

import pytest
import wasmtime

from vera.codegen import (
    CompileResult,
    compile,
    execute,
)
from vera.parser import parse_file
from vera.transform import transform

from tests.codegen_helpers import _assert_no_orphan_call_indirect


# =====================================================================
# Helpers
# =====================================================================


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    # Write to a temp source and parse
    import tempfile

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name

    tree = parse_file(path)
    ast = transform(tree)
    result = compile(ast, source=source, file=path)
    # #1185: this module owns a local `_compile`, so it does not inherit
    # the gate in `tests/codegen_helpers.py` — and it is the module with
    # the densest closure / `call_indirect` coverage, where an orphaned
    # indirect call is likeliest to be introduced.
    _assert_no_orphan_call_indirect(result.wat)
    return result


def _compile_ok(source: str) -> CompileResult:
    """Compile and assert no errors."""
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected errors: {errors}"
    return result


def _run(source: str, fn: str | None = None, args: list[int] | None = None) -> int:
    """Compile, execute, and return the integer result."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _run_float(
    source: str, fn: str | None = None, args: list[int | float] | None = None
) -> float:
    """Compile, execute, and return the float result."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None, "Expected a return value"
    assert isinstance(exec_result.value, float), (
        f"Expected float, got {type(exec_result.value).__name__}"
    )
    return exec_result.value


def _run_io(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> str:
    """Compile, execute, and return captured stdout."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    return exec_result.stdout


def _run_trap(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> None:
    """Compile, execute, and assert a WASM trap."""
    result = _compile_ok(source)
    with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
        execute(result, fn_name=fn, args=args)


def _has_gc_shadow_push(wat_body: str) -> bool:
    """Detect the canonical ``gc_shadow_push`` SP-increment sequence in
    a WAT body.

    A bare ``global.set $gc_sp`` could in principle be a stack-restore
    rather than a push — though only inside an allocating body, since
    the prologue's ``$gc_sp_save`` save/restore is gated on
    ``ctx.needs_alloc``.  This helper looks for the unique trailing
    ``i32.const 4 / i32.add / global.set $gc_sp`` pattern that
    ``vera/wasm/helpers.py::gc_shadow_push`` emits to advance the
    shadow-stack pointer after writing the rooted value — distinct
    from a restore (``local.get $gc_sp_save / global.set $gc_sp``).
    Used by the structural #593 regression tests so a non-push
    artefact in the body can never satisfy the assertion.
    """
    return bool(re.search(
        r"i32\.const 4\s+i32\.add\s+global\.set \$gc_sp",
        wat_body,
    ))


# =====================================================================
# C6h: Closures
# =====================================================================


class TestClosures:
    """Tests for closure compilation -- anonymous functions, captures,
    apply_fn, function tables, and call_indirect."""

    def test_closure_no_capture(self) -> None:
        """An anonymous function with no free variables compiles and runs."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn make_fn(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_fn(());
  apply_fn(@IntToInt.0, 7)
}
"""
        assert _run(src, "test") == 14

    def test_closure_with_capture(self) -> None:
        """An anonymous function that captures an outer binding."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn make_adder(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_adder(10);
  apply_fn(@IntToInt.0, 5)
}
"""
        assert _run(src, "test") == 15

    def test_apply_fn_basic(self) -> None:
        """apply_fn invokes a closure with the correct argument."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn make_doubler(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_doubler(());
  apply_fn(@IntToInt.0, 21)
}
"""
        assert _run(src, "test") == 42

    def test_apply_fn_with_capture(self) -> None:
        """apply_fn on a capturing closure produces the correct result."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn make_multiplier(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 * @Int.1 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_multiplier(3);
  apply_fn(@IntToInt.0, 7)
}
"""
        assert _run(src, "test") == 21

    def test_closure_in_let(self) -> None:
        """Store a closure in a let binding, then use it."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn make_fn(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_fn(100);
  let @Int = apply_fn(@IntToInt.0, 23);
  @Int.0
}
"""
        assert _run(src, "test") == 123

    def test_closure_as_param(self) -> None:
        """Pass a closure as a function parameter."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn apply(@IntToInt, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@IntToInt.0, @Int.0)
}
public fn make_fn(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_fn(50);
  apply(@IntToInt.0, 50)
}
"""
        assert _run(src, "test") == 100

    def test_closure_in_match(self) -> None:
        """Use a closure inside a match arm with an ADT constructor."""
        src = """\
private data Option<T> { None, Some(T) }
type IntMapper = fn(Int -> Int) effects(pure);
public fn option_map(@Option<Int>, @IntMapper -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> None,
    Some(@Int) -> Some(apply_fn(@IntMapper.0, @Int.0))
  }
}
public fn make_adder(@Int -> @IntMapper)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntMapper = make_adder(100);
  let @Option<Int> = option_map(Some(5), @IntMapper.0);
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(src, "test") == 105

    def test_closure_in_match_none(self) -> None:
        """option_map on None returns None."""
        src = """\
private data Option<T> { None, Some(T) }
type IntMapper = fn(Int -> Int) effects(pure);
public fn option_map(@Option<Int>, @IntMapper -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> None,
    Some(@Int) -> Some(apply_fn(@IntMapper.0, @Int.0))
  }
}
public fn make_adder(@Int -> @IntMapper)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntMapper = make_adder(100);
  let @Option<Int> = option_map(None, @IntMapper.0);
  match @Option<Int>.0 {
    None -> -1,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(src, "test") == -1

    def test_fn_type_param_compiles(self) -> None:
        """A function with a function-type parameter is not skipped.

        #1185 added the closure the fixture was missing.  `apply_fn`
        lowers to `call_indirect`, which dispatches on the module's
        function table — and that table is emitted only when a closure
        lift commits.  With no closure anywhere the module declared
        neither a table nor a memory, so the export this pins could never
        be instantiated: `execute` raised a raw wasmtime error.  The
        fixture now contains one, which pins the property the test is
        named for (a `@IntToInt` parameter does not itself cause a skip)
        against output that actually loads and runs — 99 passes through
        the identity closure, a value no fallback produces.  The
        no-closure-anywhere shape is now a located drop, pinned in
        `tests/test_codegen_orphan_call_indirect_1185.py`.
        """
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn apply(@IntToInt, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@IntToInt.0, @Int.0)
}
public fn make_fn(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_fn(());
  apply(@IntToInt.0, 99)
}
"""
        result = _compile_ok(src)
        assert "apply" in result.exports
        assert execute(result, fn_name="test").value == 99

    def test_table_in_wat(self) -> None:
        """WAT output includes a funcref table when closures are used."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn make_fn(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 }
}
"""
        result = _compile_ok(src)
        assert result.wat is not None
        assert "funcref" in result.wat
        assert "(table" in result.wat
        assert "(elem" in result.wat

    def test_call_indirect_in_wat(self) -> None:
        """WAT output contains call_indirect for apply_fn."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn apply(@IntToInt, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@IntToInt.0, @Int.0)
}
public fn make_fn(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_fn(());
  apply(@IntToInt.0, 99)
}
"""
        result = _compile_ok(src)
        assert result.wat is not None
        assert "call_indirect" in result.wat

    def test_type_sig_in_wat(self) -> None:
        """WAT output contains a closure type signature declaration."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn make_fn(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 }
}
"""
        result = _compile_ok(src)
        assert result.wat is not None
        assert "$closure_sig_" in result.wat
        assert "(type" in result.wat

    def test_closures_example_compiles(self) -> None:
        """examples/closures.vera compiles without errors."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "closures.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile(source)
        assert result.ok

    def test_closures_example_test_closure(self) -> None:
        """examples/closures.vera test_closure returns 15."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "closures.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_closure")
        assert exec_result.value == 15

    def test_closures_example_test_option_map(self) -> None:
        """examples/closures.vera test_option_map returns 105."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "closures.vera"
        source = path.read_text(encoding="utf-8")
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_option_map")
        assert exec_result.value == 105

    def test_multiple_closures(self) -> None:
        """Multiple closures get distinct table entries."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn make_adder(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_adder(10);
  let @Int = apply_fn(@IntToInt.0, 5);
  let @IntToInt = make_adder(20);
  let @Int = apply_fn(@IntToInt.0, 3);
  @Int.0 + @Int.1
}
"""
        assert _run(src, "test") == 38  # 15 + 23

    def test_closure_captures_correct_value(self) -> None:
        """Each closure captures the value at its creation point."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn make_adder(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_adder(1);
  let @Int = apply_fn(@IntToInt.0, 0);
  let @IntToInt = make_adder(100);
  let @Int = apply_fn(@IntToInt.0, 0);
  @Int.0 + @Int.1
}
"""
        assert _run(src, "test") == 101  # 1 + 100


# =====================================================================
# #1044: Future<T> is representation-transparent (#841), so a closure
# that CAPTURES a `Future<T>` free variable must serialise it with the
# same width as its payload T.  Pre-fix the capture-width decision in
# `_walk_free_vars` matched only the literal names "String" / "Array"
# and routed everything else through `_type_name_to_wasm` (which maps
# unknowns to "i32").  A captured `Future<String>` (i32_pair) was thus
# stored as ONE i32 (ptr only) — the len read back as adjacent zero, so
# the body silently saw an empty string; a captured `Future<Int>` (i64)
# pushed an i64 into an `i32.store`, trapping at WASM validation
# ("expected i32, found i64").  The fix routes the decision through the
# Future-transparent `_is_pair_type_name` + `_slot_name_to_wasm_type`.
# =====================================================================

class TestFutureCapture1044:
    """Closure capture of a `Future<T>` free variable (#1044)."""

    def test_closure_captures_future_string_value_roundtrip(self) -> None:
        """A captured `Future<String>` round-trips its (ptr, len) pair.

        RED before the fix: the capture stored only the ptr as one i32,
        so `string_length` read len from adjacent (zero) memory and the
        closure returned 0 instead of 5.
        """
        src = """\
type StrThunk = fn(Unit -> Int) effects(<Async>);

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<String> = async("hello");
  let @StrThunk = fn(@Unit -> @Int) effects(<Async>) {
    string_length(await(@Future<String>.0))
  };
  apply_fn(@StrThunk.0, ())
}
"""
        assert _run(src, "f") == 5

    def test_closure_captures_future_int_scalar(self) -> None:
        """A captured `Future<Int>` (i64) is serialised at i64 width.

        RED before the fix: the capture used the i32 default, so the i64
        value pushed into an `i32.store` trapped at WASM validation
        ("expected i32, found i64").
        """
        src = """\
type IntThunk = fn(Unit -> Int) effects(<Async>);

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(41);
  let @IntThunk = fn(@Unit -> @Int) effects(<Async>) {
    await(@Future<Int>.0)
  };
  apply_fn(@IntThunk.0, ())
}
"""
        assert _run(src, "f") == 41

    def test_closure_captures_plain_string_control(self) -> None:
        """Control: a plain `String` capture already worked and must stay
        green — pins that the #1044 fix does not regress the non-Future
        pair-capture path (#535)."""
        src = """\
type StrThunk = fn(Unit -> Int) effects(<Async>);

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @String = "hello";
  let @StrThunk = fn(@Unit -> @Int) effects(<Async>) {
    string_length(@String.0)
  };
  apply_fn(@StrThunk.0, ())
}
"""
        assert _run(src, "f") == 5


# =====================================================================
# Coverage: closures.py — additional closure compilation paths
# =====================================================================

class TestClosureCoveragePaths:
    """Cover missed lines in vera/codegen/closures.py."""

    def test_closure_bool_param_not_gc_tracked(self) -> None:
        """Closure with Bool param: not tracked as GC pointer (line 124-125)."""
        src = """\
type BoolFn = fn(Bool -> Int) effects(pure);

public fn make_fn(@Int -> @BoolFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Bool -> @Int) effects(pure) {
    if @Bool.0 then { @Int.0 } else { 0 }
  }
}

public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @BoolFn = make_fn(42);
  apply_fn(@BoolFn.0, true)
}
"""
        assert _run(src, "test") == 42

    def test_closure_with_adt_capture_gc(self) -> None:
        """Closure capturing ADT value exercises GC pointer tracking
        for captured i32 locals that are not Bool/Byte (line 190-191)."""
        src = """\
private data Option<T> { None, Some(T) }
type IntFn = fn(Int -> Int) effects(pure);

public fn make_fn(@Option<Int> -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) {
    match @Option<Int>.0 {
      None -> @Int.0,
      Some(@Int) -> @Int.0 + @Int.1
    }
  }
}

public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_fn(Some(10));
  apply_fn(@IntFn.0, 5)
}
"""
        assert _run(src, "test") == 15


# =====================================================================
# Nested closures (#514) — closures inside other closure bodies.
#
# Pre-fix bug: ``_compile_lifted_closure`` created a fresh
# ``WasmContext`` to translate the body, and any inner ``fn { ... }``
# discovered during that translation registered on the inner ctx's
# ``_pending_closures`` list — never bubbled back to the outer lifting
# loop. Result: only the outermost closure was lifted, the inner's
# ``$anon_N`` function was missing from the table, and the call_indirect
# either trapped (``unreachable``) at runtime or failed WASM validation
# (``i64 vs i32 type mismatch``) depending on the inner's return type.
#
# Fix: ``_lift_pending_closures`` is now a worklist that bubbles inner
# pending closures up after each lifting iteration.
# =====================================================================


class TestNestedClosures:
    """Tests pinning the #514 fix: closures inside closure bodies."""

    def test_nested_closure_inner_returns_int(self) -> None:
        """The simplest failing case: 2D ``array_map`` with primitive
        return types and no captures across the nesting boundary.
        Pre-fix: trapped with ``unreachable`` at runtime.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      array_length(array_map(
        array_range(0, 3),
        fn(@Int -> @Int) effects(pure) { @Int.0 }
      ))
    }
  );
  nat_to_int(array_length(@Array<Int>.0))
}
"""
        # Outer array_map produces an Array<Int> of length 3.
        assert _run(src, "test") == 3

    def test_nested_closure_inner_returns_array(self) -> None:
        """The headline #514 reproducer: outer ``array_map`` whose
        closure returns ``Array<Int>`` (built by an inner ``array_map``).

        Pre-fix: failed WASM validation with
        ``type mismatch: expected i64, found i32`` at the inner
        call_indirect site.

        Sums every cell to verify the inner ``Array<Int>`` payload
        actually contains the doubled values, not garbage. Each row is
        ``[0, 2, 4]``; three rows gives ``3 * (0 + 2 + 4) = 18``.  A
        length-only check would pass even if the inner closure returned
        a malformed Array (wrong elements, wrong length, or zeros from a
        broken pair-write); the sum forces the inner values through.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Int>> = array_map(
    array_range(0, 3),
    fn(@Int -> @Array<Int>) effects(pure) {
      array_map(
        array_range(0, 3),
        fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }
      )
    }
  );
  array_fold(
    @Array<Array<Int>>.0,
    0,
    fn(@Int, @Array<Int> -> @Int) effects(pure) {
      @Int.0 + array_fold(
        @Array<Int>.0,
        0,
        fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
      )
    }
  )
}
"""
        assert _run(src, "test") == 18

    def test_nested_closure_with_outer_param_capture(self) -> None:
        """The 'with capture' variant from the issue body — the inner
        closure references its outer's parameter via ``@Int.1``.

        Pre-fix: same WASM validation failure (offset 1536 vs 1529 in
        the issue text). The capture analysis itself worked for the
        outer; the missing-lift kept the inner from being emitted at all,
        so the capture had nowhere to land.

        Sums every cell in the resulting 3×3 grid so the assertion
        actually depends on the captured ``@Int.1`` (the outer row
        index) flowing into the inner closure body.  Cells:
            row 0: [0+0, 1+0, 2+0] = [0, 1, 2]      sum 3
            row 1: [0+1, 1+1, 2+1] = [1, 2, 3]      sum 6
            row 2: [0+2, 1+2, 2+2] = [2, 3, 4]      sum 9
        Total: 18.  A length-only check (== 3) would pass even if the
        capture silently returned 0 inside the inner closure, so we
        force the value through into the result here.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Int>> = array_map(
    array_range(0, 3),
    fn(@Int -> @Array<Int>) effects(pure) {
      array_map(
        array_range(0, 3),
        fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
      )
    }
  );
  array_fold(
    @Array<Array<Int>>.0,
    0,
    fn(@Int, @Array<Int> -> @Int) effects(pure) {
      @Int.0 + array_fold(
        @Array<Int>.0,
        0,
        fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
      )
    }
  )
}
"""
        assert _run(src, "test") == 18

    def test_three_level_nesting(self) -> None:
        """Paranoia: the worklist-based lifter must handle arbitrary
        depth, not just two levels. Three nested ``array_map`` calls.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Array<Int>>> = array_map(
    array_range(0, 2),
    fn(@Int -> @Array<Array<Int>>) effects(pure) {
      array_map(
        array_range(0, 2),
        fn(@Int -> @Array<Int>) effects(pure) {
          array_map(
            array_range(0, 2),
            fn(@Int -> @Int) effects(pure) { @Int.0 }
          )
        }
      )
    }
  );
  nat_to_int(array_length(@Array<Array<Array<Int>>>.0))
}
"""
        assert _run(src, "test") == 2

    def test_nested_closure_emits_anon_for_inner(self) -> None:
        """White-box: the emitted WAT must contain a lifted function
        for the inner closure too. Pre-fix this would have only
        ``$anon_0`` and the table would be size 1.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Int>> = array_map(
    array_range(0, 3),
    fn(@Int -> @Array<Int>) effects(pure) {
      array_map(
        array_range(0, 3),
        fn(@Int -> @Int) effects(pure) { @Int.0 }
      )
    }
  );
  nat_to_int(array_length(@Array<Array<Int>>.0))
}
"""
        import re
        result = _compile_ok(src)
        wat = result.wat
        # Both closures must have lifted functions.  Count distinct
        # ``$anon_N`` lifted-function definitions rather than asserting
        # specific names — the worklist's allocation order is an
        # implementation detail that may change as the lifting pass
        # evolves.  Two outermost closures in this fixture, so >= 2.
        anon_funcs = re.findall(r"\(func \$anon_\d+", wat)
        assert len(anon_funcs) >= 2, (
            f"Expected >= 2 lifted closure functions in WAT, got "
            f"{len(anon_funcs)} ({anon_funcs}) — #514 worklist regression"
        )
        # Function table must have at least 2 entries.
        # The exact form is `(table N funcref)` — extract N.
        m = re.search(r"\(table\s+(\d+)\s+funcref\)", wat)
        assert m is not None, f"No funcref table in WAT: {wat[:500]}"
        table_size = int(m.group(1))
        assert table_size >= 2, (
            f"Function table too small ({table_size}) for nested closures; "
            "inner closure was not lifted"
        )

    def test_two_top_level_fns_with_nested_closures(self) -> None:
        """Cross-function shared-state regression for the #514 worklist.

        Two separate top-level functions, each with one outer closure
        containing one inner closure: 4 lifted closures total.
        ``_compile_lifted_closure`` shares the module-level
        ``_closure_sigs`` and ``_next_closure_id`` by reference; a
        regression that re-initialised either of those between
        top-level functions would surface as an ID collision (two
        ``$anon_0`` definitions, rejected by the WAT parser as
        duplicate function identifiers) or a sig collision (two
        ``$closure_sig_0`` for different contents, same rejection).

        ``test_nested_closure_emits_anon_for_inner`` above only
        exercises one top-level function and so doesn't catch this
        class of bug — it would still pass even if the module-level
        state were function-scoped instead of shared.
        """
        src = """\
public fn first(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Int>> = array_map(
    array_range(0, 2),
    fn(@Int -> @Array<Int>) effects(pure) {
      array_map(
        array_range(0, 2),
        fn(@Int -> @Int) effects(pure) { @Int.0 }
      )
    }
  );
  nat_to_int(array_length(@Array<Array<Int>>.0))
}

public fn second(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Int>> = array_map(
    array_range(0, 3),
    fn(@Int -> @Array<Int>) effects(pure) {
      array_map(
        array_range(0, 3),
        fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }
      )
    }
  );
  nat_to_int(array_length(@Array<Array<Int>>.0))
}
"""
        import re
        result = _compile_ok(src)
        wat = result.wat
        # Four lifted functions total — one outer + one inner per
        # top-level function.  Names must all be distinct (no
        # ID-counter reset across top-level functions).
        anon_funcs = re.findall(r"\(func \$anon_\d+", wat)
        assert len(anon_funcs) >= 4, (
            f"Expected >= 4 lifted closures across two top-level fns, "
            f"got {len(anon_funcs)} ({anon_funcs}) — #514 cross-fn "
            "shared-state regression"
        )
        assert len(set(anon_funcs)) == len(anon_funcs), (
            f"Duplicate $anon_N identifiers in WAT — closure-ID counter "
            f"was reset between top-level functions: {anon_funcs}"
        )
        # All four must be in the function table so they're invokable.
        m = re.search(r"\(table\s+(\d+)\s+funcref\)", wat)
        assert m is not None, f"No funcref table in WAT: {wat[:500]}"
        table_size = int(m.group(1))
        assert table_size >= 4, (
            f"Function table too small ({table_size}) for 4 lifted "
            "closures — some lifted functions weren't registered for "
            "call_indirect dispatch"
        )
        # End-to-end: both functions actually run.  The cross-fn shared-
        # state bug we're guarding against would surface here as a
        # WASM validation failure when the module is instantiated.
        assert _run(src, "first") == 2
        assert _run(src, "second") == 3


# =====================================================================
# #570: iterative-builder shadow-stack leak regressions
# =====================================================================
# The lifted closure's epilogue restores its entry ``$gc_sp`` and then,
# when the return type is a heap pointer (Vera ADT, String, Array), pushes
# the return value as a fresh root so generic callers stay sound across a
# stash-then-GC pattern.  The iterative array builders consume the return
# synchronously (store into rooted dst[idx], or in-place overwrite a rooted
# slot), so the per-call root is redundant — and at scale, accumulating
# leaked slots overflows the 16 KiB / 4 096-entry shadow stack.
#
# The fix is a per-callsite unwind in each builder.  These tests assert
# the unwind: each runs the builder at a size large enough that one
# leaked slot per call WOULD overflow, and checks the result.
# =====================================================================


class TestIterativeBuilderShadowStack:
    """Shadow-stack regressions for #570 across array builders that take
    a heap-pointer-returning closure: ``array_map``, ``array_mapi``,
    ``array_fold``, and ``array_sort_by``.  Counterpart predicates
    (``array_filter`` / ``_find`` / ``_any`` / ``_all``) return Bool —
    excluded from the closure epilogue's post-restore root push, so they
    don't leak and don't need their own regression here.
    """

    def test_array_map_5000_adt_no_overflow(self) -> None:
        """``array_map`` over 5 000 elements with an ADT-returning closure.

        Pre-fix: trapped at the shadow-stack overflow check inside
        ``gc_shadow_push`` (~iteration 4 000).  Post-fix: completes and
        returns the expected sum.  Sum 0..4999 = 12 497 500.
        """
        src = """\
private data Box { MkBox(Int) }

public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Box> = array_map(
    array_range(0, 5000),
    fn(@Int -> @Box) effects(pure) { MkBox(@Int.0) }
  );
  array_fold(
    @Array<Box>.0,
    0,
    fn(@Int, @Box -> @Int) effects(pure) {
      @Int.0 + match @Box.0 { MkBox(@Int) -> @Int.0 }
    }
  )
}
"""
        assert _run(src, "test") == 12497500

    def test_array_mapi_5000_adt_no_overflow(self) -> None:
        """``array_mapi`` over 5 000 elements with an ADT-returning closure.

        Same shape as ``array_map`` but the closure additionally takes a
        Nat index.  The index doesn't change the closure's return-root
        push (still triggered by ``ret_is_pointer``), so the same per-
        callsite unwind is required.

        Boxed values are ``2 * i`` (elem index plus elem-as-int), so the
        sum is ``sum(2*i for i in 0..4999) = 24 995 000``.
        """
        src = """\
private data Box { MkBox(Int) }

public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Box> = array_mapi(
    array_range(0, 5000),
    fn(@Int, @Nat -> @Box) effects(pure) {
      MkBox(@Int.0 + nat_to_int(@Nat.0))
    }
  );
  array_fold(
    @Array<Box>.0,
    0,
    fn(@Int, @Box -> @Int) effects(pure) {
      @Int.0 + match @Box.0 { MkBox(@Int) -> @Int.0 }
    }
  )
}
"""
        assert _run(src, "test") == 24995000

    def test_array_fold_5000_adt_accumulator_no_overflow(self) -> None:
        """``array_fold`` with a heap-pointer accumulator across 5 000
        elements.

        ``array_fold`` is a special case of the same bug class with an
        additional symptom: the existing ``gc_sp - 8`` overwrite math
        assumed the closure pushed exactly zero post-call slots.  With
        the closure leaking one slot per iteration, that offset drifts
        and addresses the leaked-slot-from-the-previous-call instead of
        the accumulator's pre-call slot.  The fix pops the leak before
        computing the offset.

        Sum 0..4999 = 12 497 500.
        """
        src = """\
private data Box { MkBox(Int) }

public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box = array_fold(
    array_range(0, 5000),
    MkBox(0),
    fn(@Box, @Int -> @Box) effects(pure) {
      MkBox(match @Box.0 { MkBox(@Int) -> @Int.0 } + @Int.0)
    }
  );
  match @Box.0 { MkBox(@Int) -> @Int.0 }
}
"""
        assert _run(src, "test") == 12497500

    def test_array_sort_by_200_reverse_no_overflow(self) -> None:
        """``array_sort_by`` with a 200-element reverse-sorted input.

        The comparator returns ``Ordering`` (a heap-allocated ADT), so
        the closure epilogue post-pushes a root for each comparator
        call.  Insertion sort issues up to ``n*(n-1)/2`` comparisons —
        ~19 900 for n=200, well past the 4 096-entry shadow-stack
        capacity.  Pre-fix: trapped at ``gc_shadow_push`` overflow.
        Post-fix: returns the array length (200) after sorting.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map(
    array_range(0, 200),
    fn(@Int -> @Int) effects(pure) { 200 - @Int.0 }
  );
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) {
      if @Int.1 < @Int.0 then { Less } else {
        if @Int.1 > @Int.0 then { Greater } else { Equal }
      }
    }
  );
  nat_to_int(array_length(@Array<Int>.0))
}
"""
        assert _run(src, "test") == 200


# =====================================================================
# #593: Non-allocating closure return-value root must be pushed
# =====================================================================


class TestClosureReturnShadowPushBalance:
    """Regression tests for #593.

    The bug: ``_translate_array_map`` / ``_translate_array_mapi`` always
    emit ``global.get $gc_sp; i32.const 4; i32.sub; global.set $gc_sp``
    after each ``call_indirect`` when the element type is heap-pointer-
    like (the ``b_needs_unwind`` flag).  That pop assumes the closure's
    epilogue pushed a return-value root.

    Pre-fix: ``_compile_lifted_closure`` only emitted that push when
    ``ctx.needs_alloc=True``.  A closure body like ``render_cell(@Bool.0)``
    that returns a String literal (data segment, no heap alloc) had
    ``needs_alloc=False`` and thus emitted no push — so the array_map
    pop went BELOW the surrounding function's prologue baseline,
    corrupting earlier shadow-stack roots.  Manifested as silent string
    corruption (Conway's Life rendering — the original #593 symptom) or
    as ``call_indirect`` "out of bounds table access" trap (rebuilt
    repro at smaller scale).

    Post-fix: the return-value push is emitted whenever the return type
    is a heap pointer, regardless of ``needs_alloc``.  Tests cover both
    fix branches (i32_pair = String/Array, i32 = ADT) at four layers:
    positive fast-path regression, behavioural under eager-GC,
    end-to-end Life-shape rendering, and a structural WAT assertion
    that the push is actually emitted for non-allocating bodies.  An
    eager-GC injection self-test pins the diagnostic mechanism so a
    silent regression there can't quietly disable the eager-GC tests.
    """

    def test_non_allocating_closure_returns_string_via_array_map(
        self,
    ) -> None:
        """Positive regression for the fast path (no eager-GC): the
        i32_pair-returning closure produces the expected joined output.
        Pre-fix usually passed at small scale by coincidence; kept here
        to ensure the fix didn't break the common case."""
        src = """\
private fn pick(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { "X" } else { "." }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Bool> = array_map(array_range(0, 8), fn(@Int -> @Bool) effects(pure) { @Int.0 == 3 });
  IO.print(string_join(array_map(@Array<Bool>.0, fn(@Bool -> @String) effects(pure) { pick(@Bool.0) }), ""))
}
"""
        assert _run_io(src) == "...X...."

    def test_eager_gc_array_map_with_non_allocating_string_closure(
        self,
    ) -> None:
        """Eager-GC variant of the previous test: pins the rooting
        balance directly.  Pre-fix, eager-GC's mark phase missed the
        over-popped roots and swept their referents — surfaced as a
        ``call_indirect`` table OOB trap or NULL/U+FFFD bytes in place
        of String content.  Post-fix, eager and non-eager outputs match.
        """
        src = """\
private fn pick(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { "X" } else { "." }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Bool> = array_map(array_range(0, 8), fn(@Int -> @Bool) effects(pure) { @Int.0 == 3 });
  IO.print(string_join(array_map(@Array<Bool>.0, fn(@Bool -> @String) effects(pure) { pick(@Bool.0) }), ""))
}
"""
        with mock.patch.dict(os.environ, {"VERA_EAGER_GC": "1"}):
            result = _compile_ok(src)
        exec_result = execute(result)
        assert exec_result.stdout == "...X...."

    def test_eager_gc_array_mapi_with_non_allocating_string_closure(
        self,
    ) -> None:
        """``array_mapi`` parallel of the array_map String eager-GC
        test.  ``_translate_array_mapi`` has its own ``b_needs_unwind``
        emission; this test pins the String (i32_pair) edge of that
        path under eager-GC, complementing the ADT-shape variant
        below.  Pre-fix: same imbalance and corruption as array_map.
        """
        src = """\
private fn pick(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { "X" } else { "." }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Bool> = array_map(array_range(0, 8), fn(@Int -> @Bool) effects(pure) { @Int.0 == 3 });
  IO.print(string_join(array_mapi(@Array<Bool>.0, fn(@Bool, @Nat -> @String) effects(pure) { pick(@Bool.0) }), ""))
}
"""
        with mock.patch.dict(os.environ, {"VERA_EAGER_GC": "1"}):
            result = _compile_ok(src)
        exec_result = execute(result)
        assert exec_result.stdout == "...X...."

    def test_eager_gc_recursive_render_no_corruption(self) -> None:
        """End-to-end Life-shape under eager-GC: recursive ``run_loop``
        calling ``render_grid`` with nested ``array_map`` of
        non-allocating closures returning Strings.  This is the minimum
        shape that reproduced #593's silent string corruption.  Five
        iterations are enough for the imbalance to land on a corrupted
        slot under eager-GC; the explicit NULL / U+FFFD assertions pin
        the canonical corruption signatures from the issue.
        """
        src = """\
private fn render_cell(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { "X" } else { "." }
}

private fn render_grid(@Array<Array<Bool>> -> @String)
  requires(true) ensures(true) effects(pure)
{
  string_join(array_map(@Array<Array<Bool>>.0, fn(@Array<Bool> -> @String) effects(pure) {
    string_join(array_map(@Array<Bool>.0, fn(@Bool -> @String) effects(pure) {
      render_cell(@Bool.0)
    }), "")
  }), "\\n")
}

private fn step(@Array<Array<Bool>> -> @Array<Array<Bool>>)
  requires(true) ensures(true) effects(pure)
{
  array_mapi(@Array<Array<Bool>>.0, fn(@Array<Bool>, @Nat -> @Array<Bool>) effects(pure) {
    array_mapi(@Array<Bool>.0, fn(@Bool, @Nat -> @Bool) effects(pure) {
      @Bool.0
    })
  })
}

private fn run_loop(@Array<Array<Bool>>, @Int -> @Unit)
  requires(true) ensures(true) decreases(@Int.0) effects(<IO>)
{
  if @Int.0 <= 0 then {
    ()
  } else {
    IO.print(render_grid(@Array<Array<Bool>>.0));
    IO.print("\\n");
    run_loop(step(@Array<Array<Bool>>.0), @Int.0 - 1)
  }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Array<Bool>> = array_map(array_range(0, 3), fn(@Int -> @Array<Bool>) effects(pure) {
    array_map(array_range(0, 4), fn(@Int -> @Bool) effects(pure) { @Int.0 == 1 })
  });
  run_loop(@Array<Array<Bool>>.0, 5)
}
"""
        with mock.patch.dict(os.environ, {"VERA_EAGER_GC": "1"}):
            result = _compile_ok(src)
        exec_result = execute(result)
        # Each frame is 3 rows of ".X..", separated by \n, then a
        # trailing IO.print("\n") after each render_grid.  5 iterations.
        expected_frame = ".X..\n.X..\n.X..\n"
        assert exec_result.stdout == expected_frame * 5
        # Specifically: no NULL or U+FFFD bytes (the canonical
        # corruption signatures from #593).
        assert "\x00" not in exec_result.stdout
        assert "�" not in exec_result.stdout

    def test_lifted_closure_emits_return_root_push_when_body_is_non_allocating(
        self,
    ) -> None:
        """Structural assertion: a lifted closure whose body is
        non-allocating but whose return type is a heap pointer must
        contain a return-value ``gc_shadow_push`` in its epilogue.

        Without it, the ``b_needs_unwind`` pop in ``_translate_array_map``
        / ``_translate_array_mapi`` is unbalanced.  Detecting the push
        at the WAT level prevents regression even if a runtime test
        happens to produce correct output by coincidence at small scale.
        """
        src = """\
private fn pick(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { "X" } else { "." }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = array_map(array_range(0, 3), fn(@Int -> @String) effects(pure) { pick(@Int.0 == 1) });
  IO.print(string_join(@Array<String>.0, ""))
}
"""
        result = _compile_ok(src)
        wat = result.wat
        # Find any ``$anon_X`` returning ``(result i32 i32)`` whose body
        # has no ``call $alloc`` but contains the canonical
        # ``gc_shadow_push`` increment sequence — i.e. a non-allocating
        # closure that still pushes a return-value root.  The fix for
        # #593 requires this for every i32-pair-returning lifted
        # closure regardless of body allocations.
        pattern = re.compile(
            r"\(func \$anon_\d+ \(param \$env i32\)[^)]*\) "
            r"\(result i32 i32\)(.*?)\n  \)",
            re.DOTALL,
        )
        candidate_bodies = [m.group(1) for m in pattern.finditer(wat)]
        assert candidate_bodies, (
            "Expected at least one $anon_X with i32-pair return in WAT"
        )
        non_alloc_with_push = [
            body for body in candidate_bodies
            if _has_gc_shadow_push(body)
            and "call $alloc" not in body
        ]
        assert non_alloc_with_push, (
            "No non-allocating i32-pair-returning closure with a "
            "shadow-push return-root was found.  The fix for #593 "
            "requires the closure's epilogue to push the return-value "
            "root regardless of needs_alloc."
        )

    def test_lifted_closure_emits_return_root_push_for_non_allocating_adt_return(
        self,
    ) -> None:
        """Structural assertion for the second branch of the #593 fix.

        ``_compile_lifted_closure`` has two heap-pointer-return branches:
        ``i32_pair`` (String / Array<T>, covered by the previous test)
        and ``i32`` ADT (Option, Result, custom data — covered here).
        The previous test's regex matched only ``(result i32 i32)``;
        the ADT branch returns ``(result i32)``.  A non-allocating
        closure that just forwards an existing ADT pointer (identity
        over a captured ADT) hits the i32 branch.

        Pre-fix: the i32 ADT non-allocating branch emitted no push, so
        ``array_map(arr, identity_closure)`` over an ADT array
        over-popped one shadow-stack slot per iteration.  Post-fix the
        push is unconditional for heap-pointer returns, so this branch
        is balanced too.
        """
        src = """\
private data Box { MkBox(Int) }

public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Box> = array_map(
    array_range(0, 5),
    fn(@Int -> @Box) effects(pure) { MkBox(@Int.0) }
  );
  let @Array<Box> = array_map(
    @Array<Box>.0,
    fn(@Box -> @Box) effects(pure) { @Box.0 }
  );
  array_fold(@Array<Box>.0, 0, fn(@Int, @Box -> @Int) effects(pure) {
    @Int.0 + match @Box.0 { MkBox(@Int) -> @Int.0 }
  })
}
"""
        result = _compile_ok(src)
        wat = result.wat
        # Find any ``$anon_X`` returning ``(result i32)`` (i.e. an ADT
        # or non-pair pointer) whose body has no ``call $alloc`` but
        # contains the canonical ``gc_shadow_push`` increment sequence
        # — the i32 ADT identity-style closure.  At least the
        # ``fn(@Box -> @Box) { @Box.0 }`` lift must match.
        pattern = re.compile(
            r"\(func \$anon_\d+ \(param \$env i32\)[^)]*\) "
            r"\(result i32\)(?!\s*\(result)(.*?)\n  \)",
            re.DOTALL,
        )
        candidate_bodies = [m.group(1) for m in pattern.finditer(wat)]
        assert candidate_bodies, (
            "Expected at least one $anon_X with i32 (single, non-pair) "
            "return in WAT"
        )
        non_alloc_with_push = [
            body for body in candidate_bodies
            if _has_gc_shadow_push(body)
            and "call $alloc" not in body
        ]
        assert non_alloc_with_push, (
            "No non-allocating i32-ADT-returning closure with a "
            "shadow-push return-root was found.  The i32 ADT branch "
            "of the #593 fix is missing or regressed."
        )
        # Additionally: the existing i32-pair test checks the pair
        # branch.  Both branches together cover the heap-pointer
        # surface of _compile_lifted_closure's epilogue.

    def test_array_mapi_non_allocating_closure_emits_balanced_push(
        self,
    ) -> None:
        """Pin ``_translate_array_mapi``'s pop site independently of
        ``_translate_array_map``'s.

        ``array_mapi`` has its own ``b_needs_unwind`` pop emission, with
        the same shape as ``array_map``'s but at a separate code path.
        If a future refactor factored one but not both, the array_map
        test would still pass while array_mapi quietly regressed.  This
        test pins the array_mapi path by exercising it with a
        non-allocating, heap-pointer-returning closure.
        """
        src = """\
private data Box { MkBox(Int) }

public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Box> = array_map(
    array_range(0, 5),
    fn(@Int -> @Box) effects(pure) { MkBox(@Int.0) }
  );
  -- array_mapi closure: non-allocating, ADT return (just forwards the
  -- input box).  Pre-#593-fix this would over-pop one slot per element
  -- without a matching push; post-fix the closure's epilogue pushes
  -- the return-value root.
  let @Array<Box> = array_mapi(
    @Array<Box>.0,
    fn(@Box, @Nat -> @Box) effects(pure) { @Box.0 }
  );
  array_fold(@Array<Box>.0, 0, fn(@Int, @Box -> @Int) effects(pure) {
    @Int.0 + match @Box.0 { MkBox(@Int) -> @Int.0 }
  })
}
"""
        # Behavioural check first — the program must produce 0+1+2+3+4=10.
        assert _run(src, "test") == 10
        # And under eager-GC: the imbalance would land on the very first
        # iteration if the array_mapi path regressed.
        with mock.patch.dict(os.environ, {"VERA_EAGER_GC": "1"}):
            result = _compile_ok(src)
        exec_result = execute(result, fn_name="test")
        assert exec_result.value == 10

    def test_vera_eager_gc_injects_gc_collect_into_alloc_body(
        self,
    ) -> None:
        """Pin the eager-GC diagnostic mechanism itself.

        ``VERA_EAGER_GC=1`` is meant to force ``call $gc_collect`` as
        the first instruction of ``$alloc``'s body (after the local
        declarations).  If the env-var-reading code in
        ``AssemblyMixin._emit_alloc`` silently regresses to a no-op,
        the eager-GC behavioural tests above still pass — they
        degenerate to the non-eager case and produce the same correct
        output.  This test fails noisily in that scenario by checking
        the WAT for ``$alloc`` directly.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_range(0, 3))
}
"""
        # Without the env var, $alloc's body has no call $gc_collect
        # before the size-invariant check (it does call $gc_collect on
        # the OOM slow path, but not at the top of the body).
        plain = _compile_ok(src).wat
        plain_alloc = re.search(r"\(func \$alloc.*?\n  \)", plain, re.DOTALL)
        assert plain_alloc is not None, "Could not locate $alloc in plain WAT"
        # Strip the OOM slow path: anything before the size-invariant
        # ``i32.const 0x80000000`` check is the function header + locals
        # + (under eager-GC) the unconditional gc_collect.
        plain_prologue = plain_alloc.group(0).split("0x80000000", 1)[0]
        assert "call $gc_collect" not in plain_prologue, (
            "Plain-mode $alloc should not have call $gc_collect before "
            "the size-invariant check"
        )

        # With VERA_EAGER_GC=1, the prologue must contain call
        # $gc_collect (the eager_prefix in _emit_alloc).
        with mock.patch.dict(os.environ, {"VERA_EAGER_GC": "1"}):
            eager = _compile_ok(src).wat
        eager_alloc = re.search(r"\(func \$alloc.*?\n  \)", eager, re.DOTALL)
        assert eager_alloc is not None, "Could not locate $alloc in eager WAT"
        eager_prologue = eager_alloc.group(0).split("0x80000000", 1)[0]
        assert "call $gc_collect" in eager_prologue, (
            "VERA_EAGER_GC=1 did not inject call $gc_collect into "
            "$alloc's prologue.  Either the env-var-reading code in "
            "AssemblyMixin._emit_alloc regressed, or the eager_prefix "
            "is being inserted in the wrong place."
        )

    @pytest.mark.parametrize("flag_value", ["1", "true", "TRUE", "Yes", "On", "true "])
    def test_vera_eager_gc_accepts_case_insensitive_truthy_values(
        self, flag_value: str,
    ) -> None:
        """The env-var allowlist is case-insensitive and tolerates
        common truthy spellings.  Pre-fix only ``1``/``true``/``yes``
        matched — ``True``, ``TRUE``, ``On``, etc. were silently
        rejected, which would frustrate a user trying the obvious
        spellings.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_range(0, 3))
}
"""
        with mock.patch.dict(os.environ, {"VERA_EAGER_GC": flag_value}):
            wat = _compile_ok(src).wat
        alloc = re.search(r"\(func \$alloc.*?\n  \)", wat, re.DOTALL)
        assert alloc is not None
        prologue = alloc.group(0).split("0x80000000", 1)[0]
        assert "call $gc_collect" in prologue, (
            f"VERA_EAGER_GC={flag_value!r} did not enable eager mode"
        )


class TestIndexExprOfFnCall614:
    """Regression tests for #614 — `f()[i]` was silently dropped.

    Pre-fix: ``_infer_index_element_type_expr`` in ``vera/wasm/inference.py``
    only handled SlotRef and IndexExpr collections.  When the
    collection was an ``FnCall`` returning ``Array<T>``, inference fell
    through to ``return None``, ``_translate_index_expr`` returned
    None too, and the enclosing function got dropped from the WAT.
    At top level this surfaced as the [E602] "function body contains
    unsupported expressions — skipped" warning; inside a closure body
    the registered ``closure_id`` was never added to the function
    table, so the call_indirect at the use site referenced a missing
    entry and WASM validation rejected the module with "unknown
    table 0: table index out of bounds".

    Fix: extend ``_infer_index_element_type_expr`` to look up the
    fn's full return TypeExpr via ``_fn_ret_type_exprs`` (a sibling
    of ``_fn_ret_types`` populated by ``_register_fn``).
    """

    def test_top_level_fn_call_then_index(self) -> None:
        """Top-level `f(x)[i]` where f returns Array<Int>."""
        src = """\
private data K { A, B }
private data S { Mk(Array<Int>, K) }

private fn s_arr(@S -> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{ match @S.0 { Mk(@Array<Int>, @K) -> @Array<Int>.0 } }

public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @S = Mk([10, 20, 30], A);
  s_arr(@S.0)[1]
}
"""
        assert _run(src, "test") == 20

    def test_closure_fn_call_then_index(self) -> None:
        """Closure body `f(x)[i]` — Bug 1 minimum reproducer.

        Pre-fix this trapped at WASM instantiation with
        "unknown table 0: table index out of bounds at offset 1374"
        because ``_compile_lifted_closure`` returned None and the
        call_indirect referenced a missing table entry.
        """
        src = """\
private data K { A, B }
private data S { Mk(Array<Int>, K) }

private fn s_arr(@S -> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{ match @S.0 { Mk(@Array<Int>, @K) -> @Array<Int>.0 } }

public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @S = Mk([10, 20, 30], A);
  let @Array<Int> = array_map(array_range(0, 3), fn(@Int -> @Int) effects(pure) {
    s_arr(@S.0)[@Int.0]
  });
  @Array<Int>.0[1]
}
"""
        assert _run(src, "test") == 20

    def test_chained_fn_call_then_double_index(self) -> None:
        """Chained `f(x)[i][j]` — exercise the IndexExpr-of-IndexExpr-
        of-FnCall path, which existed pre-fix but only worked when the
        outer collection was a SlotRef or IndexExpr.
        """
        src = """\
private fn matrix(@Unit -> @Array<Array<Int>>)
  requires(true) ensures(true) effects(pure)
{
  [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
}

public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  matrix(())[1][2]
}
"""
        assert _run(src, "test") == 6


class TestNonContiguousCapture615:
    """Regression tests for #615 — closure capture order miscompile.

    Pre-fix, ``_collect_free_vars`` returned captures in walk order
    without filling missing prefix indices or sorting per-type.  This
    caused two failure shapes:

    1. **Non-contiguous outer slot.** Closure body refs ``@Int.k``
       while skipping ``@Int.j`` (j<k).  The lift-side env had no
       entry for the unreferenced outer index, so ``env.resolve("Int",
       k)`` returned None, body translation failed, the closure was
       dropped from the function table, and the call_indirect at the
       use site referenced a missing entry — WASM validation trap.

    2. **Ascending walker order silently miscomputes.** Even with
       contiguous captures, when source order put the lower outer_idx
       first (e.g. body ``@Int.1 - @Int.2``), the walker added (Int,0)
       before (Int,1) → ascending push order → wrong stack layout →
       body's slot refs resolved to the WRONG captured locals.  No
       trap, just wrong output.

    Fix: in ``_collect_free_vars``, group captures by type, fill the
    prefix [0, max] per type with synthetic entries, and sort each
    group descending by outer_idx so the lift-side push produces the
    correct stack.
    """

    def test_non_contiguous_int_capture_tail_shape(self) -> None:
        """Bug 2a: closure body refs @Int.0 (param) and @Int.2 (outer)
        but not @Int.1 (also outer).  Pre-fix: WASM validation trap.

        Asserts a *specific* element rather than a sum so a silent-
        miscompute manifestation that happened to preserve the sum
        can't pass the test.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [99, 99, 99, 99];
  let @Array<Int> = [10, 20, 30, 40];
  let @Int = 3;
  let @Int = 0;

  -- closure refs @Int.0 (param), @Int.2 (outer @Int.1=3) — skips @Int.1
  let @Array<Int> = array_map(array_range(0, 4), fn(@Int -> @Int) effects(pure) {
    let @Nat = match int_to_nat(@Int.0) {
      Some(@Nat) -> @Nat.0,
      None -> 0
    };
    @Array<Int>.0[@Nat.0] + @Int.2 + @Int.0
  });
  -- expected at index 2: arr[2] + 3 + 2 = 30 + 3 + 2 = 35
  @Array<Int>.0[2]
}
"""
        assert _run(src, "test") == 35

    def test_non_contiguous_int_capture_silent_miscompute(self) -> None:
        """Bug 2b: same skip pattern but with subsequent let pushes that
        mask the trap into a silent wrong result.  Pre-fix: returned
        ``false`` instead of ``true`` for an obviously-fitting Tetris
        I-piece on an empty board.
        """
        src = """\
private fn empty_board(@Unit -> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{
  array_map(array_range(0, 200), fn(@Int -> @Int) effects(pure) { 0 })
}

private fn cell_at(@Array<Int>, @Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Int.1 < 0 then { 1 } else {
    if @Int.1 >= 10 then { 1 } else {
      if @Int.0 >= 20 then { 1 } else {
        if @Int.0 < 0 then { 0 } else {
          let @Int = @Int.0 * 10 + @Int.1;
          match int_to_nat(@Int.0) {
            Some(@Nat) -> @Array<Int>.0[@Nat.0],
            None -> 0
          }
        }
      }
    }
  }
}

private fn fits(@Array<Int>, @Int, @Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [0, 1, 1, 1, 2, 1, 3, 1];
  array_all(array_range(0, 4), fn(@Int -> @Bool) effects(pure) {
    let @Nat = match int_to_nat(@Int.0 * 2) {
      Some(@Nat) -> @Nat.0, None -> 0
    };
    let @Nat = match int_to_nat(@Int.0 * 2 + 1) {
      Some(@Nat) -> @Nat.0, None -> 0
    };
    let @Int = @Array<Int>.0[@Nat.1] + @Int.2;
    let @Int = @Array<Int>.0[@Nat.0] + @Int.2;
    cell_at(@Array<Int>.1, @Int.1, @Int.0) == 0
  })
}

public fn test(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = empty_board(());
  fits(@Array<Int>.0, 3, 0)
}
"""
        # Bool comes back as 1 (true) or 0 (false) at the WASM ABI.
        # Pre-fix: returned 0; post-fix: returns 1 (the I-piece fits
        # on an empty board).
        assert _run(src, "test") == 1

    def test_ascending_walker_order_silent_miscompute(self) -> None:
        """Even contiguous captures miscompile when walker visits the
        lower outer_idx first.  Body ``@Int.1 - @Int.2`` means
        outer @Int.0 - outer @Int.1.  Pre-fix this returned the
        opposite (outer @Int.1 - outer @Int.0) because ascending
        capture order produced a mirror-image lift-side stack.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 100;
  let @Int = 10;
  -- body's @Int.1 = outer @Int.0 = 10, @Int.2 = outer @Int.1 = 100
  -- expect 10 - 100 = -90
  let @Array<Int> = array_map(array_range(0, 1), fn(@Int -> @Int) effects(pure) {
    @Int.1 - @Int.2
  });
  @Array<Int>.0[0]
}
"""
        assert _run(src, "test") == -90

    def test_descending_walker_order_baseline(self) -> None:
        """Mirror of the above — body ``@Int.2 - @Int.1`` (descending
        walker order).  Should produce 100 - 10 = 90 both pre- and
        post-fix; the test exists to prevent the fix from regressing
        the case that *was* working.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 100;
  let @Int = 10;
  let @Array<Int> = array_map(array_range(0, 1), fn(@Int -> @Int) effects(pure) {
    @Int.2 - @Int.1
  });
  @Array<Int>.0[0]
}
"""
        assert _run(src, "test") == 90


class TestGenericCalledOnlyFromClosureBody873:
    """`#873` — a user generic whose ONLY call site is inside a closure body
    must be monomorphized: mono discovery already walks closure bodies (the
    total AST walk), and the clone is emitted, but the LIFTED closure body must
    also rewrite the call to the mangled clone.

    Pre-fix: ``_compile_lifted_closure`` built its ``WasmContext`` without
    ``generic_fn_info``, so the lifted body left the call on the bare generic
    name (``call $are_equal``) — which has no implementation — and ``vera run``
    failed WASM validation on a ``check``/``verify``-green program.
    """

    def test_generic_in_closure_body_executes(self) -> None:
        """`are_equal(@Int.0, 2)` inside an `array_any` closure runs.

        ``array_range(1, 4)`` = [1, 2, 3]; the predicate is true for 2, so
        ``array_any`` returns true (1).  Pre-fix: ``unknown func $are_equal``.
        The observable output distinguishes the real result from any default.
        """
        src = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(@Bool.result == (@T.1 == @T.0)) effects(pure)
{
  @T.1 == @T.0
}

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  array_any(array_range(1, 4),
            fn(@Int -> @Bool) effects(pure) { are_equal(@Int.0, 2) })
}
"""
        assert _run(src, "main") == 1

    def test_generic_in_closure_body_false_case(self) -> None:
        """The same shape with a needle NOT in the range returns false (0),
        so the closure-body clone is genuinely exercised — not short-circuited
        to a constant.  ``array_range(1, 4)`` = [1, 2, 3] has no 9.
        """
        src = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(@Bool.result == (@T.1 == @T.0)) effects(pure)
{
  @T.1 == @T.0
}

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  array_any(array_range(1, 4),
            fn(@Int -> @Bool) effects(pure) { are_equal(@Int.0, 9) })
}
"""
        assert _run(src, "main") == 0

    def test_generic_only_in_closure_body_verify_and_run_agree(self) -> None:
        """`verify` and `run` agree: the generic's postcondition is proved per
        monomorphization (#732) AND the emitted clone runs — the closure-body
        instantiation is covered on both sides.
        """
        import tempfile
        from pathlib import Path

        from vera.verifier import verify

        src = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(@Bool.result == (@T.1 == @T.0)) effects(pure)
{
  @T.1 == @T.0
}

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  array_any(array_range(1, 4),
            fn(@Int -> @Bool) effects(pure) { are_equal(@Int.0, 2) })
}
"""
        assert _run(src, "main") == 1
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(src)
            f.flush()
            path = f.name
        try:
            prog = transform(parse_file(path))
            vres = verify(prog, src, file=path)
            errors = [d for d in vres.diagnostics if d.severity == "error"]
            assert errors == [], [e.description for e in errors]
        finally:
            Path(path).unlink(missing_ok=True)
class TestTransitiveFnTypeAlias867:
    """#867: an ``apply_fn`` over a closure typed as a NESTED fn-type alias
    (``type Mapper = InnerMapper;`` where ``InnerMapper = fn(...)``) must
    build the ``call_indirect`` signature from the closure's REAL return
    width, resolved transitively through the whole alias chain.

    Pre-#867, ``_infer_apply_fn_return_type`` unwrapped only ONE alias hop:
    for a chain it saw a ``NamedType`` (not a ``FnType``), fell to its
    ``i64`` default, and emitted ``call_indirect (result i64)``.  When the
    closure actually returns an ``i32_pair`` (``String``) the signature
    mismatched the emit and trapped at WASM validation
    (``expected i32, found i64``); check and verify both passed — a loud
    failure on a green program (the #867 symptom).  The single-hop control
    (``type Mapper = fn(...)`` directly) always worked, so these tests pin
    the transitivity specifically."""

    _STRING_TWO_HOP = """\
type InnerMapper = fn(String -> String) effects(pure);
type Mapper = InnerMapper;

private fn use_it(@Mapper, @String -> @String)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@Mapper.0, @String.0)
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(use_it(
    fn(@String -> @String) effects(pure) { string_concat(@String.0, "!") },
    "hi"
  ))
}
"""

    _STRING_THREE_HOP = """\
type A = fn(String -> String) effects(pure);
type B = A;
type Mapper = B;

private fn use_it(@Mapper, @String -> @String)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@Mapper.0, @String.0)
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(use_it(
    fn(@String -> @String) effects(pure) { string_concat(@String.0, "!") },
    "hi"
  ))
}
"""

    def test_two_hop_string_return_runs(self) -> None:
        """`type Mapper = InnerMapper;` with a String-returning closure:
        pre-#867 the i64-defaulted call_indirect signature trapped at WASM
        validation; post-#867 it runs and prints the real value."""
        assert _run_io(self._STRING_TWO_HOP) == "hi!"

    def test_three_hop_string_return_runs(self) -> None:
        """Same, three hops (`Mapper = B = A = fn(...)`) — depth-N."""
        assert _run_io(self._STRING_THREE_HOP) == "hi!"

    def test_two_hop_string_signature_is_i32_pair(self) -> None:
        """Compile-time discriminator: the ``call_indirect`` closure
        signature must carry the i32_pair (String) result, not the i64
        default.  Pins the fix at the emit level, network- and
        execution-free."""
        result = _compile_ok(self._STRING_TWO_HOP)
        # A String-returning closure sig has a two-i32 result; the pre-#867
        # bug emitted `(result i64)`.  No closure sig in this program should
        # carry a bare i64 result.
        sigs = re.findall(r"\(type \$closure_sig_\d+ \(func[^\n]*\)", result.wat)
        assert sigs, ("expected a closure signature type in the WAT", result.wat)
        assert all("result i64" not in s for s in sigs), (
            "the call_indirect closure signature must resolve the String "
            "return through the alias chain to an i32_pair result, not fall "
            "to the i64 default (#867)", sigs)
        assert any("result i32 i32" in s for s in sigs), (
            "expected an i32_pair (String) closure result signature", sigs)

    # PR #880 review (CodeRabbit, Major): an alias whose body is a
    # RefinementType DIRECTLY wrapping an inline fn type.  The resolver
    # peeled refinement layers mid-chain but did not treat the bared
    # FnType as terminal — it fell through the NamedType check to None,
    # and the caller fell to the i64 default.  String return makes the
    # miss observable (Int coincides with the i64 default and runs by
    # accident — the classic fallback-coincidence trap).
    _REFINEMENT_OVER_FN_TYPE = """\
type Foo = { @fn(String -> String) effects(pure) | true };

private fn use_it(@Foo, @String -> @String)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@Foo.0, @String.0)
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(use_it(
    fn(@String -> @String) effects(pure) { string_concat(@String.0, "!") },
    "hi"
  ))
}
"""

    # The chained form: an alias hop INTO a refinement-over-fn-type
    # terminal (`Foo -> Inner -> { @fn(...) | p }`).
    _CHAIN_INTO_REFINEMENT_OVER_FN_TYPE = """\
type Inner = { @fn(String -> String) effects(pure) | true };
type Foo = Inner;

private fn use_it(@Foo, @String -> @String)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@Foo.0, @String.0)
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(use_it(
    fn(@String -> @String) effects(pure) { string_concat(@String.0, "!") },
    "hi"
  ))
}
"""

    def test_refinement_over_fn_type_alias_runs(self) -> None:
        """PR #880 review: `type Foo = { @fn(String -> String) | p };`
        used as an apply_fn closure arg must resolve to the wrapped
        FnType — pre-fix the peeled FnType was not terminal, the
        signature fell to the i64 default, and WASM validation trapped
        (`expected i32, found i64`)."""
        assert _run_io(self._REFINEMENT_OVER_FN_TYPE) == "hi!"

    def test_chain_into_refinement_over_fn_type_runs(self) -> None:
        """Same, one alias hop out: `Foo = Inner = { @fn(...) | p }` —
        the FnType must be terminal at any depth after wrapper peeling."""
        assert _run_io(self._CHAIN_INTO_REFINEMENT_OVER_FN_TYPE) == "hi!"

    # PR #880 review, 4th single-hop site (CodeRabbit Major):
    # `_slot_name_to_wasm_type` (vera/wasm/inference.py) classified only a
    # BARE FnType alias as a closure pointer.  A `let`/param slot annotated
    # with a refinement-wrapped fn alias (`type Foo = { @fn(...) | p };`) or
    # a chain THROUGH a refinement (`type Foo = Inner;` where `Inner`
    # wraps the fn type) resolved to None, and the binding was rejected
    # with `CodegenSkip` ("has no WASM representation") — the whole
    # function dropped, `main` unexported, on a check/verify-green program.
    # (A plain NamedType chain `Foo = Bar = fn(...)` was already handled by
    # the `_resolve_base_type_name` prefix walk, so these deliberately
    # exercise the refinement-involving shapes that walk cannot peel.)
    _REFINEMENT_FN_ALIAS_SLOT = """\
type Foo = { @fn(String -> String) effects(pure) | true };

private fn make(@Unit -> @Foo)
  requires(true) ensures(true) effects(pure)
{
  fn(@String -> @String) effects(pure) { string_concat(@String.0, "!") }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Foo = make(());
  IO.print(apply_fn(@Foo.0, "hi"))
}
"""

    _CHAIN_THROUGH_REFINEMENT_FN_ALIAS_SLOT = """\
type Inner = { @fn(String -> String) effects(pure) | true };
type Foo = Inner;

private fn make(@Unit -> @Foo)
  requires(true) ensures(true) effects(pure)
{
  fn(@String -> @String) effects(pure) { string_concat(@String.0, "!") }
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Foo = make(());
  IO.print(apply_fn(@Foo.0, "hi"))
}
"""

    def test_refinement_fn_alias_let_slot_runs(self) -> None:
        """PR #880 4th site: a `let @Foo = …` slot annotated with a
        refinement-wrapped fn alias must classify as an i32 closure
        pointer — pre-fix `_slot_name_to_wasm_type` returned None, the
        binding was skipped (`CodegenSkip`), `main` was dropped, and
        `vera run` reported no exported function to call."""
        assert _run_io(self._REFINEMENT_FN_ALIAS_SLOT) == "hi!"

    def test_chain_through_refinement_fn_alias_let_slot_runs(self) -> None:
        """Same, chained through a refinement: `type Foo = Inner;` where
        `Inner = { @fn(...) | p }` — the resolver peels the refinement at
        the terminal hop that `_resolve_base_type_name` cannot follow."""
        assert _run_io(self._CHAIN_THROUGH_REFINEMENT_FN_ALIAS_SLOT) == "hi!"
