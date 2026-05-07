"""Tests for vera.codegen — Closures.

Covers anonymous functions, captures, apply_fn, function tables,
and call_indirect compilation.
"""

from __future__ import annotations

import os
from unittest import mock

import pytest
import wasmtime

from vera.codegen import (
    CompileResult,
    ConstructorLayout,
    ExecuteResult,
    _align_up,
    _wasm_type_align,
    _wasm_type_size,
    compile,
    execute,
)
from vera.parser import parse_file
from vera.transform import transform


# =====================================================================
# Helpers
# =====================================================================


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    # Write to a temp source and parse
    import tempfile
    from pathlib import Path

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False
    ) as f:
        f.write(source)
        f.flush()
        path = f.name

    tree = parse_file(path)
    ast = transform(tree)
    return compile(ast, source=source, file=path)


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
        """A function with a function-type parameter is not skipped."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
public fn apply(@IntToInt, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@IntToInt.0, @Int.0)
}
"""
        result = _compile_ok(src)
        assert "apply" in result.exports

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
        source = path.read_text()
        result = _compile(source)
        assert result.ok

    def test_closures_example_test_closure(self) -> None:
        """examples/closures.vera test_closure returns 15."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "closures.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_closure")
        assert exec_result.value == 15

    def test_closures_example_test_option_map(self) -> None:
        """examples/closures.vera test_option_map returns 105."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "closures.vera"
        source = path.read_text()
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
    like (``b_needs_unwind`` at ``vera/wasm/calls_arrays.py:649-655``).
    That pop assumes the closure's epilogue pushed a return-value root.

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
    is a heap pointer, regardless of ``needs_alloc``.  This validates
    that fix at three layers: structural (the WAT contains the push),
    behavioural under eager-GC (output is correct when GC fires on
    every alloc), and end-to-end (no corruption from a small Life-shape
    program).
    """

    def test_non_allocating_closure_returns_string_via_array_map(
        self,
    ) -> None:
        """A non-allocating closure returning a String literal through
        ``array_map`` produces the correct joined output.

        Pre-fix this output was usually correct at small scale (the
        corruption only manifested when GC fired during the over-pop
        window) — kept as a positive regression test that the fix
        didn't break the fast path.  The eager-GC variants below
        validate the rooting balance directly.
        """
        src = """\
effect IO { op print(String -> Unit); }

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
        """Same shape as above, but compiled under ``VERA_EAGER_GC=1``
        which fires ``$gc_collect`` on every allocation.

        Pre-fix this would corrupt the output: each iteration of the
        outer ``array_map`` over-popped the shadow stack by one slot,
        and the eager GC's mark phase would miss the over-popped roots
        and sweep their referents.  The visible failure was either a
        ``call_indirect`` table OOB trap or wrong output with NULL
        bytes / leftover heap content where String pointers should
        have been.

        Post-fix the closure's epilogue always pushes the return-value
        root, balancing the array_map pop, so eager-GC produces the
        same output as non-eager.
        """
        src = """\
effect IO { op print(String -> Unit); }

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

    def test_eager_gc_recursive_render_no_corruption(self) -> None:
        """Recursive ``run_loop`` calling ``render_grid`` with nested
        ``array_map`` of non-allocating closures returning Strings.

        This is the minimum shape that reproduced #593's silent string
        corruption (Conway's Life rendering): nested ``array_map``
        where the innermost closure body is a non-allocating String
        return (a literal lookup), driven by a recursive loop that
        builds heap pressure across iterations.

        Compiled under ``VERA_EAGER_GC=1`` so the rooting imbalance
        manifests on the first iteration rather than only at scale.
        Pre-fix: traps in ``render_grid`` with "out of bounds table
        access" or produces output containing NULL / U+FFFD bytes.
        Post-fix: 5 iterations of ``.X..`` separated by newlines.
        """
        src = """\
effect IO { op print(String -> Unit); }

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
        contain at least one ``i32.store`` to ``$gc_sp`` in its
        epilogue.

        Without this, the ``b_needs_unwind`` pop in array_map /
        array_mapi (`vera/wasm/calls_arrays.py:780-784, 1557-1561`) is
        unbalanced.  Detecting the push at the WAT level prevents
        regression even if the runtime test happens to produce correct
        output by coincidence at small scale.
        """
        src = """\
effect IO { op print(String -> Unit); }

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
        # Find every lifted closure ($anon_X) that returns an i32 pair
        # (i.e., String or Array<T>).  At least one of them — the
        # ``fn(@Int -> @String) { pick(...) }`` — has a non-allocating
        # body (pick just selects between two String literals) and so
        # has ``needs_alloc=False``.  Pre-fix that closure's epilogue
        # was empty; post-fix it must emit the return-value
        # ``gc_shadow_push``.  We detect the push by the presence of
        # the canonical ``global.get $gc_sp`` + ``i32.store`` sequence
        # in a body that contains no ``call $alloc``.
        import re

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
            if "global.set $gc_sp" in body
            and "call $alloc" not in body
        ]
        assert non_alloc_with_push, (
            "No non-allocating i32-pair-returning closure with a "
            "shadow-push return-root was found.  The fix for #593 "
            "requires the closure's epilogue to push the return-value "
            "root regardless of needs_alloc."
        )
