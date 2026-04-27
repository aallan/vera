"""Tests for vera.codegen — Closures.

Covers anonymous functions, captures, apply_fn, function tables,
and call_indirect compilation.
"""

from __future__ import annotations

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
  nat_to_int(array_length(@Array<Array<Int>>.0))
}
"""
        # Outer length 3, inner doesn't matter for this assertion.
        assert _run(src, "test") == 3

    def test_nested_closure_with_outer_param_capture(self) -> None:
        """The 'with capture' variant from the issue body — the inner
        closure references its outer's parameter via ``@Int.1``.

        Pre-fix: same WASM validation failure (offset 1536 vs 1529 in
        the issue text). The capture analysis itself worked for the
        outer; the missing-lift kept the inner from being emitted at all,
        so the capture had nowhere to land.
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
  nat_to_int(array_length(@Array<Array<Int>>.0))
}
"""
        assert _run(src, "test") == 3

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
        result = _compile_ok(src)
        wat = result.wat
        # Both closures must have lifted functions.
        assert "(func $anon_0" in wat, (
            "Outer closure missing from WAT — regression in single-level lifting"
        )
        assert "(func $anon_1" in wat, (
            "Inner closure missing from WAT — #514 worklist regression"
        )
        # Function table must have at least 2 entries.
        # The exact form is `(table N funcref)` — extract N.
        import re
        m = re.search(r"\(table\s+(\d+)\s+funcref\)", wat)
        assert m is not None, f"No funcref table in WAT: {wat[:500]}"
        table_size = int(m.group(1))
        assert table_size >= 2, (
            f"Function table too small ({table_size}) for nested closures; "
            "inner closure was not lifted"
        )
