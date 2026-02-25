"""Unit tests for vera.wasm — WASM translation layer.

Tests StringPool, WasmSlotEnv directly, and exercises less-common
expression translation branches via the full compilation pipeline.
"""

from __future__ import annotations

import tempfile
from pathlib import Path

import pytest

from vera.wasm import StringPool, WasmSlotEnv
from vera.codegen import CompileResult, compile, execute
from vera.parser import parse_file
from vera.transform import transform


# =====================================================================
# Helpers
# =====================================================================

def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
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
    result = _compile(source)
    assert result.wasm_bytes is not None, f"Compile failed: {result.errors}"
    return result


def _run(source: str, fn: str | None = None,
         args: list[int] | None = None) -> int:
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args or [])
    assert exec_result.value is not None
    return int(exec_result.value)


# =====================================================================
# StringPool
# =====================================================================

class TestStringPool:
    def test_empty_pool(self) -> None:
        pool = StringPool()
        assert not pool.has_strings()
        assert pool.entries() == []
        assert pool.heap_offset == 0

    def test_intern_string(self) -> None:
        pool = StringPool()
        offset, length = pool.intern("hello")
        assert offset == 0
        assert length == 5
        assert pool.has_strings()

    def test_deduplication(self) -> None:
        pool = StringPool()
        first = pool.intern("abc")
        second = pool.intern("abc")
        assert first == second

    def test_multiple_strings(self) -> None:
        pool = StringPool()
        o1, l1 = pool.intern("hi")
        o2, l2 = pool.intern("bye")
        assert o1 == 0
        assert l1 == 2
        assert o2 == 2  # immediately after "hi"
        assert l2 == 3

    def test_empty_string(self) -> None:
        pool = StringPool()
        offset, length = pool.intern("")
        assert length == 0

    def test_heap_offset_after_strings(self) -> None:
        pool = StringPool()
        pool.intern("abc")  # 3 bytes
        pool.intern("de")   # 2 bytes
        assert pool.heap_offset == 5

    def test_entries_sorted(self) -> None:
        pool = StringPool()
        pool.intern("beta")
        pool.intern("alpha")
        entries = pool.entries()
        offsets = [e[1] for e in entries]
        assert offsets == sorted(offsets)

    def test_utf8_encoding(self) -> None:
        pool = StringPool()
        # "é" is 2 bytes in UTF-8
        offset, length = pool.intern("é")
        assert length == 2


# =====================================================================
# WasmSlotEnv
# =====================================================================

class TestWasmSlotEnv:
    def test_empty_resolve(self) -> None:
        env = WasmSlotEnv()
        assert env.resolve("Int", 0) is None

    def test_push_and_resolve(self) -> None:
        env = WasmSlotEnv()
        env2 = env.push("Int", 5)
        assert env2.resolve("Int", 0) == 5

    def test_resolve_out_of_range(self) -> None:
        env = WasmSlotEnv()
        env2 = env.push("Int", 5)
        assert env2.resolve("Int", 1) is None

    def test_de_bruijn_ordering(self) -> None:
        env = WasmSlotEnv()
        env2 = env.push("Int", 10)
        env3 = env2.push("Int", 20)
        # Index 0 = most recent
        assert env3.resolve("Int", 0) == 20
        assert env3.resolve("Int", 1) == 10

    def test_separate_type_stacks(self) -> None:
        env = WasmSlotEnv()
        env2 = env.push("Int", 5)
        env3 = env2.push("Bool", 7)
        assert env3.resolve("Int", 0) == 5
        assert env3.resolve("Bool", 0) == 7

    def test_immutability(self) -> None:
        env = WasmSlotEnv()
        env2 = env.push("Int", 5)
        # Original env unchanged
        assert env.resolve("Int", 0) is None


# =====================================================================
# Expression translation edge cases (via compile pipeline)
# =====================================================================

class TestTranslationEdgeCases:
    def test_string_in_io_print(self) -> None:
        """IO.print with string literal compiles and runs."""
        source = """\
fn hello(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("hello world")
}
"""
        result = _compile_ok(source)
        assert b"hello world" in result.wasm_bytes

    def test_float_mod_skipped(self) -> None:
        """Float MOD is unsupported — function should be skipped."""
        source = """\
fn fmod(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  @Float64.1 % @Float64.0
}
"""
        result = _compile(source)
        # Function should be skipped (WASM has no f64.rem)
        assert "fmod" not in (result.exports or [])

    def test_call_helper_function(self) -> None:
        """Calling a helper function compiles correctly."""
        source = """\
fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  helper(@Int.0)
}
"""
        assert _run(source, "outer", [10]) == 11

    def test_nested_if_in_let(self) -> None:
        """Nested if-then-else inside let binding."""
        source = """\
fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = if @Int.0 > 0 then { 1 } else { 0 };
  @Int.0 + 100
}
"""
        assert _run(source, "f", [5]) == 101
        assert _run(source, "f", [-1]) == 100

    def test_bool_comparison_result(self) -> None:
        """Boolean comparison operations return i32."""
        source = """\
fn is_positive(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Int.0 > 0
}
"""
        assert _run(source, "is_positive", [5]) == 1
        assert _run(source, "is_positive", [-1]) == 0

    def test_multiple_let_bindings(self) -> None:
        """Chain of let bindings with different types."""
        source = """\
fn chain(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0 + 1;
  let @Int = @Int.0 * 2;
  @Int.0
}
"""
        assert _run(source, "chain", [5]) == 12

    def test_negation_int(self) -> None:
        """Unary negation on integers."""
        source = """\
fn negate(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  -@Int.0
}
"""
        assert _run(source, "negate", [42]) == -42

    def test_boolean_not(self) -> None:
        """Boolean not operation."""
        source = """\
fn invert(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  !@Bool.0
}
"""
        assert _run(source, "invert", [1]) == 0
        assert _run(source, "invert", [0]) == 1
