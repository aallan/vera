"""Shared helpers for the test_codegen_*.py suite (split from tests/test_codegen.py, #419).

The established pattern:
    _compile(source) -> CompileResult
    _compile_ok(source) -> CompileResult (assert no errors)
    _run(source, fn, args) -> int result
    _run_io(source, fn, args) -> captured stdout string
    _run_trap(source, fn, args) -> assert WASM trap
(plus _run_float / _run_refine_trap / _run_state / _compile_with_generator
and the WAT/GC assertion helpers further down).
"""
from __future__ import annotations

from collections.abc import Callable
from pathlib import Path

import pytest
import wasmtime

from vera.codegen import (
    CodeGenerator,
    compile,
    CompileResult,
    execute,
    ExecuteResult,
)
from vera.parser import parse_file
from vera.transform import transform


# =====================================================================
# Helpers
# =====================================================================


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    # Write to a temp source and parse.  delete=False + manual unlink is
    # the Windows-safe pattern (an open NamedTemporaryFile can't be
    # reopened there); the finally guarantees no temp-file leak even
    # when parsing or compilation raises.
    import tempfile

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name

    try:
        tree = parse_file(path)
        ast = transform(tree)
        return compile(ast, source=source, file=path)
    finally:
        Path(path).unlink(missing_ok=True)


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


def _run_refine_trap(
    source: str, fn: str | None = None, args: list[object] | None = None
) -> None:
    """Compile, execute, and assert a *refinement-guard* trap specifically — a
    `$vera.contract_fail` ``RuntimeError`` carrying 'Refinement violation', not
    merely *some* runtime trap (which an unrelated fault — e.g. an
    out-of-bounds index — could also raise).  Use this for refinement
    runtime-guard tests so they prove the guard fired, not just that the
    program trapped for any reason."""
    result = _compile_ok(source)
    with pytest.raises(RuntimeError, match="Refinement violation"):
        execute(result, fn_name=fn, args=args)


# =====================================================================
# 5e: String literals + IO host bindings
# =====================================================================

_IO_PRELUDE = """\
effect IO {
  op print(String -> Unit);
}
"""


# =====================================================================
# 6d: State<T> host imports
# =====================================================================

def _run_state(
    source: str,
    fn: str | None = None,
    args: list[int | float] | None = None,
    initial_state: dict[str, int | float] | None = None,
) -> ExecuteResult:
    """Compile, execute, and return the full ExecuteResult."""
    result = _compile_ok(source)
    return execute(result, fn_name=fn, args=args, initial_state=initial_state)


# =====================================================================
# 6e: Bump allocator infrastructure
# =====================================================================


def _compile_with_generator(source: str) -> tuple[CompileResult, CodeGenerator]:
    """Compile and return both result and CodeGenerator for metadata inspection."""
    import tempfile

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name

    try:
        tree = parse_file(path)
        program = transform(tree)
        gen = CodeGenerator(source=source, file=path)
        result = gen.compile_program(program)
        return result, gen
    finally:
        Path(path).unlink(missing_ok=True)


_INLINE_BUILTIN_NAMES = (
    # #471 — character classifiers + first-byte case conversion
    "is_digit", "is_alpha", "is_alphanumeric", "is_whitespace",
    "is_upper", "is_lower", "char_to_upper", "char_to_lower",
    # #470 — string utilities
    "string_chars", "string_lines", "string_words",
    "string_reverse", "string_trim_start", "string_trim_end",
    "string_pad_start", "string_pad_end",
)


def _assert_no_host_imports_for_inline_builtins(wat: str) -> None:
    """Assert the compiled WAT has no host imports for the 16 inline
    built-ins added by #470 + #471.

    These functions are documented as being implemented entirely
    inline in WAT (no host imports — bit-identical Python/browser
    output by construction).  If a future refactor accidentally
    routes one through a host import, the import would appear as
    ``(import "vera" "<name>" ...)`` in the module's import section
    and this assertion would catch it.

    The check tolerates other unrelated imports (`IO.print`,
    `gc_collect` host helpers, etc.) — it scans only for our 16
    names.
    """
    for name in _INLINE_BUILTIN_NAMES:
        marker = f'(import "vera" "{name}"'
        assert marker not in wat, (
            f"Expected no host import for inline built-in {name!r}, "
            f"but found {marker!r} in the WAT.  This contradicts the "
            f"#470/#471 design contract."
        )


# =====================================================================
# Reclamation of transient Map / Set / Decimal values
# =====================================================================
# Historically (#573) every map_new / map_insert / map_remove
# allocated an entry in `_map_store` (in `vera/codegen/api.py`) that a
# Phase-2c `$gc_collect` walk evicted via `host_decref_handle` once the
# owning wrapper was unmarked.
#
# Post-#706 (bucket-as-truth): Map and Set hold no Python store at all
# — each op builds a fresh wrapper whose `bucket_ptr` (+8) owns the
# data, and transient wrappers + buckets are reclaimed by ordinary
# mark-sweep.  `ExecuteResult.peak_heap_bytes` (the exported `$heap_ptr`
# high-water mark) is the leak signal: a working reclaimer keeps it
# ~O(N) across an insert chain; a leak grows it ~O(N^2).  Decimal alone
# still uses a Python store, so `ExecuteResult.host_store_sizes` keeps
# reporting its post-execution population.
# =====================================================================


def _assert_chain_reclaims(
    chain: Callable[[int], str],  # builds the chain source for a given size
    small_n: int,
    large_n: int,
    small_val: int,
    large_val: int,
    ratio: int = 30,
) -> None:
    """#706: run an insert/add chain at two sizes and assert the heap
    high-water mark grows ~O(N), proving transient wrappers + buckets
    are reclaimed by mark-sweep.

    With power-of-two bucket sizing a working reclaimer reuses freed
    same-size buckets, so 10x the inserts gives only ~6x the peak heap.
    A leak (transients never freed) grows ~O(N^2) → ~100x.  The bound
    sits well between the two.
    """
    small = execute(_compile_ok(chain(small_n)))
    large = execute(_compile_ok(chain(large_n)))
    assert small.value == small_val, (
        f"chain(n={small_n}) returned {small.value}, expected {small_val}"
    )
    assert large.value == large_val, (
        f"chain(n={large_n}) returned {large.value}, expected {large_val}"
    )
    assert large.peak_heap_bytes < small.peak_heap_bytes * ratio, (
        f"#706 reclamation regression: peak heap for n={large_n} "
        f"({large.peak_heap_bytes:,} bytes) exceeds {ratio}x the n="
        f"{small_n} peak ({small.peak_heap_bytes:,} bytes).  Transient "
        f"Map/Set wrappers + buckets are not being reclaimed — O(N^2) "
        f"high-water growth indicates a leak, vs the ~O(N) expected from "
        f"mark-sweep plus power-of-two bucket sizing."
    )
