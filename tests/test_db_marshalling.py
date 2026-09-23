"""Round-trip tests for the ``<DB>`` marshalling helpers (#229, S2).

The ``DB.query`` / ``DB.execute`` host ops move nested, nullable data across the
WASM boundary:

  - inbound, a ``params`` argument is an ``Array<Option<String>>`` the host must
    *read* (``_read_wasm_array_of_options_of_string``);
  - outbound, ``query`` returns ``Result<Array<Array<Option<String>>>, String>``
    (``_alloc_result_ok_rows``, via ``_alloc_array_of_options_of_string``) and
    ``execute`` returns ``Result<Int, String>`` (``_alloc_result_ok_i64``).

These exercise the allocators directly through an :class:`InstanceCaller` wrapped
around a *real compiled module* (so ``$rt.alloc`` and the GC exports are live), and
they run twice: once normally (layout correctness) and once under
``VERA_EAGER_GC=1`` (rooting correctness — every ``$rt.alloc`` fires a full
``$rt.gc_collect``, so an unrooted intermediate is swept and the read-back sees
corruption).  The ABI mirrors the existing ``_alloc_*`` family:

  - ``Option<String>``: ADT, a 4-byte heap pointer — ``None`` is tag 0 at +0;
    ``Some`` is tag 1 at +0, ``str_ptr`` at +4, ``str_len`` at +8.
  - ``Array<Option<String>>``: a (ptr, count) pair; its backing is ``count``
    4-byte ``Option`` pointers.
  - ``Array<Array<Option<String>>>``: a (ptr, count) pair; its backing is
    ``count`` 8-byte (row_ptr, n_cols) pairs.
  - ``Result.Ok(pair)``: 12 bytes — tag 0 at +0, ptr at +4, len at +8.
  - ``Result.Ok(Int)``: 16 bytes — tag 0 at +0, i64 at +8.
"""
from __future__ import annotations

from typing import ClassVar

import pytest
import wasmtime

from vera.codegen import compile as codegen_compile
from vera.parser import parse_to_ast
from vera.runtime.heap import (
    InstanceCaller,
    _alloc_array_of_options_of_string,
    _alloc_result_ok_i64,
    _alloc_result_ok_rows,
    _read_i32,
    _read_wasm_array_of_options_of_string,
    _write_i32,
)

# A pure, allocation-performing program: it exports ``$rt.alloc`` and the GC
# globals (``$gc_sp`` / ``$gc_stack_limit``) and imports nothing, so it
# instantiates with an empty import list and the heap allocators can be driven
# directly against it.
_HARNESS_SRC = (
    "public fn main(-> @String)\n"
    "  requires(true) ensures(true) effects(pure)\n"
    '{ string_repeat("ab", 3) }'
)


def _gc_caller() -> InstanceCaller:
    """Compile + instantiate the harness module and wrap it in an
    ``InstanceCaller``.  Read ``VERA_EAGER_GC`` at COMPILE time (it is baked
    into ``$rt.alloc`` by ``AssemblyMixin._emit_alloc``), so a caller wanting the
    eager-GC stress must ``monkeypatch.setenv`` *before* calling this."""
    res = codegen_compile(parse_to_ast(_HARNESS_SRC), source=_HARNESS_SRC)
    assert res.ok, res.diagnostics
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    module = wasmtime.Module(engine, res.wasm_bytes)
    instance = wasmtime.Instance(store, module, [])
    return InstanceCaller(store, instance)


def _decode_result_ok_rows(
    caller: InstanceCaller, adt_ptr: int,
) -> list[list[str | None]]:
    """Decode a ``Result.Ok(Array<Array<Option<String>>>)`` ADT pointer back
    into Python, reading the layout byte-for-byte (independent of the
    allocator, so a wrong offset in either surfaces)."""
    assert _read_i32(caller, adt_ptr) == 0, "expected Ok tag"
    outer_ptr = _read_i32(caller, adt_ptr + 4)
    n_rows = _read_i32(caller, adt_ptr + 8)
    rows: list[list[str | None]] = []
    for r in range(n_rows):
        row_ptr = _read_i32(caller, outer_ptr + r * 8)
        n_cols = _read_i32(caller, outer_ptr + r * 8 + 4)
        rows.append(_read_wasm_array_of_options_of_string(caller, row_ptr, n_cols))
    return rows


class TestOptionStringArrayRoundTrip:
    """Inbound reader ∘ outbound allocator for ``Array<Option<String>>``."""

    CASES: ClassVar[list[list[str | None]]] = [
        [],
        [None],
        ["alpha"],
        ["a", None, "b"],
        [None, None, "x", None],
        ["", "nonempty", ""],           # empty Some("") round-trips
        ["µ-value", "→arrow", "🦀"],     # multibyte UTF-8
    ]

    @pytest.mark.parametrize("cells", CASES)
    def test_round_trip(self, cells: list[str | None]) -> None:
        caller = _gc_caller()
        ptr, count = _alloc_array_of_options_of_string(caller, cells)
        assert count == len(cells)
        assert _read_wasm_array_of_options_of_string(caller, ptr, count) == cells

    @pytest.mark.parametrize("cells", CASES)
    def test_round_trip_eager_gc(
        self, cells: list[str | None], monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        # Every $rt.alloc fires $rt.gc_collect; an unrooted intermediate (the backing
        # or a Some's string) is swept and the read-back corrupts.
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        caller = _gc_caller()
        ptr, count = _alloc_array_of_options_of_string(caller, cells)
        assert _read_wasm_array_of_options_of_string(caller, ptr, count) == cells

    def test_out_of_bounds_pointer_array_raises_not_sigbus(self) -> None:
        # A guest-controlled (ptr, count) whose pointer array runs past WASM
        # memory must raise a clean out_of_bounds trap, not SIGBUS in the raw
        # ctypes slice inside `_read_i32` (#1145 class).  The pre-fix failure is
        # a hard SIGBUS that would abort pytest, so the RED baseline is proven
        # out-of-process; this asserts the fixed clean-raise.
        caller = _gc_caller()
        with pytest.raises(
            wasmtime.WasmtimeError, match="out of bounds memory access",
        ):
            _read_wasm_array_of_options_of_string(caller, 10_000_000, 4)

    def test_negative_count_raises_not_silently_empty(self) -> None:
        # A negative count (a guest i32 whose high bit is set) must raise, not
        # silently return [] through range(negative).  Pins the `count < 0`
        # guard: without it the loop simply never runs and the malformed input
        # is swallowed.
        caller = _gc_caller()
        with pytest.raises(wasmtime.WasmtimeError, match="negative count"):
            _read_wasm_array_of_options_of_string(caller, 0, -1)

    def test_element_pointer_out_of_bounds_raises_not_sigbus(self) -> None:
        # The outer pointer array is in bounds, but a per-element `opt_ptr` is
        # itself guest-controlled and points past memory.  Reading its tag
        # through the unchecked `_read_i32` would SIGBUS — the #1145 class one
        # level deeper than the outer-array guard.  A valid 1-element array has
        # its sole element pointer clobbered with an out-of-range value.
        caller = _gc_caller()
        backing, count = _alloc_array_of_options_of_string(caller, ["x"])
        _write_i32(caller, backing, 10_000_000)   # clobber element[0] -> OOB
        with pytest.raises(
            wasmtime.WasmtimeError, match="out of bounds memory access",
        ):
            _read_wasm_array_of_options_of_string(caller, backing, count)

    def test_some_cell_straddling_memory_end_raises(self) -> None:
        # An `opt_ptr` whose tag is readable (in bounds) but whose full 12-byte
        # Some(String) layout (tag + str_ptr + str_len) runs off the end of
        # memory must raise before the +4 / +8 field reads reach `_read_i32`.
        caller = _gc_caller()
        # Allocate first: `_call_alloc` can grow linear memory, so read
        # `mem_size` only after the backing is placed, or `straddle` lands
        # inside a since-grown region and no longer straddles the end.
        backing, count = _alloc_array_of_options_of_string(caller, ["x"])
        memory = caller["vera.memory"]
        assert isinstance(memory, wasmtime.Memory)
        mem_size = memory.data_len(caller)
        straddle = mem_size - 8            # tag read OK (+4); +12 overruns
        _write_i32(caller, straddle, 1)    # tag = 1 -> Some(String) path
        _write_i32(caller, backing, straddle)
        with pytest.raises(
            wasmtime.WasmtimeError, match="out of bounds memory access",
        ):
            _read_wasm_array_of_options_of_string(caller, backing, count)


class TestResultOkRowsRoundTrip:
    """``_alloc_result_ok_rows`` — the ``DB.query`` result grid."""

    CASES: ClassVar[list[list[list[str | None]]]] = [
        [],
        [[]],
        [["only"]],
        [["a", None], ["b"], [None, None, "c"]],
        [[None], ["", "x"], ["y", None, ""]],
    ]

    @pytest.mark.parametrize("rows", CASES)
    def test_round_trip(self, rows: list[list[str | None]]) -> None:
        caller = _gc_caller()
        adt_ptr = _alloc_result_ok_rows(caller, rows)
        assert _decode_result_ok_rows(caller, adt_ptr) == rows

    @pytest.mark.parametrize("rows", CASES)
    def test_round_trip_eager_gc(
        self, rows: list[list[str | None]], monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        caller = _gc_caller()
        adt_ptr = _alloc_result_ok_rows(caller, rows)
        assert _decode_result_ok_rows(caller, adt_ptr) == rows

    def test_large_grid_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        # A grid big enough that eager GC reclaims + reuses free blocks mid-
        # construction: a mis-rooted row or cell reads back wrong, not merely
        # "works by luck because nothing was reused".
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        rows = [
            [f"r{r}c{c}" if (r + c) % 3 else None for c in range(8)]
            for r in range(40)
        ]
        caller = _gc_caller()
        adt_ptr = _alloc_result_ok_rows(caller, rows)
        assert _decode_result_ok_rows(caller, adt_ptr) == rows


class TestResultOkI64RoundTrip:
    """``_alloc_result_ok_i64`` — the ``DB.execute`` affected-row count."""

    CASES: ClassVar[list[int]] = [0, 1, 42, -1, 9223372036854775807, -9223372036854775808]

    @pytest.mark.parametrize("value", CASES)
    def test_round_trip(self, value: int) -> None:
        caller = _gc_caller()
        adt_ptr = _alloc_result_ok_i64(caller, value)
        assert _read_i32(caller, adt_ptr) == 0            # Ok tag
        # i64 payload at +8 (little-endian), read as two i32 halves.
        lo = _read_i32(caller, adt_ptr + 8)
        hi = _read_i32(caller, adt_ptr + 12)
        got = (hi << 32) | lo
        if got >= 2 ** 63:
            got -= 2 ** 64
        assert got == value
