"""Set<T> effect host bindings (§9.5).

Extracted verbatim from `execute()` in `vera/codegen/api.py` (#421).  The host
callbacks call the module-level heap helpers in `vera.runtime.heap`; the
value-type WASM dispatch table lives in `vera.runtime.collections`.
"""

from __future__ import annotations

import wasmtime

from vera.runtime.collections import _VAL_WASM_TYPES
from vera.runtime.heap import (
    _WRAP_KIND_SET,
    _alloc_array_of_f64,
    _alloc_array_of_i32,
    _alloc_array_of_i64,
    _alloc_array_of_strings,
    _alloc_wrapper,
    _bkt_count,
    _bkt_raw_entries,
    _decode_column,
    _decode_field,
    _decode_set,
    _encode_raw,
    _encode_set,
    _read_wasm_string,
    _same_value_zero,
    _set_add_svz,
)


def register_set(linker: wasmtime.Linker, ops_used: set[str]) -> None:
    """Register the requested Set host functions on `linker`."""
    # set_new() → wrapper_ptr for an empty bucket-as-truth Set (#706).
    def host_set_new(caller: wasmtime.Caller) -> int:
        return _alloc_wrapper(caller, _WRAP_KIND_SET, 0)

    linker.define_func(
        "vera", "set_new",
        wasmtime.FuncType([], [wasmtime.ValType.i32()]),
        host_set_new, access_caller=True,
    )

    # #706: every Set host import takes the wrapper pointer (``wp``)
    # and goes through the bucket codec — the element lives in the
    # slot's key field, the val field is unused.

    def _define_set_add(et: str) -> None:
        name = f"set_add$e{et}"
        elem_types = _VAL_WASM_TYPES[et]
        param_types = [wasmtime.ValType.i32()] + elem_types
        ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

        if et == "s":
            def host_fn(
                caller: wasmtime.Caller, wp: int, ep: int, el: int,
            ) -> int:
                s = _decode_set(caller, wp, et)
                _set_add_svz(s, _read_wasm_string(caller, ep, el))
                return _encode_set(caller, s, et)
        else:
            def host_fn(  # type: ignore[misc]
                caller: wasmtime.Caller, wp: int, e: int | float,
            ) -> int:
                s = _decode_set(caller, wp, et)
                _set_add_svz(s, e)
                return _encode_set(caller, s, et)

        linker.define_func(
            "vera", name, ftype, host_fn, access_caller=True,
        )

    def _define_set_contains(et: str) -> None:
        name = f"set_contains$e{et}"
        elem_types = _VAL_WASM_TYPES[et]
        param_types = [wasmtime.ValType.i32()] + elem_types
        ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

        if et == "s":
            def host_fn(
                caller: wasmtime.Caller, wp: int, ep: int, el: int,
            ) -> int:
                e = _read_wasm_string(caller, ep, el)
                return 1 if any(
                    _same_value_zero(e, x)
                    for x in _decode_column(caller, wp, et, 4)
                ) else 0
        else:
            def host_fn(  # type: ignore[misc]
                caller: wasmtime.Caller, wp: int, e: int | float,
            ) -> int:
                return 1 if any(
                    _same_value_zero(e, x)
                    for x in _decode_column(caller, wp, et, 4)
                ) else 0

        linker.define_func(
            "vera", name, ftype, host_fn, access_caller=True,
        )

    def _define_set_remove(et: str) -> None:
        name = f"set_remove$e{et}"
        elem_types = _VAL_WASM_TYPES[et]
        param_types = [wasmtime.ValType.i32()] + elem_types
        ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

        # Structural rebuild dropping the matching element (the elem
        # lives in the key field; val field is copied verbatim).
        def _without(
            caller: wasmtime.Caller, wp: int, e: object,
        ) -> int:
            survivors = [
                (kb, vb)
                for kb, vb in _bkt_raw_entries(caller, wp)
                if not _same_value_zero(_decode_field(caller, et, kb, 0), e)
            ]
            return _encode_raw(caller, _WRAP_KIND_SET, survivors)

        if et == "s":
            def host_fn(
                caller: wasmtime.Caller, wp: int, ep: int, el: int,
            ) -> int:
                return _without(caller, wp, _read_wasm_string(caller, ep, el))
        else:
            def host_fn(  # type: ignore[misc]
                caller: wasmtime.Caller, wp: int, e: int | float,
            ) -> int:
                return _without(caller, wp, e)

        linker.define_func(
            "vera", name, ftype, host_fn, access_caller=True,
        )

    # set_size(wp) → i64 (O(1) from the bucket header).
    def host_set_size(caller: wasmtime.Caller, wp: int) -> int:
        return _bkt_count(caller, wp)

    linker.define_func(
        "vera", "set_size",
        wasmtime.FuncType(
            [wasmtime.ValType.i32()],
            [wasmtime.ValType.i64()],
        ),
        host_set_size, access_caller=True,
    )

    def _define_set_to_array(et: str) -> None:
        name = f"set_to_array$e{et}"
        ftype = wasmtime.FuncType(
            [wasmtime.ValType.i32()],
            [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        )

        def host_fn(
            caller: wasmtime.Caller, wp: int,
        ) -> tuple[int, int]:
            elems = _decode_column(caller, wp, et, 4)
            if et == "s":
                return _alloc_array_of_strings(caller, elems)  # type: ignore[arg-type]
            if et == "i":
                return _alloc_array_of_i64(caller, elems)  # type: ignore[arg-type]
            if et == "f":
                return _alloc_array_of_f64(caller, elems)  # type: ignore[arg-type]
            return _alloc_array_of_i32(caller, elems)  # type: ignore[arg-type]

        linker.define_func(
            "vera", name, ftype, host_fn, access_caller=True,
        )

    # Register type-specific imports based on what the WAT uses.
    for op_name in ops_used:
        if op_name.startswith("set_add$"):
            et = op_name[len("set_add$e"):]
            _define_set_add(et)
        elif op_name.startswith("set_contains$"):
            et = op_name[len("set_contains$e"):]
            _define_set_contains(et)
        elif op_name.startswith("set_remove$"):
            et = op_name[len("set_remove$e"):]
            _define_set_remove(et)
        elif op_name.startswith("set_to_array$"):
            et = op_name[len("set_to_array$e"):]
            _define_set_to_array(et)
