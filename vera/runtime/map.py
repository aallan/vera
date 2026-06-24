"""Map<K, V> effect host bindings (§9.5).

Extracted verbatim from `execute()` in `vera/codegen/api.py` (#421).  The host
callbacks call the module-level heap helpers in `vera.runtime.heap`; the
value-type WASM dispatch table lives in `vera.runtime.collections`.
"""

from __future__ import annotations

import wasmtime

from vera.runtime.collections import _VAL_WASM_TYPES
from vera.runtime.heap import (
    _WRAP_KIND_MAP,
    _alloc_array_of_f64,
    _alloc_array_of_i32,
    _alloc_array_of_i64,
    _alloc_array_of_strings,
    _alloc_option_none,
    _alloc_option_some_f64,
    _alloc_option_some_i32,
    _alloc_option_some_i64,
    _alloc_option_some_string,
    _alloc_wrapper,
    _bkt_count,
    _bkt_raw_entries,
    _decode_column,
    _decode_field,
    _decode_map,
    _encode_map,
    _encode_raw,
    _map_lookup,
    _map_put,
    _read_wasm_string,
    _same_value_zero,
)


def register_map(linker: wasmtime.Linker, ops_used: set[str]) -> None:
    """Register the requested Map host functions on `linker`."""
    # map_new() → wrapper_ptr for an empty bucket-as-truth Map (#706).
    def host_map_new(caller: wasmtime.Caller) -> int:
        return _alloc_wrapper(caller, _WRAP_KIND_MAP, 0)

    linker.define_func(
        "vera", "map_new",
        wasmtime.FuncType([], [wasmtime.ValType.i32()]),
        host_map_new, access_caller=True,
    )

    # #706: every Map host import now takes the wrapper pointer
    # (``wp``) instead of an opaque handle, decodes the wrapper's
    # bucket into a transient Python dict, runs the operation, and —
    # for the copy-on-write ops — encodes a fresh wrapper + bucket.

    def _define_map_insert(kt: str, vt: str) -> None:
        name = f"map_insert$k{kt}_v{vt}"
        key_types = _VAL_WASM_TYPES[kt]
        val_types = _VAL_WASM_TYPES[vt]
        param_types = (
            [wasmtime.ValType.i32()]  # wrapper_ptr
            + key_types + val_types
        )
        ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

        if kt == "s" and vt == "s":
            def host_fn(
                caller: wasmtime.Caller,
                wp: int, kp: int, kl: int, vp: int, vl: int,
            ) -> int:
                k = _read_wasm_string(caller, kp, kl)
                v = _read_wasm_string(caller, vp, vl)
                new_d = _decode_map(caller, wp, kt, vt)
                _map_put(new_d, k, v)
                return _encode_map(caller, new_d, kt, vt)
        elif kt == "s":
            def host_fn(  # type: ignore[misc]
                caller: wasmtime.Caller,
                wp: int, kp: int, kl: int, v: int | float,
            ) -> int:
                k = _read_wasm_string(caller, kp, kl)
                new_d = _decode_map(caller, wp, kt, vt)
                _map_put(new_d, k, v)
                return _encode_map(caller, new_d, kt, vt)
        elif vt == "s":
            def host_fn(  # type: ignore[misc]
                caller: wasmtime.Caller,
                wp: int, k: int | float, vp: int, vl: int,
            ) -> int:
                v = _read_wasm_string(caller, vp, vl)
                new_d = _decode_map(caller, wp, kt, vt)
                _map_put(new_d, k, v)
                return _encode_map(caller, new_d, kt, vt)
        else:
            def host_fn(  # type: ignore[misc]
                caller: wasmtime.Caller,
                wp: int, k: int | float, v: int | float,
            ) -> int:
                new_d = _decode_map(caller, wp, kt, vt)
                _map_put(new_d, k, v)
                return _encode_map(caller, new_d, kt, vt)

        linker.define_func(
            "vera", name, ftype, host_fn, access_caller=True,
        )

    def _define_map_get(kt: str, vt: str) -> None:
        name = f"map_get$k{kt}_v{vt}"
        key_types = _VAL_WASM_TYPES[kt]
        param_types = [wasmtime.ValType.i32()] + key_types
        ftype = wasmtime.FuncType(
            param_types, [wasmtime.ValType.i32()],
        )

        def _make_option(
            caller: wasmtime.Caller, val: object,
        ) -> int:
            """Construct Option<V> on the WASM heap."""
            if val is None:
                return _alloc_option_none(caller)
            if vt == "i":
                assert isinstance(val, int)  # noqa: S101
                return _alloc_option_some_i64(caller, val)
            if vt == "f":
                assert isinstance(val, (int, float))  # noqa: S101
                return _alloc_option_some_f64(caller, float(val))
            if vt == "s":
                assert isinstance(val, str)  # noqa: S101
                return _alloc_option_some_string(caller, val)
            # i32 (Bool, Byte, ADT, Map handle)
            assert isinstance(val, int)  # noqa: S101
            return _alloc_option_some_i32(caller, val)

        if kt == "s":
            def host_fn(
                caller: wasmtime.Caller,
                wp: int, kp: int, kl: int,
            ) -> int:
                k = _read_wasm_string(caller, kp, kl)
                d = _decode_map(caller, wp, kt, vt)
                return _make_option(caller, _map_lookup(d, k))
        else:
            def host_fn(  # type: ignore[misc]
                caller: wasmtime.Caller,
                wp: int, k: int | float,
            ) -> int:
                d = _decode_map(caller, wp, kt, vt)
                return _make_option(caller, _map_lookup(d, k))

        linker.define_func(
            "vera", name, ftype, host_fn, access_caller=True,
        )

    def _define_map_contains(kt: str) -> None:
        name = f"map_contains$k{kt}"
        key_types = _VAL_WASM_TYPES[kt]
        param_types = [wasmtime.ValType.i32()] + key_types
        ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

        if kt == "s":
            def host_fn(
                caller: wasmtime.Caller,
                wp: int, kp: int, kl: int,
            ) -> int:
                k = _read_wasm_string(caller, kp, kl)
                return 1 if any(
                    _same_value_zero(k, x)
                    for x in _decode_column(caller, wp, kt, 4)
                ) else 0
        else:
            def host_fn(  # type: ignore[misc]
                caller: wasmtime.Caller,
                wp: int, k: int | float,
            ) -> int:
                return 1 if any(
                    _same_value_zero(k, x)
                    for x in _decode_column(caller, wp, kt, 4)
                ) else 0

        linker.define_func(
            "vera", name, ftype, host_fn, access_caller=True,
        )

    def _define_map_remove(kt: str) -> None:
        name = f"map_remove$k{kt}"
        key_types = _VAL_WASM_TYPES[kt]
        param_types = [wasmtime.ValType.i32()] + key_types
        ftype = wasmtime.FuncType(param_types, [wasmtime.ValType.i32()])

        # Structural rebuild: drop the matching key's slot and copy the
        # rest verbatim (vt not needed — value fields are opaque here).
        def _without(
            caller: wasmtime.Caller, wp: int, k: object,
        ) -> int:
            survivors = [
                (kb, vb)
                for kb, vb in _bkt_raw_entries(caller, wp)
                if not _same_value_zero(_decode_field(caller, kt, kb, 0), k)
            ]
            return _encode_raw(caller, _WRAP_KIND_MAP, survivors)

        if kt == "s":
            def host_fn(
                caller: wasmtime.Caller,
                wp: int, kp: int, kl: int,
            ) -> int:
                return _without(caller, wp, _read_wasm_string(caller, kp, kl))
        else:
            def host_fn(  # type: ignore[misc]
                caller: wasmtime.Caller,
                wp: int, k: int | float,
            ) -> int:
                return _without(caller, wp, k)

        linker.define_func(
            "vera", name, ftype, host_fn, access_caller=True,
        )

    # map_size(wp) → i64 (O(1) from the bucket header).
    def host_map_size(
        caller: wasmtime.Caller, wp: int,
    ) -> int:
        return _bkt_count(caller, wp)

    linker.define_func(
        "vera", "map_size",
        wasmtime.FuncType(
            [wasmtime.ValType.i32()], [wasmtime.ValType.i64()],
        ),
        host_map_size, access_caller=True,
    )

    def _define_map_keys(kt: str) -> None:
        name = f"map_keys$k{kt}"
        ftype = wasmtime.FuncType(
            [wasmtime.ValType.i32()],
            [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        )

        def host_fn(
            caller: wasmtime.Caller, wp: int,
        ) -> tuple[int, int]:
            keys = _decode_column(caller, wp, kt, 4)
            if kt == "s":
                return _alloc_array_of_strings(caller, keys)  # type: ignore[arg-type]
            if kt == "i":
                return _alloc_array_of_i64(caller, keys)  # type: ignore[arg-type]
            if kt == "f":
                return _alloc_array_of_f64(caller, keys)  # type: ignore[arg-type]
            return _alloc_array_of_i32(caller, keys)  # type: ignore[arg-type]

        linker.define_func(
            "vera", name, ftype, host_fn, access_caller=True,
        )

    def _define_map_values(vt: str) -> None:
        name = f"map_values$v{vt}"
        ftype = wasmtime.FuncType(
            [wasmtime.ValType.i32()],
            [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        )

        def host_fn(
            caller: wasmtime.Caller, wp: int,
        ) -> tuple[int, int]:
            vals = _decode_column(caller, wp, vt, 12)
            if vt == "s":
                return _alloc_array_of_strings(caller, vals)  # type: ignore[arg-type]
            if vt == "i":
                return _alloc_array_of_i64(caller, vals)  # type: ignore[arg-type]
            if vt == "f":
                return _alloc_array_of_f64(caller, vals)  # type: ignore[arg-type]
            return _alloc_array_of_i32(caller, vals)  # type: ignore[arg-type]

        linker.define_func(
            "vera", name, ftype, host_fn, access_caller=True,
        )

    # Register type-specific imports based on what the WAT uses.
    # Parse the import names from map_ops_used to determine types.
    for op_name in ops_used:
        if op_name.startswith("map_insert$"):
            # e.g. "map_insert$ki_vi"
            suffix = op_name[len("map_insert$"):]
            kt = suffix[1]  # after 'k'
            vt = suffix[4]  # after '_v'
            _define_map_insert(kt, vt)
        elif op_name.startswith("map_get$"):
            suffix = op_name[len("map_get$"):]
            kt = suffix[1]
            vt = suffix[4]
            _define_map_get(kt, vt)
        elif op_name.startswith("map_contains$"):
            suffix = op_name[len("map_contains$"):]
            kt = suffix[1]
            _define_map_contains(kt)
        elif op_name.startswith("map_remove$"):
            suffix = op_name[len("map_remove$"):]
            kt = suffix[1]
            _define_map_remove(kt)
        elif op_name.startswith("map_keys$"):
            suffix = op_name[len("map_keys$"):]
            kt = suffix[1]
            _define_map_keys(kt)
        elif op_name.startswith("map_values$"):
            suffix = op_name[len("map_values$"):]
            vt = suffix[1]
            _define_map_values(vt)
