"""Decimal effect host bindings (§9.6).

Extracted from `execute()` in `vera/codegen/api.py` (#421).  Decimal is the one
host family that keeps a value-typed Python store (`decimal_store`, created in
`execute()` so the shared `host_decref_handle` GC hook can close over it);
`register_decimal` registers it in `host_store_refs` and wires the ops.
"""

from __future__ import annotations

from decimal import Decimal as PyDecimal
from decimal import InvalidOperation

import wasmtime

from vera.runtime.heap import (
    _WRAP_KIND_DECIMAL,
    _alloc_option_none,
    _alloc_option_some_i32,
    _alloc_ordering,
    _alloc_string,
    _read_wasm_string,
    _wrap_handle,
)


def register_decimal(
    linker: wasmtime.Linker,
    ops_used: set[str],
    decimal_store: dict[int, PyDecimal],
    host_store_refs: dict[str, dict[int, object]],
) -> None:
    """Register the requested Decimal host functions on `linker`."""
    _decimal_next_handle = [1]
    # Decimal keeps a value-typed Python store — the only host store
    # remaining after #706 moved Map / Set to bucket-as-truth.
    host_store_refs["decimal"] = decimal_store  # type: ignore[assignment]
    # #695/#706: Decimal is intentionally EXEMPT from the bucket-as-
    # truth migration.  ``PyDecimal`` is value-typed (immutable
    # digit/sign/exponent attributes, no WASM heap pointers inside
    # the stored object), so the silent-UAF window that affects
    # Map<K, T_heap> and Set<T_heap> cannot occur for Decimal.  Its
    # wrapper keeps the #573 tagged-handle layout (initialised by
    # ``_emit_wrap_handle`` / JS ``wrapHandle``), leaves ``bucket_ptr``
    # 0, and ``host_attach_bucket`` accepts only kind=3.

    def _decimal_alloc(d: PyDecimal) -> int:
        h = _decimal_next_handle[0]
        _decimal_next_handle[0] = h + 1
        decimal_store[h] = d
        return h

    if "decimal_from_int" in ops_used:
        def host_decimal_from_int(
            _caller: wasmtime.Caller, v: int,
        ) -> int:
            return _decimal_alloc(PyDecimal(v))
        linker.define_func(
            "vera", "decimal_from_int",
            wasmtime.FuncType([wasmtime.ValType.i64()],
                              [wasmtime.ValType.i32()]),
            host_decimal_from_int, access_caller=True,
        )

    if "decimal_from_float" in ops_used:
        def host_decimal_from_float(
            _caller: wasmtime.Caller, v: float,
        ) -> int:
            return _decimal_alloc(PyDecimal(str(v)))
        linker.define_func(
            "vera", "decimal_from_float",
            wasmtime.FuncType([wasmtime.ValType.f64()],
                              [wasmtime.ValType.i32()]),
            host_decimal_from_float, access_caller=True,
        )

    if "decimal_from_string" in ops_used:
        def host_decimal_from_string(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            s = _read_wasm_string(caller, ptr, length)
            try:
                d = PyDecimal(s)
                # #573 phase 3: wrap the Decimal handle so the
                # Option<Decimal>'s Some payload is a wrapper
                # pointer (matching what every other Decimal-
                # producing op now returns).
                raw = _decimal_alloc(d)
                wrapped = _wrap_handle(
                    caller, _WRAP_KIND_DECIMAL, raw,
                )
                return _alloc_option_some_i32(caller, wrapped)
            except InvalidOperation:
                return _alloc_option_none(caller)
        linker.define_func(
            "vera", "decimal_from_string",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_from_string, access_caller=True,
        )

    if "decimal_to_string" in ops_used:
        def host_decimal_to_string(
            caller: wasmtime.Caller, h: int,
        ) -> tuple[int, int]:
            s = str(decimal_store[h])
            return _alloc_string(caller, s)
        linker.define_func(
            "vera", "decimal_to_string",
            wasmtime.FuncType([wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()]),
            host_decimal_to_string, access_caller=True,
        )

    if "decimal_to_float" in ops_used:
        def host_decimal_to_float(
            _caller: wasmtime.Caller, h: int,
        ) -> float:
            return float(decimal_store[h])
        linker.define_func(
            "vera", "decimal_to_float",
            wasmtime.FuncType([wasmtime.ValType.i32()],
                              [wasmtime.ValType.f64()]),
            host_decimal_to_float, access_caller=True,
        )

    if "decimal_add" in ops_used:
        def host_decimal_add(
            _caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            return _decimal_alloc(decimal_store[a] + decimal_store[b])
        linker.define_func(
            "vera", "decimal_add",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_add, access_caller=True,
        )

    if "decimal_sub" in ops_used:
        def host_decimal_sub(
            _caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            return _decimal_alloc(decimal_store[a] - decimal_store[b])
        linker.define_func(
            "vera", "decimal_sub",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_sub, access_caller=True,
        )

    if "decimal_mul" in ops_used:
        def host_decimal_mul(
            _caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            return _decimal_alloc(decimal_store[a] * decimal_store[b])
        linker.define_func(
            "vera", "decimal_mul",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_mul, access_caller=True,
        )

    if "decimal_div" in ops_used:
        def host_decimal_div(
            caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            # #573 phase 3: ``a`` and ``b`` are raw handles
            # (the WASM-side translator unwraps wrapper
            # pointers before this call, matching the
            # pattern for every other Decimal binary op).
            # The result handle is wrapped here because the
            # host constructs ``Option<Decimal>`` internally
            # — its Some payload must be a wrapper pointer
            # to match what user code post-match expects.
            divisor = decimal_store[b]
            if divisor == 0:
                return _alloc_option_none(caller)
            raw = _decimal_alloc(decimal_store[a] / divisor)
            wrapped = _wrap_handle(
                caller, _WRAP_KIND_DECIMAL, raw,
            )
            return _alloc_option_some_i32(caller, wrapped)
        linker.define_func(
            "vera", "decimal_div",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_div, access_caller=True,
        )

    if "decimal_neg" in ops_used:
        def host_decimal_neg(
            _caller: wasmtime.Caller, h: int,
        ) -> int:
            return _decimal_alloc(-decimal_store[h])
        linker.define_func(
            "vera", "decimal_neg",
            wasmtime.FuncType([wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_neg, access_caller=True,
        )

    if "decimal_compare" in ops_used:
        def host_decimal_compare(
            caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            da, db = decimal_store[a], decimal_store[b]
            if da < db:
                tag = 0  # Less
            elif da == db:
                tag = 1  # Equal
            else:
                tag = 2  # Greater
            return _alloc_ordering(caller, tag)
        linker.define_func(
            "vera", "decimal_compare",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_compare, access_caller=True,
        )

    if "decimal_eq" in ops_used:
        def host_decimal_eq(
            _caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            return 1 if decimal_store[a] == decimal_store[b] else 0
        linker.define_func(
            "vera", "decimal_eq",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_eq, access_caller=True,
        )

    if "decimal_round" in ops_used:
        def host_decimal_round(
            _caller: wasmtime.Caller, h: int, places: int,
        ) -> int:
            d = decimal_store[h]
            # Use quantize for precise rounding
            q = PyDecimal(10) ** -places
            try:
                return _decimal_alloc(d.quantize(q))
            except InvalidOperation:
                # Extreme exponent — return original value unchanged
                return _decimal_alloc(d)
        linker.define_func(
            "vera", "decimal_round",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i64()],
                              [wasmtime.ValType.i32()]),
            host_decimal_round, access_caller=True,
        )

    if "decimal_abs" in ops_used:
        def host_decimal_abs(
            _caller: wasmtime.Caller, h: int,
        ) -> int:
            return _decimal_alloc(abs(decimal_store[h]))
        linker.define_func(
            "vera", "decimal_abs",
            wasmtime.FuncType([wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_abs, access_caller=True,
        )
