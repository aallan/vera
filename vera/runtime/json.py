"""JSON effect host bindings (JSON effect §9.7.5).

Extracted verbatim from `execute()` in `vera/codegen/api.py` (#421);
the host callbacks call the module-level heap helpers in
`vera.runtime.heap` instead of closing over `execute()` locals.
"""

from __future__ import annotations

import wasmtime

from vera.runtime.heap import (
    _ShadowGuard,
    _alloc_map_wrapper,
    _alloc_result_err_string,
    _alloc_result_ok_i32,
    _alloc_string,
    _call_alloc,
    _decode_jobject,
    _read_f64,
    _read_i32,
    _read_wasm_string,
    _write_f64,
    _write_i32,
)


def register_json(linker: wasmtime.Linker, ops_used: set[str]) -> None:
    """Register the requested JSON host functions on `linker`."""
    import json as _json

    from vera.wasm.json_serde import read_json, write_json

    if "json_parse" in ops_used:
        def host_json_parse(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            text = _read_wasm_string(caller, ptr, length)
            try:
                parsed = _json.loads(text)
            except (ValueError, TypeError) as exc:
                return _alloc_result_err_string(caller, str(exc))
            # #692: hold the shadow-stack window open across the
            # full tree marshalling AND the final Result.Ok
            # wrapper alloc.  ``guard.__exit__`` restores
            # ``$gc_sp`` on the way out — pops everything we
            # pushed.
            with _ShadowGuard(caller) as guard:
                json_ptr = write_json(
                    caller, _call_alloc, _write_i32, _write_f64,
                    _alloc_string, _alloc_map_wrapper, guard, parsed,
                )
                # Push the tree root before the Result.Ok alloc —
                # that alloc could trigger GC and free the
                # otherwise-unrooted tree.
                guard.push(json_ptr)
                return _alloc_result_ok_i32(caller, json_ptr)

        linker.define_func(
            "vera", "json_parse",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_json_parse, access_caller=True,
        )

    if "json_stringify" in ops_used:
        def host_json_stringify(
            caller: wasmtime.Caller, ptr: int,
        ) -> tuple[int, int]:
            value = read_json(
                caller, ptr, _read_i32, _read_f64,
                _read_wasm_string, _decode_jobject,
            )
            # Note: json.dumps rejects NaN/Infinity by default
            # (raises ValueError).  This matches the JSON spec
            # (RFC 8259) which forbids these values.  The JS
            # runtime's JSON.stringify outputs "null" for them
            # instead.  Both behaviours are acceptable: Vera's
            # JNumber wraps Float64, so users should guard against
            # NaN/Infinity before serialising.
            text = _json.dumps(
                value, ensure_ascii=False, allow_nan=False,
            )
            return _alloc_string(caller, text)

        linker.define_func(
            "vera", "json_stringify",
            wasmtime.FuncType(
                [wasmtime.ValType.i32()],
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
            ),
            host_json_stringify, access_caller=True,
        )
