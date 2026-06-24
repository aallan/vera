"""Shared collection-runtime constants (#421).

The value-type -> WASM-type dispatch table used by the Map and Set host
families when registering their per-element-type operations.
"""

from __future__ import annotations

import wasmtime

_VAL_WASM_TYPES = {
    "i": [wasmtime.ValType.i64()],
    "f": [wasmtime.ValType.f64()],
    "b": [wasmtime.ValType.i32()],
    "s": [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
}
