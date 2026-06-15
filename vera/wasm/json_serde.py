"""WASM memory marshalling for Json ADT.

Provides bidirectional conversion between Python JSON values
(dict, list, str, float, bool, None) and the WASM Json ADT
memory representation.  Used by host function bindings in
vera.codegen.api.

Write direction (Python → WASM):
  write_json(caller, alloc, write_i32, write_f64, alloc_string,
             map_alloc, value) → int (heap pointer)

Read direction (WASM → Python):
  read_json(caller, ptr, read_i32, read_f64, read_string,
            decode_jobject) → Any

Json ADT layouts (from prelude injection → registration.py):
  JNull                        tag=0  ()               total=8
  JBool(Bool)                  tag=1  (4, i32)         total=8
  JNumber(Float64)             tag=2  (8, f64)         total=16
  JString(String)              tag=3  (4, i32_pair)    total=16
  JArray(Array<Json>)          tag=4  (4, i32_pair)    total=16
  JObject(Map<String, Json>)   tag=5  (4, i32)         total=8
"""

from __future__ import annotations

import struct
from collections.abc import Callable
from typing import Any

import wasmtime

# Type aliases for host function callbacks
AllocFn = Callable[[wasmtime.Caller, int], int]
WriteI32Fn = Callable[[wasmtime.Caller, int, int], None]
WriteF64Fn = Callable[[wasmtime.Caller, int, float], None]
AllocStringFn = Callable[[wasmtime.Caller, str], tuple[int, int]]
# #706: map_alloc is ``_alloc_map_wrapper`` — it encodes the Python
# dict into a fresh bucket-as-truth wrapper and returns the wrapper
# pointer (no host store, no wrap-table registration).  It accepts
# ``caller`` so it can call the exported ``$alloc`` to build the
# wrapper + bucket in WASM memory.
MapAllocFn = Callable[[wasmtime.Caller, dict[object, object]], int]
ReadI32Fn = Callable[[wasmtime.Caller, int], int]
ReadF64Fn = Callable[[wasmtime.Caller, int], float]
ReadStringFn = Callable[[wasmtime.Caller, int, int], str]

# Tag constants matching prelude ADT declaration order
_TAG_JNULL = 0
_TAG_JBOOL = 1
_TAG_JNUMBER = 2
_TAG_JSTRING = 3
_TAG_JARRAY = 4
_TAG_JOBJECT = 5


def write_json(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    write_f64: WriteF64Fn,
    alloc_string: AllocStringFn,
    map_alloc: MapAllocFn,
    guard: Any,
    value: Any,
) -> int:
    """Write a Python JSON value to WASM memory as a Json ADT.

    Returns the heap pointer to the allocated Json node.

    *guard* is a ``_ShadowGuard`` (defined in
    ``vera.codegen.api``).  Intermediate WASM heap pointers
    (string body, array backing, map wrapper) are pushed onto
    its shadow-stack window before any subsequent alloc that
    could trigger ``$gc_collect``.  See #692 + the analogous
    notes in ``html_serde.write_html`` for the bug class.

    The returned root pointer is NOT pushed — the caller is
    responsible for rooting it before the next alloc.
    """
    if value is None:
        # JNull — tag=0, total=8.  Single alloc, no cross-pointer
        # holding, no rooting needed.
        ptr = alloc(caller, 8)
        write_i32(caller, ptr, _TAG_JNULL)
        return ptr

    if isinstance(value, bool):
        # JBool(Bool) — tag=1, i32 at offset 4, total=8.  Single
        # alloc, no rooting needed.
        ptr = alloc(caller, 8)
        write_i32(caller, ptr, _TAG_JBOOL)
        write_i32(caller, ptr + 4, 1 if value else 0)
        return ptr

    if isinstance(value, (int, float)):
        # JNumber(Float64) — tag=2, f64 at offset 8, total=16.
        # Single alloc, no rooting needed.
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, _TAG_JNUMBER)
        write_f64(caller, ptr + 8, float(value))
        return ptr

    if isinstance(value, str):
        # JString(String) — tag=3, i32_pair at offset 4, total=16.
        # Allocate the string FIRST and root it before the body
        # alloc; the original order (body alloc then string alloc)
        # could trigger GC mid-construction while the body is in
        # a Python local with only the tag written.
        s_ptr, s_len = alloc_string(caller, value)
        if s_ptr != 0:
            guard.push(s_ptr)
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, _TAG_JSTRING)
        write_i32(caller, ptr + 4, s_ptr)
        write_i32(caller, ptr + 8, s_len)
        return ptr

    if isinstance(value, list):
        # JArray(Array<Json>) — tag=4, i32_pair at offset 4,
        # total=16.  Root arr_ptr before recursing into children
        # (each sub-write may trigger GC) and across the final
        # body alloc.  Child pointers become reachable via the
        # rooted arr_ptr's slots as soon as we ``write_i32`` them.
        count = len(value)
        if count > 0:
            arr_ptr = alloc(caller, count * 4)
            guard.push(arr_ptr)
            for i, elem in enumerate(value):
                elem_ptr = write_json(
                    caller, alloc, write_i32, write_f64,
                    alloc_string, map_alloc, guard, elem,
                )
                write_i32(caller, arr_ptr + i * 4, elem_ptr)
        else:
            arr_ptr = 0
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, _TAG_JARRAY)
        write_i32(caller, ptr + 4, arr_ptr)
        write_i32(caller, ptr + 8, count)
        return ptr

    if isinstance(value, dict):
        # JObject(Map<String, Json>) — tag=5, i32 at offset 4, total=8
        # Create a Map<String, Json> using the host map store.
        # Keys are stored as Python strings (matching map_contains$ks
        # which reads WASM strings and compares against Python strings).
        # Values are i32 Json heap pointers.
        #
        # #706: ``map_alloc`` is ``_alloc_map_wrapper`` (in
        # ``vera/codegen/api.py``), which encodes this Python dict
        # into a fresh bucket-as-truth wrapper + bucket and returns
        # the wrapper pointer.  That makes the JObject's i32 field
        # type-compatible with user-level ``map_get`` /
        # ``map_contains`` calls, which take the wrapper pointer
        # directly.  The JObject's Map is reclaimed by ordinary
        # mark-sweep when the wrapper becomes unreachable — there is
        # no host store to evict.
        #
        # #692: each iteration's val_ptr is pushed onto the
        # shadow stack BEFORE the next iteration's recursive
        # ``write_json`` (which may GC).  Without this, the
        # Python dict (``map_dict``) holds val_ptrs as ints that
        # the conservative scan can't see; the WASM blocks they
        # point to would be freed by the very next sub-alloc.
        #
        # Exception-safety note: if a recursive ``write_json``
        # raises mid-loop, the outer ``__exit__`` resets
        # ``$gc_sp`` and pops every prior ``val_ptr`` push.
        # ``map_dict`` still holds those ints as plain Python
        # values when the exception unwinds — but that's safe:
        # the function exits via the raise BEFORE the
        # ``map_alloc(caller, map_dict)`` call below, so the
        # stale ints never reach WASM.  A future maintainer
        # should NOT try to recover ``map_dict`` partial state
        # — the val_ptrs are guaranteed-invalid after the
        # guard exit.
        map_dict: dict[object, object] = {}
        for k, v in value.items():
            val_ptr = write_json(
                caller, alloc, write_i32, write_f64,
                alloc_string, map_alloc, guard, v,
            )
            guard.push(val_ptr)
            map_dict[str(k)] = val_ptr
        wrapper_ptr = map_alloc(caller, map_dict)
        guard.push(wrapper_ptr)
        ptr = alloc(caller, 8)
        write_i32(caller, ptr, _TAG_JOBJECT)
        write_i32(caller, ptr + 4, wrapper_ptr)
        return ptr

    # Fallback: treat as string
    return write_json(
        caller, alloc, write_i32, write_f64,
        alloc_string, map_alloc, guard, str(value),
    )


def read_json(
    caller: wasmtime.Caller,
    ptr: int,
    read_i32: ReadI32Fn,
    read_f64: ReadF64Fn,
    read_string: ReadStringFn,
    decode_jobject: "Callable[[wasmtime.Caller, int], dict[Any, Any]]",
) -> Any:
    """Read a Json ADT from WASM memory back to a Python value.

    Returns: None, bool, float, str, list, or dict.

    #706: ``decode_jobject(caller, wrapper_ptr)`` decodes a JObject's
    ``Map<String, Json>`` from its bucket-as-truth wrapper (there is no
    ``_map_store`` to look up by handle anymore).
    """
    tag = read_i32(caller, ptr)

    if tag == _TAG_JNULL:
        return None

    if tag == _TAG_JBOOL:
        return read_i32(caller, ptr + 4) != 0

    if tag == _TAG_JNUMBER:
        return read_f64(caller, ptr + 8)

    if tag == _TAG_JSTRING:
        s_ptr = read_i32(caller, ptr + 4)
        s_len = read_i32(caller, ptr + 8)
        return read_string(caller, s_ptr, s_len)

    if tag == _TAG_JARRAY:
        arr_ptr = read_i32(caller, ptr + 4)
        arr_len = read_i32(caller, ptr + 8)
        items: list[Any] = []
        for i in range(arr_len):
            elem_ptr = read_i32(caller, arr_ptr + i * 4)
            items.append(read_json(
                caller, elem_ptr, read_i32, read_f64,
                read_string, decode_jobject,
            ))
        return items

    if tag == _TAG_JOBJECT:
        # #706: JObject's i32 field at offset 4 is a Map wrapper
        # pointer whose bucket IS the map (bucket-as-truth).  Decode
        # the ``Map<String, Json>`` directly from the bucket — the
        # values are i32 Json heap pointers.
        wrapper_ptr = read_i32(caller, ptr + 4)
        raw_map = decode_jobject(caller, wrapper_ptr)
        obj: dict[str, Any] = {}
        for k, v in raw_map.items():
            obj[str(k)] = read_json(
                caller, int(v), read_i32, read_f64,
                read_string, decode_jobject,
            )
        return obj

    import warnings
    warnings.warn(
        f"read_json: unknown tag {tag} at pointer {ptr}; "
        "possible memory corruption or unsupported Json layout",
        RuntimeWarning,
        stacklevel=2,
    )
    return None  # Unknown tag — should not happen
