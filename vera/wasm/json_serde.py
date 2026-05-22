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
            map_store) → Any

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
# #573: map_alloc now returns a wrapper-ADT pointer, not a raw
# handle.  The signature accepts ``caller`` so the helper can call
# the exported ``$alloc`` and ``$register_wrapper`` to construct
# the wrapper in WASM memory.
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
        # #573: ``map_alloc`` is now ``_alloc_map_wrapper`` (in
        # ``vera/codegen/api.py``), which both allocates the host
        # dict AND emits an 8-byte wrapper ADT in WASM memory
        # registered with ``$register_wrapper``.  The returned
        # value is therefore a wrapper-ADT pointer, not a raw
        # handle.  This makes the JObject's i32 field type-
        # compatible with user-level ``map_get`` /
        # ``map_contains`` calls (which now expect wrapper
        # pointers and unwrap with ``i32.load offset=4`` before
        # the host dispatch).  GC reclaims the JObject's Map
        # entry from ``_map_store`` when the wrapper becomes
        # unreachable, just like a user-allocated Map.
        #
        # #692: each iteration's val_ptr is pushed onto the
        # shadow stack BEFORE the next iteration's recursive
        # ``write_json`` (which may GC).  Without this, the
        # Python dict (``map_dict``) holds val_ptrs as ints that
        # the conservative scan can't see; the WASM blocks they
        # point to would be freed by the very next sub-alloc.
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
    map_store: dict[int, Any],
) -> Any:
    """Read a Json ADT from WASM memory back to a Python value.

    Returns: None, bool, float, str, list, or dict.
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
                read_string, map_store,
            ))
        return items

    if tag == _TAG_JOBJECT:
        # #573: JObject's i32 field at offset 4 is now a wrapper-
        # ADT pointer, not a raw handle.  Wrapper layout: tag at
        # body[0], handle at body[4].  Unwrap before looking up
        # the dict in ``map_store``.
        #
        # #578: the in-heap handle field is tagged with bit 31
        # (so the conservative GC scan can't mistake it for a
        # heap pointer).  Mask with 0x7FFFFFFF to recover the
        # raw handle.  Mirrors the WAT-side ``_emit_unwrap_handle``
        # in ``vera/wasm/calls_containers.py``.
        wrapper_ptr = read_i32(caller, ptr + 4)
        handle = read_i32(caller, wrapper_ptr + 4) & 0x7FFFFFFF
        if handle not in map_store:
            import warnings
            warnings.warn(
                f"read_json: unknown JObject handle {handle} at pointer {ptr}; "
                "possible memory corruption or missing map allocation",
                RuntimeWarning,
                stacklevel=2,
            )
            return {}
        raw_map = map_store[handle]
        obj: dict[str, Any] = {}
        for k, v in raw_map.items():
            key_str = str(k)
            # v is an i32 Json heap pointer
            obj[key_str] = read_json(
                caller, v, read_i32, read_f64,
                read_string, map_store,
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
