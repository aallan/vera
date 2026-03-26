"""WASM memory marshalling for HtmlNode ADT.

Provides bidirectional conversion between Python HTML node dicts
and the WASM HtmlNode ADT memory representation.  Used by host
function bindings in vera.codegen.api.

Write direction (Python -> WASM):
  write_html(caller, alloc, write_i32, alloc_string, map_alloc,
             node) -> int (heap pointer)

Read direction (WASM -> Python):
  read_html(caller, ptr, read_i32, read_string,
            map_store) -> dict

HtmlNode ADT layouts (from prelude injection -> registration.py):
  HtmlElement(String, Map<String,String>, Array<HtmlNode>)
    tag=0  String at +4, Map handle at +12, Array(ptr,len) at +16  total=24
  HtmlText(String)
    tag=1  String at +4  total=12 (padded to 16 for 8-byte alignment)
  HtmlComment(String)
    tag=2  String at +4  total=12 (padded to 16 for 8-byte alignment)

Python HtmlNode representation:
  {"tag": "element", "name": "div", "attrs": {"class": "foo"}, "children": [...]}
  {"tag": "text", "content": "hello"}
  {"tag": "comment", "content": "<!-- ... -->"}
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import wasmtime

# Type aliases for host function callbacks
AllocFn = Callable[[wasmtime.Caller, int], int]
WriteI32Fn = Callable[[wasmtime.Caller, int, int], None]
AllocStringFn = Callable[[wasmtime.Caller, str], tuple[int, int]]
MapAllocFn = Callable[[dict[object, object]], int]
ReadI32Fn = Callable[[wasmtime.Caller, int], int]
ReadStringFn = Callable[[wasmtime.Caller, int, int], str]

# Tag constants matching ADT declaration order
_TAG_HTML_ELEMENT = 0
_TAG_HTML_TEXT = 1
_TAG_HTML_COMMENT = 2


def write_html(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    alloc_string: AllocStringFn,
    map_alloc: MapAllocFn,
    node: dict[str, Any],
) -> int:
    """Write a Python HTML node dict to WASM memory as an HtmlNode ADT.

    Returns the heap pointer to the allocated HtmlNode.
    """
    tag = node.get("tag", "text")

    if tag == "element":
        # HtmlElement(String, Map<String,String>, Array<HtmlNode>)
        # tag=0, String(name) at +4, Map handle at +12, Array at +16, total=24
        name = node.get("name", "")
        attrs = node.get("attrs", {})
        children = node.get("children", [])

        # Allocate name string
        name_ptr, name_len = alloc_string(caller, name)

        # Allocate Map<String, String> for attributes.
        # Keys and values are Python strings — the Map host runtime
        # stores Python values and converts to WASM on access (via
        # map_get which calls _alloc_option_some_string).
        map_dict: dict[object, object] = {}
        for k, v in attrs.items():
            map_dict[str(k)] = str(v)
        handle = map_alloc(map_dict)

        # Allocate children array
        child_count = len(children)
        if child_count > 0:
            arr_ptr = alloc(caller, child_count * 4)
            for i, child in enumerate(children):
                child_ptr = write_html(
                    caller, alloc, write_i32, alloc_string,
                    map_alloc, child,
                )
                write_i32(caller, arr_ptr + i * 4, child_ptr)
        else:
            arr_ptr = 0

        # Allocate the HtmlElement node
        ptr = alloc(caller, 24)
        write_i32(caller, ptr, _TAG_HTML_ELEMENT)
        write_i32(caller, ptr + 4, name_ptr)
        write_i32(caller, ptr + 8, name_len)
        write_i32(caller, ptr + 12, handle)
        write_i32(caller, ptr + 16, arr_ptr)
        write_i32(caller, ptr + 20, child_count)
        return ptr

    if tag == "comment":
        # HtmlComment(String) — tag=2, String at +4, total=16
        content = node.get("content", "")
        s_ptr, s_len = alloc_string(caller, content)
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, _TAG_HTML_COMMENT)
        write_i32(caller, ptr + 4, s_ptr)
        write_i32(caller, ptr + 8, s_len)
        return ptr

    # Default: HtmlText(String) — tag=1, String at +4, total=16
    content = node.get("content", "")
    s_ptr, s_len = alloc_string(caller, content)
    ptr = alloc(caller, 16)
    write_i32(caller, ptr, _TAG_HTML_TEXT)
    write_i32(caller, ptr + 4, s_ptr)
    write_i32(caller, ptr + 8, s_len)
    return ptr


def read_html(
    caller: wasmtime.Caller,
    ptr: int,
    read_i32: ReadI32Fn,
    read_string: ReadStringFn,
    map_store: dict[int, Any],
) -> dict[str, Any]:
    """Read an HtmlNode ADT from WASM memory back to a Python dict.

    Returns a dict with 'tag' key indicating the node type.
    """
    tag = read_i32(caller, ptr)

    if tag == _TAG_HTML_ELEMENT:
        # String(name) at +4, Map handle at +12, Array at +16
        name_ptr = read_i32(caller, ptr + 4)
        name_len = read_i32(caller, ptr + 8)
        name = read_string(caller, name_ptr, name_len)
        handle = read_i32(caller, ptr + 12)
        arr_ptr = read_i32(caller, ptr + 16)
        arr_len = read_i32(caller, ptr + 20)

        # Read attributes from map store.
        # Values are Python strings (stored by write_html and by the
        # Map host runtime for Map<String, String>).
        attrs: dict[str, str] = {}
        if handle in map_store:
            raw_map = map_store[handle]
            for k, v in raw_map.items():
                attrs[str(k)] = str(v)

        # Read children
        children: list[dict[str, Any]] = []
        for i in range(arr_len):
            child_ptr = read_i32(caller, arr_ptr + i * 4)
            children.append(read_html(
                caller, child_ptr, read_i32, read_string, map_store,
            ))

        return {
            "tag": "element",
            "name": name,
            "attrs": attrs,
            "children": children,
        }

    if tag == _TAG_HTML_COMMENT:
        s_ptr = read_i32(caller, ptr + 4)
        s_len = read_i32(caller, ptr + 8)
        content = read_string(caller, s_ptr, s_len)
        return {"tag": "comment", "content": content}

    if tag == _TAG_HTML_TEXT:
        s_ptr = read_i32(caller, ptr + 4)
        s_len = read_i32(caller, ptr + 8)
        content = read_string(caller, s_ptr, s_len)
        return {"tag": "text", "content": content}

    import warnings
    warnings.warn(
        f"read_html: unknown tag {tag} at pointer {ptr}; "
        "possible memory corruption or unsupported HtmlNode layout",
        RuntimeWarning,
        stacklevel=2,
    )
    return {"tag": "text", "content": ""}
