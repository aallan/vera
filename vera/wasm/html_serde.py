"""WASM memory marshalling for HtmlNode ADT.

Provides bidirectional conversion between Python HTML node dicts
and the WASM HtmlNode ADT memory representation.  Used by host
function bindings in vera.codegen.api.

Write direction (Python -> WASM):
  write_html(caller, alloc, write_i32, alloc_string, map_alloc,
             guard, node) -> int (heap pointer)

Read direction (WASM -> Python):
  read_html(caller, ptr, read_i32, read_string,
            decode_attrs) -> dict

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

#692: ``write_html`` takes a ``guard`` parameter — a context-manager
helper from ``vera.codegen.api._ShadowGuard`` — that pushes
intermediate WASM heap pointers (``name_ptr``, ``wrapper_ptr``,
``arr_ptr``) onto the GC shadow stack across sub-tree recursion and
the final node body alloc.  Without this rooting, an alloc that
triggers ``$gc_collect`` mid-walk reclaims those Python-held
pointers and a subsequent write into freed memory corrupts the
free list (concrete trap: ``Out-of-bounds memory access`` at
``0xfffffffd`` from inside ``$alloc``'s free-list traversal).
"""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, Any

import wasmtime

if TYPE_CHECKING:
    # Forward reference: ``_ShadowGuard`` is defined inside
    # ``compile_to_wasm``'s closure in ``vera/codegen/api.py``.
    # Typing as a structural callable (``push(int) -> int``) keeps
    # this module free of an api->wasm import cycle.
    class _Guard:
        def push(self, ptr: int) -> int: ...


# Type aliases for host function callbacks
AllocFn = Callable[[wasmtime.Caller, int], int]
WriteI32Fn = Callable[[wasmtime.Caller, int, int], None]
AllocStringFn = Callable[[wasmtime.Caller, str], tuple[int, int]]
# #573: map_alloc returns a wrapper-ADT pointer.  See json_serde.py
# for the long version; the HTML side mirrors it for HtmlElement
# attrs.
MapAllocFn = Callable[[wasmtime.Caller, dict[object, object]], int]
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
    guard: Any,
    node: dict[str, Any],
) -> int:
    """Write a Python HTML node dict to WASM memory as an HtmlNode ADT.

    Returns the heap pointer to the allocated HtmlNode.

    *guard* is a ``_ShadowGuard`` (defined in
    ``vera.codegen.api``) — an active context manager that owns
    the WASM shadow-stack window for this walk.  Intermediate
    pointers (name, wrapper, arr) are pushed onto it via
    ``guard.push(ptr)`` before any subsequent alloc that could
    trigger ``$gc_collect``.  See module docstring + #692.

    The returned root pointer is NOT pushed onto the guard — the
    caller (parent ``write_html`` writing into its child array,
    or ``host_html_parse`` allocating the ``Result.Ok`` wrapper)
    is responsible for rooting it before the next alloc.  This
    keeps the contract symmetric across recursion depth.
    """
    tag = node.get("tag", "text")

    if tag == "element":
        # HtmlElement(String, Map<String,String>, Array<HtmlNode>)
        # tag=0, String(name) at +4, Map handle at +12, Array at +16, total=24
        name = node.get("name", "")
        attrs = node.get("attrs", {})
        children = node.get("children", [])

        # Allocate name string and root it — subsequent
        # ``map_alloc`` / ``alloc`` calls may trigger GC.  ``push``
        # is a no-op for the empty-string case (name_ptr == 0,
        # which is the GC's sentinel for "not a heap object").
        name_ptr, name_len = alloc_string(caller, name)
        if name_ptr != 0:
            guard.push(name_ptr)

        # Allocate Map<String, String> for attributes.
        # Keys and values are Python strings — the Map host runtime
        # stores Python values and converts to WASM on access (via
        # map_get which calls _alloc_option_some_string).
        # #706: ``map_alloc`` (``_alloc_map_wrapper``) encodes this
        # Python dict into a fresh bucket-as-truth wrapper; store the
        # wrapper pointer in HtmlElement's attrs field so user-level
        # ``map_get`` / ``map_contains`` calls take it directly.  The
        # attrs Map is reclaimed by ordinary mark-sweep when the
        # wrapper becomes unreachable — no host store to evict.
        map_dict: dict[object, object] = {}
        for k, v in attrs.items():
            map_dict[str(k)] = str(v)
        wrapper_ptr = map_alloc(caller, map_dict)
        guard.push(wrapper_ptr)

        # Allocate children array
        child_count = len(children)
        if child_count > 0:
            arr_ptr = alloc(caller, child_count * 4)
            guard.push(arr_ptr)
            for i, child in enumerate(children):
                # Recursive write_html may run many sub-allocs that
                # trigger GC; the conservative scan reaches
                # ``arr_ptr`` via ``guard``'s shadow-stack window
                # and finds child pointers we've already written
                # into its slots.  The freshly-returned
                # ``child_ptr`` lives unrooted until we
                # ``write_i32`` it into the rooted ``arr_ptr``
                # slot — no allocations happen between the call
                # and the write, so no GC window exists.
                child_ptr = write_html(
                    caller, alloc, write_i32, alloc_string,
                    map_alloc, guard, child,
                )
                write_i32(caller, arr_ptr + i * 4, child_ptr)
        else:
            arr_ptr = 0

        # Allocate the HtmlElement node — by this point all field
        # pointers are rooted (via guard pushes above for name and
        # wrapper, via guard.push(arr_ptr) for children, or = 0
        # for the empty-children case) so this alloc is safe.
        ptr = alloc(caller, 24)
        write_i32(caller, ptr, _TAG_HTML_ELEMENT)
        write_i32(caller, ptr + 4, name_ptr)
        write_i32(caller, ptr + 8, name_len)
        write_i32(caller, ptr + 12, wrapper_ptr)
        write_i32(caller, ptr + 16, arr_ptr)
        write_i32(caller, ptr + 20, child_count)
        return ptr

    if tag == "comment":
        # HtmlComment(String) — tag=2, String at +4, total=16.
        # Two allocs (string + node body) → root the string before
        # the body alloc fires.
        content = node.get("content", "")
        s_ptr, s_len = alloc_string(caller, content)
        if s_ptr != 0:
            guard.push(s_ptr)
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, _TAG_HTML_COMMENT)
        write_i32(caller, ptr + 4, s_ptr)
        write_i32(caller, ptr + 8, s_len)
        return ptr

    # Default: HtmlText(String) — tag=1, String at +4, total=16.
    # Same rooting discipline as the comment branch.
    content = node.get("content", "")
    s_ptr, s_len = alloc_string(caller, content)
    if s_ptr != 0:
        guard.push(s_ptr)
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
    decode_attrs: "Callable[[wasmtime.Caller, int], dict[Any, Any]]",
) -> dict[str, Any]:
    """Read an HtmlNode ADT from WASM memory back to a Python dict.

    Returns a dict with 'tag' key indicating the node type.

    #706: ``decode_attrs(caller, wrapper_ptr)`` decodes an HtmlElement's
    ``Map<String, String>`` attributes from its bucket-as-truth wrapper.
    """
    tag = read_i32(caller, ptr)

    if tag == _TAG_HTML_ELEMENT:
        # String(name) at +4, Map handle at +12, Array at +16
        name_ptr = read_i32(caller, ptr + 4)
        name_len = read_i32(caller, ptr + 8)
        name = read_string(caller, name_ptr, name_len)
        # #706: HtmlElement's i32 field at offset 12 is the attrs
        # Map's wrapper pointer (see write_html).  Its bucket IS the
        # map, so ``decode_attrs`` decodes it directly — no handle to
        # unwrap, no ``map_store`` lookup.
        wrapper_ptr = read_i32(caller, ptr + 12)
        arr_ptr = read_i32(caller, ptr + 16)
        arr_len = read_i32(caller, ptr + 20)

        # #706: decode attributes (Map<String, String>) directly from
        # the wrapper's bucket — values are Python strings.
        attrs: dict[str, str] = {}
        for k, v in decode_attrs(caller, wrapper_ptr).items():
            attrs[str(k)] = str(v)

        # Read children
        children: list[dict[str, Any]] = []
        for i in range(arr_len):
            child_ptr = read_i32(caller, arr_ptr + i * 4)
            children.append(read_html(
                caller, child_ptr, read_i32, read_string, decode_attrs,
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
