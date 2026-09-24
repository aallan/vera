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

#692: ``write_html`` takes a ``guard`` parameter — a
``vera.runtime.heap._ShadowGuard`` — that roots each node's
intermediate WASM heap pointers (``name_ptr``, ``wrapper_ptr``,
``arr_ptr``) until the node itself is allocated and stored in a
reachable slot, then releases them (#1502: the walk is iterative and
its roots do not grow with the tree).  Without this rooting, an alloc that
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

    Returns the heap pointer to the allocated HtmlNode.  *guard* is a
    ``_ShadowGuard`` (``vera.runtime.heap``) that owns the shadow-stack
    window for this walk.  The returned root pointer is NOT pushed onto
    the guard — the caller (``host_html_parse`` allocating the
    ``Result.Ok`` wrapper, or ``host_html_query`` storing it into its
    rooted result array) roots it before its next alloc.

    #1502: iterative and pre-order, with O(1) shadow-stack use at any
    depth and width.  Each node is written into a DESTINATION slot that
    is already reachable — a root cell pushed once for the whole walk, or
    a slot of a children array linked into the tree — so a node is
    reachable the moment it is stored.  An element allocates its name,
    its attribute map, its zero-filled children array and the node
    itself, with those fields rooted only until the node is stored, and
    then queues its children into the array's slots.  The recursive
    writer this replaces rooted every field of every node until the walk
    ended: ``html_query`` writing back each match's subtree under one
    guard exhausted the 4,096-root window at 100 nested elements, and the
    recursion itself ended the program a few hundred levels down.
    """
    base = guard.mark()
    cell = alloc(caller, 4)
    write_i32(caller, cell, 0)
    guard.push(cell)

    tasks: list[tuple[dict[str, Any], int]] = [(node, cell)]
    while tasks:
        current, dest = tasks.pop()
        mark = guard.mark()
        tag = current.get("tag", "text")
        pending: list[tuple[dict[str, Any], int]] = []

        if tag == "element":
            # HtmlElement(String, Map<String,String>, Array<HtmlNode>)
            # tag=0, String(name) at +4, Map handle at +12, Array at +16,
            # total=24.  ``push`` is skipped for the empty name
            # (name_ptr == 0 is the GC's "not a heap object").
            name = current.get("name", "")
            attrs = current.get("attrs", {})
            children = current.get("children", [])
            name_ptr, name_len = alloc_string(caller, name)
            if name_ptr != 0:
                guard.push(name_ptr)
            # #706: ``map_alloc`` (``_alloc_map_wrapper``) encodes the
            # attributes into a fresh bucket-as-truth wrapper, reclaimed
            # by ordinary mark-sweep once unreachable.
            map_dict: dict[object, object] = {
                str(k): str(v) for k, v in attrs.items()
            }
            wrapper_ptr = map_alloc(caller, map_dict)
            guard.push(wrapper_ptr)
            child_count = len(children)
            arr_ptr = 0
            if child_count > 0:
                arr_ptr = alloc(caller, child_count * 4)
                _zero_fill(caller, arr_ptr, child_count * 4)
                guard.push(arr_ptr)
            ptr = alloc(caller, 24)
            write_i32(caller, ptr, _TAG_HTML_ELEMENT)
            write_i32(caller, ptr + 4, name_ptr)
            write_i32(caller, ptr + 8, name_len)
            write_i32(caller, ptr + 12, wrapper_ptr)
            write_i32(caller, ptr + 16, arr_ptr)
            write_i32(caller, ptr + 20, child_count)
            pending = [
                (child, arr_ptr + i * 4) for i, child in enumerate(children)
            ]
        else:
            # HtmlComment(String) — tag=2 — or, by default, HtmlText
            # (String) — tag=1: String at +4, total=16.
            content = current.get("content", "")
            s_ptr, s_len = alloc_string(caller, content)
            if s_ptr != 0:
                guard.push(s_ptr)
            ptr = alloc(caller, 16)
            write_i32(
                caller, ptr,
                _TAG_HTML_COMMENT if tag == "comment" else _TAG_HTML_TEXT,
            )
            write_i32(caller, ptr + 4, s_ptr)
            write_i32(caller, ptr + 8, s_len)

        write_i32(caller, dest, ptr)
        guard.release(mark)
        tasks.extend(reversed(pending))

    root = _read_slot(caller, cell)
    guard.release(base)
    return root


def _read_slot(caller: wasmtime.Caller, addr: int) -> int:
    """Read back the i32 pointer the writer stored at ``addr``."""
    from vera.runtime.heap import _read_i32_at

    return _read_i32_at(caller, addr)


def _zero_fill(caller: wasmtime.Caller, ptr: int, nbytes: int) -> None:
    """Zero a freshly allocated children array before anything else allocates.

    The conservative collector scans a reachable block's words as
    candidate pointers; a slot not yet written must not hold one.
    """
    from vera.runtime.heap import _write_bytes

    _write_bytes(caller, ptr, bytes(nbytes))


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

    #1502: iterative.  A tree built in Vera can nest far deeper than
    Python's recursion limit; each element's dict is created with an
    empty children list that the stack fills in document order.
    """
    holder: list[dict[str, Any]] = []
    # Each task appends the node at ``node_ptr`` to the ``into`` list.
    tasks: list[tuple[int, list[dict[str, Any]]]] = [(ptr, holder)]
    while tasks:
        node_ptr, into = tasks.pop()
        tag = read_i32(caller, node_ptr)

        if tag == _TAG_HTML_ELEMENT:
            # String(name) at +4, Map handle at +12, Array at +16
            name_ptr = read_i32(caller, node_ptr + 4)
            name_len = read_i32(caller, node_ptr + 8)
            name = read_string(caller, name_ptr, name_len)
            # #706: HtmlElement's i32 field at offset 12 is the attrs
            # Map's wrapper pointer (see write_html).  Its bucket IS the
            # map, so ``decode_attrs`` decodes it directly.
            wrapper_ptr = read_i32(caller, node_ptr + 12)
            arr_ptr = read_i32(caller, node_ptr + 16)
            arr_len = read_i32(caller, node_ptr + 20)
            attrs: dict[str, str] = {}
            for k, v in decode_attrs(caller, wrapper_ptr).items():
                attrs[str(k)] = str(v)
            children: list[dict[str, Any]] = []
            into.append({
                "tag": "element",
                "name": name,
                "attrs": attrs,
                "children": children,
            })
            for i in range(arr_len - 1, -1, -1):
                tasks.append((read_i32(caller, arr_ptr + i * 4), children))
        elif tag == _TAG_HTML_COMMENT or tag == _TAG_HTML_TEXT:
            s_ptr = read_i32(caller, node_ptr + 4)
            s_len = read_i32(caller, node_ptr + 8)
            content = read_string(caller, s_ptr, s_len)
            kind = "comment" if tag == _TAG_HTML_COMMENT else "text"
            into.append({"tag": kind, "content": content})
        else:
            import warnings
            warnings.warn(
                f"read_html: unknown tag {tag} at pointer {node_ptr}; "
                "possible memory corruption or unsupported HtmlNode layout",
                RuntimeWarning,
                stacklevel=2,
            )
            into.append({"tag": "text", "content": ""})
    return holder[0]
