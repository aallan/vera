"""WASM memory marshalling for MdInline / MdBlock ADTs.

Provides bidirectional conversion between Python Markdown dataclasses
(vera.markdown) and their WASM memory representations.  Used by the
host function bindings in vera.codegen.api.

Write direction (Python → WASM):
  write_md_inline(caller, alloc, write_i32, alloc_string, guard, inline) → ptr
  write_md_block(caller, alloc, write_i32, write_bytes, alloc_string,
                 guard, block) → ptr

Read direction (WASM → Python):
  read_md_block(caller, ptr) → MdBlock
  read_md_inline(caller, ptr) → MdInline

All layouts match the ConstructorLayout registrations in
vera/codegen/registration.py.

#692: ``guard`` is a ``_ShadowGuard`` from
``vera.codegen.api`` — an active context manager owning the
WASM shadow-stack window for this walk.  Intermediate heap
pointers (strings, child arrays) are pushed onto it before
any subsequent alloc that could trigger ``$gc_collect``.
The convention applied throughout this module is **allocate
fields first, root them, allocate the body last** — that way
the body's own pointer is never held in a Python local
across another alloc, so the body never needs rooting.

The returned root pointer is NOT pushed — the caller is
responsible for rooting it before the next alloc.
"""

from __future__ import annotations

import struct
from typing import Any, Callable

import wasmtime

from vera.markdown import (
    MdBlock,
    MdBlockQuote,
    MdCode,
    MdCodeBlock,
    MdDocument,
    MdEmph,
    MdHeading,
    MdImage,
    MdInline,
    MdLink,
    MdList,
    MdParagraph,
    MdStrong,
    MdTable,
    MdText,
    MdThematicBreak,
)
from vera.runtime.heap import _require_readable, _slice_and_decode
from vera.runtime.heap import _write_bytes as _heap_write_bytes

# Type aliases for the helper functions passed from api.py
AllocFn = Callable[["wasmtime.Caller", int], int]
WriteI32Fn = Callable[["wasmtime.Caller", int, int], None]
WriteI64Fn = Callable[["wasmtime.Caller", int, int], None]
WriteBytesFn = Callable[["wasmtime.Caller", int, bytes], None]
AllocStringFn = Callable[["wasmtime.Caller", str], tuple[int, int]]


# =====================================================================
# Write direction: Python → WASM memory
# =====================================================================


def write_md_inline(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    alloc_string: AllocStringFn,
    guard: Any,
    inline: MdInline,
) -> int:
    """Allocate an MdInline ADT node in WASM memory.  Returns the heap pointer.

    MdInline layouts (from registration.py):
      MdText(String)           tag=0  (4, i32_pair)  total=16
      MdCode(String)           tag=1  (4, i32_pair)  total=16
      MdEmph(Array<MdInline>)  tag=2  (4, i32_pair)  total=16
      MdStrong(Array<MdInline>)tag=3  (4, i32_pair)  total=16
      MdLink(Array, String)    tag=4  (4, i32_pair) (12, i32_pair)  total=24
      MdImage(String, String)  tag=5  (4, i32_pair) (12, i32_pair)  total=24

    See :func:`_write_md_tree` for the walk and its rooting discipline.
    """
    return _write_md_tree(
        caller, alloc, write_i32, _heap_write_bytes, alloc_string, guard,
        inline,
    )


def write_md_block(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    write_bytes: WriteBytesFn,
    alloc_string: AllocStringFn,
    guard: Any,
    block: MdBlock,
) -> int:
    """Allocate an MdBlock ADT node in WASM memory.  Returns the heap pointer.

    MdBlock layouts (from registration.py):
      MdParagraph(Array<MdInline>)        tag=0  (4, i32_pair)         total=16
      MdHeading(Nat, Array<MdInline>)     tag=1  (8, i64) (16, i32_pair) total=24
      MdCodeBlock(String, String)         tag=2  (4, i32_pair) (12, i32_pair) total=24
      MdBlockQuote(Array<MdBlock>)        tag=3  (4, i32_pair)         total=16
      MdList(Bool, Array<Array<MdBlock>>) tag=4  (4, i32) (8, i32_pair) total=16
      MdThematicBreak                     tag=5  ()                    total=8
      MdTable(Array<Array<Array<MdInline>>>)  tag=6  (4, i32_pair)     total=16
      MdDocument(Array<MdBlock>)          tag=7  (4, i32_pair)         total=16

    See :func:`_write_md_tree` for the walk and its rooting discipline.
    """
    return _write_md_tree(
        caller, alloc, write_i32, write_bytes, alloc_string, guard, block,
    )


def _write_md_tree(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    write_bytes: WriteBytesFn,
    alloc_string: AllocStringFn,
    guard: Any,
    root: MdBlock | MdInline,
) -> int:
    """Write a Markdown tree into WASM memory; return the root pointer.

    The returned pointer is NOT rooted — the caller roots it before its
    next allocation.

    #1502: iterative and pre-order, with shadow-stack use that does not
    grow with the tree.  Each node is written into a DESTINATION slot
    that is already reachable — a root cell pushed once for the whole
    walk, or a slot in an array block linked into the tree — so a node is
    reachable the moment it is stored.  A node allocates its strings and
    its zero-filled child arrays first, rooted only until the node itself
    is allocated and stored, then queues its children into those arrays'
    slots.  The recursive writer this replaces kept every intermediate
    pointer pushed until the whole walk ended: a flat document of 5,000
    paragraphs exhausted the 4,096-root window, and the recursion itself
    ended the program at a few hundred levels.
    """
    base = guard.mark()
    cell = alloc(caller, 4)
    write_i32(caller, cell, 0)
    guard.push(cell)

    def child_array(count: int, stride: int = 4) -> int:
        # A zero-filled array of ``count`` slots, rooted until the node
        # that owns it is stored.  Empty arrays are (0, 0), as before.
        if count == 0:
            return 0
        arr = alloc(caller, count * stride)
        write_bytes(caller, arr, bytes(count * stride))
        guard.push(arr)
        return arr

    def string_field(text: str) -> tuple[int, int]:
        s_ptr, s_len = alloc_string(caller, text)
        if s_ptr != 0:
            guard.push(s_ptr)
        return s_ptr, s_len

    tasks: list[tuple[MdBlock | MdInline, int]] = [(root, cell)]
    while tasks:
        node, dest = tasks.pop()
        mark = guard.mark()
        pending: list[tuple[MdBlock | MdInline, int]] = []

        if isinstance(node, (MdText, MdCode)):
            text = node.text if isinstance(node, MdText) else node.code
            s_ptr, s_len = string_field(text)
            ptr = alloc(caller, 16)
            write_i32(caller, ptr, 0 if isinstance(node, MdText) else 1)
            write_i32(caller, ptr + 4, s_ptr)
            write_i32(caller, ptr + 8, s_len)

        elif isinstance(node, (MdEmph, MdStrong)):
            arr = child_array(len(node.children))
            ptr = alloc(caller, 16)
            write_i32(caller, ptr, 2 if isinstance(node, MdEmph) else 3)
            write_i32(caller, ptr + 4, arr)
            write_i32(caller, ptr + 8, len(node.children))
            pending = [(c, arr + i * 4) for i, c in enumerate(node.children)]

        elif isinstance(node, MdLink):
            arr = child_array(len(node.children))
            u_ptr, u_len = string_field(node.url)
            ptr = alloc(caller, 24)
            write_i32(caller, ptr, 4)
            write_i32(caller, ptr + 4, arr)
            write_i32(caller, ptr + 8, len(node.children))
            write_i32(caller, ptr + 12, u_ptr)
            write_i32(caller, ptr + 16, u_len)
            pending = [(c, arr + i * 4) for i, c in enumerate(node.children)]

        elif isinstance(node, MdImage):
            a_ptr, a_len = string_field(node.alt)
            s_ptr, s_len = string_field(node.src)
            ptr = alloc(caller, 24)
            write_i32(caller, ptr, 5)
            write_i32(caller, ptr + 4, a_ptr)
            write_i32(caller, ptr + 8, a_len)
            write_i32(caller, ptr + 12, s_ptr)
            write_i32(caller, ptr + 16, s_len)

        elif isinstance(node, MdParagraph):
            arr = child_array(len(node.children))
            ptr = alloc(caller, 16)
            write_i32(caller, ptr, 0)
            write_i32(caller, ptr + 4, arr)
            write_i32(caller, ptr + 8, len(node.children))
            pending = [(c, arr + i * 4) for i, c in enumerate(node.children)]

        elif isinstance(node, MdHeading):
            arr = child_array(len(node.children))
            ptr = alloc(caller, 24)
            write_i32(caller, ptr, 1)
            # Nat at offset 8 as i64 (8-byte aligned)
            _write_i64(caller, write_bytes, ptr + 8, node.level)
            write_i32(caller, ptr + 16, arr)
            write_i32(caller, ptr + 20, len(node.children))
            pending = [(c, arr + i * 4) for i, c in enumerate(node.children)]

        elif isinstance(node, MdCodeBlock):
            l_ptr, l_len = string_field(node.language)
            c_ptr, c_len = string_field(node.code)
            ptr = alloc(caller, 24)
            write_i32(caller, ptr, 2)
            write_i32(caller, ptr + 4, l_ptr)
            write_i32(caller, ptr + 8, l_len)
            write_i32(caller, ptr + 12, c_ptr)
            write_i32(caller, ptr + 16, c_len)

        elif isinstance(node, (MdBlockQuote, MdDocument)):
            arr = child_array(len(node.children))
            ptr = alloc(caller, 16)
            write_i32(caller, ptr, 3 if isinstance(node, MdBlockQuote) else 7)
            write_i32(caller, ptr + 4, arr)
            write_i32(caller, ptr + 8, len(node.children))
            pending = [(c, arr + i * 4) for i, c in enumerate(node.children)]

        elif isinstance(node, MdList):
            # Array<Array<MdBlock>>: each outer slot is an i32_pair.  The
            # inner arrays are linked into the rooted outer array as soon
            # as each is allocated, so they need no roots of their own.
            outer = child_array(len(node.items), 8)
            for i, item in enumerate(node.items):
                inner = 0
                if item:
                    inner = alloc(caller, len(item) * 4)
                    write_bytes(caller, inner, bytes(len(item) * 4))
                write_i32(caller, outer + i * 8, inner)
                write_i32(caller, outer + i * 8 + 4, len(item))
                pending.extend(
                    (c, inner + k * 4) for k, c in enumerate(item)
                )
            ptr = alloc(caller, 16)
            write_i32(caller, ptr, 4)
            write_i32(caller, ptr + 4, 1 if node.ordered else 0)  # Bool
            write_i32(caller, ptr + 8, outer)
            write_i32(caller, ptr + 12, len(node.items))

        elif isinstance(node, MdThematicBreak):
            ptr = alloc(caller, 8)
            write_i32(caller, ptr, 5)

        elif isinstance(node, MdTable):
            # Array<Array<Array<MdInline>>>: rows of cells of inlines,
            # each level linked into the rooted level above it.
            rows = child_array(len(node.rows), 8)
            for i, row in enumerate(node.rows):
                cells = 0
                if row:
                    cells = alloc(caller, len(row) * 8)
                    write_bytes(caller, cells, bytes(len(row) * 8))
                write_i32(caller, rows + i * 8, cells)
                write_i32(caller, rows + i * 8 + 4, len(row))
                for j, cell_inlines in enumerate(row):
                    inl = 0
                    if cell_inlines:
                        inl = alloc(caller, len(cell_inlines) * 4)
                        write_bytes(
                            caller, inl, bytes(len(cell_inlines) * 4),
                        )
                    write_i32(caller, cells + j * 8, inl)
                    write_i32(caller, cells + j * 8 + 4, len(cell_inlines))
                    pending.extend(
                        (c, inl + k * 4) for k, c in enumerate(cell_inlines)
                    )
            ptr = alloc(caller, 16)
            write_i32(caller, ptr, 6)
            write_i32(caller, ptr + 4, rows)
            write_i32(caller, ptr + 8, len(node.rows))

        else:  # pragma: no cover — the parser builds no other node
            raise ValueError(f"Unknown Markdown node type: {type(node)}")

        write_i32(caller, dest, ptr)
        guard.release(mark)
        tasks.extend(reversed(pending))

    root_ptr = _read_i32(caller, cell)
    guard.release(base)
    return root_ptr


def _write_i64(
    caller: wasmtime.Caller,
    write_bytes: WriteBytesFn,
    offset: int,
    value: int,
) -> None:
    """Write a little-endian i64 (unsigned) into WASM memory."""
    write_bytes(caller, offset, struct.pack("<Q", value & 0xFFFF_FFFF_FFFF_FFFF))


# =====================================================================
# Read direction: WASM memory → Python
# =====================================================================


def _read_i32(caller: wasmtime.Caller, offset: int) -> int:
    """Read a little-endian i32 from WASM memory.

    Bounds-checked through ``heap._require_readable`` (#1442).  This
    module's markdown-AST walkers follow pointers read out of the tree
    they are decoding (``_read_i32(caller, arr_ptr + i * 4)`` and
    friends), so an offset here is guest data, not an allocator's
    answer, and a raw ctypes slice would read the guard page.
    """
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    _require_readable(memory, caller, offset, 4, "i32")
    buf = memory.data_ptr(caller)
    val: int = struct.unpack_from("<I", bytes(buf[offset:offset + 4]))[0]
    return val


def _read_i64(caller: wasmtime.Caller, offset: int) -> int:
    """Read a little-endian i64 from WASM memory.

    Bounds-checked through ``heap._require_readable`` (#1442), as
    :func:`_read_i32` above and for the same reason.
    """
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    _require_readable(memory, caller, offset, 8, "i64")
    buf = memory.data_ptr(caller)
    val: int = struct.unpack_from("<Q", bytes(buf[offset:offset + 8]))[0]
    return val


def _read_string(caller: wasmtime.Caller, ptr: int, length: int) -> str:
    """Read a UTF-8 string from WASM memory.

    Delegates the slice-and-decode to
    ``vera.runtime.heap._slice_and_decode`` (#592), so ``errors="replace"``
    surfaces a corrupt String ``(ptr, len)`` pair from an upstream codegen bug
    as U+FFFD characters rather than a raw ``UnicodeDecodeError`` escaping
    through wasmtime's trampoline as a "python exception" cause (#589 -- the same
    single decode home as ``_read_wasm_string`` in ``vera/runtime/heap.py``).
    Invoked from the four Markdown host imports (``host_md_render`` /
    ``host_md_has_heading`` / ``host_md_extract_text`` /
    ``host_md_count_blocks``) which all decode user-supplied String arguments --
    exactly the same surface as ``IO.print``.

    Bounds-checked through ``heap._require_readable`` before the slice
    (#1442): ``(ptr, length)`` is guest data — the host imports receive it as
    i32 arguments and ``_read_string_pair`` reads it out of a guest-built
    AST — and ``_slice_and_decode`` bounds-checks nothing of its own, so a
    pair that leaves linear memory must be refused here, the way
    ``_read_wasm_string`` refuses it for ``IO.print``.
    """
    if length == 0:
        return ""  # pragma: no cover
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    _require_readable(memory, caller, ptr, length, "string")
    return _slice_and_decode(memory, caller, ptr, length)


def _read_string_pair(caller: wasmtime.Caller, offset: int) -> str:
    """Read a String (i32_pair: ptr, len) from WASM memory."""
    ptr = _read_i32(caller, offset)
    length = _read_i32(caller, offset + 4)
    return _read_string(caller, ptr, length)


def read_md_inline(caller: wasmtime.Caller, ptr: int) -> MdInline:
    """Read an MdInline ADT node from WASM memory."""
    node = _read_md_tree(caller, ptr, _INLINE)
    assert not isinstance(node, _BLOCK_TYPES)  # noqa: S101
    return node


def read_md_block(caller: wasmtime.Caller, ptr: int) -> MdBlock:
    """Read an MdBlock ADT node from WASM memory."""
    node = _read_md_tree(caller, ptr, _BLOCK)
    return node  # type: ignore[return-value]


_BLOCK = 0
_INLINE = 1
_BLOCK_TYPES = (
    MdParagraph, MdHeading, MdCodeBlock, MdBlockQuote, MdList,
    MdThematicBreak, MdTable, MdDocument,
)


def _array_elements(caller: wasmtime.Caller, offset: int) -> list[int]:
    """The element pointers of the Array whose i32_pair is at ``offset``."""
    arr_ptr = _read_i32(caller, offset)
    arr_len = _read_i32(caller, offset + 4)
    return [_read_i32(caller, arr_ptr + i * 4) for i in range(arr_len)]


def _read_md_tree(
    caller: wasmtime.Caller, root_ptr: int, root_kind: int,
) -> MdBlock | MdInline:
    """Read a Markdown tree out of WASM memory, iteratively (#1502).

    The node dataclasses are immutable, so a node is built after its
    children: each is visited once to read its own fields and queue its
    children, and built once their values sit, in order, on ``built``.
    A tree built in Vera can nest far deeper than Python's recursion
    limit, and every Markdown query and ``md_render`` reads the tree
    first.
    """
    built: list[Any] = []
    # (pointer, kind) to visit, or (builder, child count) to build.
    stack: list[tuple[Any, int, bool]] = [(root_ptr, root_kind, False)]
    while stack:
        item, count_or_kind, is_build = stack.pop()
        if is_build:
            n = count_or_kind
            kids = built[len(built) - n:] if n else []
            if n:
                del built[len(built) - n:]
            built.append(item(kids))
            continue

        ptr, kind = item, count_or_kind
        tag = _read_i32(caller, ptr)
        children: list[tuple[int, int]] = []
        builder: Callable[[list[Any]], Any]

        if kind == _INLINE:
            if tag == 0:  # MdText(String)
                built.append(MdText(_read_string_pair(caller, ptr + 4)))
                continue
            if tag == 1:  # MdCode(String)
                built.append(MdCode(_read_string_pair(caller, ptr + 4)))
                continue
            if tag == 2 or tag == 3:  # MdEmph / MdStrong(Array<MdInline>)
                ctor = MdEmph if tag == 2 else MdStrong
                children = [
                    (p, _INLINE) for p in _array_elements(caller, ptr + 4)
                ]

                def builder(kids: list[Any], ctor: Any = ctor) -> Any:
                    return ctor(tuple(kids))
            elif tag == 4:  # MdLink(Array<MdInline>, String)
                children = [
                    (p, _INLINE) for p in _array_elements(caller, ptr + 4)
                ]
                url = _read_string_pair(caller, ptr + 12)

                def builder(kids: list[Any], url: str = url) -> Any:
                    return MdLink(tuple(kids), url)
            elif tag == 5:  # MdImage(String, String)
                alt = _read_string_pair(caller, ptr + 4)
                src = _read_string_pair(caller, ptr + 12)
                built.append(MdImage(alt, src))
                continue
            else:
                raise ValueError(f"Unknown MdInline tag: {tag}")  # pragma: no cover
        else:
            if tag == 0:  # MdParagraph(Array<MdInline>)
                children = [
                    (p, _INLINE) for p in _array_elements(caller, ptr + 4)
                ]

                def builder(kids: list[Any]) -> Any:
                    return MdParagraph(tuple(kids))
            elif tag == 1:  # MdHeading(Nat, Array<MdInline>)
                level = _read_i64(caller, ptr + 8)
                children = [
                    (p, _INLINE) for p in _array_elements(caller, ptr + 16)
                ]

                def builder(kids: list[Any], level: int = level) -> Any:
                    return MdHeading(level, tuple(kids))
            elif tag == 2:  # MdCodeBlock(String, String)
                language = _read_string_pair(caller, ptr + 4)
                code = _read_string_pair(caller, ptr + 12)
                built.append(MdCodeBlock(language, code))
                continue
            elif tag == 3 or tag == 7:  # MdBlockQuote / MdDocument
                container: Any = MdBlockQuote if tag == 3 else MdDocument
                children = [
                    (p, _BLOCK) for p in _array_elements(caller, ptr + 4)
                ]

                def builder(kids: list[Any], ctor: Any = container) -> Any:
                    return ctor(tuple(kids))
            elif tag == 4:  # MdList(Bool, Array<Array<MdBlock>>)
                ordered = _read_i32(caller, ptr + 4) != 0
                outer = _read_i32(caller, ptr + 8)
                outer_len = _read_i32(caller, ptr + 12)
                sizes: list[int] = []
                for i in range(outer_len):
                    item = _array_elements(caller, outer + i * 8)
                    sizes.append(len(item))
                    children.extend((p, _BLOCK) for p in item)

                def builder(
                    kids: list[Any], ordered: bool = ordered,
                    sizes: list[int] = sizes,
                ) -> Any:
                    items: list[tuple[MdBlock, ...]] = []
                    pos = 0
                    for size in sizes:
                        items.append(tuple(kids[pos:pos + size]))
                        pos += size
                    return MdList(ordered, tuple(items))
            elif tag == 5:  # MdThematicBreak
                built.append(MdThematicBreak())
                continue
            elif tag == 6:  # MdTable(Array<Array<Array<MdInline>>>)
                rows_ptr = _read_i32(caller, ptr + 4)
                rows_len = _read_i32(caller, ptr + 8)
                shape: list[list[int]] = []
                for i in range(rows_len):
                    cell_ptr = _read_i32(caller, rows_ptr + i * 8)
                    cell_len = _read_i32(caller, rows_ptr + i * 8 + 4)
                    row_shape: list[int] = []
                    for j in range(cell_len):
                        inlines = _array_elements(caller, cell_ptr + j * 8)
                        row_shape.append(len(inlines))
                        children.extend((p, _INLINE) for p in inlines)
                    shape.append(row_shape)

                def builder(
                    kids: list[Any], shape: list[list[int]] = shape,
                ) -> Any:
                    rows: list[tuple[tuple[MdInline, ...], ...]] = []
                    pos = 0
                    for row_shape in shape:
                        cells: list[tuple[MdInline, ...]] = []
                        for size in row_shape:
                            cells.append(tuple(kids[pos:pos + size]))
                            pos += size
                        rows.append(tuple(cells))
                    return MdTable(tuple(rows))
            else:
                raise ValueError(f"Unknown MdBlock tag: {tag}")  # pragma: no cover

        stack.append((builder, len(children), True))
        for child_ptr, child_kind in reversed(children):
            stack.append((child_ptr, child_kind, False))
    return built[0]  # type: ignore[no-any-return]
