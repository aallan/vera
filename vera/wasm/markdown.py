"""WASM memory marshalling for MdInline / MdBlock ADTs.

Provides bidirectional conversion between Python Markdown dataclasses
(vera.markdown) and their WASM memory representations.  Used by the
host function bindings in vera.codegen.api.

Write direction (Python → WASM):
  write_md_inline(caller, alloc, write_i32, write_i64, write_bytes, inline) → ptr
  write_md_block(caller, alloc, write_i32, write_i64, write_bytes, block) → ptr

Read direction (WASM → Python):
  read_md_block(caller, ptr) → MdBlock
  read_md_inline(caller, ptr) → MdInline

All layouts match the ConstructorLayout registrations in
vera/codegen/registration.py.
"""

from __future__ import annotations

import struct
from typing import Callable

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
    """
    if isinstance(inline, MdText):
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, 0)  # tag
        s_ptr, s_len = alloc_string(caller, inline.text)
        write_i32(caller, ptr + 4, s_ptr)
        write_i32(caller, ptr + 8, s_len)
        return ptr

    if isinstance(inline, MdCode):
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, 1)  # tag
        s_ptr, s_len = alloc_string(caller, inline.code)
        write_i32(caller, ptr + 4, s_ptr)
        write_i32(caller, ptr + 8, s_len)
        return ptr

    if isinstance(inline, MdEmph):
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, 2)  # tag
        arr_ptr, arr_len = _write_inline_array(
            caller, alloc, write_i32, alloc_string, inline.children,
        )
        write_i32(caller, ptr + 4, arr_ptr)
        write_i32(caller, ptr + 8, arr_len)
        return ptr

    if isinstance(inline, MdStrong):
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, 3)  # tag
        arr_ptr, arr_len = _write_inline_array(
            caller, alloc, write_i32, alloc_string, inline.children,
        )
        write_i32(caller, ptr + 4, arr_ptr)
        write_i32(caller, ptr + 8, arr_len)
        return ptr

    if isinstance(inline, MdLink):
        ptr = alloc(caller, 24)
        write_i32(caller, ptr, 4)  # tag
        arr_ptr, arr_len = _write_inline_array(
            caller, alloc, write_i32, alloc_string, inline.children,
        )
        write_i32(caller, ptr + 4, arr_ptr)
        write_i32(caller, ptr + 8, arr_len)
        u_ptr, u_len = alloc_string(caller, inline.url)
        write_i32(caller, ptr + 12, u_ptr)
        write_i32(caller, ptr + 16, u_len)
        return ptr

    if isinstance(inline, MdImage):
        ptr = alloc(caller, 24)
        write_i32(caller, ptr, 5)  # tag
        a_ptr, a_len = alloc_string(caller, inline.alt)
        write_i32(caller, ptr + 4, a_ptr)
        write_i32(caller, ptr + 8, a_len)
        s_ptr, s_len = alloc_string(caller, inline.src)
        write_i32(caller, ptr + 12, s_ptr)
        write_i32(caller, ptr + 16, s_len)
        return ptr

    raise ValueError(f"Unknown MdInline type: {type(inline)}")


def write_md_block(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    write_bytes: WriteBytesFn,
    alloc_string: AllocStringFn,
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
    """
    if isinstance(block, MdParagraph):
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, 0)  # tag
        arr_ptr, arr_len = _write_inline_array(
            caller, alloc, write_i32, alloc_string, block.children,
        )
        write_i32(caller, ptr + 4, arr_ptr)
        write_i32(caller, ptr + 8, arr_len)
        return ptr

    if isinstance(block, MdHeading):
        ptr = alloc(caller, 24)
        write_i32(caller, ptr, 1)  # tag
        # Nat at offset 8 as i64 (8-byte aligned)
        _write_i64(caller, write_bytes, ptr + 8, block.level)
        arr_ptr, arr_len = _write_inline_array(
            caller, alloc, write_i32, alloc_string, block.children,
        )
        write_i32(caller, ptr + 16, arr_ptr)
        write_i32(caller, ptr + 20, arr_len)
        return ptr

    if isinstance(block, MdCodeBlock):
        ptr = alloc(caller, 24)
        write_i32(caller, ptr, 2)  # tag
        l_ptr, l_len = alloc_string(caller, block.language)
        write_i32(caller, ptr + 4, l_ptr)
        write_i32(caller, ptr + 8, l_len)
        c_ptr, c_len = alloc_string(caller, block.code)
        write_i32(caller, ptr + 12, c_ptr)
        write_i32(caller, ptr + 16, c_len)
        return ptr

    if isinstance(block, MdBlockQuote):
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, 3)  # tag
        arr_ptr, arr_len = _write_block_array(
            caller, alloc, write_i32, write_bytes, alloc_string,
            block.children,
        )
        write_i32(caller, ptr + 4, arr_ptr)
        write_i32(caller, ptr + 8, arr_len)
        return ptr

    if isinstance(block, MdList):
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, 4)  # tag
        write_i32(caller, ptr + 4, 1 if block.ordered else 0)  # Bool
        # Array<Array<MdBlock>> — outer array of inner arrays
        arr_ptr, arr_len = _write_array_of_block_arrays(
            caller, alloc, write_i32, write_bytes, alloc_string,
            block.items,
        )
        write_i32(caller, ptr + 8, arr_ptr)
        write_i32(caller, ptr + 12, arr_len)
        return ptr

    if isinstance(block, MdThematicBreak):
        ptr = alloc(caller, 8)
        write_i32(caller, ptr, 5)  # tag
        return ptr

    if isinstance(block, MdTable):
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, 6)  # tag
        # Array<Array<Array<MdInline>>> — rows of cells of inlines
        arr_ptr, arr_len = _write_table_data(
            caller, alloc, write_i32, alloc_string, block.rows,
        )
        write_i32(caller, ptr + 4, arr_ptr)
        write_i32(caller, ptr + 8, arr_len)
        return ptr

    if isinstance(block, MdDocument):
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, 7)  # tag
        arr_ptr, arr_len = _write_block_array(
            caller, alloc, write_i32, write_bytes, alloc_string,
            block.children,
        )
        write_i32(caller, ptr + 4, arr_ptr)
        write_i32(caller, ptr + 8, arr_len)
        return ptr

    raise ValueError(f"Unknown MdBlock type: {type(block)}")


# -----------------------------------------------------------------
# Array writing helpers
# -----------------------------------------------------------------


def _write_i64(
    caller: wasmtime.Caller,
    write_bytes: WriteBytesFn,
    offset: int,
    value: int,
) -> None:
    """Write a little-endian i64 (unsigned) into WASM memory."""
    write_bytes(caller, offset, struct.pack("<Q", value & 0xFFFF_FFFF_FFFF_FFFF))


def _write_inline_array(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    alloc_string: AllocStringFn,
    inlines: tuple[MdInline, ...],
) -> tuple[int, int]:
    """Write Array<MdInline> — backing buffer of i32 element pointers."""
    count = len(inlines)
    if count == 0:
        return (0, 0)
    # Each element is an i32 pointer (4 bytes)
    backing = alloc(caller, count * 4)
    for i, inline in enumerate(inlines):
        elem_ptr = write_md_inline(caller, alloc, write_i32, alloc_string, inline)
        write_i32(caller, backing + i * 4, elem_ptr)
    return (backing, count)


def _write_block_array(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    write_bytes: WriteBytesFn,
    alloc_string: AllocStringFn,
    blocks: tuple[MdBlock, ...],
) -> tuple[int, int]:
    """Write Array<MdBlock> — backing buffer of i32 element pointers."""
    count = len(blocks)
    if count == 0:
        return (0, 0)
    backing = alloc(caller, count * 4)
    for i, block in enumerate(blocks):
        elem_ptr = write_md_block(
            caller, alloc, write_i32, write_bytes, alloc_string, block,
        )
        write_i32(caller, backing + i * 4, elem_ptr)
    return (backing, count)


def _write_array_of_block_arrays(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    write_bytes: WriteBytesFn,
    alloc_string: AllocStringFn,
    items: tuple[tuple[MdBlock, ...], ...],
) -> tuple[int, int]:
    """Write Array<Array<MdBlock>> — each inner array is an i32_pair."""
    count = len(items)
    if count == 0:
        return (0, 0)
    # Each element is an i32_pair (ptr, len) = 8 bytes
    backing = alloc(caller, count * 8)
    for i, item in enumerate(items):
        inner_ptr, inner_len = _write_block_array(
            caller, alloc, write_i32, write_bytes, alloc_string, item,
        )
        write_i32(caller, backing + i * 8, inner_ptr)
        write_i32(caller, backing + i * 8 + 4, inner_len)
    return (backing, count)


def _write_table_data(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    alloc_string: AllocStringFn,
    rows: tuple[tuple[tuple[MdInline, ...], ...], ...],
) -> tuple[int, int]:
    """Write Array<Array<Array<MdInline>>> — table rows."""
    row_count = len(rows)
    if row_count == 0:
        return (0, 0)
    # Each row is an i32_pair (ptr to Array<Array<MdInline>>, len)
    backing = alloc(caller, row_count * 8)
    for i, row in enumerate(rows):
        # Each row is Array<Array<MdInline>> — cells
        cell_count = len(row)
        if cell_count == 0:
            write_i32(caller, backing + i * 8, 0)
            write_i32(caller, backing + i * 8 + 4, 0)
            continue
        # Each cell is an i32_pair (ptr to Array<MdInline>, len)
        cell_backing = alloc(caller, cell_count * 8)
        for j, cell in enumerate(row):
            inline_ptr, inline_len = _write_inline_array(
                caller, alloc, write_i32, alloc_string, cell,
            )
            write_i32(caller, cell_backing + j * 8, inline_ptr)
            write_i32(caller, cell_backing + j * 8 + 4, inline_len)
        write_i32(caller, backing + i * 8, cell_backing)
        write_i32(caller, backing + i * 8 + 4, cell_count)
    return (backing, row_count)


# =====================================================================
# Read direction: WASM memory → Python
# =====================================================================


def _read_i32(caller: wasmtime.Caller, offset: int) -> int:
    """Read a little-endian i32 from WASM memory."""
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)
    buf = memory.data_ptr(caller)
    val: int = struct.unpack_from("<I", bytes(buf[offset:offset + 4]))[0]
    return val


def _read_i64(caller: wasmtime.Caller, offset: int) -> int:
    """Read a little-endian i64 from WASM memory."""
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)
    buf = memory.data_ptr(caller)
    val: int = struct.unpack_from("<Q", bytes(buf[offset:offset + 8]))[0]
    return val


def _read_string(caller: wasmtime.Caller, ptr: int, length: int) -> str:
    """Read a UTF-8 string from WASM memory."""
    if length == 0:
        return ""
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)
    buf = memory.data_ptr(caller)
    return bytes(buf[ptr:ptr + length]).decode("utf-8")


def _read_string_pair(caller: wasmtime.Caller, offset: int) -> str:
    """Read a String (i32_pair: ptr, len) from WASM memory."""
    ptr = _read_i32(caller, offset)
    length = _read_i32(caller, offset + 4)
    return _read_string(caller, ptr, length)


def read_md_inline(caller: wasmtime.Caller, ptr: int) -> MdInline:
    """Read an MdInline ADT node from WASM memory."""
    tag = _read_i32(caller, ptr)

    if tag == 0:  # MdText(String)
        text = _read_string_pair(caller, ptr + 4)
        return MdText(text)

    if tag == 1:  # MdCode(String)
        code = _read_string_pair(caller, ptr + 4)
        return MdCode(code)

    if tag == 2:  # MdEmph(Array<MdInline>)
        children = _read_inline_array(caller, ptr + 4)
        return MdEmph(children)

    if tag == 3:  # MdStrong(Array<MdInline>)
        children = _read_inline_array(caller, ptr + 4)
        return MdStrong(children)

    if tag == 4:  # MdLink(Array<MdInline>, String)
        children = _read_inline_array(caller, ptr + 4)
        url = _read_string_pair(caller, ptr + 12)
        return MdLink(children, url)

    if tag == 5:  # MdImage(String, String)
        alt = _read_string_pair(caller, ptr + 4)
        src = _read_string_pair(caller, ptr + 12)
        return MdImage(alt, src)

    raise ValueError(f"Unknown MdInline tag: {tag}")


def read_md_block(caller: wasmtime.Caller, ptr: int) -> MdBlock:
    """Read an MdBlock ADT node from WASM memory."""
    tag = _read_i32(caller, ptr)

    if tag == 0:  # MdParagraph(Array<MdInline>)
        inlines_0 = _read_inline_array(caller, ptr + 4)
        return MdParagraph(inlines_0)

    if tag == 1:  # MdHeading(Nat, Array<MdInline>)
        level = _read_i64(caller, ptr + 8)
        inlines_1 = _read_inline_array(caller, ptr + 16)
        return MdHeading(level, inlines_1)

    if tag == 2:  # MdCodeBlock(String, String)
        language = _read_string_pair(caller, ptr + 4)
        code = _read_string_pair(caller, ptr + 12)
        return MdCodeBlock(language, code)

    if tag == 3:  # MdBlockQuote(Array<MdBlock>)
        blocks_3 = _read_block_array(caller, ptr + 4)
        return MdBlockQuote(blocks_3)

    if tag == 4:  # MdList(Bool, Array<Array<MdBlock>>)
        ordered = _read_i32(caller, ptr + 4) != 0
        items = _read_array_of_block_arrays(caller, ptr + 8)
        return MdList(ordered, items)

    if tag == 5:  # MdThematicBreak
        return MdThematicBreak()

    if tag == 6:  # MdTable(Array<Array<Array<MdInline>>>)
        rows = _read_table_data(caller, ptr + 4)
        return MdTable(rows)

    if tag == 7:  # MdDocument(Array<MdBlock>)
        blocks_7 = _read_block_array(caller, ptr + 4)
        return MdDocument(blocks_7)

    raise ValueError(f"Unknown MdBlock tag: {tag}")


# -----------------------------------------------------------------
# Array reading helpers
# -----------------------------------------------------------------


def _read_inline_array(
    caller: wasmtime.Caller, offset: int,
) -> tuple[MdInline, ...]:
    """Read Array<MdInline> from an i32_pair at the given offset."""
    arr_ptr = _read_i32(caller, offset)
    arr_len = _read_i32(caller, offset + 4)
    if arr_len == 0:
        return ()
    result: list[MdInline] = []
    for i in range(arr_len):
        elem_ptr = _read_i32(caller, arr_ptr + i * 4)
        result.append(read_md_inline(caller, elem_ptr))
    return tuple(result)


def _read_block_array(
    caller: wasmtime.Caller, offset: int,
) -> tuple[MdBlock, ...]:
    """Read Array<MdBlock> from an i32_pair at the given offset."""
    arr_ptr = _read_i32(caller, offset)
    arr_len = _read_i32(caller, offset + 4)
    if arr_len == 0:
        return ()
    result: list[MdBlock] = []
    for i in range(arr_len):
        elem_ptr = _read_i32(caller, arr_ptr + i * 4)
        result.append(read_md_block(caller, elem_ptr))
    return tuple(result)


def _read_array_of_block_arrays(
    caller: wasmtime.Caller, offset: int,
) -> tuple[tuple[MdBlock, ...], ...]:
    """Read Array<Array<MdBlock>> from an i32_pair at the given offset."""
    arr_ptr = _read_i32(caller, offset)
    arr_len = _read_i32(caller, offset + 4)
    if arr_len == 0:
        return ()
    result: list[tuple[MdBlock, ...]] = []
    for i in range(arr_len):
        inner = _read_block_array(caller, arr_ptr + i * 8)
        result.append(inner)
    return tuple(result)


def _read_table_data(
    caller: wasmtime.Caller, offset: int,
) -> tuple[tuple[tuple[MdInline, ...], ...], ...]:
    """Read Array<Array<Array<MdInline>>> from an i32_pair."""
    arr_ptr = _read_i32(caller, offset)
    arr_len = _read_i32(caller, offset + 4)
    if arr_len == 0:
        return ()
    rows: list[tuple[tuple[MdInline, ...], ...]] = []
    for i in range(arr_len):
        cell_ptr = _read_i32(caller, arr_ptr + i * 8)
        cell_len = _read_i32(caller, arr_ptr + i * 8 + 4)
        cells: list[tuple[MdInline, ...]] = []
        for j in range(cell_len):
            inline_arr = _read_inline_array(caller, cell_ptr + j * 8)
            cells.append(inline_arr)
        rows.append(tuple(cells))
    return tuple(rows)
