"""Markdown effect host bindings (§9.7.3).

Extracted verbatim from `execute()` in `vera/codegen/api.py` (#421);
the host callbacks call the module-level heap helpers in
`vera.runtime.heap` instead of closing over `execute()` locals.
"""

from __future__ import annotations

import wasmtime

from vera.runtime.heap import (
    _ShadowGuard,
    _alloc_array_of_strings,
    _alloc_result_err_string,
    _alloc_result_ok_i32,
    _alloc_string,
    _call_alloc,
    _read_wasm_string,
    _write_bytes,
    _write_i32,
)


def register_md(linker: wasmtime.Linker) -> None:
    """Register the requested Markdown host functions on `linker`."""
    from vera.markdown import (
        extract_code_blocks as _md_extract_code_blocks,
        has_code_block as _md_has_code_block,
        has_heading as _md_has_heading,
        parse_markdown as _md_parse,
        render_markdown as _md_render,
    )
    from vera.wasm.markdown import (
        read_md_block,
        write_md_block,
    )

    # md_parse(ptr, len) → i32 (Result<MdBlock, String>)
    def host_md_parse(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> int:
        text = _read_wasm_string(caller, ptr, length)
        # Parse errors are user-domain — convert to Result.Err.
        # The shadow-stack work + write_md_block + Result.Ok
        # alloc are deliberately OUTSIDE this except so host-
        # side invariant violations (shadow-stack overflow
        # from _ShadowGuard, unknown-tag ValueError from
        # write_md_block's exhaustive match, AssertionErrors
        # from internal bugs) propagate as wasmtime traps
        # rather than being swallowed as parse errors.
        # Matches the parse-only-in-try structure of
        # host_html_parse and host_json_parse (both narrow
        # their catch around only the parse call, with
        # _ShadowGuard usage outside).
        try:
            doc = _md_parse(text)
        except Exception as exc:
            return _alloc_result_err_string(caller, str(exc))
        # #692: same shadow-stack-rooting concern as
        # ``host_html_parse`` / ``host_json_parse``.
        # write_md_block holds intermediate pointers (string
        # bodies, child-array backings) in Python locals
        # across many sub-allocs; ``guard`` keeps them
        # visible to the conservative GC scan.
        with _ShadowGuard(caller) as guard:
            block_ptr = write_md_block(
                caller, _call_alloc, _write_i32,
                _write_bytes, _alloc_string, guard, doc,
            )
            guard.push(block_ptr)
            return _alloc_result_ok_i32(caller, block_ptr)

    md_parse_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "md_parse", md_parse_type,
        host_md_parse, access_caller=True,
    )

    # md_render(ptr) → (i32, i32) (String pair)
    def host_md_render(
        caller: wasmtime.Caller, ptr: int,
    ) -> tuple[int, int]:
        block = read_md_block(caller, ptr)
        text = _md_render(block)
        return _alloc_string(caller, text)

    md_render_type = wasmtime.FuncType(
        [wasmtime.ValType.i32()],
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "md_render", md_render_type,
        host_md_render, access_caller=True,
    )

    # md_has_heading(ptr, level_i64) → i32 (Bool)
    def host_md_has_heading(
        caller: wasmtime.Caller, ptr: int, level: int,
    ) -> int:
        block = read_md_block(caller, ptr)
        return 1 if _md_has_heading(block, level) else 0

    md_has_heading_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i64()],
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "md_has_heading", md_has_heading_type,
        host_md_has_heading, access_caller=True,
    )

    # md_has_code_block(ptr, lang_ptr, lang_len) → i32 (Bool)
    def host_md_has_code_block(
        caller: wasmtime.Caller,
        ptr: int, lang_ptr: int, lang_len: int,
    ) -> int:
        block = read_md_block(caller, ptr)
        lang = _read_wasm_string(caller, lang_ptr, lang_len)
        return 1 if _md_has_code_block(block, lang) else 0

    md_has_code_block_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
         wasmtime.ValType.i32()],
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "md_has_code_block", md_has_code_block_type,
        host_md_has_code_block, access_caller=True,
    )

    # md_extract_code_blocks(ptr, lang_ptr, lang_len) → (i32, i32)
    def host_md_extract_code_blocks(
        caller: wasmtime.Caller,
        ptr: int, lang_ptr: int, lang_len: int,
    ) -> tuple[int, int]:
        block = read_md_block(caller, ptr)
        lang = _read_wasm_string(caller, lang_ptr, lang_len)
        codes = _md_extract_code_blocks(block, lang)
        return _alloc_array_of_strings(caller, codes)

    md_extract_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
         wasmtime.ValType.i32()],
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "md_extract_code_blocks", md_extract_type,
        host_md_extract_code_blocks, access_caller=True,
    )
