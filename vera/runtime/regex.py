"""Regex effect host bindings (§9.6.15).

Extracted verbatim from `execute()` in `vera/codegen/api.py` (#421); the host
callbacks call the module-level heap helpers in `vera.runtime.heap`.
"""

from __future__ import annotations

import wasmtime

from vera.runtime.heap import (
    _alloc_array_of_strings,
    _alloc_option_none,
    _alloc_option_some_string,
    _alloc_result_err_string,
    _alloc_result_ok_i32,
    _alloc_result_ok_string,
    _call_alloc,
    _read_wasm_string,
    _ShadowGuard,
    _write_i32,
)


def register_regex(linker: wasmtime.Linker) -> None:
    """Register the requested Regex host functions on `linker`."""
    import re as _re

    def host_regex_match(
        caller: wasmtime.Caller,
        in_ptr: int, in_len: int, pat_ptr: int, pat_len: int,
    ) -> int:
        input_str = _read_wasm_string(caller, in_ptr, in_len)
        pattern = _read_wasm_string(caller, pat_ptr, pat_len)
        try:
            matched = _re.search(pattern, input_str) is not None
            return _alloc_result_ok_i32(caller, 1 if matched else 0)
        except _re.error as exc:
            return _alloc_result_err_string(
                caller, f"invalid regex: {exc}",
            )

    regex_match_type = wasmtime.FuncType(
        [wasmtime.ValType.i32()] * 4,
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "regex_match", regex_match_type,
        host_regex_match, access_caller=True,
    )

    def host_regex_find(
        caller: wasmtime.Caller,
        in_ptr: int, in_len: int, pat_ptr: int, pat_len: int,
    ) -> int:
        input_str = _read_wasm_string(caller, in_ptr, in_len)
        pattern = _read_wasm_string(caller, pat_ptr, pat_len)
        try:
            m = _re.search(pattern, input_str)
            if m:
                option_ptr = _alloc_option_some_string(
                    caller, m.group(0),
                )
            else:
                option_ptr = _alloc_option_none(caller)
            return _alloc_result_ok_i32(caller, option_ptr)
        except _re.error as exc:
            return _alloc_result_err_string(
                caller, f"invalid regex: {exc}",
            )

    regex_find_type = wasmtime.FuncType(
        [wasmtime.ValType.i32()] * 4,
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "regex_find", regex_find_type,
        host_regex_find, access_caller=True,
    )

    def host_regex_find_all(
        caller: wasmtime.Caller,
        in_ptr: int, in_len: int, pat_ptr: int, pat_len: int,
    ) -> int:
        input_str = _read_wasm_string(caller, in_ptr, in_len)
        pattern = _read_wasm_string(caller, pat_ptr, pat_len)
        try:
            # Use finditer + group(0) to always get full match
            # strings, even when the pattern has capture groups.
            matches = [
                m.group(0)
                for m in _re.finditer(pattern, input_str)
            ]
            backing_ptr, count = _alloc_array_of_strings(
                caller, matches,
            )
            # GC-rooting (folded into #706): root backing_ptr across
            # the Result.Ok struct alloc so a GC can't sweep it.
            with _ShadowGuard(caller) as guard:
                if backing_ptr != 0:
                    guard.push(backing_ptr)
                # Wrap in Result.Ok: tag=0, backing_ptr, count (12 bytes)
                adt_ptr = _call_alloc(caller, 12)
                _write_i32(caller, adt_ptr, 0)            # tag = Ok
                _write_i32(caller, adt_ptr + 4, backing_ptr)
                _write_i32(caller, adt_ptr + 8, count)
            return adt_ptr
        except _re.error as exc:
            return _alloc_result_err_string(
                caller, f"invalid regex: {exc}",
            )

    regex_find_all_type = wasmtime.FuncType(
        [wasmtime.ValType.i32()] * 4,
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "regex_find_all", regex_find_all_type,
        host_regex_find_all, access_caller=True,
    )

    def host_regex_replace(
        caller: wasmtime.Caller,
        in_ptr: int, in_len: int,
        pat_ptr: int, pat_len: int,
        rep_ptr: int, rep_len: int,
    ) -> int:
        input_str = _read_wasm_string(caller, in_ptr, in_len)
        pattern = _read_wasm_string(caller, pat_ptr, pat_len)
        replacement = _read_wasm_string(caller, rep_ptr, rep_len)
        try:
            result_str = _re.sub(
                pattern, replacement, input_str, count=1,
            )
            return _alloc_result_ok_string(caller, result_str)
        except _re.error as exc:
            return _alloc_result_err_string(
                caller, f"invalid regex: {exc}",
            )

    regex_replace_type = wasmtime.FuncType(
        [wasmtime.ValType.i32()] * 6,
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "regex_replace", regex_replace_type,
        host_regex_replace, access_caller=True,
    )
