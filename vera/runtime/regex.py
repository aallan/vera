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


def regex_error_message(exc: Exception) -> str:
    """The ``Err`` message for any failure of a regex host call (#1502).

    The four ``regex_*`` built-ins return a ``Result`` (spec §9.6.15:
    "to safely handle invalid patterns"), so EVERY exception the host's
    ``re`` work raises on the inputs is that ``Err``, not a trap —
    ``re.error`` for a malformed pattern, but also ``OverflowError`` for a
    repetition bound past the engine's limit, ``IndexError`` for a
    replacement naming a group the pattern lacks, and ``RecursionError``
    for a pattern nested deeper than the compiler recurses.  The last is
    the only one whose own text would describe the host rather than the
    pattern, so it gets a sentence of its own.
    """
    if isinstance(exc, RecursionError):
        return "invalid regex: the pattern nests too deeply to compile"
    return f"invalid regex: {exc}"


def register_regex(linker: wasmtime.Linker) -> None:
    """Register the requested Regex host functions on `linker`.

    #1502: each host function computes its answer from the input strings
    inside one ``except Exception`` (every failure there is the ``Err``
    arm, via :func:`regex_error_message`) and marshals the answer into
    WASM memory outside it, so a failure of the marshalling itself — a
    guest trap from ``$alloc`` — is never repackaged as a pattern error.
    """
    import re as _re

    def host_regex_match(
        caller: wasmtime.Caller,
        in_ptr: int, in_len: int, pat_ptr: int, pat_len: int,
    ) -> int:
        input_str = _read_wasm_string(caller, in_ptr, in_len)
        pattern = _read_wasm_string(caller, pat_ptr, pat_len)
        try:
            matched = _re.search(pattern, input_str) is not None
        except Exception as exc:  # noqa: BLE001 — host boundary; any failure becomes Result.Err
            return _alloc_result_err_string(caller, regex_error_message(exc))
        return _alloc_result_ok_i32(caller, 1 if matched else 0)

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
            found = m.group(0) if m else None
        except Exception as exc:  # noqa: BLE001 — host boundary; any failure becomes Result.Err
            return _alloc_result_err_string(caller, regex_error_message(exc))
        if found is not None:
            option_ptr = _alloc_option_some_string(caller, found)
        else:
            option_ptr = _alloc_option_none(caller)
        return _alloc_result_ok_i32(caller, option_ptr)

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
        except Exception as exc:  # noqa: BLE001 — host boundary; any failure becomes Result.Err
            return _alloc_result_err_string(caller, regex_error_message(exc))
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
        except Exception as exc:  # noqa: BLE001 — host boundary; any failure becomes Result.Err
            return _alloc_result_err_string(caller, regex_error_message(exc))
        return _alloc_result_ok_string(caller, result_str)

    regex_replace_type = wasmtime.FuncType(
        [wasmtime.ValType.i32()] * 6,
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "regex_replace", regex_replace_type,
        host_regex_replace, access_caller=True,
    )
