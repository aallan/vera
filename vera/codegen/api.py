"""Public API for the Vera code generator.

Standalone functions (``compile``, ``execute``), result dataclasses,
and ADT memory-layout helpers.  These are the only symbols imported
by external modules.

See spec/11-compilation.md for the compilation specification.
"""

from __future__ import annotations

import os
import struct
import sys
from dataclasses import dataclass, field
from io import StringIO
from pathlib import Path
from typing import TYPE_CHECKING

import wasmtime

from vera import ast

if TYPE_CHECKING:
    from vera.resolver import ResolvedModule


# =====================================================================
# ADT memory layout
# =====================================================================


@dataclass
class ConstructorLayout:
    """WASM memory layout for a single ADT constructor."""

    tag: int  # discriminant (0, 1, 2, ...)
    field_offsets: tuple[tuple[int, str], ...]  # (byte_offset, wasm_type) per field
    total_size: int  # total bytes, 8-byte aligned


def _wasm_type_size(wt: str) -> int:
    """Byte size of a WASM value type."""
    if wt == "i32":
        return 4
    if wt in ("i64", "f64"):
        return 8
    if wt == "i32_pair":
        return 8
    raise ValueError(f"Unknown WASM type: {wt}")


def _wasm_type_align(wt: str) -> int:
    """Natural alignment of a WASM value type."""
    if wt == "i32":
        return 4
    if wt in ("i64", "f64"):
        return 8
    if wt == "i32_pair":
        return 4
    raise ValueError(f"Unknown WASM type: {wt}")


def _align_up(offset: int, align: int) -> int:
    """Round offset up to the next multiple of align."""
    return (offset + align - 1) & ~(align - 1)


# =====================================================================
# Public API
# =====================================================================

@dataclass
class CompileResult:
    """Result of compiling a Vera program to WebAssembly."""

    wat: str
    wasm_bytes: bytes
    exports: list[str]
    diagnostics: list["Diagnostic"] = field(default_factory=list)
    state_types: list[tuple[str, str]] = field(default_factory=list)
    md_ops_used: set[str] = field(default_factory=set)
    regex_ops_used: set[str] = field(default_factory=set)

    @property
    def ok(self) -> bool:
        """True if compilation succeeded with no errors."""
        return not any(d.severity == "error" for d in self.diagnostics)


@dataclass
class ExecuteResult:
    """Result of executing a WASM function."""

    value: int | float | None  # Return value (None for void/Unit functions)
    stdout: str  # Captured IO.print output
    state: dict[str, int | float] = field(default_factory=dict)
    exit_code: int | None = None  # Set by IO.exit


class _VeraExit(Exception):
    """Sentinel exception raised by IO.exit to abort WASM execution."""

    def __init__(self, code: int) -> None:
        self.code = code
        super().__init__(f"IO.exit({code})")


# Import Diagnostic here to avoid circular imports at module level
from vera.errors import Diagnostic, SourceLocation  # noqa: E402


def compile(
    program: ast.Program,
    source: str = "",
    file: str | None = None,
    resolved_modules: list[ResolvedModule] | None = None,
) -> CompileResult:
    """Compile a type-checked Vera Program AST to WebAssembly.

    Returns a CompileResult with WAT text, WASM binary, exports,
    and any diagnostics.  The program should already have passed
    type checking and (optionally) verification.
    """
    from vera.codegen.core import CodeGenerator

    gen = CodeGenerator(
        source=source, file=file, resolved_modules=resolved_modules,
    )
    return gen.compile_program(program)


def execute(
    result: CompileResult,
    fn_name: str | None = None,
    args: list[int | float] | None = None,
    initial_state: dict[str, int | float] | None = None,
    stdin: str | None = None,
    cli_args: list[str] | None = None,
    env_vars: dict[str, str] | None = None,
) -> ExecuteResult:
    """Execute a function from a compiled WASM module.

    Uses wasmtime to instantiate the module with host bindings
    for IO and State effects.  Returns the function's return value,
    any captured stdout output, and final state values.

    Parameters
    ----------
    stdin : str | None
        Input for ``IO.read_line``.  If *None*, reads from ``sys.stdin``.
    cli_args : list[str] | None
        Command-line arguments returned by ``IO.args``.
    env_vars : dict[str, str] | None
        Environment variables for ``IO.get_env``.  If *None*, uses
        ``os.environ``.
    """
    if not result.ok:
        raise RuntimeError("Cannot execute: compilation had errors")

    config = wasmtime.Config()
    config.wasm_exceptions = True
    engine = wasmtime.Engine(config)
    module = wasmtime.Module(engine, result.wat)
    linker = wasmtime.Linker(engine)
    store = wasmtime.Store(engine)

    # Captured output from IO.print
    output_buf = StringIO()

    # stdin buffer for IO.read_line
    stdin_buf = StringIO(stdin) if stdin is not None else None

    # -----------------------------------------------------------------
    # Memory helpers for host → WASM string/ADT allocation
    # -----------------------------------------------------------------

    def _read_wasm_string(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> str:
        """Read a UTF-8 string from WASM memory."""
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)
        buf = memory.data_ptr(store)
        return bytes(buf[ptr:ptr + length]).decode("utf-8")

    def _write_bytes(
        caller: wasmtime.Caller, offset: int, data: bytes,
    ) -> None:
        """Write raw bytes into WASM linear memory."""
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)
        buf = memory.data_ptr(store)
        for i, b in enumerate(data):
            buf[offset + i] = b

    def _write_i32(
        caller: wasmtime.Caller, offset: int, value: int,
    ) -> None:
        """Write a little-endian i32 into WASM memory."""
        _write_bytes(caller, offset, struct.pack("<I", value & 0xFFFF_FFFF))

    def _call_alloc(caller: wasmtime.Caller, size: int) -> int:
        """Call the exported $alloc to allocate WASM heap memory."""
        alloc_fn = caller["alloc"]
        assert isinstance(alloc_fn, wasmtime.Func)
        ptr = alloc_fn(caller, size)
        assert isinstance(ptr, int)
        return ptr

    def _alloc_string(
        caller: wasmtime.Caller, s: str,
    ) -> tuple[int, int]:
        """Allocate a string in WASM memory; returns (ptr, len)."""
        encoded = s.encode("utf-8")
        length = len(encoded)
        if length == 0:
            return (0, 0)
        ptr = _call_alloc(caller, length)
        _write_bytes(caller, ptr, encoded)
        return (ptr, length)

    def _alloc_result_ok_string(
        caller: wasmtime.Caller, s: str,
    ) -> int:
        """Allocate Result.Ok(String) on the WASM heap; returns ADT ptr."""
        str_ptr, str_len = _alloc_string(caller, s)
        # Layout: tag(i32)=0 at +0, str_ptr(i32) at +4, str_len(i32) at +8
        adt_ptr = _call_alloc(caller, 12)
        _write_i32(caller, adt_ptr, 0)       # tag = Ok
        _write_i32(caller, adt_ptr + 4, str_ptr)
        _write_i32(caller, adt_ptr + 8, str_len)
        return adt_ptr

    def _alloc_result_err_string(
        caller: wasmtime.Caller, s: str,
    ) -> int:
        """Allocate Result.Err(String) on the WASM heap; returns ADT ptr."""
        str_ptr, str_len = _alloc_string(caller, s)
        # Layout: tag(i32)=1 at +0, str_ptr(i32) at +4, str_len(i32) at +8
        adt_ptr = _call_alloc(caller, 12)
        _write_i32(caller, adt_ptr, 1)       # tag = Err
        _write_i32(caller, adt_ptr + 4, str_ptr)
        _write_i32(caller, adt_ptr + 8, str_len)
        return adt_ptr

    def _alloc_result_ok_unit(caller: wasmtime.Caller) -> int:
        """Allocate Result.Ok(()) on the WASM heap; returns ADT ptr."""
        # Layout: tag(i32)=0 at +0, no payload
        adt_ptr = _call_alloc(caller, 4)
        _write_i32(caller, adt_ptr, 0)       # tag = Ok
        return adt_ptr

    def _alloc_option_some_string(
        caller: wasmtime.Caller, s: str,
    ) -> int:
        """Allocate Option.Some(String) on the WASM heap; returns ADT ptr."""
        str_ptr, str_len = _alloc_string(caller, s)
        # Layout: tag(i32)=1 at +0, str_ptr(i32) at +4, str_len(i32) at +8
        adt_ptr = _call_alloc(caller, 12)
        _write_i32(caller, adt_ptr, 1)       # tag = Some
        _write_i32(caller, adt_ptr + 4, str_ptr)
        _write_i32(caller, adt_ptr + 8, str_len)
        return adt_ptr

    def _alloc_option_none(caller: wasmtime.Caller) -> int:
        """Allocate Option.None on the WASM heap; returns ADT ptr."""
        # Layout: tag(i32)=0 at +0, no payload
        adt_ptr = _call_alloc(caller, 4)
        _write_i32(caller, adt_ptr, 0)       # tag = None
        return adt_ptr

    def _alloc_array_of_strings(
        caller: wasmtime.Caller, strings: list[str],
    ) -> tuple[int, int]:
        """Allocate an Array<String> on the WASM heap.

        Returns (backing_ptr, count) — the WASM pair representation.
        Each element occupies 8 bytes: (i32 ptr, i32 len).
        """
        count = len(strings)
        if count == 0:
            return (0, 0)
        backing_ptr = _call_alloc(caller, count * 8)
        for i, s in enumerate(strings):
            str_ptr, str_len = _alloc_string(caller, s)
            _write_i32(caller, backing_ptr + i * 8, str_ptr)
            _write_i32(caller, backing_ptr + i * 8 + 4, str_len)
        return (backing_ptr, count)

    def _alloc_result_ok_i32(
        caller: wasmtime.Caller, value: int,
    ) -> int:
        """Allocate Result.Ok(i32) — wraps a heap pointer in Ok."""
        # Layout: tag(i32)=0 at +0, value(i32) at +4
        adt_ptr = _call_alloc(caller, 8)
        _write_i32(caller, adt_ptr, 0)       # tag = Ok
        _write_i32(caller, adt_ptr + 4, value)
        return adt_ptr

    # -----------------------------------------------------------------
    # IO host functions
    # -----------------------------------------------------------------

    # Host function: vera.print(ptr: i32, len: i32) -> ()
    def host_print(caller: wasmtime.Caller, ptr: int, length: int) -> None:
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)
        buf = memory.data_ptr(store)
        data = bytes(buf[ptr:ptr + length])
        text = data.decode("utf-8")
        output_buf.write(text)

    print_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [],
    )
    linker.define_func(
        "vera", "print", print_type, host_print, access_caller=True
    )

    # Host function: vera.read_line() -> (i32, i32)  [String pair]
    def host_read_line(caller: wasmtime.Caller) -> tuple[int, int]:
        if stdin_buf is not None:
            line = stdin_buf.readline()
        else:
            try:
                line = sys.stdin.readline()
            except EOFError:
                line = ""
        # Strip trailing newline (like getline)
        if line.endswith("\n"):
            line = line[:-1]
        return _alloc_string(caller, line)

    read_line_type = wasmtime.FuncType(
        [],
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "read_line", read_line_type,
        host_read_line, access_caller=True,
    )

    # Host function: vera.read_file(ptr, len) -> i32  [Result<String,String>]
    def host_read_file(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> int:
        path = _read_wasm_string(caller, ptr, length)
        try:
            contents = Path(path).read_text(encoding="utf-8")
            return _alloc_result_ok_string(caller, contents)
        except Exception as exc:
            return _alloc_result_err_string(caller, str(exc))

    read_file_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "read_file", read_file_type,
        host_read_file, access_caller=True,
    )

    # Host function: vera.write_file(p_ptr, p_len, d_ptr, d_len) -> i32
    # Result<Unit, String>
    def host_write_file(
        caller: wasmtime.Caller,
        p_ptr: int, p_len: int,
        d_ptr: int, d_len: int,
    ) -> int:
        path = _read_wasm_string(caller, p_ptr, p_len)
        data = _read_wasm_string(caller, d_ptr, d_len)
        try:
            Path(path).write_text(data, encoding="utf-8")
            return _alloc_result_ok_unit(caller)
        except Exception as exc:
            return _alloc_result_err_string(caller, str(exc))

    write_file_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
         wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "write_file", write_file_type,
        host_write_file, access_caller=True,
    )

    # Host function: vera.args() -> (i32, i32)  [Array<String> pair]
    def host_args(caller: wasmtime.Caller) -> tuple[int, int]:
        return _alloc_array_of_strings(caller, cli_args or [])

    args_type = wasmtime.FuncType(
        [],
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "args", args_type, host_args, access_caller=True,
    )

    # Host function: vera.exit(code: i64) -> ()
    def host_exit(_caller: wasmtime.Caller, code: int) -> None:
        raise _VeraExit(code)

    exit_type = wasmtime.FuncType(
        [wasmtime.ValType.i64()],
        [],
    )
    linker.define_func(
        "vera", "exit", exit_type, host_exit, access_caller=True,
    )

    # Host function: vera.get_env(ptr, len) -> i32  [Option<String>]
    def host_get_env(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> int:
        name = _read_wasm_string(caller, ptr, length)
        if env_vars is not None:
            value = env_vars.get(name)
        else:
            value = os.environ.get(name)
        if value is not None:
            return _alloc_option_some_string(caller, value)
        return _alloc_option_none(caller)

    get_env_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [wasmtime.ValType.i32()],
    )
    linker.define_func(
        "vera", "get_env", get_env_type,
        host_get_env, access_caller=True,
    )

    # -----------------------------------------------------------------
    # Contract violation reporting
    # -----------------------------------------------------------------

    # Host function: vera.contract_fail(ptr: i32, len: i32) -> ()
    # Stores the violation message so it can be reported on trap.
    last_violation: list[str] = []

    def host_contract_fail(
        caller: wasmtime.Caller, ptr: int, length: int,
    ) -> None:
        memory = caller["memory"]
        assert isinstance(memory, wasmtime.Memory)
        buf = memory.data_ptr(store)
        data = bytes(buf[ptr:ptr + length])
        last_violation.clear()
        last_violation.append(data.decode("utf-8"))

    contract_fail_type = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [],
    )
    linker.define_func(
        "vera", "contract_fail", contract_fail_type,
        host_contract_fail, access_caller=True,
    )

    # State<T> host functions
    _WASM_VAL_TYPE = {
        "i64": wasmtime.ValType.i64(),
        "i32": wasmtime.ValType.i32(),
        "f64": wasmtime.ValType.f64(),
    }
    _DEFAULT_STATE: dict[str, int | float] = {
        "i64": 0, "i32": 0, "f64": 0.0,
    }

    state_store: dict[str, int | float] = {}

    for type_name, wasm_t in result.state_types:
        state_key = f"State_{type_name}"
        state_store[state_key] = _DEFAULT_STATE[wasm_t]
        val_type = _WASM_VAL_TYPE[wasm_t]

        # Closure factories to capture correct state_key per type
        def _make_host_get(key: str):  # type: ignore[no-untyped-def]
            def host_get() -> int | float:
                return state_store[key]
            return host_get

        def _make_host_put(key: str):  # type: ignore[no-untyped-def]
            def host_put(val: int | float) -> None:
                state_store[key] = val
            return host_put

        get_type = wasmtime.FuncType([], [val_type])
        linker.define_func(
            "vera", f"state_get_{type_name}", get_type,
            _make_host_get(state_key),
        )

        put_type = wasmtime.FuncType([val_type], [])
        linker.define_func(
            "vera", f"state_put_{type_name}", put_type,
            _make_host_put(state_key),
        )

    # Apply initial state overrides (for testing)
    if initial_state:
        for key, val in initial_state.items():
            if key in state_store:
                state_store[key] = val

    # -----------------------------------------------------------------
    # Markdown host functions (§9.7.3)
    # -----------------------------------------------------------------

    if result.md_ops_used:
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
            try:
                doc = _md_parse(text)
                block_ptr = write_md_block(
                    caller, _call_alloc, _write_i32,
                    _write_bytes, _alloc_string, doc,
                )
                return _alloc_result_ok_i32(caller, block_ptr)
            except Exception as exc:
                return _alloc_result_err_string(caller, str(exc))

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

    # -----------------------------------------------------------------
    # Regex host functions (§9.6.15)
    # -----------------------------------------------------------------

    if result.regex_ops_used:
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

    instance = linker.instantiate(store, module)

    # Determine function to call
    auto_selected = False
    if fn_name is None:
        # Try "main" first, then first export
        if "main" in result.exports:
            fn_name = "main"
        elif result.exports:
            fn_name = result.exports[0]
            auto_selected = True
        else:
            raise RuntimeError("No exported functions to call")

    func = instance.exports(store).get(fn_name)
    if func is None or not isinstance(func, wasmtime.Func):
        exports_str = ", ".join(result.exports) if result.exports else "(none)"
        raise RuntimeError(
            f"Function '{fn_name}' not found in exports. "
            f"Available: {exports_str}"
        )

    # Check parameter count before calling
    call_args: list[int | float] = args or []
    func_type = func.type(store)
    expected = len(func_type.params)
    given = len(call_args)
    if given != expected:
        exports_str = ", ".join(result.exports)
        msg = (
            f"Function '{fn_name}' expects {expected} "
            f"parameter{'s' if expected != 1 else ''} "
            f"but {given} {'were' if given != 1 else 'was'} provided."
        )
        if auto_selected:
            msg += (
                f"\n\nNo 'main' function found. "
                f"'{fn_name}' was selected as the first export."
            )
        msg += (
            f"\n\nAvailable exports: {exports_str}"
            f"\n\nTo call a specific function with arguments:"
            f"\n\n  vera run <file> --fn {fn_name} -- <args>"
        )
        raise RuntimeError(msg)

    try:
        raw_result = func(store, *call_args)
    except _VeraExit as exit_exc:
        # IO.exit(code) — return captured output with exit code
        return ExecuteResult(
            value=None,
            stdout=output_buf.getvalue(),
            state=dict(state_store),
            exit_code=exit_exc.code,
        )
    except Exception as exc:
        # _VeraExit may be wrapped by wasmtime in a Trap/WasmtimeError.
        # Check the exception chain for our sentinel.
        cause: BaseException | None = exc
        while cause is not None:
            if isinstance(cause, _VeraExit):
                return ExecuteResult(
                    value=None,
                    stdout=output_buf.getvalue(),
                    state=dict(state_store),
                    exit_code=cause.code,
                )
            cause = cause.__cause__ or cause.__context__
            if cause is exc:
                break  # avoid infinite loop

        # Convert contract violation traps to RuntimeError with
        # the informative message stored by host_contract_fail.
        exc_name = type(exc).__name__
        if exc_name in ("Trap", "WasmtimeError") and last_violation:
            raise RuntimeError(last_violation[0]) from exc
        raise

    # Extract return value
    value: int | float | None
    if raw_result is None:
        value = None
    elif isinstance(raw_result, (tuple, list)):
        # Multi-value return (e.g. String/Array as (ptr, len))
        value = raw_result[0] if raw_result else None
    elif isinstance(raw_result, float):
        value = raw_result
    elif isinstance(raw_result, int):
        value = raw_result
    else:
        value = int(raw_result)

    return ExecuteResult(
        value=value,
        stdout=output_buf.getvalue(),
        state=dict(state_store),
    )
