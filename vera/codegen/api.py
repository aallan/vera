"""Public API for the Vera code generator.

Standalone functions (``compile``, ``execute``), result dataclasses,
and ADT memory-layout helpers.  These are the only symbols imported
by external modules.

See spec/11-compilation.md for the compilation specification.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from io import StringIO
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
    raise ValueError(f"Unknown WASM type: {wt}")


def _wasm_type_align(wt: str) -> int:
    """Natural alignment of a WASM value type."""
    if wt == "i32":
        return 4
    if wt in ("i64", "f64"):
        return 8
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
) -> ExecuteResult:
    """Execute a function from a compiled WASM module.

    Uses wasmtime to instantiate the module with host bindings
    for IO and State effects.  Returns the function's return value,
    any captured stdout output, and final state values.
    """
    if not result.ok:
        raise RuntimeError("Cannot execute: compilation had errors")

    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, result.wat)
    linker = wasmtime.Linker(engine)
    store = wasmtime.Store(engine)

    # Captured output from IO.print
    output_buf = StringIO()

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
    except Exception as exc:
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
