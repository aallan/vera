"""Every artifact the compiler builds is validated where it is built (#1900).

``wasmtime.wat2wasm`` assembles text: it resolves names and encodes, and
type-checks nothing, so a module that assembles can still be one no loader
accepts (a load from a memory it does not declare, #1900).  Each artifact
is therefore checked once, where it is built:

- the core module, by :func:`validate_module`, in
  ``CodeGenerator.compile_program`` right after assembly.  Every command
  compiles through it (``vera compile``, ``run``, ``test``, ``serve``,
  ``verify``'s reconciliation, the browser bundle, which writes the same
  bytes);
- the wasi-p2 component, by :func:`build_component`, which constructs it
  (wasmtime has no separate component validator), where ``vera compile
  --target wasi-p2`` and ``vera run --target wasi-p2`` build it.

A failure raises :class:`~vera.skip.CodegenInvariantError`: a module that
does not validate is a compiler defect, reported as E699
(:func:`assembly_error`), and nothing is written.
"""

from __future__ import annotations

import re
import threading
from typing import TYPE_CHECKING

import wasmtime

from vera.errors import Diagnostic, locate
from vera.skip import CodegenInvariantError

if TYPE_CHECKING:
    from wasmtime.component import Component

_ENGINE: wasmtime.Engine | None = None
_ENGINE_LOCK = threading.Lock()

#: How wasmtime names a function in a compile error:
#: ``wasm[0]::function[3]:::unwrap_or`` (the name after the last ``::`` is the
#: module's own, a user function's carrying its namespace's leading ``:``).
_FUNCTION_RE = re.compile(r"function\[\d+\]::(\S+)")


def engine() -> wasmtime.Engine:
    """The engine every artifact is checked with: the feature set
    ``execute()`` and the wasi-p2 host run modules under (``handle[Exn]``
    lowers to the exception-handling proposal, which wasmtime leaves off by
    default).  Built once per process, under a lock, so two threads that
    both find none built get one engine.  Lazily rather than at import:
    building one takes milliseconds, which every command would pay, a
    `vera check` that compiles nothing included."""
    global _ENGINE
    with _ENGINE_LOCK:
        if _ENGINE is None:
            config = wasmtime.Config()
            config.wasm_exceptions = True
            _ENGINE = wasmtime.Engine(config)
        return _ENGINE


def _one_line(text: str) -> str:
    return " ".join(text.split())


def _function_named(wasm_bytes: bytes | bytearray) -> str | None:
    """The function a compile of *wasm_bytes* reports its failure in, if it
    names one.  Run only after validation has failed."""
    try:
        wasmtime.Module(engine(), bytes(wasm_bytes))
    except wasmtime.WasmtimeError as exc:
        found = _FUNCTION_RE.search(str(exc))
        if found:
            return found.group(1).rsplit(":", 1)[-1] or found.group(1)
    return None


def validate_module(wasm_bytes: bytes | bytearray) -> None:
    """Refuse a core module that does not validate.

    The message is the validator's, with the function it fails in when a
    compile names one."""
    try:
        wasmtime.Module.validate(engine(), wasm_bytes)
    except wasmtime.WasmtimeError as exc:
        where = _function_named(wasm_bytes)
        raise CodegenInvariantError(
            "the module does not validate: "
            + _one_line(str(exc))
            + (f", in the function `{where}`" if where else "")
            + ". No loader accepts it, so it is not written."
        ) from exc


def build_component(wat: str) -> tuple[bytes, wasmtime.Engine, "Component"]:
    """Assemble a wasi-p2 component and construct it, which validates it.

    Returns the binary, the engine and the component, so a caller that
    runs it constructs nothing twice."""
    from wasmtime.component import Component

    binary = bytes(wasmtime.wat2wasm(wat))
    # Read once: the component and the store a caller makes from the
    # returned engine must share it.
    built_with = engine()
    try:
        component = Component(built_with, binary)
    except wasmtime.WasmtimeError as exc:
        raise CodegenInvariantError(
            "the wasi-p2 component does not validate: "
            + _one_line(str(exc))
            + ". No loader accepts it, so it is not written."
        ) from exc
    return binary, built_with, component


def assembly_error(msg: str, file: str | None) -> Diagnostic:
    """The E699 for an artifact assembly or validation refuses: a compiler
    defect, not something to change in the program."""
    return Diagnostic(
        description=(
            f"Internal compiler error while assembling the module: {msg}"
        ),
        **locate(file, ""),
        rationale=(
            "Code generation produced a module WebAssembly "
            "cannot load. That is a bug in the compiler, not "
            "something to change in the program: a program the "
            "checker should have refused was not, or a valid "
            "one was compiled under a clashing name or into a "
            "module that does not validate."
        ),
        fix=(
            "Please file a bug report with the offending "
            "program at https://github.com/aallan/vera/issues"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E699",
    )
