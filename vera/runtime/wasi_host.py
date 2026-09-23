"""#237 — host-side runner for the WASI Preview 2 target.

``execute_wasi_p2`` runs a compiled program as a wasip2 *component*
under wasmtime's built-in WASI host (``component.Linker.add_wasip2()``)
— none of the ``vera.*`` host bindings in ``vera/codegen/api.py`` are
registered.  This is the same execution environment a stock
``wasmtime run`` gives the artifact ``vera compile --target wasi-p2``
writes, so behavior here is evidence the component is genuinely
host-independent.

Contract parity with the core-path ``execute()``:

* stdout/stderr are captured into ``ExecuteResult`` via
  ``WasiConfig.stdout_custom``/``stderr_custom`` (with an optional
  live tee for the #543 streaming behavior in text mode);
* ``IO.get_env`` sees the process environment (snapshotted into the
  config at launch — a wasip2 component receives its environment once);
* ``IO.read_file``/``write_file`` resolve relative to the current
  directory via a ``preopen_dir(".", "/")`` mapping;
* traps re-raise as :class:`WasmTrapError` with the same ``kind``
  taxonomy.  The component path loses structured trap frames (WASI.md
  spike check 5), so ``frames`` is always empty; the adapter function
  names surviving in the wasmtime backtrace text — ``contract_fail``, and
  the per-kind ``trap_kind_<name>`` functions ``vera.trap`` dispatches to
  (#1479) — stand in for the core path's host-import side channels.

Known divergence (inherent to WASI 0.2, documented in spec chapter
13): ``wasi:cli/exit@0.2.0`` carries only ok/err, so ``IO.exit(n)``
surfaces as exit code 0 or 1 — under this runner *and* every stock
wasip2 host.

A ``WasiConfig`` is ALWAYS set on the store before any call: invoking
a wasip2 import on a config-less store aborts the whole process
(SIGABRT), per the WASI.md spike invariants.

The store is ALWAYS released before ``execute_wasi_p2`` returns or raises,
and the call waits until wasmtime has let go of both output callbacks
(:func:`_release_store`): a callback wasmtime releases from one of its own
threads while the interpreter shuts down aborts the process the same way.
"""

from __future__ import annotations

import codecs
import os
import re
import sys
import threading
import time
import weakref
from collections.abc import Sequence
from typing import TYPE_CHECKING, Protocol

from vera.codegen.api import ExecuteResult, WasmTrapError
from vera.codegen.wasi import emit_wasi_component
from vera.runtime.text import safe_utf8_decode
from vera.runtime.traps import _classify_trap
from vera.trap_registry import NATIVE_TRAP_OPCODES, TRAP_KINDS

#: The adapter function a named trap executes its ``unreachable`` in, as the
#: wasmtime backtrace renders it (``Adapter!trap_kind_nat_underflow``).
_TRAP_KIND_FRAME = re.compile(r"!trap_kind_([a-z_]+)")

#: The innermost frame of a component trap's rendered backtrace
#: (``    0:    0x840 - Main!main``): its offset is into the component
#: binary, which is how the trapping instruction is read (#1479).
_INNERMOST_FRAME_OFFSET = re.compile(r"^\s*0:\s+0x([0-9a-f]+)\s", re.MULTILINE)


def _component_trap_instruction(message: str, binary: bytes) -> str | None:
    """The natively trapping instruction a component trap stopped at, read
    from *binary* — the component the trap came from — at the innermost
    frame's offset; None when the backtrace names no frame there."""
    frame = _INNERMOST_FRAME_OFFSET.search(message)
    if frame is None:
        return None
    offset = int(frame.group(1), 16)
    if not 0 <= offset < len(binary):
        return None
    return NATIVE_TRAP_OPCODES.get(binary[offset])

#: The longest :func:`_release_store` waits for wasmtime to let go of the
#: output callbacks.  A release takes well under a millisecond; the bound only
#: keeps a wasmtime that never releases them from hanging a run.
_OUTPUT_RELEASE_TIMEOUT_S = 2.0


class _Closable(Protocol):
    def close(self) -> None: ...


def _release_store(
    store: _Closable,
    released: Sequence[threading.Event],
    *,
    timeout: float = _OUTPUT_RELEASE_TIMEOUT_S,
) -> bool:
    """Release *store* now, then wait until every event in *released* is set.

    wasmtime drops a stdout / stderr stream on whichever thread holds it
    last — a stream the program wrote to belongs to a tokio worker, which
    drops it after the store is freed — and the drop calls back into Python
    to release the output callback.  A Python callback from a foreign thread
    while the interpreter shuts down ends that thread with ``pthread_exit``,
    whose forced unwind cannot cross wasmtime's Rust frames, so the process
    aborts (SIGABRT, "panic in a function that cannot unwind").  Freeing the
    store here, rather than whenever the last Python reference goes, is what
    keeps the release inside the call: after a trap the error wasmtime-py
    raises holds its own frame, and with it the store, in a reference cycle
    that only the cycle collector frees — at interpreter shutdown, in a
    process about to exit.  Each event is set when wasmtime lets go of one
    callback, so returning after them means no wasmtime thread calls into
    Python once the call is over.  Returns whether they all were set within
    *timeout* seconds.
    """
    store.close()
    deadline = time.monotonic() + timeout
    return all(
        event.wait(max(0.0, deadline - time.monotonic()))
        for event in released
    )

if TYPE_CHECKING:
    import wasmtime
    from wasmtime.component import Component, Linker

    from vera.codegen.api import CompileResult


def execute_wasi_p2(
    result: "CompileResult",
    *,
    cli_args: list[str] | None = None,
    argv0: str = "vera-program",
    tee_stdout: bool = False,
) -> ExecuteResult:
    """Run ``result`` as a wasip2 component; call the ``main`` lift.

    ``cli_args`` become ``argv[1:]`` (``IO.args`` skips ``argv0``, the
    canonical WASI convention).  A String-returning ``main`` has no
    scalar lift in v1 — the runner drives the ``wasi:cli/run`` world
    entry instead and ``value`` is ``None``.

    Raises ``ValueError`` (from the emitter's family gate) when the
    program uses a host family the target does not support, and
    ``WasmTrapError`` on a runtime trap.
    """
    import wasmtime
    from wasmtime.component import Component, Linker

    wat = emit_wasi_component(result)
    # Assembled here rather than inside `Component`, so a trap's backtrace
    # offset can be read against the same bytes (#1479).
    binary = bytes(wasmtime.wat2wasm(wat))

    # Same engine feature set as the core-path execute(): handle[Exn]
    # compiles to the WASM exception-handling proposal, which wasmtime
    # gates off by default — without it an EH program's component
    # fails to PARSE (caught by the dual-target conformance sweep).
    engine_config = wasmtime.Config()
    engine_config.wasm_exceptions = True
    engine = wasmtime.Engine(engine_config)
    component = Component(engine, binary)
    linker = Linker(engine)
    linker.add_wasip2()
    store = wasmtime.Store(engine)

    config = wasmtime.WasiConfig()
    out_buf = bytearray()
    err_buf = bytearray()
    # The adapter writes a contract-violation message as ONE stderr
    # write immediately before trapping, and messages are far below the
    # 4096-byte chunking cap — so the last chunk seen here IS the
    # violation text when a contract_fail trap fires.
    last_err_chunk: list[bytes] = [b""]

    if tee_stdout:
        # Incremental decoder: the 4096-byte write cap can split a
        # multibyte UTF-8 sequence across chunks; decoding each chunk
        # independently would corrupt it at the boundary.
        tee_decoder = codecs.getincrementaldecoder("utf-8")(
            errors="replace",
        )

        def _on_stdout(chunk: bytes) -> None:
            out_buf.extend(chunk)
            sys.stdout.write(tee_decoder.decode(chunk))
            sys.stdout.flush()
    else:

        def _on_stdout(chunk: bytes) -> None:
            out_buf.extend(chunk)

    def _on_stderr(chunk: bytes) -> None:
        err_buf.extend(chunk)
        last_err_chunk[0] = bytes(chunk)

    # wasmtime owns each callback until it drops the stream that writes
    # through it; each event is set when it lets go, which `_release_store`
    # waits for.  The names go, so wasmtime's is the last reference.
    released = (threading.Event(), threading.Event())
    weakref.finalize(_on_stdout, released[0].set)
    weakref.finalize(_on_stderr, released[1].set)
    config.stdout_custom = _on_stdout
    config.stderr_custom = _on_stderr
    del _on_stdout, _on_stderr
    try:
        return _run_component(
            store, config, linker, component,
            out_buf, err_buf, last_err_chunk,
            argv=[argv0, *(cli_args or [])], binary=binary,
        )
    finally:
        # A config the store never took still owns the callbacks.
        config.close()
        _release_store(store, released)


def _run_component(
    store: "wasmtime.Store",
    config: "wasmtime.WasiConfig",
    linker: "Linker",
    component: "Component",
    out_buf: bytearray,
    err_buf: bytearray,
    last_err_chunk: list[bytes],
    *,
    argv: list[str],
    binary: bytes,
) -> ExecuteResult:
    """Configure, instantiate and call the component; the body of
    :func:`execute_wasi_p2`, which releases the store around it."""
    import wasmtime

    config.argv = argv
    config.env = list(os.environ.items())
    config.inherit_stdin()
    config.preopen_dir(".", "/")
    store.set_wasi(config)

    instance = linker.instantiate(store, component)
    exit_code: int | None = None
    value: int | float | str | None = None
    try:
        func = instance.get_func(store, "main")
        if func is not None:
            raw = func(store)
            func.post_return(store)
            if isinstance(raw, (int, float, str)):
                value = raw
        else:
            # String-returning main: no scalar lift — use the
            # wasi:cli/run world entry (what stock `wasmtime run`
            # invokes).  A trap inside main propagates as an
            # exception, so reaching post_return means it ran ok.
            iface = instance.get_export_index(
                store, "wasi:cli/run@0.2.0",
            )
            run_idx = (
                None if iface is None
                else instance.get_export_index(
                    store, "run", instance=iface,
                )
            )
            run_func = (
                None if run_idx is None
                else instance.get_func(store, run_idx)
            )
            if run_func is None:
                raise RuntimeError(
                    "emitted component lacks both a 'main' lift and "
                    "the wasi:cli/run entry — emitter invariant broken"
                )
            run_func(store)
            run_func.post_return(store)
    except wasmtime.ExitTrap as trap:
        # wasi:cli/exit carries ok/err only: .code is 0 or 1 no matter
        # what IO.exit was given (see module docstring).
        exit_code = trap.code if trap.code is not None else 1
    except wasmtime.WasmtimeError as trap:
        raise _component_trap_error(
            trap, out_buf, err_buf, last_err_chunk[0], binary,
        ) from trap

    return ExecuteResult(
        value=value,
        stdout=safe_utf8_decode(bytes(out_buf)),
        exit_code=exit_code,
        stderr=safe_utf8_decode(bytes(err_buf)),
    )


def _component_trap_error(
    trap: BaseException,
    out_buf: bytearray,
    err_buf: bytearray,
    last_err_chunk: bytes,
    binary: bytes = b"",
) -> WasmTrapError:
    """Wrap a component trap in the core path's ``WasmTrapError`` shape.

    The core path's host-import side channels (``last_violation``,
    ``last_trap``) don't exist inside a component, so the adapter function
    names in the wasmtime backtrace text identify the same conditions:
    ``contract_fail`` for a contract, and ``trap_kind_<name>`` for a check
    ``vera.trap`` named (#1479) — the adapter traps inside a function named
    for the kind precisely so this can read it.  A message travels the one
    way a component can send one: the adapter writes it to WASI stderr as
    its last act before trapping, so the last chunk seen here IS the
    message for a contract and for any kind whose sites carry their own
    (``TrapKind.site_message``).  It is removed from the program's stderr
    transcript, which restores the core path's stream separation.
    """
    msg = str(trap)
    stdout = safe_utf8_decode(bytes(out_buf))
    stderr = safe_utf8_decode(bytes(err_buf))

    def _take_message(fallback: str) -> str:
        nonlocal stderr
        text = safe_utf8_decode(last_err_chunk) or fallback
        if text and stderr.endswith(text):
            stderr = stderr[: -len(text)]
        return text

    named = _TRAP_KIND_FRAME.search(msg)
    if "contract_fail" in msg:
        violation = _take_message("Contract violation")
        kind, description, fix = _classify_trap(trap, [violation])
    elif named is not None and named.group(1) in TRAP_KINDS:
        row = TRAP_KINDS[named.group(1)]
        message = (_take_message(row.description) if row.site_message
                   else "")
        kind, description, fix = _classify_trap(
            trap, [], [(row.code, message)])
    else:
        # A trap the engine raised itself: its kind needs the instruction
        # where wasmtime's reason is shared (#1479), read from *binary*.
        kind, description, fix = _classify_trap(
            trap, [], instruction=_component_trap_instruction(msg, binary))
    return WasmTrapError(
        description,
        stdout=stdout,
        stderr=stderr,
        kind=kind,
        frames=[],  # structured frames don't cross the component boundary
        fix=fix,
    )
