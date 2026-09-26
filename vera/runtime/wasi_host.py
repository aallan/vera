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
from vera.codegen.wasi import (
    ADAPTER_MODULE,
    CONTRACT_FAIL_FUNCTION,
    MESSAGE_START_MARK,
    TRAP_KIND_FUNCTION_PREFIX,
    emit_wasi_component,
)
from vera.runtime.text import safe_utf8_decode
from vera.runtime.traps import _classify_trap
from vera.trap_registry import NATIVE_TRAP_OPCODES, TRAP_KINDS

#: The innermost frame of a component trap's rendered backtrace,
#: ``    0:    0xf9e - Adapter!trap_kind_index_out_of_bounds``: the offset is
#: into the component binary, and the name is ``<module>!<function>``.
_INNERMOST_FRAME = re.compile(
    r"^\s*0:\s+0x([0-9a-f]+)\s+-\s+(\S+)", re.MULTILINE)

#: The frame a contract violation traps in, and the frames a named check
#: traps in — the adapter's own functions (#1479).  Matched against the
#: WHOLE innermost frame name, and only it: every program function on the
#: stack is in the backtrace too, as ``Main!<name>``, and a program function
#: may be called ``contract_fail`` or ``trap_kind_overflow``; none can live
#: in the adapter module.
_CONTRACT_FRAME = f"{ADAPTER_MODULE}!{CONTRACT_FAIL_FUNCTION}"
_TRAP_KIND_FRAME = re.compile(
    re.escape(f"{ADAPTER_MODULE}!{TRAP_KIND_FUNCTION_PREFIX}") + r"([a-z_]+)")


def _innermost_frame(message: str) -> tuple[int, str] | None:
    """The innermost frame of a component trap's backtrace, as its offset
    into the component binary and its ``<module>!<function>`` name; None
    when the backtrace names none."""
    frame = _INNERMOST_FRAME.search(message)
    if frame is None:
        return None
    return int(frame.group(1), 16), frame.group(2)


def _component_trap_instruction(offset: int, binary: bytes) -> str | None:
    """The natively trapping instruction at *offset* in *binary* — the
    component the trap came from — or None."""
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
    # Every stderr write, as its (offset, length) in err_buf: a trap's
    # message starts after the adapter's mark, which only the write
    # boundaries can tell from the same byte in the program's output
    # (`message_start`, #1479).
    err_writes: list[tuple[int, int]] = []

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
        err_writes.append((len(err_buf), len(chunk)))
        err_buf.extend(chunk)

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
            out_buf, err_buf, err_writes,
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
    err_writes: list[tuple[int, int]],
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
            trap, out_buf, err_buf, message_mark(err_buf, err_writes),
            binary,
        ) from trap

    return ExecuteResult(
        value=value,
        stdout=safe_utf8_decode(bytes(out_buf)),
        exit_code=exit_code,
        stderr=safe_utf8_decode(bytes(err_buf)),
    )


def message_mark(
    err_buf: bytes | bytearray, writes: list[tuple[int, int]],
) -> int | None:
    """The offset in *err_buf* of the mark a trap's message follows, or
    None.

    Each of the adapter's message channels writes its mark — the one byte
    ``MESSAGE_START_MARK``, as a write of its own — and then the message,
    every chunk of it but the last a full 4096 bytes (#1479).  So the mark
    is the last one-byte write of that byte that another write follows: no
    chunk of the message is one byte except possibly its last, which
    nothing follows, and everything the program wrote came before.  What
    precedes the mark is the program's own stderr, and everything after it
    is the message; *writes* holds each write's ``(offset, length)``.  None
    when no write is the mark, or when the writes after it are not a
    message's chunks.
    """
    for i in range(len(writes) - 2, -1, -1):
        offset, length = writes[i]
        if length == 1 and err_buf[offset] == MESSAGE_START_MARK[0]:
            chunks = [n for _, n in writes[i + 1:-1]]
            return offset if all(n == 4096 for n in chunks) else None
    return None


def _component_trap_error(
    trap: BaseException,
    out_buf: bytearray,
    err_buf: bytearray,
    mark: int | None,
    binary: bytes = b"",
) -> WasmTrapError:
    """Wrap a component trap in the core path's ``WasmTrapError`` shape.

    The core path's host-import side channels (``last_violation``,
    ``last_trap``) don't exist inside a component, so the adapter function a
    trap happened in identifies the same conditions: the innermost frame is
    ``Adapter!op_contract_fail`` for a contract, and ``Adapter!trap_kind_<name>``
    for a check ``vera.trap`` named (#1479) — the adapter traps inside a
    function named for the kind precisely so this can read it.  Only the
    innermost frame's whole name is read, and only the adapter module's: the
    backtrace names every program function on the stack too, and a program
    function's name must not decide the kind.  A message travels the one
    way a component can send one: the adapter writes it to WASI stderr as
    its last act before trapping, after a mark saying where it starts —
    *mark*, the mark's offset in *err_buf* (:func:`message_mark`) — so
    everything after the mark IS the message, whole, for a contract and for
    any kind whose sites carry their own (``TrapKind.site_message``).  The
    mark and the message are removed from the program's stderr transcript,
    which restores the core path's stream separation.
    """
    msg = str(trap)
    stdout = safe_utf8_decode(bytes(out_buf))
    stderr = safe_utf8_decode(bytes(err_buf))

    def _take_message(fallback: str) -> str:
        nonlocal stderr
        if mark is None:
            return fallback
        stderr = safe_utf8_decode(bytes(err_buf[:mark]))
        text = err_buf[mark + len(MESSAGE_START_MARK):]
        return safe_utf8_decode(bytes(text)) or fallback

    frame = _innermost_frame(msg)
    frame_name = frame[1] if frame is not None else ""
    named = _TRAP_KIND_FRAME.fullmatch(frame_name)
    if frame_name == _CONTRACT_FRAME:
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
        instruction = (_component_trap_instruction(frame[0], binary)
                       if frame is not None else None)
        kind, description, fix = _classify_trap(
            trap, [], instruction=instruction)
    return WasmTrapError(
        description,
        stdout=stdout,
        stderr=stderr,
        kind=kind,
        frames=[],  # structured frames don't cross the component boundary
        fix=fix,
    )
