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
  spike check 5), so ``frames`` is always empty; the ``contract_fail``
  / ``overflow_trap`` shim names surviving in the wasmtime backtrace
  text stand in for the core path's host-import side channels.

Known divergence (inherent to WASI 0.2, documented in spec chapter
13): ``wasi:cli/exit@0.2.0`` carries only ok/err, so ``IO.exit(n)``
surfaces as exit code 0 or 1 — under this runner *and* every stock
wasip2 host.

A ``WasiConfig`` is ALWAYS set on the store before any call: invoking
a wasip2 import on a config-less store aborts the whole process
(SIGABRT), per the WASI.md spike invariants.
"""

from __future__ import annotations

import codecs
import os
import sys
from typing import TYPE_CHECKING

from vera.codegen.api import ExecuteResult, WasmTrapError
from vera.codegen.wasi import emit_wasi_component
from vera.runtime.text import safe_utf8_decode
from vera.runtime.traps import _classify_trap

if TYPE_CHECKING:
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

    # Same engine feature set as the core-path execute(): handle[Exn]
    # compiles to the WASM exception-handling proposal, which wasmtime
    # gates off by default — without it an EH program's component
    # fails to PARSE (caught by the dual-target conformance sweep).
    engine_config = wasmtime.Config()
    engine_config.wasm_exceptions = True
    engine = wasmtime.Engine(engine_config)
    component = Component(engine, wat)
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

        config.stdout_custom = _on_stdout
    else:
        config.stdout_custom = out_buf.extend

    def _on_stderr(chunk: bytes) -> None:
        err_buf.extend(chunk)
        last_err_chunk[0] = bytes(chunk)

    config.stderr_custom = _on_stderr
    config.argv = [argv0, *(cli_args or [])]
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
            trap, out_buf, err_buf, last_err_chunk[0],
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
) -> WasmTrapError:
    """Wrap a component trap in the core path's ``WasmTrapError`` shape.

    The core path's host-import side channels (``last_violation``,
    ``last_overflow``) don't exist inside a component; the shim names
    in the wasmtime backtrace text (``Main!vera.contract_fail``,
    ``Main!vera.overflow_trap``) identify the same conditions, and the
    violation message itself is the last thing the adapter wrote to
    WASI stderr before trapping.
    """
    msg = str(trap)
    stdout = safe_utf8_decode(bytes(out_buf))
    stderr = safe_utf8_decode(bytes(err_buf))
    if "contract_fail" in msg:
        violation = safe_utf8_decode(last_err_chunk) or "Contract violation"
        # Restore core-path stream separation: the violation text
        # travels in the diagnostic description, not in the program's
        # stderr transcript.
        if violation and stderr.endswith(violation):
            stderr = stderr[: -len(violation)]
        kind, description, fix = _classify_trap(trap, [violation])
    elif "overflow_trap" in msg:
        kind, description, fix = _classify_trap(trap, [], [True])
    else:
        kind, description, fix = _classify_trap(trap, [])
    return WasmTrapError(
        description,
        stdout=stdout,
        stderr=stderr,
        kind=kind,
        frames=[],  # structured frames don't cross the component boundary
        fix=fix,
    )
