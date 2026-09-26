"""#305 — the ``vera serve`` HTTP driver.

Serves a compiled program's ``handle(Request -> Response)`` function
over HTTP with **instance-per-request isolation**: each request runs a
fresh ``execute()`` (fresh Store, fresh host state — WASI.md check 9
measured instantiation at ~0.02 ms, so isolation is effectively free).
The accept loop lives HERE, in the host — handlers are total,
termination-checked functions and need no ``Diverge``.

Request handling is sequential (v1, per the #305 plan): stdlib
``http.server.HTTPServer`` on a single thread.  A handler trap —
including a runtime contract violation — maps to a 500 whose JSON body
carries the trap diagnostic (``trap_kind``, message, frames), the same
envelope shape ``vera run --json`` uses.  Handler ``IO.print`` output
is forwarded to the server console.
"""

from __future__ import annotations

import http.server
import json
import sys

from vera.codegen.api import CompileResult, HttpRequestData, execute
from vera.runtime.traps import WasmTrapError


def _is_prelude_adt(result: CompileResult, actual: str | None, want: str) -> bool:
    """Is *actual* the PRELUDE's ``want``, and not merely spelled like it?

    Two facts, both required (#1442).  The name must match, and the
    prelude injection must be the thing that supplied it: an entry file
    may declare its own ``data Request``, which shadows the prelude's
    (spec 8.4.1) and takes over the single ``adt_layouts`` slot for that
    name, leaving a program whose Vera signature reads ``@Request ->
    @Response`` while neither type is the one the host marshals.
    Per-owner ADT identity is what makes the second question meaningful:
    a type is identified by who declared it, not by how it is spelled.
    """
    return actual == want and want in result.prelude_injected_adts


def validate_handler(
    result: CompileResult, *, context: str = "vera serve",
) -> None:
    """Fail loudly unless the program has a servable handler.

    The contract: a public ``handle`` export taking exactly the prelude
    ``Request`` and returning the prelude ``Response``.

    Checked against the VERA types (``fn_adt_signatures``), because the
    lowered ABI cannot express the contract and neither can the layout
    map (#1442).  This guard used to ask two proxy questions — are
    ``Request`` and ``Response`` in ``adt_layouts``, and does ``handle``
    lower to ``["i32"]`` — and a program can satisfy both while
    ``handle`` has nothing to do with either type:

    - the prelude injects the ADTs when the PROGRAM mentions them, so
      any other function in the file supplies the layouts; and
    - ``i32`` is the lowered shape of ``Bool``, of every heap ADT and of
      every boxed value, so the ABI cannot tell a ``Request`` pointer
      from anything else that is pointer-shaped.

    A ``handle(@Bool -> @Bool)`` beside a ``keep(@Request -> @Response)``
    passed both, and then ``make_server`` marshalled an
    ``HttpRequestData`` into guest memory, handed the pointer to a
    ``Bool`` parameter, and decoded whatever came back as a ``Response``
    — reading a garbage headers pointer past the end of linear memory
    into wasmtime's guard page, which is a ``SIGBUS`` in the host
    process rather than a guest trap.

    Shared between this #305 host driver and the wasi-p2 server-world
    emitter (``vera/codegen/wasi.py``) so the two serving surfaces
    cannot drift; ``context`` prefixes the diagnostics with the surface
    that rejected the program.
    """
    if "handle" not in result.exports:
        raise ValueError(
            f"{context}: the program must export a public "
            "'handle' function (public fn handle(@Request -> @Response) "
            "effects(<HttpServer>))"
        )
    if "handle" not in result.fn_adt_signatures:
        # `handle` is in `exports`, so codegen compiled it, but no
        # declaration of that name was walked.  That is a compiler
        # invariant violation rather than anything the program did, and
        # reporting it through the parameter-count branch below would
        # blame the user for "0 parameter(s)".  Refusing is still the
        # right outcome — the guard fails closed — but it has to say
        # what it actually observed.
        raise ValueError(
            f"{context}: internal error — 'handle' is exported but has "
            "no recorded Vera signature, so it cannot be checked against "
            "@Request / @Response; please report this with the program"
        )
    params, ret = result.fn_adt_signatures["handle"]
    wrong = []
    if len(params) != 1:
        wrong.append(
            f"it takes {len(params)} parameter(s), not exactly one @Request"
        )
    elif not _is_prelude_adt(result, params[0], "Request"):
        wrong.append(_explain("its parameter is", params[0], "Request"))
    if not _is_prelude_adt(result, ret, "Response"):
        wrong.append(_explain("it returns", ret, "Response"))
    if wrong:
        raise ValueError(
            f"{context}: 'handle' must take exactly one @Request "
            "parameter and return @Response — " + "; ".join(wrong)
        )


def _explain(position: str, actual: str | None, want: str) -> str:
    """One clause saying how a handler position is wrong.

    Three ways, because the REMEDY differs in each and a diagnostic's
    job is to name the fix:

    - not a data type at all (a primitive, String, Array, ...) — the
      signature is simply something else;
    - a different data type — likewise a signature to change, and
      naming it saves the reader guessing which position is meant;
    - the RIGHT name, declared by this program — a shadowing to delete,
      which no message mentioning only ``@Request`` could convey, since
      the program plainly does say ``@Request``.

    Each clause is complete on its own: the caller joins them, and does
    not append a shared "not the prelude @X" tail, which turned the
    first case into the double negative "is not a data type, not the
    prelude @Request".
    """
    if actual is None:
        return f"{position} not a data type, so it cannot be @{want}"
    if actual == want:
        return (
            f"{position} this program's own @{actual}, which shadows the "
            "prelude's"
        )
    return f"{position} @{actual}, not the prelude @{want}"


def _validate_handler(result: CompileResult) -> None:
    """#305 driver entry — ``validate_handler`` with the serve context."""
    validate_handler(result, context="vera serve")


def make_server(
    result: CompileResult,
    host: str = "127.0.0.1",
    port: int = 8000,
    env_vars: dict[str, str] | None = None,
) -> http.server.HTTPServer:
    """Bind an HTTP server that serves ``result``'s handler.

    Returns the bound (not yet running) server; callers drive it with
    ``serve_forever()`` and stop it with ``shutdown()``.  ``port=0``
    binds an ephemeral port (tests read ``server_address[1]``).
    """
    _validate_handler(result)

    class _Handler(http.server.BaseHTTPRequestHandler):
        # One fresh execute() per request — perfect isolation.
        def _serve(self) -> None:
            length = int(self.headers.get("Content-Length") or 0)
            body = (
                self.rfile.read(length).decode("utf-8", errors="replace")
                if length
                else ""
            )
            request = HttpRequestData(
                method=self.command,
                path=self.path,
                headers={k.lower(): v for k, v in self.headers.items()},
                body=body,
            )
            try:
                er = execute(
                    result, fn_name="handle", http_request=request,
                    env_vars=env_vars,
                )
            except WasmTrapError as trap:
                # Contract violation, runtime trap, or a host import
                # that raised (#1302 routes those here too, as
                # ``kind="host_error"``) → 500 with the diagnostic; the
                # connection is always answered.  Before #1302 a host
                # callback's exception escaped this handler entirely and
                # the request went unanswered.
                payload = json.dumps({
                    "error": str(trap),
                    "trap_kind": trap.kind,
                    "frames": [f.to_dict() for f in trap.frames],
                })
                self._respond(500, {"content-type": "application/json"},
                              payload)
                if trap.stdout:
                    sys.stdout.write(trap.stdout)
                return
            if er.stdout:
                sys.stdout.write(er.stdout)
                sys.stdout.flush()
            resp = er.http_response
            assert resp is not None  # noqa: S101 — set for http_request calls
            from typing import cast
            status = cast("int", resp["status"])
            headers = cast("dict[str, str]", resp["headers"])
            body_out = cast("str", resp["body"])
            self._respond(status, headers, body_out)

        def _respond(
            self, status: int, headers: dict[str, str], body: str,
        ) -> None:
            data = body.encode("utf-8")
            self.send_response(status)
            for k, v in headers.items():
                if k.lower() not in ("content-length",):
                    self.send_header(k, v)
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        # Same handler for every method the stdlib dispatches by name.
        do_GET = _serve
        do_POST = _serve
        do_PUT = _serve
        do_DELETE = _serve
        do_PATCH = _serve
        do_HEAD = _serve

        def log_message(self, fmt: str, *args: object) -> None:
            # One concise access-log line to the server console.
            sys.stderr.write(
                f"{self.address_string()} - {fmt % args}\n"
            )

    return http.server.HTTPServer((host, port), _Handler)
