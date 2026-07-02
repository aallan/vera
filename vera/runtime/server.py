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


def validate_handler(
    result: CompileResult, *, context: str = "vera serve",
) -> None:
    """Fail loudly unless the program has a servable handler.

    The contract: a public ``handle`` export taking exactly the prelude
    ``Request`` and returning ``Response``.  The layouts check doubles
    as the type check — the prelude injects Request/Response only when
    the program mentions them, so their absence means ``handle`` (if
    any) has some other signature.

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
    if (
        "Request" not in result.adt_layouts
        or "Response" not in result.adt_layouts
        or result.fn_param_types.get("handle") != ["i32"]
    ):
        raise ValueError(
            f"{context}: 'handle' must take exactly one @Request "
            "parameter and return @Response"
        )


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
                # Contract violation / runtime trap → 500 with the
                # trap diagnostic; the connection is always answered.
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
        do_GET = _serve  # noqa: N815 (stdlib API names)
        do_POST = _serve  # noqa: N815
        do_PUT = _serve  # noqa: N815
        do_DELETE = _serve  # noqa: N815
        do_PATCH = _serve  # noqa: N815
        do_HEAD = _serve  # noqa: N815

        def log_message(self, fmt: str, *args: object) -> None:
            # One concise access-log line to the server console.
            sys.stderr.write(
                f"{self.address_string()} - {fmt % args}\n"
            )

    return http.server.HTTPServer((host, port), _Handler)
