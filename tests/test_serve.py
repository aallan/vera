"""End-to-end tests for the #305 ``vera serve`` driver.

The driver (``vera/runtime/server.py``) serves a compiled program's
``handle(Request -> Response)`` function over HTTP: one fresh
instantiation per request (perfect isolation — WASI.md check 9 measured
instantiation at ~0.02 ms), the Request ADT built into guest memory
host-side, the Response ADT decoded back, and a handler trap (including
a contract violation) mapped to a 500 whose body carries the trap
diagnostic.

All tests bind an ephemeral port (``port=0``) per the cross-platform
fixture rules in TESTING.md.
"""

from __future__ import annotations

import json
import threading
import urllib.request

import pytest

from tests.codegen_helpers import _compile_ok
from vera.runtime.server import make_server


ECHO_HANDLER = """
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  match @Request.0 {
    Request(@String, @String, @Map<String, String>, @String) ->
      Response(200, map_insert(map_new(), "x-echo-path", @String.1),
               string_concat(@String.0, @String.2))
  }
}
"""
# De Bruijn in the arm: the three String bindings are method (oldest,
# @String.2), path (@String.1), body (most recent, @String.0); headers
# bind the @Map slot and do not shift String indices.


def _request(
    url: str, method: str = "GET", body: bytes | None = None,
) -> tuple[int, dict[str, str], str]:
    req = urllib.request.Request(url, data=body, method=method)
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            return (
                resp.status,
                {k.lower(): v for k, v in resp.headers.items()},
                resp.read().decode("utf-8"),
            )
    except urllib.error.HTTPError as err:  # 4xx/5xx still carry a body
        return (
            err.code,
            {k.lower(): v for k, v in err.headers.items()},
            err.read().decode("utf-8"),
        )


class _Server:
    """Context manager: serve `source` on an ephemeral port."""

    def __init__(self, source: str) -> None:
        self._result = _compile_ok(source)
        self._httpd = make_server(self._result, host="127.0.0.1", port=0)
        self.port = self._httpd.server_address[1]

    def __enter__(self) -> "_Server":
        self._thread = threading.Thread(
            target=self._httpd.serve_forever, daemon=True,
        )
        self._thread.start()
        return self

    def __exit__(self, *exc: object) -> None:
        self._httpd.shutdown()
        self._httpd.server_close()

    def url(self, path: str) -> str:
        return f"http://127.0.0.1:{self.port}{path}"


class TestServeEndToEnd305:
    def test_get_echoes_method_and_path_header(self) -> None:
        with _Server(ECHO_HANDLER) as srv:
            status, headers, body = _request(srv.url("/hello"))
        assert status == 200
        assert body == "GET"  # empty request body + method
        assert headers.get("x-echo-path") == "/hello"

    def test_post_body_reaches_the_handler(self) -> None:
        with _Server(ECHO_HANDLER) as srv:
            status, _headers, body = _request(
                srv.url("/submit"), method="POST", body=b"payload:",
            )
        assert status == 200
        assert body == "payload:POST"

    def test_handler_status_propagates(self) -> None:
        source = """
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{ Response(404, map_new(), "nope") }
"""
        with _Server(source) as srv:
            status, _headers, body = _request(srv.url("/missing"))
        assert status == 404
        assert body == "nope"

    def test_contract_violation_maps_to_500_with_diagnostic(self) -> None:
        """The #305 headline inverse: a handler whose postcondition
        fails at runtime answers 500, and the body carries the
        contract-violation trap diagnostic — never a hung connection
        or a silent empty 200."""
        source = """
public fn handle(@Request -> @Response)
  requires(true)
  ensures(false)
  effects(<HttpServer>)
{ Response(200, map_new(), "never") }
"""
        with _Server(source) as srv:
            status, _headers, body = _request(srv.url("/boom"))
        assert status == 500
        payload = json.loads(body)
        assert payload["trap_kind"] == "contract_violation"

    def test_requests_are_isolated_fresh_instance_each(self) -> None:
        """Instance-per-request: State<Int> mutated inside one request
        must not leak into the next (both requests observe the same
        initial state and answer identically)."""
        source = """
public fn bump(@Unit -> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{
  put(get(()) + 1);
  get(())
}

public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer, State<Int>>)
{ Response(200, map_new(), int_to_string(bump(()))) }
"""
        with _Server(source) as srv:
            _s1, _h1, body1 = _request(srv.url("/a"))
            _s2, _h2, body2 = _request(srv.url("/b"))
        assert body1 == "1"
        assert body2 == "1", (
            "state leaked across requests — instance-per-request "
            "isolation is broken"
        )


class TestServeValidation305:
    def test_missing_handler_is_a_clean_error(self) -> None:
        result = _compile_ok("""
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")
        with pytest.raises(ValueError, match="handle"):
            make_server(result, host="127.0.0.1", port=0)

    def test_wrong_signature_is_a_clean_error(self) -> None:
        result = _compile_ok("""
public fn handle(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        with pytest.raises(ValueError, match="Request"):
            make_server(result, host="127.0.0.1", port=0)
