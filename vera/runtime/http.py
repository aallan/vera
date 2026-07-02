"""HTTP effect host bindings.

Extracted from `execute()` in `vera/codegen/api.py` (#421); stateless --
the host callbacks use only the module-level `vera.runtime.heap` helpers.

#841: the pure fetch halves (`fetch_get` / `fetch_post`) are split out
from the host callbacks so the fused-async bindings in
`vera/runtime/async_http.py` can run the same request logic on a host
worker thread (which must never touch guest memory) and defer the
Result-ADT construction to the guest thread at await time.
"""

from __future__ import annotations

import wasmtime

from vera.runtime.heap import (
    _alloc_result_err_string,
    _alloc_result_ok_string,
    _read_wasm_string,
)

_HTTP_TIMEOUT: int = 60  # seconds; prevents indefinite hangs on slow HTTP calls


def _is_allowed_http_url(url: str) -> bool:
    """True iff ``url`` uses the ``http`` or ``https`` scheme.

    #789: the ``Http`` effect must not open ``file://``, ``ftp://``,
    ``data:``, etc. — ``urllib.request.urlopen`` would otherwise read
    local files or speak arbitrary protocols on behalf of a Vera
    program.  Both fetch halves validate the scheme and return an err
    tuple for anything that isn't HTTP(S).  Pure + module-level so it
    is unit-testable without a wasmtime instance.
    """
    from urllib.parse import urlparse

    return urlparse(url).scheme.lower() in ("http", "https")


def fetch_get(url: str) -> tuple[bool, str]:
    """Perform ``Http.get`` and return ``(is_ok, payload)``.

    Pure Python (no guest-memory access), so it is safe on a host
    worker thread (#841).  Never raises for value-level failures — the
    err payload is the message the guest sees in ``Result.Err``.
    """
    if not _is_allowed_http_url(url):
        return (
            False,
            "Http.get: refusing non-HTTP(S) URL; only 'http' "
            "and 'https' schemes are permitted",
        )
    try:
        import urllib.request
        # Scheme validated above, so the S310 audit is satisfied.
        with urllib.request.urlopen(url, timeout=_HTTP_TIMEOUT) as resp:  # noqa: S310
            # #591 — `errors="replace"` keeps the response
            # data flowing to the user even when the
            # remote server's Content-Type lies about
            # the encoding.  Invalid bytes surface as
            # U+FFFD inside the OK-branch string rather
            # than as a Python `UnicodeDecodeError`
            # message leaking into the Err branch.  The
            # data trade-off is acceptable for a generic
            # HTTP GET — the user's intent is "fetch
            # this URL's body", not "fail if it isn't
            # cleanly UTF-8".
            body = resp.read().decode("utf-8", errors="replace")
        return (True, body)
    except Exception as exc:
        return (False, str(exc))


def fetch_post(url: str, body: str) -> tuple[bool, str]:
    """Perform ``Http.post`` and return ``(is_ok, payload)``.

    Same worker-thread-safety contract as :func:`fetch_get` (#841).
    """
    if not _is_allowed_http_url(url):
        return (
            False,
            "Http.post: refusing non-HTTP(S) URL; only 'http' "
            "and 'https' schemes are permitted",
        )
    try:
        import urllib.request
        # Http.post is intentionally JSON-only: the Vera-level API
        # takes a String body and always sends it as application/json.
        # Custom Content-Type headers require #351 (custom headers).
        req = urllib.request.Request(  # noqa: S310
            url, data=body.encode("utf-8"), method="POST",
            headers={"Content-Type": "application/json"},
        )
        with urllib.request.urlopen(req, timeout=_HTTP_TIMEOUT) as resp:  # noqa: S310
            # #591 — `errors="replace"` for the same
            # reason as `fetch_get`: keep response data
            # flowing as U+FFFD substitutions rather
            # than letting a `UnicodeDecodeError`
            # message leak into the Err branch.
            response_body = resp.read().decode(
                "utf-8", errors="replace",
            )
        return (True, response_body)
    except Exception as exc:
        return (False, str(exc))


def _alloc_fetch_result(
    caller: wasmtime.Caller, outcome: tuple[bool, str],
) -> int:
    """Build the guest ``Result<String, String>`` from a fetch tuple."""
    is_ok, payload = outcome
    if is_ok:
        return _alloc_result_ok_string(caller, payload)
    return _alloc_result_err_string(caller, payload)


def register_http(linker: wasmtime.Linker, ops_used: set[str]) -> None:
    """Register the requested HTTP host functions on `linker`."""
    if "http_get" in ops_used:
        def host_http_get(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            url = _read_wasm_string(caller, ptr, length)
            return _alloc_fetch_result(caller, fetch_get(url))

        linker.define_func(
            "vera", "http_get",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_http_get, access_caller=True,
        )

    if "http_post" in ops_used:
        def host_http_post(
            caller: wasmtime.Caller,
            url_ptr: int, url_len: int,
            body_ptr: int, body_len: int,
        ) -> int:
            url = _read_wasm_string(caller, url_ptr, url_len)
            body = _read_wasm_string(caller, body_ptr, body_len)
            return _alloc_fetch_result(caller, fetch_post(url, body))

        linker.define_func(
            "vera", "http_post",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
                 wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_http_post, access_caller=True,
        )
