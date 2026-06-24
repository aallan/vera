"""HTTP effect host bindings.

Extracted from `execute()` in `vera/codegen/api.py` (#421); stateless --
the host callbacks use only the module-level `vera.runtime.heap` helpers.
"""

from __future__ import annotations

import wasmtime

from vera.runtime.heap import (
    _alloc_result_err_string,
    _alloc_result_ok_string,
    _read_wasm_string,
)

_HTTP_TIMEOUT: int = 60  # seconds; prevents indefinite hangs on slow HTTP calls


def register_http(linker: wasmtime.Linker, ops_used: set[str]) -> None:
    """Register the requested HTTP host functions on `linker`."""
    if "http_get" in ops_used:
        def host_http_get(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            url = _read_wasm_string(caller, ptr, length)
            try:
                import urllib.request
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
                return _alloc_result_ok_string(caller, body)
            except Exception as exc:
                return _alloc_result_err_string(caller, str(exc))

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
                    # reason as `http_get`: keep response data
                    # flowing as U+FFFD substitutions rather
                    # than letting a `UnicodeDecodeError`
                    # message leak into the Err branch.
                    response_body = resp.read().decode(
                        "utf-8", errors="replace",
                    )
                return _alloc_result_ok_string(caller, response_body)
            except Exception as exc:
                return _alloc_result_err_string(caller, str(exc))

        linker.define_func(
            "vera", "http_post",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
                 wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_http_post, access_caller=True,
        )
