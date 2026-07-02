"""Fused-async HTTP host bindings (#841).

``async(Http.get/post(...))`` fuses into a ``vera.async_http_*`` import
that submits the request to a host ``ThreadPoolExecutor`` and returns a
raw i32 future handle; the guest wraps the handle in a #578-tagged
kind-4 wrapper (see ``vera/wasm/calls_containers.py``).
``vera.async_await(handle)`` blocks on the guest thread and builds the
``Result<String, String>`` ADT there — worker threads only ever run the
pure fetch halves from ``vera/runtime/http.py`` and return Python
strings, never touching guest memory (the #570/#692 UAF class cannot
reach them).

Stateful like Decimal (#421): the handle → future store lives in
``execute()`` and is passed in so the shared ``host_decref_handle`` GC
hook can evict — and cancel — a future whose wrapper became
unreachable without ever being awaited.

Ctrl-C: ``Future.result()`` blocks on the guest thread, so a
``KeyboardInterrupt`` raises inside the host callback and rides the
wasmtime>=45 ``BaseException`` trampoline to the single exit-130
handler in ``execute()`` (#595/#599); it is deliberately not caught
here.
"""

from __future__ import annotations

from concurrent.futures import CancelledError, Executor, Future

import wasmtime

from vera.runtime.heap import (
    _alloc_result_err_string,
    _read_wasm_string,
)
from vera.runtime.http import _alloc_fetch_result, fetch_get, fetch_post


def register_async(
    linker: wasmtime.Linker,
    ops_used: set[str],
    future_store: dict[int, "Future[tuple[bool, str]]"],
    host_store_refs: dict[str, dict[int, object]],
    executor: Executor,
) -> None:
    """Register the fused-async host functions on ``linker``."""
    # Expose the store for ExecuteResult.host_store_sizes, so the GC
    # reclamation tests can observe unawaited futures being evicted
    # (same observability contract as the Decimal store).
    host_store_refs["future"] = future_store  # type: ignore[assignment]

    # Handles are small sequential ints (starting at 1, so a zeroed
    # wrapper field can never alias a live handle) and must stay below
    # 2^31 — the guest stores them bit-31-tagged (#578).
    next_handle = [1]

    def _submit(fut: "Future[tuple[bool, str]]") -> int:
        handle = next_handle[0]
        next_handle[0] += 1
        future_store[handle] = fut
        return handle

    if "async_http_get" in ops_used:
        def host_async_http_get(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            # Read the URL on the guest thread, then hand the pure
            # fetch to a worker — the request goes on the wire at the
            # async(...) point, preserving program order for request
            # issuance.
            url = _read_wasm_string(caller, ptr, length)
            return _submit(executor.submit(fetch_get, url))

        linker.define_func(
            "vera", "async_http_get",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_async_http_get, access_caller=True,
        )

    if "async_http_post" in ops_used:
        def host_async_http_post(
            caller: wasmtime.Caller,
            url_ptr: int, url_len: int,
            body_ptr: int, body_len: int,
        ) -> int:
            url = _read_wasm_string(caller, url_ptr, url_len)
            body = _read_wasm_string(caller, body_ptr, body_len)
            return _submit(executor.submit(fetch_post, url, body))

        linker.define_func(
            "vera", "async_http_post",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
                 wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_async_http_post, access_caller=True,
        )

    if "async_await" in ops_used:
        def host_async_await(
            caller: wasmtime.Caller, handle: int,
        ) -> int:
            fut = future_store.get(handle)
            if fut is None:
                # Defensive: a live wrapper implies a live store entry
                # (Phase 2c only evicts unreachable wrappers, and GC
                # runs on the guest thread, which is here).  Reachable
                # only via a runtime that violated that invariant —
                # surface as a value-level Err, not a crash.
                return _alloc_result_err_string(
                    caller,
                    "await: future was already reclaimed (#841 "
                    "invariant violation — please report)",
                )
            try:
                # Blocks the guest thread until the worker finishes.
                # Repeat awaits of the same future are fine —
                # Future.result() memoizes, and each call rebuilds a
                # fresh Result ADT (matching eager-await semantics).
                # KeyboardInterrupt propagates (see module docstring).
                outcome = fut.result()
            except CancelledError:
                return _alloc_result_err_string(
                    caller, "await: future was cancelled",
                )
            return _alloc_fetch_result(caller, outcome)

        linker.define_func(
            "vera", "async_await",
            wasmtime.FuncType(
                [wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_async_await, access_caller=True,
        )
