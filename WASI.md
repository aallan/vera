# WASI toolchain facts

The WASI Preview 2 target (`--target wasi-p2`, spec Chapter 13), its `wasi:http` server world (`--world server`, spec §13.7), concurrent `<Async>` (#841) and `<HttpServer>` (#305) rest on the toolchain facts below.  WASI 0.3 and native async I/O (#406) are planned and gated on the last invariant in the list.  Each fact was established by an executed check against wasmtime-py 45.0.0 and the wasmtime CLI 46.0.1 on macOS (2026-07-02).  The checks are numbered, and comments in `vera/runtime/` and the tests cite them by number.

## The nine checks

| # | Check | Verdict | Load-bearing detail |
|---|---|---|---|
| 1 | Component text instantiation | **PASS** | `wasmtime.component.Component(engine, wat_text)` parses component-model TEXT format and instantiates. Vera already emits WAT, so the component target needs **no external componentizer** and no new runtime dependency. |
| 2 | Two core modules sharing memory | **PASS** | An adapter module can import the main module's exported `memory` + `alloc` via `(with "main" (instance (export ...)))`, write into shared memory, and the main module reads it back: the WASI-target adapter/shim architecture. |
| 3 | `add_wasip2()` + stdout capture | **PASS** | A hand-written component importing `wasi:cli/stdout@0.2.0` + `wasi:io/streams@0.2.0` runs under `component.Linker.add_wasip2()`. **Capture:** `wasmtime.WasiConfig.stdout_custom` (set via `Store.set_wasi`) is honoured by the p2 host, so bytes are captured in-process and feed `ExecuteResult.stdout` directly. |
| 4 | `handle[Exn]` (exnref) inside a component | **PASS** | A Vera-compiled module using WASM exception handling runs inside a component (`config.wasm_exceptions = True`), with its `vera.*` core imports satisfied by an in-component stub instance: the pattern for every non-WASI import family. |
| 5 | Trap frames through a component | **PARTIAL** | A guest trap surfaces as `WasmtimeError` with the backtrace in **message text** (`m!under`); the structured `.frames` list that frame resolution (#516) reads on the core path is lost. The WASI target classifies trap kinds from the message text instead (below). |
| 6 | Component-level host functions | **PASS** | `LinkerInstance.add_func` callbacks receive `(store, *lifted_values)`; a Python `str` arrives already lifted, with **no access to guest memory or the caller**. That canonical-ABI cliff is why the target uses an adapter module. A round trip takes about 17 µs per call including the manual `post_return` (a core-path host call takes about 1 µs), which is acceptable for IO-class operations. |
| 7 | `wasmtime serve` incoming-handler | **PASS** | A hand-written WAT component exporting `wasi:http/incoming-handler@0.2.0#handle` (full 39-case `error-code` variant, borrow-before-transfer resource ordering) is served by the stock CLI with **no flags**: `HTTP/1.1 200 OK` + exact body. Import/export versions `@0.2.0` and `@0.2.3` both link (semver-compatible lookup). |
| 8 | Host threads + Ctrl-C during await | **PASS** | Two 300 ms host tasks submitted from guest-triggered host imports overlap (307 ms wall total); SIGINT while blocked in a host `await` unwinds cleanly through wasm (the `wasmtime>=45` BaseException trampoline), `ThreadPoolExecutor.shutdown(cancel_futures=True)` does not hang, and the process exits 130. This is the `<Async>` (#841) execution pattern. |
| 9 | Per-request instantiation cost | **PASS** | Fresh `Store` + instantiate + call of a compiled Vera module takes **0.020 ms**, so instance-per-request isolation for `<HttpServer>` (#305) costs almost nothing. |

## Invariants

- **Always set a `WasiConfig` before calling into a wasip2-linked component**: a
  wasip2 import invoked on a store with no `Store.set_wasi(...)` panics inside the
  Rust C-API and **aborts the whole process** (SIGABRT, not a catchable Python
  exception).  The component execution path sets a config unconditionally.
- **Canonical-ABI text-format landmines** (for the compiler's emitter): export-id
  binding is `(export "name" (type $id (sub resource)))`; `canon lower` cannot
  forward-reference the instance that consumes it, so the memory/realloc module
  comes first, the lowers second and the consumer shim third; interface versions
  must be full semver (`@0.2` does not parse; `@0.2.0` to `@0.2.6` semver-match).
- **`blocking-write-and-flush` caps writes at 4096 bytes per call**, so the adapter
  chunks larger output.
- **wasmtime-py 45 component calls are sync-only** (`wasmtime_component_func_call_async`
  exists at the FFI layer with no Python plumbing).  This is what gates #406.
- **The PyPI package named `wasm-tools` is not Bytecode Alliance tooling** (it is an
  unrelated parser); the component path needs no such tool (check 1).

## Where each fact is used

- **Trap classification (check 5).**  The runner (`vera/runtime/wasi_host.py`)
  classifies trap kinds from the backtrace text and the WASI stderr channel;
  structured frames are core-path only (spec §13.6).
- **Output capture (check 3).**  `WasiConfig.stdout_custom` feeds
  `ExecuteResult.stdout` in the same runner, which closes its store before it
  returns or raises and waits, for up to two seconds, until wasmtime has let go of
  both output callbacks.  wasmtime releases a stream the program wrote to from a
  tokio worker thread; that thread calling into Python during interpreter shutdown
  is ended by `pthread_exit`, whose forced unwind cannot cross wasmtime's Rust
  frames, and the process aborts (SIGABRT).  A trapping call leaves the store in a
  wasmtime-py reference cycle, which the explicit close breaks; without it the
  store would be freed at shutdown.
- **The server world (check 7).**  `--world server` (spec §13.7) is the `wasmtime
  serve` deployment path.  It needs no separate realloc module, because the main
  module owns the memory and so defines realloc before the lowers, and it needs no
  `[static]incoming-body.finish`, because a plain `resource.drop` of the incoming
  body is accepted.  The pure-Python `vera serve` driver (#305) is independent of it.
- **Tests.**  `tests/test_wasi_target.py` holds the checks as tests: component
  parse, live `add_wasip2` instantiation, execution semantics, the dual-target
  conformance differential (spec §13.8) and a stock-CLI smoke test.
