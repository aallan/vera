# WASI and the server-effects sprint

Design record for the sprint that takes Vera from ad-hoc `vera.*` host imports to
verified HTTP handling: concurrent `<Async>` (#841) → `<HttpServer>` (#305) → an
experimental WASI Preview 2 target (#237) → a `wasi:http` serve backend → WASI 0.3
(#406, gated).  The stage designs live in the issues; this file records the
**toolchain facts** every stage builds on, established by an executed spike
(2026-07-02, wasmtime-py 45.0.0, wasmtime CLI 46.0.1, macOS; scripts under the
planning session's scratchpad, keepers to become CI smoke tests in the WASI-target
stage).

## Spike results (9/9 — no stage invalidated)

| # | Check | Verdict | Load-bearing detail |
|---|---|---|---|
| 1 | Component text instantiation | **PASS** | `wasmtime.component.Component(engine, wat_text)` parses component-model TEXT format and instantiates. Vera already emits WAT, so the component target needs **no external componentizer** — no new runtime dependency. |
| 2 | Two core modules sharing memory | **PASS** | An adapter module can import the main module's exported `memory` + `alloc` via `(with "main" (instance (export ...)))`, write into shared memory, and the main module reads it back — the WASI-target adapter/shim architecture. |
| 3 | `add_wasip2()` + stdout capture | **PASS** | A hand-written component importing `wasi:cli/stdout@0.2.0` + `wasi:io/streams@0.2.0` runs under `component.Linker.add_wasip2()`. **Capture:** `wasmtime.WasiConfig.stdout_custom` (set via `Store.set_wasi`) is honored by the p2 host — bytes captured in-process, feeding `ExecuteResult.stdout` directly. |
| 4 | `handle[Exn]` (exnref) inside a component | **PASS** | A real Vera-compiled module using WASM exception handling runs inside a component (`config.wasm_exceptions = True`), with its `vera.*` core imports satisfied by an in-component stub instance — the pattern for every non-WASI import family. |
| 5 | Trap frames through a component | **PARTIAL** | A guest trap surfaces as `WasmtimeError` with the backtrace in **message text** (`m!under`); the structured `.frames` list (which #516's frame resolution uses on the core path) is lost. The WASI target must parse the text or accept degraded frame mapping. |
| 6 | Component-level host functions | **PASS** | `LinkerInstance.add_func` callbacks receive `(store, *lifted_values)` — a Python `str` arrives already lifted; **no access to guest memory or the caller** (confirming the canonical-ABI cliff that motivates the adapter architecture). ~17 µs/call round-trip incl. the manual `post_return` (core-path host call ≈ 1 µs) — fine for IO-class operations. |
| 7 | `wasmtime serve` incoming-handler | **PASS** | A hand-written WAT component exporting `wasi:http/incoming-handler@0.2.0#handle` (full 39-case `error-code` variant, borrow-before-transfer resource ordering) is served by the stock CLI with **no flags**: `HTTP/1.1 200 OK` + exact body. Import/export versions `@0.2.0` and `@0.2.3` both link (semver-compatible lookup). |
| 8 | Host threads + Ctrl-C during await | **PASS** | Two 300 ms host tasks submitted from guest-triggered host imports overlap (307 ms wall total); SIGINT while blocked in a host `await` unwinds cleanly through wasm (the `wasmtime>=45` BaseException trampoline), `ThreadPoolExecutor.shutdown(cancel_futures=True)` does not hang, process exits 130. This is the `<Async>` (#841) execution pattern. |
| 9 | Per-request instantiation cost | **PASS** | Fresh `Store` + instantiate + call of a compiled Vera module: **0.020 ms** — instance-per-request isolation for `<HttpServer>` (#305) is effectively free. |

## Invariants the spike established

- **Always set a `WasiConfig` before calling into a wasip2-linked component**: a
  wasip2 import invoked on a store with no `Store.set_wasi(...)` panics inside the
  Rust C-API and **aborts the whole process** (SIGABRT — not a catchable Python
  exception).  The component execution path must set a config unconditionally.
- **Canonical-ABI text-format landmines** (for the compiler's emitter): export-id
  binding is `(export "name" (type $id (sub resource)))`; `canon lower` cannot
  forward-reference the instance that consumes it — memory/realloc module first,
  lowers second, consumer shim third; interface versions must be full semver
  (`@0.2` does not parse; `@0.2.0`–`@0.2.6` semver-match).
- **`blocking-write-and-flush` caps writes at 4096 bytes per call** — the adapter
  chunks larger output.
- **wasmtime-py 45 component calls are sync-only** (`wasmtime_component_func_call_async`
  exists at the FFI layer with no Python plumbing) — the #406 gate.
- **The PyPI package named `wasm-tools` is not Bytecode Alliance tooling** (an
  unrelated parser) — never adopt it; the component path needs no such tool anyway
  (see check 1).

## Where the loose ends live

- Frame-resolution degradation through components (check 5) → **resolved in the
  #237 target**: the runner classifies trap kinds from the backtrace text +
  the WASI stderr channel (`vera/runtime/wasi_host.py`); structured frames stay
  core-path-only (spec §13.6).  The stdout-capture wiring (check 3) landed as
  `WasiConfig.stdout_custom` → `ExecuteResult.stdout` in the same runner.
- The `wasmtime serve` deployment path (check 7) → **landed as `--world server`**
  (spec §13.7).  Two check-7 findings were superseded during the Stage-D design
  study: the `$Libc` two-module realloc dodge is unnecessary (the Stage-C
  MAIN-owns-memory topology already sequences realloc before the lowers), and
  `[static]incoming-body.finish` is not required (plain `resource.drop` of the
  incoming body is accepted).  The pure-Python `vera serve` driver (#305) remains
  independent.
- Spike keeper-scripts → landed as `tests/test_wasi_target.py` with the #237
  target: component parse + live `add_wasip2` instantiation + execution
  semantics + the dual-target conformance differential + a stock-CLI smoke test.
