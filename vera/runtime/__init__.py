"""Vera execution runtime.

The wasmtime host layer, extracted from `vera/codegen/api.py` (#421):

- `traps.py` — trap classification + source-backtrace resolution
  (`WasmTrapError`, `_classify_trap`, `_resolve_trap_frames`).
- `heap.py` — WASM linear-memory marshalling primitives, the ADT /
  Option / Array codecs, `_ShadowGuard`, and the helpers a host builds
  and reads a `Map<String, V>` through, which call the module's own map
  functions (#1676).
- one module per **optional effect family**, each exposing a single
  `register_<family>(linker, ...)` that defines and registers its
  wasmtime host callbacks: `random`, `math`, `md`, `json`, `regex`,
  `html`, `decimal`, `http`, `inference`, `state`.

The IO host bindings are deliberately NOT here: IO is execute()'s
observation channel (its buffers become `ExecuteResult` fields), not a
pluggable adapter, so it stays inline in `codegen/api.py`.  See
`vera/README.md`, "Host-binding families (`vera/runtime/`)", for the
boundary rationale.
"""
