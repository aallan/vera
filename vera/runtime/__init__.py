"""Vera execution runtime.

The wasmtime host layer, extracted from `vera/codegen/api.py` (#421):

- `traps.py` — trap classification + source-backtrace resolution
  (`WasmTrapError`, `_classify_trap`, `_resolve_trap_frames`).
- `heap.py` — WASM linear-memory marshalling primitives, the ADT /
  Option / Array / bucket codecs, `_ShadowGuard`, and the collection
  marshalling helpers shared by the container families.
- `collections.py` — the `_VAL_WASM_TYPES` value-type dispatch table
  shared by Map and Set.
- one module per **optional effect family**, each exposing a single
  `register_<family>(linker, ...)` that defines and registers its
  wasmtime host callbacks: `random`, `math`, `md`, `json`, `regex`,
  `html`, `map`, `set`, `decimal`, `http`, `inference`, `state`.

The IO host bindings are deliberately NOT here: IO is execute()'s
observation channel (its buffers become `ExecuteResult` fields), not a
pluggable adapter, so it stays inline in `codegen/api.py`.  See
`vera/README.md`, "Host-binding families (`vera/runtime/`)", for the
boundary rationale.
"""
