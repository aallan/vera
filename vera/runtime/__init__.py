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

#: What every name the compiled module exports its runtime under starts
#: with (#1694): the memory, the allocator, the GC globals a host walks the
#: shadow stack through, the wrapper registration and the WASI adapter's
#: table, arena and realloc.  ``.`` is no Vera identifier's character, so a
#: program's public function named ``alloc`` is exported beside the
#: allocator, never over it.  Code generation writes these names and every
#: host reads them through :func:`runtime_export`.
RUNTIME_EXPORT_PREFIX = "vera."


def runtime_export(name: str) -> str:
    """The export name of the runtime's *name* (``memory``, ``alloc``, …)."""
    return RUNTIME_EXPORT_PREFIX + name
