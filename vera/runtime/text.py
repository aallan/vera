"""Single home for the UTF-8 "safe decode" invariant (#589).

Vera strings live in WASM linear memory as ``(ptr, len)`` pairs.  A corrupt pair
— produced by an upstream codegen bug, e.g. the captured-Array-indexing-in-closure
bug (#588) that shipped garbage String pointers — must **never** surface as a raw
Python ``UnicodeDecodeError`` escaping wasmtime's trampoline as a "python
exception" cause.  That would give a user program a 30-line Python traceback,
violating the WasmTrapError contract (#516 / #522 / #547): a user-level program
never produces a Python traceback regardless of what it does.

Every site that decodes WASM-memory bytes to ``str`` (the ``host_print`` /
``host_stderr`` / ``host_contract_fail`` host imports and the String-return
extractor in ``vera/codegen/api.py``, plus ``_read_wasm_string`` in
``vera/runtime/heap.py`` and ``_read_string`` in ``vera/wasm/markdown.py``)
routes through :func:`safe_utf8_decode` so the ``errors="replace"`` invariant has
one home rather than six copies to keep in sync.
"""

from __future__ import annotations


def safe_utf8_decode(data: bytes) -> str:
    """Decode ``data`` as UTF-8, mapping invalid bytes to U+FFFD.

    Uses ``errors="replace"`` so corrupt bytes surface as the U+FFFD replacement
    character rather than raising ``UnicodeDecodeError`` — the single #589
    invariant every WASM-memory decode site depends on.
    """
    return data.decode("utf-8", errors="replace")
