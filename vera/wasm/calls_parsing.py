"""Parser built-in translation mixin for WasmContext.

Handles: parse_nat, parse_int, parse_bool, parse_float64. Each parser
emits a state-machine loop in WAT and returns a ``Result<T, String>``
ADT, using the heap allocator for error messages via ``string_pool``.
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class CallsParsingMixin:
    """Methods for translating parse_* built-in functions."""
