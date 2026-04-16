"""Array built-in translation mixin for WasmContext.

Handles: array_length, array_append, array_range, array_concat, array_slice.
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import (
    WasmSlotEnv,
    _element_mem_size,
    _element_store_op,
    _is_pair_element_type,
    gc_shadow_push,
)


class CallsArraysMixin:
    """Methods for translating array built-in functions."""
