"""String built-in translation mixin for WasmContext.

Handles: string_length, string_concat, string_slice, string_char_code,
string_from_char_code, string_repeat, string_contains, string_starts_with,
string_ends_with, string_strip, string_upper, string_lower, string_index_of,
string_replace, string_split, string_join, plus to-string conversions
(to_string, bool_to_string, byte_to_string, float_to_string).
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


class CallsStringsMixin:
    """Methods for translating string built-in functions."""
