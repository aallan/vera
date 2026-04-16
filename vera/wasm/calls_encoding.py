"""Encoding and URL built-in translation mixin for WasmContext.

Handles: base64_encode, base64_decode, url_encode, url_decode,
url_parse, url_join. All emit heap-allocating state machines in WAT.
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class CallsEncodingMixin:
    """Methods for translating base64 and URL built-in functions."""
