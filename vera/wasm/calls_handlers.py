"""Ability and effect handler translation mixin for WasmContext.

Handles: Show ability (_translate_show), Hash ability (_translate_hash,
_translate_hash_string), and effect handlers (State<T>, Exn<E>).
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class CallsHandlersMixin:
    """Methods for translating Show/Hash dispatch and effect handlers."""
