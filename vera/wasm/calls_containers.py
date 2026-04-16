"""Container type translation mixin for WasmContext.

Handles the three opaque-handle types: Map<K,V>, Set<E>, and Decimal.
All three use the host-import pattern with lazy registration of
type-specialised imports (e.g. ``map_insert$ks_vi`` for String key /
Int value).
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class CallsContainersMixin:
    """Methods for translating Map, Set, and Decimal built-in functions."""
