"""Math and numeric conversion translation mixin for WasmContext.

Handles: abs, min, max, floor, ceil, round, sqrt, pow, float_is_nan,
float_is_infinite, nan, infinity, and numeric conversions (int_to_float,
float_to_int, nat_to_int, int_to_nat, byte_to_int, int_to_byte).
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class CallsMathMixin:
    """Methods for translating math and numeric conversion built-ins."""
