"""Markup and regex translation mixin for WasmContext.

Handles: JSON (parse, stringify), HTML (parse, to_string, query, text),
Markdown (parse, render, has_heading, has_code_block, extract_code_blocks),
Regex (match, find, find_all, replace), and async/await (identity ops).

All operations are thin wrappers around host imports — the parsing and
rendering logic lives in the Python runtime (api.py) and JS runtime
(runtime.mjs).
"""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv


class CallsMarkupMixin:
    """Methods for translating JSON, HTML, Markdown, Regex, and async built-ins."""
