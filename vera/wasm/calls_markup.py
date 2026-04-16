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

    # ---- Json host-import builtins ------------------------------------

    def _translate_json_parse(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """json_parse(s) → Result<Json, String> via host import.

        String arg is (ptr, len) pair on stack → call $vera.json_parse → i32.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        self._json_ops_used.add("json_parse")
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.json_parse")
        return ins

    def _translate_json_stringify(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """json_stringify(j) → String via host import.

        Json arg is i32 heap pointer → call $vera.json_stringify → (i32, i32).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        self._json_ops_used.add("json_stringify")
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.json_stringify")
        return ins

    # ---- Html host-import builtins ------------------------------------

    def _translate_html_parse(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """html_parse(s) -> Result<HtmlNode, String> via host import.

        String arg is (ptr, len) pair on stack -> call $vera.html_parse -> i32.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        self._html_ops_used.add("html_parse")
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.html_parse")
        return ins

    def _translate_html_to_string(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """html_to_string(node) -> String via host import.

        HtmlNode arg is i32 heap pointer -> call $vera.html_to_string -> (i32, i32).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        self._html_ops_used.add("html_to_string")
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.html_to_string")
        return ins

    def _translate_html_query(
        self, node_arg: ast.Expr, sel_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """html_query(node, selector) -> Array<HtmlNode> via host import.

        HtmlNode is i32, selector String is (ptr, len) -> call $vera.html_query -> (i32, i32).
        """
        node_instrs = self.translate_expr(node_arg, env)
        sel_instrs = self.translate_expr(sel_arg, env)
        if node_instrs is None or sel_instrs is None:
            return None
        self.needs_alloc = True
        self._html_ops_used.add("html_query")
        ins: list[str] = []
        ins.extend(node_instrs)
        ins.extend(sel_instrs)
        ins.append("call $vera.html_query")
        return ins

    def _translate_html_text(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """html_text(node) -> String via host import.

        HtmlNode is i32 heap pointer -> call $vera.html_text -> (i32, i32).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        self._html_ops_used.add("html_text")
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.html_text")
        return ins

    # ---- Markdown host-import builtins ---------------------------------

    def _translate_md_parse(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """md_parse(s) → Result<MdBlock, String> via host import.

        String arg is (ptr, len) pair on stack → call $vera.md_parse → i32.
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.md_parse")
        return ins

    def _translate_md_render(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """md_render(block) → String via host import.

        MdBlock arg is i32 (heap ptr) → call $vera.md_render → (i32, i32).
        """
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(arg_instrs)
        ins.append("call $vera.md_render")
        return ins

    def _translate_md_has_heading(
        self, block_arg: ast.Expr, level_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """md_has_heading(block, level) → Bool via host import.

        (i32 ptr, i64 level) → call $vera.md_has_heading → i32.
        """
        b_instrs = self.translate_expr(block_arg, env)
        l_instrs = self.translate_expr(level_arg, env)
        if b_instrs is None or l_instrs is None:
            return None
        ins: list[str] = []
        ins.extend(b_instrs)
        ins.extend(l_instrs)
        ins.append("call $vera.md_has_heading")
        return ins

    def _translate_md_has_code_block(
        self, block_arg: ast.Expr, lang_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """md_has_code_block(block, lang) → Bool via host import.

        (i32 ptr, i32 lang_ptr, i32 lang_len) → call → i32.
        """
        b_instrs = self.translate_expr(block_arg, env)
        l_instrs = self.translate_expr(lang_arg, env)
        if b_instrs is None or l_instrs is None:
            return None
        ins: list[str] = []
        ins.extend(b_instrs)
        ins.extend(l_instrs)
        ins.append("call $vera.md_has_code_block")
        return ins

    def _translate_md_extract_code_blocks(
        self, block_arg: ast.Expr, lang_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """md_extract_code_blocks(block, lang) → Array<String> via host import.

        (i32 ptr, i32 lang_ptr, i32 lang_len) → call → (i32, i32).
        """
        b_instrs = self.translate_expr(block_arg, env)
        l_instrs = self.translate_expr(lang_arg, env)
        if b_instrs is None or l_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(b_instrs)
        ins.extend(l_instrs)
        ins.append("call $vera.md_extract_code_blocks")
        return ins

    # ---- Regex host-import builtins -------------------------------------

    def _translate_regex_match(
        self, input_arg: ast.Expr, pattern_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """regex_match(input, pattern) → Result<Bool, String> via host import.

        Two string args → (i32, i32, i32, i32) → call $vera.regex_match → i32.
        """
        in_instrs = self.translate_expr(input_arg, env)
        pat_instrs = self.translate_expr(pattern_arg, env)
        if in_instrs is None or pat_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(in_instrs)
        ins.extend(pat_instrs)
        ins.append("call $vera.regex_match")
        return ins

    def _translate_regex_find(
        self, input_arg: ast.Expr, pattern_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """regex_find(input, pattern) → Result<Option<String>, String>.

        Two string args → (i32, i32, i32, i32) → call $vera.regex_find → i32.
        """
        in_instrs = self.translate_expr(input_arg, env)
        pat_instrs = self.translate_expr(pattern_arg, env)
        if in_instrs is None or pat_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(in_instrs)
        ins.extend(pat_instrs)
        ins.append("call $vera.regex_find")
        return ins

    def _translate_regex_find_all(
        self, input_arg: ast.Expr, pattern_arg: ast.Expr,
        env: WasmSlotEnv,
    ) -> list[str] | None:
        """regex_find_all(input, pattern) → Result<Array<String>, String>.

        Two string args → (i32, i32, i32, i32) → call → i32.
        """
        in_instrs = self.translate_expr(input_arg, env)
        pat_instrs = self.translate_expr(pattern_arg, env)
        if in_instrs is None or pat_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(in_instrs)
        ins.extend(pat_instrs)
        ins.append("call $vera.regex_find_all")
        return ins

    def _translate_regex_replace(
        self, input_arg: ast.Expr, pattern_arg: ast.Expr,
        replacement_arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """regex_replace(input, pattern, replacement) → Result<String, String>.

        Three string args → (i32, i32, i32, i32, i32, i32) → call → i32.
        """
        in_instrs = self.translate_expr(input_arg, env)
        pat_instrs = self.translate_expr(pattern_arg, env)
        rep_instrs = self.translate_expr(replacement_arg, env)
        if in_instrs is None or pat_instrs is None or rep_instrs is None:
            return None
        self.needs_alloc = True
        ins: list[str] = []
        ins.extend(in_instrs)
        ins.extend(pat_instrs)
        ins.extend(rep_instrs)
        ins.append("call $vera.regex_replace")
        return ins

    # ---- Async builtins -----------------------------------------------

    def _translate_async(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate async(expr) → Future<T> (identity, eager evaluation).

        The reference implementation evaluates async(expr) eagerly.
        Future<T> is WASM-transparent — same representation as T.
        True concurrency will be available via WASI 0.3 (#237).
        """
        return self.translate_expr(arg, env)

    def _translate_await(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate await(future) → T (identity unwrap).

        Future<T> is WASM-transparent, so await is a no-op.
        """
        return self.translate_expr(arg, env)
