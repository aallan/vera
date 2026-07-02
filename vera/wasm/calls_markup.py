"""Markup and regex translation mixin for WasmContext.

Handles: JSON (parse, stringify), HTML (parse, to_string, query, text),
Markdown (parse, render, has_heading, has_code_block, extract_code_blocks),
Regex (match, find, find_all, replace), and async/await (#841: fused
concurrent lowering for ``async(Http.get/post(...))``, identity
otherwise).

All operations are thin wrappers around host imports — the parsing and
rendering logic lives in the Python runtime (api.py + runtime/) and JS
runtime (runtime.mjs).
"""

from __future__ import annotations

from vera import ast
from vera.wasm.async_fusion import await_needs_check, fused_async_arg_target
from vera.wasm.calls_containers import _FUTURE_HANDLE_TAG, _WRAP_KIND_FUTURE
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
        # #757: runtime-guard an @Int -> @Nat narrowing of the heading level
        # before it is passed to the host import (CR #756).
        if self._narrows_into_nat(level_arg):
            l_instrs = self._emit_nat_bind_guard(l_instrs)
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

    # ---- Async builtins (#841) ----------------------------------------

    def _translate_async(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate async(expr) → Future<T>.

        Two lowerings, decided by ``fused_async_arg_target`` (shared
        with the ``_scan_io_ops`` import pre-scan — see
        ``vera/wasm/async_fusion.py`` for why the predicate must not
        be re-derived here):

        * Fused — ``async(Http.get/post(...))`` with call-free request
          args becomes one ``vera.async_http_*`` host import that
          submits the request to a host worker thread and returns the
          Future as a #578-tagged handle wrapper (kind 4), registered
          with the wrap table so an unawaited future is reclaimed via
          ``host_decref_handle`` like a Decimal handle.
        * Eager (identity) — every other shape.  Future<T> is
          WASM-transparent, so the value IS the future.  The checker's
          W002 warns on the non-commutative eager cases.
        """
        target = fused_async_arg_target(arg)
        if target is None:
            return self.translate_expr(arg, env)
        assert isinstance(arg, ast.QualifiedCall)  # fused shape
        instructions: list[str] = []
        for http_arg in arg.args:
            arg_instrs = self.translate_expr(http_arg, env)
            if arg_instrs is None:
                return None
            instructions.extend(arg_instrs)
        self._async_ops_used.add(target)
        self.needs_alloc = True
        instructions.append(f"call $vera.{target}")
        # Wrap the returned raw handle exactly like a Decimal handle
        # (#573/#578 pattern): tag word, bit-31-tagged handle,
        # register_wrapper, shadow push.
        handle_tmp = self.alloc_local("i32")
        wrapper_tmp = self.alloc_local("i32")
        instructions.append(f"local.set {handle_tmp}")
        instructions.extend(
            self._emit_wrap_handle(
                _WRAP_KIND_FUTURE, handle_tmp, wrapper_tmp,
            ),
        )
        return instructions

    def _translate_await(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate await(future) → T.

        For shapes that can carry a fused future (``await_needs_check``
        — statically typed Future<Result<String, String>>, the only
        type fused futures inhabit), emit a runtime probe of the
        value's first word: the fused wrapper's tag (0xFEEDC004) can
        never collide with an eager Result pointer's constructor tag,
        and both are valid heap pointers, so the load is always safe.
        Fused → unwrap the bit-31-tagged handle and block on
        ``vera.async_await`` (the host resolves the worker's result and
        builds the Result ADT on the guest thread); eager → the value
        already IS the result.

        Everything else keeps the identity lowering — value-typed
        futures (e.g. Future<Int>, an i64) can never hold a fused
        handle.
        """
        if not await_needs_check(arg, self._future_ret_fns):
            return self.translate_expr(arg, env)
        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None
        self._async_ops_used.add("async_await")
        self.needs_alloc = True
        value_tmp = self.alloc_local("i32")
        return [
            *arg_instrs,
            f"local.tee {value_tmp}",
            "i32.load offset=0",
            f"i32.const {_FUTURE_HANDLE_TAG}",
            "i32.eq",
            "if (result i32)",
            f"local.get {value_tmp}",
            "i32.load offset=4",
            "i32.const 0x7FFFFFFF",
            "i32.and",
            "call $vera.async_await",
            "else",
            f"local.get {value_tmp}",
            "end",
        ]
