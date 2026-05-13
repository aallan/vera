"""Mixin for WAT module assembly.

Assembles the final WAT module text from compiled functions, imports,
memory, data sections, and closure infrastructure.
"""

from __future__ import annotations

import os


class AssemblyMixin:
    """Methods for assembling the WAT module."""

    def _assemble_module(self, functions: list[str]) -> str:
        """Assemble a complete WAT module from compiled functions."""
        parts: list[str] = ["(module"]

        # Import IO operations as needed
        _IO_IMPORTS: dict[str, str] = {
            "print": "(func $vera.print (param i32 i32))",
            "read_line": "(func $vera.read_line (result i32 i32))",
            "read_file":
                "(func $vera.read_file (param i32 i32) (result i32))",
            "write_file":
                "(func $vera.write_file"
                " (param i32 i32 i32 i32) (result i32))",
            "args": "(func $vera.args (result i32 i32))",
            "exit": "(func $vera.exit (param i64))",
            "get_env":
                "(func $vera.get_env (param i32 i32) (result i32))",
            # #463 — time and flow-control.
            # sleep: ms (i64 Nat) → no result
            # time: no params (Unit arg erased at WASM level) → i64 Nat
            # stderr: (ptr, len) for String → no result
            "sleep": "(func $vera.sleep (param i64))",
            "time": "(func $vera.time (result i64))",
            "stderr": "(func $vera.stderr (param i32 i32))",
        }
        _IO_OPS_NEEDING_ALLOC = {
            "read_line", "read_file", "write_file", "args", "get_env",
        }
        for op_name in sorted(self._io_ops_used):
            sig = _IO_IMPORTS.get(op_name)
            if sig:
                parts.append(f'  (import "vera" "{op_name}" {sig})')
        if self._io_ops_used & _IO_OPS_NEEDING_ALLOC:
            self._needs_alloc = True

        # Import Markdown host-import builtins (pure functions)
        _MD_IMPORTS: dict[str, str] = {
            "md_parse":
                "(func $vera.md_parse (param i32 i32) (result i32))",
            "md_render":
                "(func $vera.md_render (param i32) (result i32 i32))",
            "md_has_heading":
                "(func $vera.md_has_heading"
                " (param i32 i64) (result i32))",
            "md_has_code_block":
                "(func $vera.md_has_code_block"
                " (param i32 i32 i32) (result i32))",
            "md_extract_code_blocks":
                "(func $vera.md_extract_code_blocks"
                " (param i32 i32 i32) (result i32 i32))",
        }
        for op_name in sorted(self._md_ops_used):
            sig = _MD_IMPORTS.get(op_name)
            if sig:
                parts.append(f'  (import "vera" "{op_name}" {sig})')
        if self._md_ops_used:
            self._needs_alloc = True

        # Import Regex host-import builtins (pure functions)
        _REGEX_IMPORTS: dict[str, str] = {
            "regex_match":
                "(func $vera.regex_match"
                " (param i32 i32 i32 i32) (result i32))",
            "regex_find":
                "(func $vera.regex_find"
                " (param i32 i32 i32 i32) (result i32))",
            "regex_find_all":
                "(func $vera.regex_find_all"
                " (param i32 i32 i32 i32) (result i32))",
            "regex_replace":
                "(func $vera.regex_replace"
                " (param i32 i32 i32 i32 i32 i32) (result i32))",
        }
        for op_name in sorted(self._regex_ops_used):
            sig = _REGEX_IMPORTS.get(op_name)
            if sig:
                parts.append(f'  (import "vera" "{op_name}" {sig})')
        if self._regex_ops_used:
            self._needs_alloc = True

        # Import Map host-import builtins (per-type-instantiation)
        for import_line in sorted(self._map_imports):
            parts.append(import_line)
        if self._map_ops_used:
            self._needs_alloc = True
            self._needs_memory = True
            # #573: Map / Set / Decimal all migrate to the heap-
            # wrap-as-ADT scheme.  Any of them being used flips
            # the wrap-table flag — ``assembly.py`` then allocates
            # the 64 KiB side-table region, emits
            # ``$register_wrapper``, adds Phase 2c to
            # ``$gc_collect``, and (below, after all three blocks)
            # imports the ``host_decref_handle`` helper.
            self._needs_wrap_table = True

        # Import Set host-import builtins (per-type-instantiation)
        for import_line in sorted(self._set_imports):
            parts.append(import_line)
        if self._set_ops_used:
            self._needs_alloc = True
            self._needs_memory = True
            # #573 phase 2: Set migrated to heap-wrap-as-ADT.
            self._needs_wrap_table = True

        # Import Decimal host-import builtins
        for import_line in sorted(self._decimal_imports):
            parts.append(import_line)
        if self._decimal_ops_used:
            self._needs_alloc = True
            self._needs_memory = True
            # #573 phase 3: Decimal migrated to heap-wrap-as-ADT.
            self._needs_wrap_table = True

        # #573: JSON and HTML host parsers allocate Map wrappers
        # internally (for JObject's ``Map<String, Json>`` field
        # and HtmlElement's ``Map<String, String>`` attrs) via
        # ``_alloc_map_wrapper`` in ``vera/codegen/api.py``.
        # Those allocations register with the wrap table and rely
        # on Phase 2c + ``host_decref_handle`` for reclamation —
        # without flipping the flag here, JSON/HTML-only programs
        # (no user-level ``map_*`` ops) leak the underlying
        # ``_map_store`` entries indefinitely because
        # ``register_wrapper`` is unexported and Phase 2c isn't
        # emitted.  Same flag flip; the gating cost is one extra
        # 64 KiB region in linear memory.
        if self._json_ops_used or self._html_ops_used:
            self._needs_wrap_table = True

        # #573: emit ``host_decref_handle`` import after the
        # gating blocks above have all run.  Phase 2c of
        # ``$gc_collect`` calls this for each unmarked wrapper.
        # Must come after the per-type imports so the WAT
        # ``(import "vera" ...)`` declarations stay grouped by
        # subsystem, but before the GC infrastructure is emitted
        # (which references the import).
        if self._needs_wrap_table:
            parts.append(
                '  (import "vera" "host_decref_handle" '
                "(func $vera.host_decref_handle "
                "(param i32) (param i32)))"
            )

        # Import Json host-import builtins
        if "json_parse" in self._json_ops_used:
            parts.append(
                '  (import "vera" "json_parse" '
                "(func $vera.json_parse (param i32 i32) (result i32)))"
            )
        if "json_stringify" in self._json_ops_used:
            parts.append(
                '  (import "vera" "json_stringify" '
                "(func $vera.json_stringify (param i32) (result i32 i32)))"
            )
        if self._json_ops_used:
            self._needs_alloc = True
            self._needs_memory = True

        # Import Html host-import builtins
        if "html_parse" in self._html_ops_used:
            parts.append(
                '  (import "vera" "html_parse" '
                "(func $vera.html_parse (param i32 i32) (result i32)))"
            )
        if "html_to_string" in self._html_ops_used:
            parts.append(
                '  (import "vera" "html_to_string" '
                "(func $vera.html_to_string (param i32) (result i32 i32)))"
            )
        if "html_query" in self._html_ops_used:
            parts.append(
                '  (import "vera" "html_query" '
                "(func $vera.html_query (param i32 i32 i32) (result i32 i32)))"
            )
        if "html_text" in self._html_ops_used:
            parts.append(
                '  (import "vera" "html_text" '
                "(func $vera.html_text (param i32) (result i32 i32)))"
            )
        if self._html_ops_used:
            self._needs_alloc = True
            self._needs_memory = True

        # Http host imports — http_get(url_ptr, url_len) -> i32 Result ptr
        #                      http_post(url_ptr, url_len, body_ptr, body_len) -> i32
        if "http_get" in self._http_ops_used:
            parts.append(
                '  (import "vera" "http_get" '
                "(func $vera.http_get (param i32 i32) (result i32)))"
            )
        if "http_post" in self._http_ops_used:
            parts.append(
                '  (import "vera" "http_post" '
                "(func $vera.http_post (param i32 i32 i32 i32) (result i32)))"
            )
        if self._http_ops_used:
            self._needs_alloc = True
            self._needs_memory = True

        # Inference effect host imports: inference_complete(prompt_ptr, prompt_len) -> i32
        if "inference_complete" in self._inference_ops_used:
            parts.append(
                '  (import "vera" "inference_complete" '
                "(func $vera.inference_complete (param i32 i32) (result i32)))"
            )
        if self._inference_ops_used:
            self._needs_alloc = True
            self._needs_memory = True

        # Random effect host imports (#465).  None of these allocate
        # or return heap data — `random_int` returns a scalar i64,
        # `random_float` returns f64, `random_bool` returns i32 (0/1).
        # Unit arguments at the Vera level are erased, so
        # `random_float()` and `random_bool()` take no parameters.
        if "random_int" in self._random_ops_used:
            parts.append(
                '  (import "vera" "random_int" '
                "(func $vera.random_int (param i64 i64) (result i64)))"
            )
        if "random_float" in self._random_ops_used:
            parts.append(
                '  (import "vera" "random_float" '
                "(func $vera.random_float (result f64)))"
            )
        if "random_bool" in self._random_ops_used:
            parts.append(
                '  (import "vera" "random_bool" '
                "(func $vera.random_bool (result i32)))"
            )

        # Math host imports (#467).  All log/trig ops share the
        # same Float64 → Float64 unary shape, except atan2 which is
        # (Float64, Float64) → Float64.  Mathematical constants
        # pi()/e() and sign/clamp/float_clamp are inlined — no
        # host import needed.
        _MATH_UNARY = (
            "log", "log2", "log10",
            "sin", "cos", "tan", "asin", "acos", "atan",
        )
        for op_name in _MATH_UNARY:
            if op_name in self._math_ops_used:
                parts.append(
                    f'  (import "vera" "{op_name}" '
                    f"(func $vera.{op_name} (param f64) (result f64)))"
                )
        if "atan2" in self._math_ops_used:
            parts.append(
                '  (import "vera" "atan2" '
                "(func $vera.atan2 (param f64 f64) (result f64)))"
            )

        # Import contract_fail for informative violation messages
        if self._needs_contract_fail:
            parts.append(
                '  (import "vera" "contract_fail" '
                "(func $vera.contract_fail (param i32 i32)))"
            )

        # Import State<T> host functions if needed
        for type_name, wasm_t in self._state_types:
            parts.append(
                f'  (import "vera" "state_get_{type_name}" '
                f"(func $vera.state_get_{type_name} (result {wasm_t})))"
            )
            parts.append(
                f'  (import "vera" "state_put_{type_name}" '
                f"(func $vera.state_put_{type_name} (param {wasm_t})))"
            )
            parts.append(
                f'  (import "vera" "state_push_{type_name}" '
                f"(func $vera.state_push_{type_name}))"
            )
            parts.append(
                f'  (import "vera" "state_pop_{type_name}" '
                f"(func $vera.state_pop_{type_name}))"
            )

        # Exception tags for Exn<E>
        for type_name, wasm_t in self._exn_types:
            parts.append(
                f"  (tag $exn_{type_name} (param {wasm_t}))"
            )

        # Memory (for string data and heap)
        if self._needs_memory or self.string_pool.has_strings():
            parts.append('  (memory (export "memory") 1)')

        # Data section (string constants)
        for value, offset, _length in self.string_pool.entries():
            # Escape special characters for WAT string literals
            escaped = self._escape_wat_string(value)
            parts.append(f'  (data (i32.const {offset}) "{escaped}")')

        # GC infrastructure: globals, allocator, and collector
        if self._needs_alloc:
            data_end = self.string_pool.heap_offset
            gc_stack_base = data_end
            gc_stack_size = 16384  # 16K shadow stack
            # #348: GC mark-phase worklist.  Pre-fix this was 16 KiB
            # (4096 entries) and silently dropped pushes once full,
            # which left reachable objects unmarked and they got
            # swept as garbage — a real use-after-free hole for
            # programs whose live object graph held more than ~4 K
            # pointers reachable from a single root.  Post-fix:
            # quadruple the capacity (64 KiB / 16 384 entries — covers
            # reasonable program shapes) AND trap (`unreachable`)
            # on overflow rather than silently dropping, so any
            # residual overflow is a clean runtime failure rather
            # than silent corruption.  Eliminating the trap entirely
            # via iterative deepening or dynamic worklist growth is
            # tracked separately for follow-up.
            gc_worklist_size = 65536  # 64 KiB worklist (16 384 entries)
            # #573: wrap-table region for host-handle ADT wrappers.
            # Sized for 4 096 simultaneously-live wrapper objects at
            # 16 bytes per entry (obj_ptr / kind / handle / reserved).
            # Sweep compacts in place, so the table grows with
            # *live* wrappers, not total allocations.  Programs that
            # don't use any wrap-table-backed type pay no memory
            # cost — `_needs_wrap_table` gates inclusion of both
            # this region and the corresponding sweep pass.
            #
            # Note: only Map<K, V> migrates in this release
            # (#573 phase 1 — Plan B).  Set / Decimal / JSON / HTML
            # follow in tracked follow-ups so each migration's
            # design choices can be reviewed independently.
            gc_wraptable_size = 65536  # 64 KiB / 4 096 wrapper entries
            wrap_enabled = self._needs_wrap_table
            wraptable_overhead = gc_wraptable_size if wrap_enabled else 0
            gc_wraptable_base = (
                data_end + gc_stack_size + gc_worklist_size
            )
            gc_heap_start = (
                data_end + gc_stack_size + gc_worklist_size
                + wraptable_overhead
            )
            parts.append(
                f"  (global $heap_ptr (export \"heap_ptr\") "
                f"(mut i32) (i32.const {gc_heap_start}))"
            )
            parts.append(
                f"  (global $gc_sp (mut i32) "
                f"(i32.const {gc_stack_base}))"
            )
            parts.append(
                f"  (global $gc_stack_base i32 "
                f"(i32.const {gc_stack_base}))"
            )
            gc_stack_limit = gc_stack_base + gc_stack_size
            parts.append(
                f"  (global $gc_stack_limit i32 "
                f"(i32.const {gc_stack_limit}))"
            )
            parts.append(
                f"  (global $gc_heap_start i32 "
                f"(i32.const {gc_heap_start}))"
            )
            # #573: dedicated worklist-end constant.  Pre-#573
            # the mark phase used ``$gc_heap_start`` as the
            # worklist upper bound, on the (correct-at-the-time)
            # assumption that the worklist sat directly before
            # the heap.  After the wrap-table region was
            # inserted between worklist and heap, that
            # assumption broke: the worklist would think it had
            # ``worklist_size + wraptable_size`` of capacity and
            # could grow into the wrap-table, corrupting
            # entries.  Phase 2c would then operate on garbage
            # (wrong obj_ptr / kind / handle triples), evicting
            # arbitrary host-store entries.  This dedicated
            # constant is always exactly one ``gc_worklist_size``
            # past ``gc_stack_limit`` regardless of whether the
            # wrap-table is enabled.
            gc_worklist_end = gc_stack_limit + gc_worklist_size
            parts.append(
                f"  (global $gc_worklist_end i32 "
                f"(i32.const {gc_worklist_end}))"
            )
            parts.append(
                "  (global $gc_free_head (mut i32) (i32.const 0))"
            )
            if wrap_enabled:
                gc_wraptable_end = gc_wraptable_base + gc_wraptable_size
                parts.append(
                    f"  (global $gc_wrap_base i32 "
                    f"(i32.const {gc_wraptable_base}))"
                )
                parts.append(
                    f"  (global $gc_wrap_ptr (mut i32) "
                    f"(i32.const {gc_wraptable_base}))"
                )
                parts.append(
                    f"  (global $gc_wrap_end i32 "
                    f"(i32.const {gc_wraptable_end}))"
                )
            parts.append(self._emit_alloc())
            if wrap_enabled:
                parts.append(self._emit_register_wrapper())
                # #573: export $register_wrapper so host helpers
                # (JSON / HTML parsers in `vera/codegen/api.py`)
                # can register wrappers for Map allocations they
                # build internally — otherwise JObject /
                # HtmlElement field Maps wouldn't get reclaimed
                # and would also break ``map_contains`` / ``map_get``
                # at the WASM layer (which now expects wrapper
                # pointers, not raw handles, on the operand stack).
                parts.append(
                    '  (export "register_wrapper" '
                    '(func $register_wrapper))'
                )
            parts.append(self._emit_gc_collect())

        # Export $alloc when host functions need to allocate WASM memory,
        # or when the heap allocator is compiled in (e.g. String params need
        # allocation for CLI argument passing)
        if (
            (self._io_ops_used & _IO_OPS_NEEDING_ALLOC)
            or self._md_ops_used
            or self._regex_ops_used
            or self._map_ops_used
            or self._set_ops_used
            or self._decimal_ops_used
            or self._json_ops_used
            or self._html_ops_used
            or self._http_ops_used
            or self._inference_ops_used
            or self._needs_alloc
        ):
            parts.append('  (export "alloc" (func $alloc))')

        # Closure type declarations (for call_indirect)
        for sig_content, sig_name in self._closure_sigs.items():
            parts.append(f"  (type {sig_name} (func {sig_content}))")

        # Function table (for indirect calls via closures)
        if self._needs_table and self._closure_table:
            table_size = len(self._closure_table)
            parts.append(f"  (table {table_size} funcref)")
            elem_entries = " ".join(self._closure_table)
            parts.append(
                f"  (elem (i32.const 0) func {elem_entries})"
            )

        # Functions (user-defined)
        for fn_wat in functions:
            parts.append(fn_wat)

        # Lifted closure functions
        for closure_wat in self._closure_fns_wat:
            parts.append(closure_wat)

        parts.append(")")
        return "\n".join(parts)

    # -----------------------------------------------------------------
    # GC infrastructure helpers
    # -----------------------------------------------------------------

    def _emit_alloc(self) -> str:
        """Emit the $alloc function with GC headers, free list, and grow.

        $alloc(payload_size) -> ptr  (ptr points past the 4-byte header)

        Algorithm:
          1. Try the free list (first-fit).
          2. Bump-allocate with a 4-byte object header.
          3. If OOM: run $gc_collect, retry free list, else memory.grow.

        Diagnostic mode: when ``VERA_EAGER_GC=1`` (case-insensitive,
        also accepts ``true``/``yes``/``on``) is set in the environment
        at compile time, emit ``call $gc_collect`` as the first
        instruction of the function body — immediately after the
        ``(local ...)`` declarations, since WAT requires locals at the
        top — so a collection runs on EVERY allocation.  This converts
        latent missing-shadow-root bugs from "fires occasionally at
        scale" into "fires on the very next allocation," giving a sharp
        signal for debugging GC-rooting regressions (#593).  Slow —
        orders of magnitude slower than normal — never enable in
        production.
        """
        eager = os.environ.get("VERA_EAGER_GC", "").strip().lower() in (
            "1", "true", "yes", "on",
        )
        eager_prefix = (
            "    ;; VERA_EAGER_GC=1 — force GC on every alloc to surface\n"
            "    ;; missing shadow-stack roots (debugging knob, see\n"
            "    ;; AssemblyMixin._emit_alloc docstring).\n"
            "    call $gc_collect\n"
            if eager
            else ""
        )
        return (
            "  (func $alloc (param $size i32) (result i32)\n"
            "    (local $total i32)\n"
            "    (local $ptr i32)\n"
            "    (local $prev i32)\n"
            "    (local $node i32)\n"
            "    (local $node_size i32)\n"
            + eager_prefix
            + "    ;; Enforce the 31-bit size invariant: the header packs\n"
            "    ;; (size << 1) | mark into an i32, so size >= 2^31 would\n"
            "    ;; wrap into bit 0 (mark) and silently produce a zero-\n"
            "    ;; size header.  Trap cleanly instead.\n"
            "    local.get $size\n"
            "    i32.const 0x80000000\n"
            "    i32.and\n"
            "    if\n"
            "      unreachable\n"
            "    end\n"
            "    ;; total = align_up(size + 4, 8)\n"
            "    local.get $size\n"
            "    i32.const 4\n"
            "    i32.add\n"
            "    i32.const 7\n"
            "    i32.add\n"
            "    i32.const -8\n"
            "    i32.and\n"
            "    local.set $total\n"
            "\n"
            "    ;; --- Try free list (first-fit) ---\n"
            "    i32.const 0\n"
            "    local.set $prev\n"
            "    global.get $gc_free_head\n"
            "    local.set $node\n"
            "    block $fl_done\n"
            "    loop $fl_loop\n"
            "      local.get $node\n"
            "      i32.eqz\n"
            "      br_if $fl_done\n"
            "      ;; node_size = header.size (bits 1-31; bit 0 = mark)\n"
            "      local.get $node\n"
            "      i32.const 4\n"
            "      i32.sub\n"
            "      i32.load\n"
            "      i32.const 1\n"
            "      i32.shr_u\n"
            "      local.set $node_size\n"
            "      ;; if node_size >= requested size, reuse block\n"
            "      local.get $node_size\n"
            "      local.get $size\n"
            "      i32.ge_u\n"
            "      if\n"
            "        ;; Unlink: prev.next = node.next\n"
            "        local.get $prev\n"
            "        i32.eqz\n"
            "        if\n"
            "          ;; node is the head\n"
            "          local.get $node\n"
            "          i32.load\n"
            "          global.set $gc_free_head\n"
            "        else\n"
            "          local.get $prev\n"
            "          local.get $node\n"
            "          i32.load\n"
            "          i32.store\n"
            "        end\n"
            "        ;; Clear mark bit, keep size\n"
            "        local.get $node\n"
            "        i32.const 4\n"
            "        i32.sub\n"
            "        local.get $node_size\n"
            "        i32.const 1\n"
            "        i32.shl\n"
            "        i32.store\n"
            "        local.get $node\n"
            "        return\n"
            "      end\n"
            "      ;; Advance: prev = node, node = node.next\n"
            "      local.get $node\n"
            "      local.set $prev\n"
            "      local.get $node\n"
            "      i32.load\n"
            "      local.set $node\n"
            "      br $fl_loop\n"
            "    end\n"
            "    end\n"
            "\n"
            "    ;; --- Bump allocate ---\n"
            "    global.get $heap_ptr\n"
            "    local.get $total\n"
            "    i32.add\n"
            "    memory.size\n"
            "    i32.const 16\n"
            "    i32.shl\n"
            "    i32.gt_u\n"
            "    if\n"
            "      ;; OOM — try GC\n"
            "      call $gc_collect\n"
            "      ;; Retry free list after GC\n"
            "      i32.const 0\n"
            "      local.set $prev\n"
            "      global.get $gc_free_head\n"
            "      local.set $node\n"
            "      block $fl2_done\n"
            "      loop $fl2_loop\n"
            "        local.get $node\n"
            "        i32.eqz\n"
            "        br_if $fl2_done\n"
            "        local.get $node\n"
            "        i32.const 4\n"
            "        i32.sub\n"
            "        i32.load\n"
            "        i32.const 1\n"
            "        i32.shr_u\n"
            "        local.set $node_size\n"
            "        local.get $node_size\n"
            "        local.get $size\n"
            "        i32.ge_u\n"
            "        if\n"
            "          local.get $prev\n"
            "          i32.eqz\n"
            "          if\n"
            "            local.get $node\n"
            "            i32.load\n"
            "            global.set $gc_free_head\n"
            "          else\n"
            "            local.get $prev\n"
            "            local.get $node\n"
            "            i32.load\n"
            "            i32.store\n"
            "          end\n"
            "          local.get $node\n"
            "          i32.const 4\n"
            "          i32.sub\n"
            "          local.get $node_size\n"
            "          i32.const 1\n"
            "          i32.shl\n"
            "          i32.store\n"
            "          local.get $node\n"
            "          return\n"
            "        end\n"
            "        local.get $node\n"
            "        local.set $prev\n"
            "        local.get $node\n"
            "        i32.load\n"
            "        local.set $node\n"
            "        br $fl2_loop\n"
            "      end\n"
            "      end\n"
            "      ;; Still OOM — grow memory.\n"
            "      ;; #487: pre-fix this grew by exactly 1 page (64 KB)\n"
            "      ;; regardless of how short of memory we were, so a\n"
            "      ;; single allocation more than ~64 KB past the\n"
            "      ;; current memory boundary would silently fall\n"
            "      ;; through to the bump-allocate below and trap on\n"
            "      ;; out-of-bounds memory access.  Post-fix: compute\n"
            "      ;; the number of pages needed via\n"
            "      ;;   shortage = (heap_ptr + total) - memory.size*65536\n"
            "      ;;   pages_needed = ceil(shortage / 65536)\n"
            "      ;;                = (shortage + 65535) >> 16\n"
            "      ;; and grow by that many pages in a single call.\n"
            "      global.get $heap_ptr\n"
            "      local.get $total\n"
            "      i32.add\n"
            "      memory.size\n"
            "      i32.const 16\n"
            "      i32.shl\n"
            "      i32.gt_u\n"
            "      if\n"
            "        ;; pages_needed = (shortage + 65535) >> 16\n"
            "        global.get $heap_ptr\n"
            "        local.get $total\n"
            "        i32.add\n"
            "        memory.size\n"
            "        i32.const 16\n"
            "        i32.shl\n"
            "        i32.sub\n"
            "        i32.const 65535\n"
            "        i32.add\n"
            "        i32.const 16\n"
            "        i32.shr_u\n"
            "        memory.grow\n"
            "        i32.const -1\n"
            "        i32.eq\n"
            "        if\n"
            "          unreachable\n"
            "        end\n"
            "      end\n"
            "    end\n"
            "\n"
            "    ;; #578: heap-ceiling guard.  heap_ptr + total must\n"
            "    ;; stay below 0x80000000 (2 GiB) so wrapper handles\n"
            "    ;; tagged with bit 31 in their in-heap field remain\n"
            "    ;; outside the conservative-scan heap-range check.\n"
            "    ;; Without this guard, a >2 GiB heap would let real\n"
            "    ;; heap pointers reach 0x80000000+ and start colliding\n"
            "    ;; with the tagged-handle pattern, reintroducing the\n"
            "    ;; spurious-retention bug.  Programs we have measured\n"
            "    ;; stay well below the 2 GiB ceiling; this trap fires\n"
            "    ;; only when something has gone very wrong.\n"
            # TODO (#578 follow-up): the heap-ceiling trap below
            # surfaces via the trap classifier as the generic
            # ``unreachable`` kind with a Fix message about match
            # arms — misleading for this case.  Practical programs
            # never hit this trap (heap << 2 GiB) so the polish is
            # deferred; a follow-up would either populate
            # ``last_violation`` via a host import or add a
            # dedicated classifier kind.  Kept as a Python comment
            # rather than a WAT comment so the emitted WAT stays
            # compact and the adjacent-sequence regex in
            # tests/test_codegen.py::TestWrapperHandleTagging578::
            # test_alloc_emits_heap_ceiling_guard stays simple.
            "    global.get $heap_ptr\n"
            "    local.get $total\n"
            "    i32.add\n"
            "    i32.const 0x80000000\n"
            "    i32.ge_u\n"
            "    if\n"
            "      unreachable\n"
            "    end\n"
            "\n"
            "    ;; Bump: store header, advance heap_ptr, return payload\n"
            "    global.get $heap_ptr\n"
            "    local.set $ptr\n"
            "    ;; Header: (size << 1) | 0  (mark=0)\n"
            "    local.get $ptr\n"
            "    local.get $size\n"
            "    i32.const 1\n"
            "    i32.shl\n"
            "    i32.store\n"
            "    ;; Advance heap_ptr\n"
            "    global.get $heap_ptr\n"
            "    local.get $total\n"
            "    i32.add\n"
            "    global.set $heap_ptr\n"
            "    ;; Return payload pointer (past header)\n"
            "    local.get $ptr\n"
            "    i32.const 4\n"
            "    i32.add\n"
            "  )"
        )

    def _emit_register_wrapper(self) -> str:
        """Emit ``$register_wrapper(ptr, kind, handle)`` for #573.

        Appends a 16-byte entry to the wrap-table region:

        ::

            offset 0: ptr   (i32) — pointer to wrapper ADT in the GC heap
            offset 4: kind  (i32) — 1=Map, 2=Set, 3=Decimal, 4..N reserved
            offset 8: handle (i32) — index into the host-side store
            offset 12: reserved (zero) — alignment / future use

        On overflow (4 096 simultaneously-live wrappers between
        collections) the slow path triggers ``$gc_collect``, which
        runs Phase 2c compaction — survivors are kept in place,
        dead entries are dropped, ``$gc_wrap_ptr`` is reset to the
        compacted end.  After the collect the overflow check is
        re-evaluated; only if the table is *still* full do we trap
        with ``unreachable`` (which means 4 096+ wrappers are
        genuinely live and the program is over the budget; bumping
        ``gc_wraptable_size`` is the cure).

        The slow path roots the in-flight wrapper on the shadow
        stack *before* calling ``$gc_collect`` because the wrapper
        isn't in the wrap-table yet (that's what we're trying to
        do) and its body has just been allocated by the caller —
        without rooting, Phase 2b would mark it unreachable and
        Phase 3 would link it into the free list, leaving us
        appending to a freed object after the collect.  The pop
        immediately after the collect keeps the shadow stack
        stable so iterative builders' per-iteration push count
        doesn't drift across calls.

        The destructor side (firing ``host_decref_handle`` for
        unmarked wrappers) lives in ``$gc_collect`` Phase 2c.
        """
        return (
            "  (func $register_wrapper "
            "(param $ptr i32) (param $kind i32) (param $handle i32)\n"
            "    ;; Overflow check: try compaction first, only\n"
            "    ;; trap if still full afterwards (#573 / #579).\n"
            "    global.get $gc_wrap_ptr\n"
            "    global.get $gc_wrap_end\n"
            "    i32.ge_u\n"
            "    if\n"
            "      ;; Slow path: root the in-flight wrapper, then\n"
            "      ;; collect.  Without the push, Phase 2b marks the\n"
            "      ;; in-flight wrapper unreachable and Phase 3\n"
            "      ;; frees it; we'd append to a freed object.\n"
            "      global.get $gc_sp\n"
            "      global.get $gc_stack_limit\n"
            "      i32.ge_u\n"
            "      if\n"
            "        unreachable\n"
            "      end\n"
            "      global.get $gc_sp\n"
            "      local.get $ptr\n"
            "      i32.store\n"
            "      global.get $gc_sp\n"
            "      i32.const 4\n"
            "      i32.add\n"
            "      global.set $gc_sp\n"
            "      ;; Compact: Phase 2c walks the wrap-table,\n"
            "      ;; drops unmarked entries, resets $gc_wrap_ptr.\n"
            "      call $gc_collect\n"
            "      ;; Pop the temporary root.\n"
            "      global.get $gc_sp\n"
            "      i32.const 4\n"
            "      i32.sub\n"
            "      global.set $gc_sp\n"
            "      ;; Re-check; trap only if still full.\n"
            "      global.get $gc_wrap_ptr\n"
            "      global.get $gc_wrap_end\n"
            "      i32.ge_u\n"
            "      if\n"
            "        unreachable\n"
            "      end\n"
            "    end\n"
            "    ;; entry[0] = ptr\n"
            "    global.get $gc_wrap_ptr\n"
            "    local.get $ptr\n"
            "    i32.store offset=0\n"
            "    ;; entry[4] = kind\n"
            "    global.get $gc_wrap_ptr\n"
            "    local.get $kind\n"
            "    i32.store offset=4\n"
            "    ;; entry[8] = handle\n"
            "    global.get $gc_wrap_ptr\n"
            "    local.get $handle\n"
            "    i32.store offset=8\n"
            "    ;; entry[12] = 0 (reserved; explicit init covers re-use\n"
            "    ;; of compacted-out slots that may carry stale bytes).\n"
            "    global.get $gc_wrap_ptr\n"
            "    i32.const 0\n"
            "    i32.store offset=12\n"
            "    ;; Advance write pointer by 16 bytes.\n"
            "    global.get $gc_wrap_ptr\n"
            "    i32.const 16\n"
            "    i32.add\n"
            "    global.set $gc_wrap_ptr\n"
            "  )"
        )

    def _emit_phase_2c(self) -> str:
        """Emit Phase 2c of ``$gc_collect`` for #573.

        Walks the wrap-table side index of host-handle wrapper
        objects.  After Phase 2b has completed marking, every
        wrapper-object's mark bit reflects reachability from the
        live root set.  For each entry:

        * **Marked** → wrapper is reachable.  Copy entry to the
          compaction write pointer (``$wrap_write``) and advance.
        * **Unmarked** → wrapper is unreachable.  Call the
          ``host_decref_handle(kind, handle)`` host import, which
          evicts the corresponding entry from the Python-side
          (or browser-side) store.  Drop the entry by *not*
          copying it forward.

        After the walk, ``$gc_wrap_ptr := $wrap_write``, so the
        wrap table tracks live wrappers only.  Runs **before**
        Phase 3 (sweep) so an unmarked wrapper's body is still
        intact when its kind/handle are read; Phase 3 then links
        the unmarked wrapper object itself into the free list
        like any other unreachable allocation.
        """
        return (
            "    ;; === Phase 2c: Walk wrap table — fire destructors ===\n"
            "    ;; #573: each wrap-table entry is 16 bytes:\n"
            "    ;;   [0] obj_ptr — pointer to wrapper ADT body\n"
            "    ;;   [4] kind    — 1=Map, 2=Set, 3=Decimal\n"
            "    ;;   [8] handle  — i32 index into host-side store\n"
            "    ;;   [12] reserved\n"
            "    ;; Compact in place: write pointer trails read.\n"
            "    global.get $gc_wrap_base\n"
            "    local.set $wrap_read\n"
            "    global.get $gc_wrap_base\n"
            "    local.set $wrap_write\n"
            "    block $wt_done\n"
            "    loop $wt_loop\n"
            "      local.get $wrap_read\n"
            "      global.get $gc_wrap_ptr\n"
            "      i32.ge_u\n"
            "      br_if $wt_done\n"
            "      ;; Load entry fields.\n"
            "      local.get $wrap_read\n"
            "      i32.load offset=0\n"
            "      local.set $obj_ptr\n"
            "      local.get $wrap_read\n"
            "      i32.load offset=4\n"
            "      local.set $wrap_kind\n"
            "      local.get $wrap_read\n"
            "      i32.load offset=8\n"
            "      local.set $wrap_handle\n"
            "      ;; Mark bit lives in header at obj_ptr - 4.\n"
            "      local.get $obj_ptr\n"
            "      i32.const 4\n"
            "      i32.sub\n"
            "      i32.load\n"
            "      i32.const 1\n"
            "      i32.and\n"
            "      if\n"
            "        ;; Marked → keep.  Copy to compaction position.\n"
            "        local.get $wrap_write\n"
            "        local.get $obj_ptr\n"
            "        i32.store offset=0\n"
            "        local.get $wrap_write\n"
            "        local.get $wrap_kind\n"
            "        i32.store offset=4\n"
            "        local.get $wrap_write\n"
            "        local.get $wrap_handle\n"
            "        i32.store offset=8\n"
            "        local.get $wrap_write\n"
            "        i32.const 0\n"
            "        i32.store offset=12\n"
            "        local.get $wrap_write\n"
            "        i32.const 16\n"
            "        i32.add\n"
            "        local.set $wrap_write\n"
            "      else\n"
            "        ;; Unmarked → fire destructor.  Evicts entry from\n"
            "        ;; Python/JS host store; the wrapper-ADT object\n"
            "        ;; itself is reclaimed by Phase 3 below like any\n"
            "        ;; other unreachable allocation.\n"
            "        local.get $wrap_kind\n"
            "        local.get $wrap_handle\n"
            "        call $vera.host_decref_handle\n"
            "      end\n"
            "      local.get $wrap_read\n"
            "      i32.const 16\n"
            "      i32.add\n"
            "      local.set $wrap_read\n"
            "      br $wt_loop\n"
            "    end\n"
            "    end\n"
            "    ;; Truncate wrap table to compacted live entries.\n"
            "    local.get $wrap_write\n"
            "    global.set $gc_wrap_ptr\n"
            "\n"
        )

    def _emit_gc_collect(self) -> str:
        """Emit the $gc_collect function: mark-sweep garbage collector.

        Three phases (plus Phase 2c when the wrap table is enabled):
          1. Clear all mark bits in the heap.
          2. Mark from shadow-stack roots (iterative, conservative).
          2c. (#573) Walk the wrap table: fire ``host_decref_handle``
              for unmarked wrapper entries; compact survivors in
              place.  Only emitted when ``self._needs_wrap_table``
              is true.
          3. Sweep: link unmarked objects into the free list.
        """
        wrap_enabled = self._needs_wrap_table
        wrap_locals = (
            "    (local $wrap_read i32)\n"
            "    (local $wrap_write i32)\n"
            "    (local $wrap_kind i32)\n"
            "    (local $wrap_handle i32)\n"
            if wrap_enabled
            else ""
        )
        # Worklist region sits right after shadow stack, sized to match
        return (
            "  (func $gc_collect\n"
            "    (local $ptr i32)\n"
            "    (local $header i32)\n"
            "    (local $obj_size i32)\n"
            "    (local $scan_ptr i32)\n"
            "    (local $val i32)\n"
            "    (local $wl_base i32)\n"
            "    (local $wl_ptr i32)\n"
            "    (local $wl_end i32)\n"
            "    (local $obj_ptr i32)\n"
            "    (local $free_head i32)\n"
            + wrap_locals
            + "\n"
            "    ;; Worklist region: gc_stack_limit .. gc_worklist_end.\n"
            "    ;; #573: use the dedicated worklist-end constant\n"
            "    ;; rather than $gc_heap_start — with the wrap-table\n"
            "    ;; enabled, $gc_heap_start sits past the wrap-table\n"
            "    ;; and the worklist could grow into and corrupt\n"
            "    ;; wrap-table entries.\n"
            "    global.get $gc_stack_limit\n"
            "    local.set $wl_base\n"
            "    local.get $wl_base\n"
            "    local.set $wl_ptr\n"
            "    global.get $gc_worklist_end\n"
            "    local.set $wl_end\n"
            "\n"
            "    ;; === Phase 1: Clear all mark bits ===\n"
            "    global.get $gc_heap_start\n"
            "    local.set $ptr\n"
            "    block $c_done\n"
            "    loop $c_loop\n"
            "      local.get $ptr\n"
            "      global.get $heap_ptr\n"
            "      i32.ge_u\n"
            "      br_if $c_done\n"
            "      ;; Clear mark bit (bit 0)\n"
            "      local.get $ptr\n"
            "      local.get $ptr\n"
            "      i32.load\n"
            "      i32.const -2\n"
            "      i32.and\n"
            "      i32.store\n"
            "      ;; Advance: ptr += align_up(size + 4, 8)\n"
            "      local.get $ptr\n"
            "      i32.load\n"
            "      i32.const 1\n"
            "      i32.shr_u\n"
            "      i32.const 11\n"
            "      i32.add\n"
            "      i32.const -8\n"
            "      i32.and\n"
            "      local.get $ptr\n"
            "      i32.add\n"
            "      local.set $ptr\n"
            "      br $c_loop\n"
            "    end\n"
            "    end\n"
            "\n"
            "    ;; === Phase 2: Seed worklist from shadow stack ===\n"
            "    global.get $gc_stack_base\n"
            "    local.set $scan_ptr\n"
            "    block $s_done\n"
            "    loop $s_loop\n"
            "      local.get $scan_ptr\n"
            "      global.get $gc_sp\n"
            "      i32.ge_u\n"
            "      br_if $s_done\n"
            "      local.get $scan_ptr\n"
            "      i32.load\n"
            "      local.set $val\n"
            "      ;; Check if val is a valid heap pointer.\n"
            "      ;;\n"
            "      ;; #578 invariant (do not weaken without revisiting\n"
            "      ;; the spurious-retention proof): wrapper-handle\n"
            "      ;; fields are stored at body+4 with bit 31 set\n"
            "      ;; (`handle | 0x80000000`).  The $alloc heap-ceiling\n"
            "      ;; guard enforces heap_ptr < 0x80000000, so any\n"
            "      ;; tagged value (>= 2 GiB) fails `val < heap_ptr`\n"
            "      ;; below — they are structurally disjoint from\n"
            "      ;; real heap pointers.  If a future change moves\n"
            "      ;; the wrap tag to a different bit (e.g. `handle\n"
            "      ;; | 0x40000000`) OR raises the heap ceiling above\n"
            "      ;; 2 GiB, this scan can re-classify wrapper handles\n"
            "      ;; as heap pointers and #578 reappears.  Two\n"
            "      ;; structural tests pin the invariant against that\n"
            "      ;; class of regression:\n"
            "      ;; tests/test_codegen.py::TestWrapperHandleTagging578::\n"
            "      ;;   test_wrap_emits_tag_or (pins the bit)\n"
            "      ;;   test_alloc_emits_heap_ceiling_guard (pins ceiling)\n"
            "      local.get $val\n"
            "      global.get $gc_heap_start\n"
            "      i32.const 4\n"
            "      i32.add\n"
            "      i32.ge_u\n"
            "      if\n"
            "        local.get $val\n"
            "        global.get $heap_ptr\n"
            "        i32.lt_u\n"
            "        if\n"
            "          ;; Check alignment: (val - gc_heap_start) % 8 == 4\n"
            "          local.get $val\n"
            "          global.get $gc_heap_start\n"
            "          i32.sub\n"
            "          i32.const 7\n"
            "          i32.and\n"
            "          i32.const 4\n"
            "          i32.eq\n"
            "          if\n"
            "            ;; Push onto worklist.  #348: pre-fix this\n"
            "            ;; silently dropped pushes when the worklist\n"
            "            ;; was full — reachable objects beyond the\n"
            "            ;; capacity stayed unmarked and got swept\n"
            "            ;; (use-after-free).  Post-fix: trap on\n"
            "            ;; overflow so the failure is a clean WASM\n"
            "            ;; trap rather than memory corruption.  The\n"
            "            ;; worklist size has been quadrupled (64 KiB,\n"
            "            ;; 16 384 entries) so reasonable program\n"
            "            ;; shapes shouldn't reach this path.\n"
            "            local.get $wl_ptr\n"
            "            local.get $wl_end\n"
            "            i32.ge_u\n"
            "            if\n"
            "              unreachable\n"
            "            end\n"
            "            local.get $wl_ptr\n"
            "            local.get $val\n"
            "            i32.store\n"
            "            local.get $wl_ptr\n"
            "            i32.const 4\n"
            "            i32.add\n"
            "            local.set $wl_ptr\n"
            "          end\n"
            "        end\n"
            "      end\n"
            "      local.get $scan_ptr\n"
            "      i32.const 4\n"
            "      i32.add\n"
            "      local.set $scan_ptr\n"
            "      br $s_loop\n"
            "    end\n"
            "    end\n"
            "\n"
            "    ;; === Phase 2b: Mark loop (drain worklist) ===\n"
            "    block $m_done\n"
            "    loop $m_loop\n"
            "      ;; Pop from worklist\n"
            "      local.get $wl_ptr\n"
            "      local.get $wl_base\n"
            "      i32.le_u\n"
            "      br_if $m_done\n"
            "      local.get $wl_ptr\n"
            "      i32.const 4\n"
            "      i32.sub\n"
            "      local.set $wl_ptr\n"
            "      local.get $wl_ptr\n"
            "      i32.load\n"
            "      local.set $obj_ptr\n"
            "      ;; Load header\n"
            "      local.get $obj_ptr\n"
            "      i32.const 4\n"
            "      i32.sub\n"
            "      i32.load\n"
            "      local.set $header\n"
            "      ;; Compute obj_size early so we can sanity-check it.\n"
            "      local.get $header\n"
            "      i32.const 1\n"
            "      i32.shr_u\n"
            "      local.set $obj_size\n"
            "      ;; Layer 2 (issue #515): conservative-GC sanity check.\n"
            "      ;; The Phase 2 worklist push only guards on alignment and\n"
            "      ;; range, not on header validity.  A non-pointer i32 in\n"
            "      ;; payload data can satisfy those guards, in which case\n"
            "      ;; $header here is garbage and $obj_size can be wildly\n"
            "      ;; larger than the heap.  Skip this entry entirely if\n"
            "      ;; obj_ptr + obj_size walks past heap_ptr — without this,\n"
            "      ;; the scan below traps reading past the memory boundary,\n"
            "      ;; and the mark store further down would corrupt a random\n"
            "      ;; payload word.\n"
            "      local.get $obj_ptr\n"
            "      local.get $obj_size\n"
            "      i32.add\n"
            "      global.get $heap_ptr\n"
            "      i32.gt_u\n"
            "      if\n"
            "        br $m_loop\n"
            "      end\n"
            "      ;; Already marked? Skip.\n"
            "      local.get $header\n"
            "      i32.const 1\n"
            "      i32.and\n"
            "      if\n"
            "        br $m_loop\n"
            "      end\n"
            "      ;; Set mark bit\n"
            "      local.get $obj_ptr\n"
            "      i32.const 4\n"
            "      i32.sub\n"
            "      local.get $header\n"
            "      i32.const 1\n"
            "      i32.or\n"
            "      i32.store\n"
            "      ;; Conservative scan: check every i32-aligned word\n"
            "      i32.const 0\n"
            "      local.set $scan_ptr\n"
            "      block $sc_done\n"
            "      loop $sc_loop\n"
            "        local.get $scan_ptr\n"
            "        local.get $obj_size\n"
            "        i32.ge_u\n"
            "        br_if $sc_done\n"
            "        ;; Layer 1 (issue #515): defence-in-depth bound check.\n"
            "        ;; Even with the upstream sanity check above, never load\n"
            "        ;; from an address >= heap_ptr.  Cheap (a single ge_u)\n"
            "        ;; relative to the i32.load it guards, and protects any\n"
            "        ;; future caller that reaches this loop without the\n"
            "        ;; Layer-2 check.\n"
            "        local.get $obj_ptr\n"
            "        local.get $scan_ptr\n"
            "        i32.add\n"
            "        i32.const 4\n"
            "        i32.add\n"
            "        global.get $heap_ptr\n"
            "        i32.gt_u\n"
            "        br_if $sc_done\n"
            "        ;; val = load(obj_ptr + scan_ptr)\n"
            "        local.get $obj_ptr\n"
            "        local.get $scan_ptr\n"
            "        i32.add\n"
            "        i32.load\n"
            "        local.set $val\n"
            "        ;; Valid heap pointer check\n"
            "        local.get $val\n"
            "        global.get $gc_heap_start\n"
            "        i32.const 4\n"
            "        i32.add\n"
            "        i32.ge_u\n"
            "        if\n"
            "          local.get $val\n"
            "          global.get $heap_ptr\n"
            "          i32.lt_u\n"
            "          if\n"
            "            local.get $val\n"
            "            global.get $gc_heap_start\n"
            "            i32.sub\n"
            "            i32.const 7\n"
            "            i32.and\n"
            "            i32.const 4\n"
            "            i32.eq\n"
            "            if\n"
            "              ;; Not already marked? Push to worklist.\n"
            "              ;; #348: trap on overflow rather than\n"
            "              ;; silently dropping (see Phase 2 seed for\n"
            "              ;; the rationale).\n"
            "              local.get $val\n"
            "              i32.const 4\n"
            "              i32.sub\n"
            "              i32.load\n"
            "              i32.const 1\n"
            "              i32.and\n"
            "              i32.eqz\n"
            "              if\n"
            "                local.get $wl_ptr\n"
            "                local.get $wl_end\n"
            "                i32.ge_u\n"
            "                if\n"
            "                  unreachable\n"
            "                end\n"
            "                local.get $wl_ptr\n"
            "                local.get $val\n"
            "                i32.store\n"
            "                local.get $wl_ptr\n"
            "                i32.const 4\n"
            "                i32.add\n"
            "                local.set $wl_ptr\n"
            "              end\n"
            "            end\n"
            "          end\n"
            "        end\n"
            "        local.get $scan_ptr\n"
            "        i32.const 4\n"
            "        i32.add\n"
            "        local.set $scan_ptr\n"
            "        br $sc_loop\n"
            "      end\n"
            "      end\n"
            "      br $m_loop\n"
            "    end\n"
            "    end\n"
            "\n"
            + (
                self._emit_phase_2c()
                if wrap_enabled
                else ""
            )
            + "    ;; === Phase 3: Sweep — build free list ===\n"
            "    i32.const 0\n"
            "    local.set $free_head\n"
            "    global.get $gc_heap_start\n"
            "    local.set $ptr\n"
            "    block $sw_done\n"
            "    loop $sw_loop\n"
            "      local.get $ptr\n"
            "      global.get $heap_ptr\n"
            "      i32.ge_u\n"
            "      br_if $sw_done\n"
            "      local.get $ptr\n"
            "      i32.load\n"
            "      local.set $header\n"
            "      ;; size = header >> 1 (bit 0 = mark)\n"
            "      local.get $header\n"
            "      i32.const 1\n"
            "      i32.shr_u\n"
            "      local.set $obj_size\n"
            "      ;; Is it marked?\n"
            "      local.get $header\n"
            "      i32.const 1\n"
            "      i32.and\n"
            "      i32.eqz\n"
            "      if\n"
            "        ;; Unmarked: add to free list\n"
            "        ;; payload[0] = free_head (next pointer)\n"
            "        local.get $ptr\n"
            "        i32.const 4\n"
            "        i32.add\n"
            "        local.get $free_head\n"
            "        i32.store\n"
            "        ;; free_head = payload_ptr\n"
            "        local.get $ptr\n"
            "        i32.const 4\n"
            "        i32.add\n"
            "        local.set $free_head\n"
            "      end\n"
            "      ;; Advance: ptr += align_up(size + 4, 8)\n"
            "      local.get $obj_size\n"
            "      i32.const 11\n"
            "      i32.add\n"
            "      i32.const -8\n"
            "      i32.and\n"
            "      local.get $ptr\n"
            "      i32.add\n"
            "      local.set $ptr\n"
            "      br $sw_loop\n"
            "    end\n"
            "    end\n"
            "    ;; Update global free list head\n"
            "    local.get $free_head\n"
            "    global.set $gc_free_head\n"
            "  )"
        )
