"""Mixin for WAT module assembly.

Assembles the final WAT module text from compiled functions, imports,
memory, data sections, and closure infrastructure.
"""

from __future__ import annotations


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
            gc_heap_start = data_end + 8192  # 4K shadow stack + 4K worklist
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
            parts.append(
                f"  (global $gc_heap_start i32 "
                f"(i32.const {gc_heap_start}))"
            )
            parts.append(
                "  (global $gc_free_head (mut i32) (i32.const 0))"
            )
            parts.append(self._emit_alloc())
            parts.append(self._emit_gc_collect())

        # Export $alloc when host functions need to allocate WASM memory
        if self._io_ops_used & _IO_OPS_NEEDING_ALLOC:
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
        """
        return (
            "  (func $alloc (param $size i32) (result i32)\n"
            "    (local $total i32)\n"
            "    (local $ptr i32)\n"
            "    (local $prev i32)\n"
            "    (local $node i32)\n"
            "    (local $node_size i32)\n"
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
            "      ;; node_size = header.size (bits 1-16)\n"
            "      local.get $node\n"
            "      i32.const 4\n"
            "      i32.sub\n"
            "      i32.load\n"
            "      i32.const 1\n"
            "      i32.shr_u\n"
            "      i32.const 65535\n"
            "      i32.and\n"
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
            "        i32.const 65535\n"
            "        i32.and\n"
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
            "      ;; Still OOM — grow memory\n"
            "      global.get $heap_ptr\n"
            "      local.get $total\n"
            "      i32.add\n"
            "      memory.size\n"
            "      i32.const 16\n"
            "      i32.shl\n"
            "      i32.gt_u\n"
            "      if\n"
            "        i32.const 1\n"
            "        memory.grow\n"
            "        i32.const -1\n"
            "        i32.eq\n"
            "        if\n"
            "          unreachable\n"
            "        end\n"
            "      end\n"
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

    def _emit_gc_collect(self) -> str:
        """Emit the $gc_collect function: mark-sweep garbage collector.

        Three phases:
          1. Clear all mark bits in the heap.
          2. Mark from shadow-stack roots (iterative, conservative).
          3. Sweep: link unmarked objects into the free list.
        """
        # Worklist region sits at gc_stack_base + 4096, size 4096 (1024 entries)
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
            "\n"
            "    ;; Worklist region: gc_stack_base + 4096 .. +8192\n"
            "    global.get $gc_stack_base\n"
            "    i32.const 4096\n"
            "    i32.add\n"
            "    local.set $wl_base\n"
            "    local.get $wl_base\n"
            "    local.set $wl_ptr\n"
            "    local.get $wl_base\n"
            "    i32.const 4096\n"
            "    i32.add\n"
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
            "      i32.const 65535\n"
            "      i32.and\n"
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
            "      ;; Check if val is a valid heap pointer\n"
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
            "            ;; Push onto worklist (if space)\n"
            "            local.get $wl_ptr\n"
            "            local.get $wl_end\n"
            "            i32.lt_u\n"
            "            if\n"
            "              local.get $wl_ptr\n"
            "              local.get $val\n"
            "              i32.store\n"
            "              local.get $wl_ptr\n"
            "              i32.const 4\n"
            "              i32.add\n"
            "              local.set $wl_ptr\n"
            "            end\n"
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
            "      local.get $header\n"
            "      i32.const 1\n"
            "      i32.shr_u\n"
            "      i32.const 65535\n"
            "      i32.and\n"
            "      local.set $obj_size\n"
            "      i32.const 0\n"
            "      local.set $scan_ptr\n"
            "      block $sc_done\n"
            "      loop $sc_loop\n"
            "        local.get $scan_ptr\n"
            "        local.get $obj_size\n"
            "        i32.ge_u\n"
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
            "                i32.lt_u\n"
            "                if\n"
            "                  local.get $wl_ptr\n"
            "                  local.get $val\n"
            "                  i32.store\n"
            "                  local.get $wl_ptr\n"
            "                  i32.const 4\n"
            "                  i32.add\n"
            "                  local.set $wl_ptr\n"
            "                end\n"
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
            "    ;; === Phase 3: Sweep — build free list ===\n"
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
            "      ;; size = (header >> 1) & 0xFFFF\n"
            "      local.get $header\n"
            "      i32.const 1\n"
            "      i32.shr_u\n"
            "      i32.const 65535\n"
            "      i32.and\n"
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
