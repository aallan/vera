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

        # Import IO.print if needed
        if self._needs_io_print:
            parts.append(
                '  (import "vera" "print" '
                "(func $vera.print (param i32 i32)))"
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

        # Heap pointer global and bump allocator (for ADT allocation)
        if self._needs_alloc:
            heap_start = self.string_pool.heap_offset
            parts.append(
                f"  (global $heap_ptr (export \"heap_ptr\") "
                f"(mut i32) (i32.const {heap_start}))"
            )
            parts.append(
                "  (func $alloc (param $size i32) (result i32)\n"
                "    (local $ptr i32)\n"
                "    ;; Save current heap pointer\n"
                "    global.get $heap_ptr\n"
                "    local.set $ptr\n"
                "    ;; Advance heap_ptr by size rounded up to 8\n"
                "    global.get $heap_ptr\n"
                "    local.get $size\n"
                "    i32.const 7\n"
                "    i32.add\n"
                "    i32.const -8\n"
                "    i32.and\n"
                "    i32.add\n"
                "    global.set $heap_ptr\n"
                "    ;; Return old pointer\n"
                "    local.get $ptr\n"
                "  )"
            )

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
