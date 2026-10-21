"""Mixin for WAT module assembly.

Assembles the final WAT module text from compiled functions, imports,
memory, data sections, and closure infrastructure.
"""

from __future__ import annotations

import re

from vera.builtins import (
    HOST_FAMILIES,
    Gate,
    cell_lines,
    declaration_lines,
    family_rows,
    host_import,
)
from vera.envflags import flag_enabled
from vera.runtime import runtime_export
from vera.monomorphize import mangle_type_name
from vera.skip import CodegenInvariantError
from vera.trap_registry import signal_instructions
from vera.wasm.helpers import MAX_INLINE_I32_VALUE

# The two fixed regions between the data section and the GC heap.  Named
# because the #1255 heap-start invariant argues FROM them: they are
# compile-time constants, so `$gc_heap_start` clears the inline i32 scalar
# range whatever the data section holds — the guard below is what turns
# that argument into something a layout change cannot silently invalidate.
GC_STACK_SIZE = 16384  # 16 KiB shadow stack (4 096 roots)

# The GC mark phase's worklist.  Its size bounds the collector's memory,
# not the heap it can mark (#1510): a child push that finds it full is
# dropped and the object being scanned recorded as dirty, and once the
# worklist empties the dirty objects are scanned again, so marking
# completes for any heap (`_emit_gc_collect`).  The seed's pushes are the
# exception — one per shadow-stack root, onto an empty worklist, with no
# object to record a drop against — so the worklist must hold at least as
# many entries as the shadow stack holds roots (`_assemble_module` checks).
GC_WORKLIST_SIZE = 65536  # 64 KiB worklist (16 384 entries)
# #573: the wrapper table — 16 bytes per entry (obj_ptr / kind / handle /
# reserved), 4 096 entries.
GC_WRAPTABLE_SIZE = 65536
GC_WRAPTABLE_ENTRY_SIZE = 16


def heap_trap(indent: str) -> str:
    """The allocator's heap-exhaustion trap as WAT text, at *indent* (#1479).

    ``$alloc`` and ``$gc_collect`` are runtime functions, emitted once per
    module and belonging to no source site, so they render the signal
    directly rather than through ``WasmContext._emit_trap``; the import is
    declared whenever they are (``_needs_alloc``)."""
    return "".join(
        f"{indent}{instr}\n" for instr in signal_instructions("heap_exhausted"))

# #1433: the two ways a module BINDS a function identifier — a definition,
# `(func $name ...)` opening its line, and a function import,
# `(import "m" "f" (func $name ...))`.  Both are in the one function index
# space, so any two binding one name is wasm-tools' `duplicate func
# identifier`.  An export `(export "x" (func $name))`, an `elem` segment's
# `func $a $b` and a `call $name` REFERENCE an identifier and bind none.
_WAT_FUNC_DEF_RE = re.compile(r"^[ \t]*\(func \$([^\s()]+)", re.MULTILINE)
_WAT_FUNC_IMPORT_RE = re.compile(
    r'^[ \t]*\(import "[^"]*" "[^"]*" \(func \$([^\s()]+)', re.MULTILINE,
)


class AssemblyMixin:
    """Methods for assembling the WAT module."""

    def _declare_host_imports(self, parts: list[str]) -> None:
        """Declare the host imports the module calls, from the registry.

        ``_host_imports_used`` holds the import name of every call the
        module's emitted code makes, each emitter's: an effect operation's
        import, a host-imported built-in's name, and an instance's
        (``map_insert$ks_vi``) for a ``Map`` or ``Set`` call, so a call
        code generation never emits declares nothing and raises no flag.
        A family the module calls by name declares its rows among them.
        The wrap table's helpers and the two signals are declared by flag,
        and the four imports of a `State` cell once per cell, which a
        handler or a declared effect row registers before the function is
        emitted (the `old()` snapshot reads the cells while it is).

        Every flag an import in use sets is set before anything is declared:
        the wrap table's helpers come before the Json, Html and fused-async
        imports, whose use declares them too.
        """
        named: dict[str, list[str]] = {}
        for name in self._host_imports_used:
            row = host_import(name)
            if row is None:
                continue
            named.setdefault(row.family, []).append(name)
            if row.needs_alloc:
                self._needs_alloc = True
            if row.needs_memory:
                self._needs_memory = True
            if row.needs_wrap_table:
                # #573: the 64 KiB wrap table, `$register_wrapper`, phase 2c
                # of `$gc_collect` and the two helpers declared below.
                self._needs_wrap_table = True
        flagged = {
            "wrap": self._needs_wrap_table,
            "contract": self._needs_contract_fail,
            # #1479: a check called the signal, or the allocator reports
            # heap exhaustion through it.
            "trap": self._needs_trap or self._needs_alloc,
        }
        for family in HOST_FAMILIES:
            if family.gate is Gate.NAMES:
                parts.extend(declaration_lines(family.name, named.get(family.name, ())))
            elif family.gate is Gate.FLAG:
                if flagged[family.name]:
                    parts.extend(declaration_lines(
                        family.name,
                        [row.name for row in family_rows(family.name)]))
            else:
                # #914: a composite cell type is mangled (#775) for the
                # field string and the `$vera.…` identifier alike, as the
                # host registration and the handler-body calls mangle it.
                for cell, wasm_t in self._state_types:
                    parts.extend(cell_lines(mangle_type_name(cell.family), wasm_t))

    @staticmethod
    def _assert_unique_func_names(wat: str) -> None:
        """Refuse a module that binds one function identifier twice (#1433).

        Run over the ASSEMBLED module — every definition and every function
        import, user code and generated code alike — because that is the
        whole set wasm-tools will bind, and nothing short of it is.  Two
        declarations of one name are refused at check (E184); this is the
        backstop behind that rule, because the failure it replaces was
        reached with ``check`` and ``verify`` both passing, and surfaced as
        ``duplicate func identifier`` against a symbol the author never
        wrote.

        It raises :class:`~vera.skip.CodegenInvariantError`, which
        ``_compile_program`` reports as E699: reaching here is a compiler bug
        rather than a property of the program — the posture `vera/skip.py`
        documents for codegen invariants.
        """
        seen: set[str] = set()
        for match in (*_WAT_FUNC_IMPORT_RE.finditer(wat),
                      *_WAT_FUNC_DEF_RE.finditer(wat)):
            name = match.group(1)
            if name in seen:
                raise CodegenInvariantError(
                    f"the module binds the function identifier ${name} "
                    f"twice, which WebAssembly refuses as a duplicate func "
                    f"identifier. Two declarations of one name in one "
                    f"namespace are refused at check (E184), so a module "
                    f"reaching here either bypassed the checker or has a "
                    f"declaration named after a symbol code generation also "
                    f"emits."
                )
            seen.add(name)

    def _assemble_module(self, functions: list[str]) -> str:
        """Assemble a complete WAT module from compiled functions."""
        parts: list[str] = ["(module"]

        # The host imports: every declaration is the registry's
        # (`vera.builtins`, #735), in the order its families list them.
        self._declare_host_imports(parts)

        # Exception tags for Exn<E>
        for type_name, wasm_t in self._exn_types:
            parts.append(
                f"  (tag $exn_{mangle_type_name(type_name)} (param {wasm_t}))"
            )

        # Memory (for string data and heap)
        if self._needs_memory or self.string_pool.has_strings():
            parts.append(
                f'  (memory (export "{runtime_export("memory")}") 1)')

        # Data section (string constants)
        for value, offset, _length in self.string_pool.entries():
            # Escape special characters for WAT string literals
            escaped = self._escape_wat_string(value)
            parts.append(f'  (data (i32.const {offset}) "{escaped}")')

        # GC infrastructure: globals, allocator, and collector
        if self._needs_alloc:
            data_end = self.string_pool.heap_offset
            gc_stack_base = data_end
            gc_stack_size = GC_STACK_SIZE
            gc_worklist_size = GC_WORKLIST_SIZE
            # #573: wrap-table region for host-handle ADT wrappers.
            # Sized for 4 096 simultaneously-live wrapper objects at
            # 16 bytes per entry (obj_ptr / kind / handle / reserved).
            # Sweep compacts in place, so the table grows with
            # *live* wrappers, not total allocations.  Programs that
            # don't use any wrap-table-backed type pay no memory
            # cost — `_needs_wrap_table` gates inclusion of both
            # this region and the corresponding sweep pass.
            #
            # It holds the values `vera.trap_registry.WRAP_TABLE_VALUES`
            # lists — `Decimal` values and pending async requests; `Map`
            # and `Set` values are plain heap objects since #706.
            gc_wraptable_size = GC_WRAPTABLE_SIZE
            wrap_enabled = self._needs_wrap_table
            wraptable_overhead = gc_wraptable_size if wrap_enabled else 0
            gc_wraptable_base = (
                data_end + gc_stack_size + gc_worklist_size
            )
            gc_heap_start = (
                data_end + gc_stack_size + gc_worklist_size
                + wraptable_overhead
            )
            # #1255: the heap starts ABOVE every value an inline i32 scalar
            # can hold, which is what makes a scalar that reaches the shadow
            # stack harmless — the mark phase's first guard is `val >=
            # $gc_heap_start + 4`, so a `@Byte` (0..255) or `@Bool` (0/1) is
            # rejected before alignment or header is ever read.  The
            # classification that decides which values are pushed resolves
            # aliases now (`is_gc_pointer_base`), so nothing SHOULD arrive
            # here needing that rejection; this keeps the property true by
            # construction rather than by the string pool's presence, which
            # is what it rested on when #1255 was filed.  The margin is
            # structural — `gc_stack_size + gc_worklist_size` is 80 KiB of
            # compile-time constant before `data_end` contributes anything —
            # so the guard can only fire if those constants are reworked,
            # which is exactly when the argument needs re-deriving.  A raise
            # rather than an assert: `python -O` must not strip it (ruff S).
            if gc_heap_start <= MAX_INLINE_I32_VALUE + 4:
                raise CodegenInvariantError(
                    f"GC heap starts at {gc_heap_start}, inside the inline "
                    f"i32 scalar range (0..{MAX_INLINE_I32_VALUE}): the "
                    "conservative mark phase could not distinguish a @Byte "
                    "or @Bool value on the shadow stack from a heap pointer"
                )
            # #1510: the mark phase's seed pushes one 4-byte worklist entry
            # per 4-byte shadow-stack root onto an empty worklist, and is the
            # one push with no dirty object to record a dropped push against
            # (`_emit_gc_collect`), so it must always fit.  It does while the
            # worklist is no smaller than the shadow stack; a raise for the
            # same reason as the guard above.
            if gc_worklist_size < gc_stack_size:
                raise CodegenInvariantError(
                    f"the GC worklist ({gc_worklist_size} bytes) is smaller "
                    f"than the shadow stack ({gc_stack_size} bytes): a "
                    "collection's seed could fill the worklist with roots, "
                    "and a root the seed dropped would be swept while live"
                )
            parts.append(
                f"  (global $heap_ptr (export \"{runtime_export('heap_ptr')}\") "
                f"(mut i32) (i32.const {gc_heap_start}))"
            )
            # #692: $gc_sp and $gc_stack_limit are exported so host
            # walkers (`write_html`, `write_json`, markdown serde) can
            # push intermediate WASM heap pointers onto the shadow
            # stack across allocations.  Without that, a Python-held
            # `arr_ptr` from `write_html` is invisible to the
            # conservative GC scan; if a sub-walk triggers
            # `$gc_collect` the block gets reclaimed and the next
            # write scribbles into freed memory → free-list
            # corruption → trap.  Same #570/#515/#593 bug class but
            # on the host side.  $gc_sp is (mut) — the host
            # advances it to push, resets it to pop.
            # $gc_stack_limit is immutable — the host reads it to
            # detect overflow before pushing.
            parts.append(
                f"  (global $gc_sp (export \"{runtime_export('gc_sp')}\") (mut i32) "
                f"(i32.const {gc_stack_base}))"
            )
            parts.append(
                f"  (global $gc_stack_base i32 "
                f"(i32.const {gc_stack_base}))"
            )
            gc_stack_limit = gc_stack_base + gc_stack_size
            parts.append(
                f"  (global $gc_stack_limit "
                f"(export \"{runtime_export('gc_stack_limit')}\") "
                f"i32 (i32.const {gc_stack_limit}))"
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
            # #1382: origin of the transient object-base bitmap, rebuilt
            # at the top of every collection (see ``_emit_gc_collect``
            # Phase 0).  It lives immediately above ``$heap_ptr`` — scratch
            # that the next ``$alloc`` bump is free to overwrite, because
            # the bitmap is only live for the duration of one collection.
            parts.append(
                "  (global $gc_bm_base (mut i32) (i32.const 0))"
            )
            # #1510: the mark phase's dirty range — the header of the lowest
            # object a full worklist dropped a child of, the word it dropped
            # at, and the header of the highest — and its resume point: the
            # header of the object the last walk stopped in, the word it
            # stopped at, and the header of the highest drop recorded below
            # that object since (`_emit_gc_collect`).  Module globals rather
            # than `$gc_collect` locals: only the collector's cold paths
            # touch them, and as locals they stayed live across the drain
            # loop and cost every collection 10-20% with nothing dropped.
            parts.extend(
                f"  (global ${name} (mut i32) (i32.const 0))"
                for name in ("gc_rs_lo", "gc_rs_off", "gc_rs_hi",
                             "gc_rs_stop", "gc_rs_stop_off", "gc_rs_below")
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
                    f'  (export "{runtime_export("register_wrapper")}" '
                    '(func $register_wrapper))'
                )
            parts.append(self._emit_gc_base_bitmap_helpers())
            parts.append(self._emit_gc_collect())

        # #1172: per-guarded-function termination-measure state.  Each
        # function with a `decreases` clause gets one i64 baseline global
        # per lexicographic component plus an activation flag; the entry
        # guard in `_compile_decreases_entry` checks and updates them,
        # and every exit restores what the activation saved.  Emitted
        # unconditionally of the GC machinery — a pure scalar-recursive
        # function is guarded without needing an allocator.
        for dec_fn, n_comps in sorted(self._dec_guard_fns.items()):
            for k in range(n_comps):
                parts.append(
                    f"  (global $dec_prev_{dec_fn}_{k} "
                    f"(mut i64) (i64.const 0))"
                )
            parts.append(
                f"  (global $dec_active_{dec_fn} "
                f"(mut i32) (i32.const 0))"
            )

        # Export $alloc when the heap allocator is compiled in: a host
        # import that allocates in the module's memory set the flag when it
        # was declared (its registry row's `needs_alloc`), and so does
        # anything else that allocates (e.g. String params need allocation
        # for CLI argument passing)
        if self._needs_alloc:
            parts.append(
                f'  (export "{runtime_export("alloc")}" (func $alloc))')

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

        # #773: generated structural-Eq helper functions ($eq_<type>, plus the
        # shared $eq_String content comparator).  Deduped by name across the
        # whole module; sorted for deterministic output.
        for _name, eq_wat in sorted(self._adt_eq_helpers.items()):
            parts.append(eq_wat)

        # #1172: structural-size helpers for ADT decreases measures
        # ($dec_size_<T>) — same dedupe-by-name/sorted discipline as the
        # Eq helpers above.
        for _name, size_wat in sorted(self._dec_rank_helpers.items()):
            if size_wat:
                parts.append(size_wat)

        # #924: generated recursive show/hash helper functions ($show_<type> /
        # $hash_<type>).  Deduped by name across the whole module; sorted for
        # deterministic output.
        for _name, sh_wat in sorted(self._show_hash_helpers.items()):
            parts.append(sh_wat)

        # #1676: the generated Map and Set functions, and the exports of the
        # ones a host builds or reads a map through.
        for _name, coll_wat in sorted(self._collection_helpers.items()):
            parts.append(coll_wat)
        for name in sorted(self._collection_exports):
            parts.append(f'  (export "{name}" (func ${name}))')

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

        Every way it can run out of heap — a request of 2 GiB or more, a
        ``memory.grow`` the host refuses, a heap that would pass the 2 GiB
        ceiling — signals ``heap_exhausted`` through ``vera.trap`` before
        trapping (#1479), so the runtime names the limit and the remedy
        instead of the generic ``unreachable``.
        """
        eager = flag_enabled("VERA_EAGER_GC")
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
            + heap_trap("      ")
            + "    end\n"
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
            + heap_trap("          ")
            + "        end\n"
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
            # Two-step overflow-safe form:
            # 1. Reject ``total >= 0x80000000`` outright (the
            #    single allocation is larger than the ceiling).
            # 2. Verify ``heap_ptr >= 0x80000000 - total`` via
            #    SUBTRACTION (not addition).  The ``i32.add`` form
            #    we used initially could wrap on overflow — e.g.
            #    ``heap_ptr=0xFFFFFFFF, total=10`` wraps to
            #    ``0x09``, which is ``< 0x80000000``, so the guard
            #    would silently pass and the heap would overflow
            #    past 2 GiB.  Upstream ``memory.grow`` makes the
            #    wraparound unreachable in practice but the
            #    algebraic gap is real and worth closing.  Step 1
            #    guarantees ``0x80000000 - total`` doesn't underflow
            #    so step 2 is well-defined.
            "    ;; Step 1: total < 2 GiB\n"
            "    local.get $total\n"
            "    i32.const 0x80000000\n"
            "    i32.ge_u\n"
            "    if\n"
            + heap_trap("      ")
            + "    end\n"
            "    ;; Step 2: heap_ptr < 0x80000000 - total\n"
            "    global.get $heap_ptr\n"
            "    i32.const 0x80000000\n"
            "    local.get $total\n"
            "    i32.sub\n"
            "    i32.ge_u\n"
            "    if\n"
            + heap_trap("      ")
            + "    end\n"
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
            "      ;; Slot-complete bound (#860, following #791): the\n"
            "      ;; store below writes FOUR bytes, so the check is on\n"
            "      ;; $gc_sp + 4, not on $gc_sp — a $gc_sp within four\n"
            "      ;; bytes of the limit passed `i32.ge_u` and then\n"
            "      ;; stored past the end of the shadow stack.\n"
            "      global.get $gc_sp\n"
            "      i32.const 4\n"
            "      i32.add\n"
            "      global.get $gc_stack_limit\n"
            "      i32.gt_u\n"
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

    def _emit_gc_base_bitmap_helpers(self) -> str:
        """Emit ``$gc_set_base`` / ``$gc_is_base`` for #1382.

        The conservative mark phase classifies a word as a heap pointer
        from two cheap tests — heap range and ``(val - $gc_heap_start) &
        7 == 4``.  Those are sound for *reads* (a false positive costs
        retention, nothing more) but the mark phase also **writes**: it
        ORs the mark bit into the word four bytes below the candidate.
        A false positive that lands in the interior or the tail padding
        of a live object therefore corrupts live data — observed as an
        ``Array<Int>`` element whose high word flipped from 0 to 1
        because a candidate's "header" read as 0 and ``0 | 1`` was
        stored over it.

        The fix is to make the *write* conditional on the candidate
        actually being an object base.  Phase 1 already walks every
        object along the exact ``align_up(size + 4, 8)`` chain that
        ``$alloc`` bumps by, so it knows every valid body address for
        free; it records them here, one bit per 8-byte granule, and both
        the Phase 2 shadow-stack seed and the Phase 2b transitive scan
        consult the bit before enqueueing (and therefore before any mark
        store).  Reads stay conservative; only the write is narrowed.

        Bit for body address ``p`` is granule ``(p - $gc_heap_start) >>
        3``, held in byte ``$gc_bm_base + (granule >> 3)`` at position
        ``granule & 7``.  Callers must range-check ``p`` first — both
        call sites do, inside the existing heap-range guards.
        """
        index = (
            "    local.get $p\n"
            "    global.get $gc_heap_start\n"
            "    i32.sub\n"
            "    i32.const 3\n"
            "    i32.shr_u\n"
            "    local.set $bi\n"
            "    global.get $gc_bm_base\n"
            "    local.get $bi\n"
            "    i32.const 3\n"
            "    i32.shr_u\n"
            "    i32.add\n"
        )
        return (
            "  (func $gc_set_base (param $p i32)\n"
            "    (local $bi i32)\n"
            "    (local $ba i32)\n"
            + index
            + "    local.set $ba\n"
            "    local.get $ba\n"
            "    local.get $ba\n"
            "    i32.load8_u\n"
            "    i32.const 1\n"
            "    local.get $bi\n"
            "    i32.const 7\n"
            "    i32.and\n"
            "    i32.shl\n"
            "    i32.or\n"
            "    i32.store8\n"
            "  )\n"
            "  (func $gc_is_base (param $p i32) (result i32)\n"
            "    (local $bi i32)\n"
            + index
            + "    i32.load8_u\n"
            "    i32.const 1\n"
            "    local.get $bi\n"
            "    i32.const 7\n"
            "    i32.and\n"
            "    i32.shl\n"
            "    i32.and\n"
            "    i32.const 0\n"
            "    i32.ne\n"
            "  )"
            + (self._emit_gc_assert_base()
               if flag_enabled("VERA_GC_CHECK_MARKS") else "")
        )

    def _emit_gc_assert_base(self) -> str:
        """Emit ``$gc_assert_base`` — the ``VERA_GC_CHECK_MARKS`` invariant.

        Traps unless ``$p`` is a real object body address, established the
        only way that does not itself depend on the bitmap: by walking the
        heap from ``$gc_heap_start`` along the same
        ``align_up(size + 4, 8)`` chain ``$alloc`` bumps by.  Deliberately
        base-independent, so the same assertion can be dropped into a
        pre-#1382 collector and will fire there — which is what makes it a
        red-first check rather than a restatement of the fix.  O(heap) per
        mark store: a debugging knob, never production.
        """
        return (
            "\n  (func $gc_assert_base (param $p i32)\n"
            "    (local $w i32)\n"
            "    global.get $gc_heap_start\n"
            "    local.set $w\n"
            "    block $ab_found\n"
            "    loop $ab_walk\n"
            "      local.get $w\n"
            "      global.get $heap_ptr\n"
            "      i32.ge_u\n"
            "      if\n"
            "        unreachable\n"
            "      end\n"
            "      local.get $w\n"
            "      i32.const 4\n"
            "      i32.add\n"
            "      local.get $p\n"
            "      i32.eq\n"
            "      br_if $ab_found\n"
            "      local.get $w\n"
            "      i32.load\n"
            "      i32.const 1\n"
            "      i32.shr_u\n"
            "      i32.const 11\n"
            "      i32.add\n"
            "      i32.const -8\n"
            "      i32.and\n"
            "      local.get $w\n"
            "      i32.add\n"
            "      local.set $w\n"
            "      br $ab_walk\n"
            "    end\n"
            "    end\n"
            "  )"
        )

    @staticmethod
    def _emit_gc_scan(done: str, drop: str, loop: str, indent: str) -> str:
        """The mark phase's scan of one object's words, as WAT text.

        Scans the payload of ``$obj_ptr`` (``$obj_size`` bytes) from word
        offset ``$scan_ptr`` and pushes every word that is an unmarked
        object base onto the worklist.  A push that finds the worklist full
        is dropped (#1510): the value stays unmarked, the scan stops — every
        later push would be dropped too — and the object is recorded as
        dirty from that word, the lowest dirty object's header in
        ``$gc_rs_lo`` with the word in ``$gc_rs_off``, the highest in
        ``$gc_rs_hi``; a drop below the object the last walk stopped in
        (``$gc_rs_stop``) also raises ``$gc_rs_below``, the highest drop
        recorded below it.  The loop leaves for the recording by a bare
        ``br_if`` to *drop*, so the recording stays out of the loop the
        collector spends its time in, and the range is held in module
        globals, which no register carries through that loop.  The Phase 2b
        drain and its rescan of the dirty range both scan through this,
        under labels of their own.
        """
        lines = (
            f"block {done}",
            f"block {drop}",
            f"loop {loop}",
            "  local.get $scan_ptr",
            "  local.get $obj_size",
            "  i32.ge_u",
            f"  br_if {done}",
            "  ;; Layer 1 (issue #515): defence-in-depth bound check.",
            "  ;; Never load from an address >= heap_ptr.  Cheap (a single",
            "  ;; ge_u) relative to the i32.load it guards.",
            "  local.get $obj_ptr",
            "  local.get $scan_ptr",
            "  i32.add",
            "  i32.const 4",
            "  i32.add",
            "  global.get $heap_ptr",
            "  i32.gt_u",
            f"  br_if {done}",
            "  ;; val = load(obj_ptr + scan_ptr)",
            "  local.get $obj_ptr",
            "  local.get $scan_ptr",
            "  i32.add",
            "  i32.load",
            "  local.set $val",
            "  ;; Valid heap pointer check",
            "  local.get $val",
            "  global.get $gc_heap_start",
            "  i32.const 4",
            "  i32.add",
            "  i32.ge_u",
            "  if",
            "    local.get $val",
            "    global.get $heap_ptr",
            "    i32.lt_u",
            "    if",
            "      local.get $val",
            "      global.get $gc_heap_start",
            "      i32.sub",
            "      i32.const 7",
            "      i32.and",
            "      i32.const 4",
            "      i32.eq",
            "      ;; Layer 2 (issues #515, #1382): and it must be a REAL",
            "      ;; object base.  The mark store writes through this",
            "      ;; candidate, so a false positive that merely looks",
            "      ;; aligned would corrupt whatever it points into.",
            "      local.get $val",
            "      call $gc_is_base",
            "      i32.and",
            "      if",
            "        ;; Not already marked? Push to worklist.",
            "        local.get $val",
            "        i32.const 4",
            "        i32.sub",
            "        i32.load",
            "        i32.const 1",
            "        i32.and",
            "        i32.eqz",
            "        if",
            "          ;; #1510: a full worklist drops the push, leaving",
            "          ;; $val unmarked and $scan_ptr at this word.",
            "          local.get $wl_ptr",
            "          local.get $wl_end",
            "          i32.ge_u",
            f"          br_if {drop}",
            "          local.get $wl_ptr",
            "          local.get $val",
            "          i32.store",
            "          local.get $wl_ptr",
            "          i32.const 4",
            "          i32.add",
            "          local.set $wl_ptr",
            "        end",
            "      end",
            "    end",
            "  end",
            "  local.get $scan_ptr",
            "  i32.const 4",
            "  i32.add",
            "  local.set $scan_ptr",
            f"  br {loop}",
            "end",
            "end",
            ";; Reached only from a dropped push: this object is dirty from",
            ";; word $scan_ptr on, so the rescan reaches the value dropped.",
            "local.get $obj_ptr",
            "i32.const 4",
            "i32.sub",
            "global.get $gc_rs_lo",
            "i32.lt_u",
            "if",
            "  local.get $obj_ptr",
            "  i32.const 4",
            "  i32.sub",
            "  global.set $gc_rs_lo",
            "  local.get $scan_ptr",
            "  global.set $gc_rs_off",
            "end",
            "local.get $obj_ptr",
            "i32.const 4",
            "i32.sub",
            "global.get $gc_rs_hi",
            "i32.gt_u",
            "if",
            "  local.get $obj_ptr",
            "  i32.const 4",
            "  i32.sub",
            "  global.set $gc_rs_hi",
            "end",
            ";; A drop below the object the last walk stopped in raises the",
            ";; highest such drop, where the next walk jumps to that object.",
            "local.get $obj_ptr",
            "i32.const 4",
            "i32.sub",
            "global.get $gc_rs_stop",
            "i32.lt_u",
            "if",
            "  local.get $obj_ptr",
            "  i32.const 4",
            "  i32.sub",
            "  global.get $gc_rs_below",
            "  i32.gt_u",
            "  if",
            "    local.get $obj_ptr",
            "    i32.const 4",
            "    i32.sub",
            "    global.set $gc_rs_below",
            "  end",
            "end",
            "end",
        )
        return "".join(f"{indent}{line}\n" for line in lines)

    def _emit_gc_collect(self) -> str:
        """Emit the $gc_collect function: mark-sweep garbage collector.

        Three phases (plus Phase 2c when the wrap table is enabled):
          1. Clear all mark bits in the heap.
          2. Mark from shadow-stack roots (iterative, conservative):
             seed the worklist from the roots, drain it, and — when a
             full worklist dropped a push (#1510) — rescan the dirty
             objects and drain again, until a drain drops nothing.
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
            "    (local $bm_bytes i32)\n"
            "    (local $bm_i i32)\n"
            "    (local $rs_end i32)\n"
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
            "    ;; === Phase 0 (#1382): reset the object-base bitmap ===\n"
            "    ;; Transient scratch immediately above $heap_ptr — one bit\n"
            "    ;; per 8-byte heap granule.  $heap_ptr cannot move during a\n"
            "    ;; collection (the only caller allocates after we return),\n"
            "    ;; so the region is stable here and free for the next bump\n"
            "    ;; to reuse afterwards.  Phase 1 fills it as it walks.\n"
            "    global.get $heap_ptr\n"
            "    global.set $gc_bm_base\n"
            "    global.get $heap_ptr\n"
            "    global.get $gc_heap_start\n"
            "    i32.sub\n"
            "    i32.const 6\n"
            "    i32.shr_u\n"
            "    i32.const 1\n"
            "    i32.add\n"
            "    local.set $bm_bytes\n"
            "    ;; Grow memory if the bitmap would run past the end.\n"
            "    global.get $gc_bm_base\n"
            "    local.get $bm_bytes\n"
            "    i32.add\n"
            "    memory.size\n"
            "    i32.const 16\n"
            "    i32.shl\n"
            "    i32.gt_u\n"
            "    if\n"
            "      global.get $gc_bm_base\n"
            "      local.get $bm_bytes\n"
            "      i32.add\n"
            "      memory.size\n"
            "      i32.const 16\n"
            "      i32.shl\n"
            "      i32.sub\n"
            "      i32.const 65535\n"
            "      i32.add\n"
            "      i32.const 16\n"
            "      i32.shr_u\n"
            "      memory.grow\n"
            "      i32.const -1\n"
            "      i32.eq\n"
            "      if\n"
            + heap_trap("        ")
            + "      end\n"
            "    end\n"
            "    i32.const 0\n"
            "    local.set $bm_i\n"
            "    block $bz_done\n"
            "    loop $bz_loop\n"
            "      local.get $bm_i\n"
            "      local.get $bm_bytes\n"
            "      i32.ge_u\n"
            "      br_if $bz_done\n"
            "      global.get $gc_bm_base\n"
            "      local.get $bm_i\n"
            "      i32.add\n"
            "      i32.const 0\n"
            "      i32.store8\n"
            "      local.get $bm_i\n"
            "      i32.const 1\n"
            "      i32.add\n"
            "      local.set $bm_i\n"
            "      br $bz_loop\n"
            "    end\n"
            "    end\n"
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
            "      ;; #1382: record body = ptr + 4 as a real object base.\n"
            "      local.get $ptr\n"
            "      i32.const 4\n"
            "      i32.add\n"
            "      call $gc_set_base\n"
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
            "      ;; tests/test_codegen_collections.py::TestWrapperHandleTagging578::\n"
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
            "          ;; Layer 2 (issues #515, #1382): and it must be a REAL\n"
            "          ;; object base.  The mark store writes through this\n"
            "          ;; candidate, so a false positive that merely looks\n"
            "          ;; aligned would corrupt whatever it points into.\n"
            "          local.get $val\n"
            "          call $gc_is_base\n"
            "          i32.and\n"
            "          if\n"
            "            ;; Push onto worklist.  #1510: the seed cannot\n"
            "            ;; overflow it — one entry per shadow-stack root,\n"
            "            ;; onto an empty worklist no smaller than the\n"
            "            ;; shadow stack (`_assemble_module` refuses a\n"
            "            ;; layout where it is) — so this push, unlike a\n"
            "            ;; child's in Phase 2b, needs no capacity test.\n"
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
            "    ;; === Phase 2b: Mark — drain, then rescan the drops ===\n"
            "    ;; #1510: a child push that finds the worklist full is\n"
            "    ;; dropped and the object being scanned recorded as dirty\n"
            "    ;; (`_emit_gc_scan`), so the dirty objects' headers lie in\n"
            "    ;; [$gc_rs_lo, $gc_rs_hi] along the allocation chain, the\n"
            "    ;; lowest dirty from word $gc_rs_off.  A round drains the\n"
            "    ;; worklist, then walks the dirty range, scanning each marked\n"
            "    ;; object again, which pushes the children it dropped.\n"
            "    ;; Marking is complete when a drain ends with nothing dirty.\n"
            "    ;; A walk starts on an empty worklist, so it either pushes\n"
            "    ;; nothing, and the next drain ends clean, or gives that\n"
            "    ;; drain an unmarked object to mark: the rounds end.\n"
            "    ;; A drop during a walk stops it there, and its object and\n"
            "    ;; word become the resume point, $gc_rs_stop from\n"
            "    ;; $gc_rs_stop_off: a walk scans that object from that word.\n"
            "    ;; A drop recorded below the resume object lowers the range's\n"
            "    ;; bottom but not the resume point, and raises $gc_rs_below.\n"
            "    ;; The invariant: below the resume object, the only dirty\n"
            "    ;; objects are drops recorded since the walk that set it\n"
            "    ;; stopped, all in [$gc_rs_lo, $gc_rs_below].  It holds at\n"
            "    ;; the stop, the walk's first drop: every dirty object below\n"
            "    ;; it lay in the walk's range, which the walk scanned up to\n"
            "    ;; the stop, jumping only a stretch the invariant left\n"
            "    ;; clean; and the recording keeps it for every drop since.\n"
            "    ;; So a walk jumps from past $gc_rs_below straight to the\n"
            "    ;; resume object.  A walk that stops below the resume object\n"
            "    ;; stops inside [$gc_rs_lo, $gc_rs_below] and keeps both;\n"
            "    ;; one that stops at or above it moves the resume point to\n"
            "    ;; its stop, with nothing below dirty; one that reaches its\n"
            "    ;; range's end leaves nothing pending and clears all three.\n"
            "    i32.const -1\n"
            "    global.set $gc_rs_lo\n"
            "    i32.const 0\n"
            "    global.set $gc_rs_hi\n"
            "    i32.const 0\n"
            "    global.set $gc_rs_stop\n"
            "    i32.const 0\n"
            "    global.set $gc_rs_stop_off\n"
            "    i32.const 0\n"
            "    global.set $gc_rs_below\n"
            "    block $mk_done\n"
            "    loop $mk_loop\n"
            "      block $m_done\n"
            "      loop $m_loop\n"
            "        ;; Pop from worklist\n"
            "        local.get $wl_ptr\n"
            "        local.get $wl_base\n"
            "        i32.le_u\n"
            "        br_if $m_done\n"
            "        local.get $wl_ptr\n"
            "        i32.const 4\n"
            "        i32.sub\n"
            "        local.set $wl_ptr\n"
            "        local.get $wl_ptr\n"
            "        i32.load\n"
            "        local.set $obj_ptr\n"
            "        ;; Load header\n"
            "        local.get $obj_ptr\n"
            "        i32.const 4\n"
            "        i32.sub\n"
            "        i32.load\n"
            "        local.set $header\n"
            "        ;; Compute obj_size early so we can sanity-check it.\n"
            "        local.get $header\n"
            "        i32.const 1\n"
            "        i32.shr_u\n"
            "        local.set $obj_size\n"
            "        ;; Layer 2 (issue #515): conservative-GC sanity check.\n"
            "        ;; The Phase 2 worklist push only guards on alignment\n"
            "        ;; and range, not on header validity.  A non-pointer i32\n"
            "        ;; in payload data can satisfy those guards, in which\n"
            "        ;; case #1382: the pre-#1382 guard here (skip when\n"
            "        ;;   obj_ptr + obj_size > heap_ptr) existed only to\n"
            "        ;;   stop a false-positive candidate's garbage header\n"
            "        ;;   from driving an out-of-bounds scan and a mark\n"
            "        ;;   store into a random payload word.  It caught only\n"
            "        ;;   the LARGE-size false positive; a candidate whose\n"
            "        ;;   header read as 0 passed it and corrupted live\n"
            "        ;;   data.  Candidates are now validated against the\n"
            "        ;;   object-base bitmap before they are ever enqueued,\n"
            "        ;;   so $obj_ptr is a real body address and $header a\n"
            "        ;;   real header: the bound holds by construction and\n"
            "        ;;   the partial guard is gone (one mechanism).\n"
            "        ;; Already marked? Skip.\n"
            "        local.get $header\n"
            "        i32.const 1\n"
            "        i32.and\n"
            "        if\n"
            "          br $m_loop\n"
            "        end\n"
            + (
                "        local.get $obj_ptr\n"
                "        call $gc_assert_base\n"
                if flag_enabled("VERA_GC_CHECK_MARKS")
                else ""
            )
            + "        ;; Set mark bit\n"
            "        local.get $obj_ptr\n"
            "        i32.const 4\n"
            "        i32.sub\n"
            "        local.get $header\n"
            "        i32.const 1\n"
            "        i32.or\n"
            "        i32.store\n"
            "        ;; Conservative scan: check every i32-aligned word\n"
            "        i32.const 0\n"
            "        local.set $scan_ptr\n"
            + self._emit_gc_scan("$sc_done", "$sc_drop", "$sc_loop",
                                 "        ")
            + "        br $m_loop\n"
            "      end\n"
            "      end\n"
            "      ;; The worklist is empty.  Nothing dirty: marking is done.\n"
            "      global.get $gc_rs_lo\n"
            "      global.get $gc_rs_hi\n"
            "      i32.gt_u\n"
            "      br_if $mk_done\n"
            "      ;; Walk the dirty range, the first object from its\n"
            "      ;; dropped word, with the range emptied for this walk's\n"
            "      ;; own drops.\n"
            "      global.get $gc_rs_lo\n"
            "      local.set $ptr\n"
            "      global.get $gc_rs_hi\n"
            "      local.set $rs_end\n"
            "      global.get $gc_rs_off\n"
            "      local.set $scan_ptr\n"
            "      i32.const -1\n"
            "      global.set $gc_rs_lo\n"
            "      i32.const 0\n"
            "      global.set $gc_rs_hi\n"
            "      block $rw_done\n"
            "      loop $rw_loop\n"
            "        ;; Past its range's end the walk is complete: nothing it\n"
            "        ;; was given is pending, so no object resumes.\n"
            "        local.get $ptr\n"
            "        local.get $rs_end\n"
            "        i32.gt_u\n"
            "        if\n"
            "          i32.const 0\n"
            "          global.set $gc_rs_stop\n"
            "          i32.const 0\n"
            "          global.set $gc_rs_stop_off\n"
            "          i32.const 0\n"
            "          global.set $gc_rs_below\n"
            "          br $rw_done\n"
            "        end\n"
            "        local.get $ptr\n"
            "        i32.load\n"
            "        local.set $header\n"
            "        ;; Only a marked object can hold a dropped child.\n"
            "        local.get $header\n"
            "        i32.const 1\n"
            "        i32.and\n"
            "        if\n"
            "          local.get $ptr\n"
            "          i32.const 4\n"
            "          i32.add\n"
            "          local.set $obj_ptr\n"
            "          local.get $header\n"
            "          i32.const 1\n"
            "          i32.shr_u\n"
            "          local.set $obj_size\n"
            "          ;; The resume object is scanned from its word.\n"
            "          local.get $ptr\n"
            "          global.get $gc_rs_stop\n"
            "          i32.eq\n"
            "          if\n"
            "            global.get $gc_rs_stop_off\n"
            "            local.set $scan_ptr\n"
            "          end\n"
            + self._emit_gc_scan("$rs_scan_done", "$rs_scan_drop",
                                 "$rs_scan_loop", "          ")
            + "          ;; A dropped push ends the walk here, the rest of\n"
            "          ;; the range dirty for the next.  A stop at or above\n"
            "          ;; the resume object becomes the resume point, with\n"
            "          ;; nothing below it dirty; a stop below it, inside\n"
            "          ;; [$gc_rs_lo, $gc_rs_below], keeps it.\n"
            "          global.get $gc_rs_lo\n"
            "          global.get $gc_rs_hi\n"
            "          i32.le_u\n"
            "          if\n"
            "            local.get $ptr\n"
            "            global.get $gc_rs_stop\n"
            "            i32.ge_u\n"
            "            if\n"
            "              local.get $ptr\n"
            "              global.set $gc_rs_stop\n"
            "              local.get $scan_ptr\n"
            "              global.set $gc_rs_stop_off\n"
            "              i32.const 0\n"
            "              global.set $gc_rs_below\n"
            "            end\n"
            "            local.get $rs_end\n"
            "            global.set $gc_rs_hi\n"
            "            br $rw_done\n"
            "          end\n"
            "        end\n"
            "        i32.const 0\n"
            "        local.set $scan_ptr\n"
            "        ;; Advance: ptr += align_up(size + 4, 8)\n"
            "        local.get $header\n"
            "        i32.const 1\n"
            "        i32.shr_u\n"
            "        i32.const 11\n"
            "        i32.add\n"
            "        i32.const -8\n"
            "        i32.and\n"
            "        local.get $ptr\n"
            "        i32.add\n"
            "        local.set $ptr\n"
            "        ;; Past the highest drop below the resume object nothing\n"
            "        ;; up to that object is dirty: jump to it.  The test for\n"
            "        ;; the resume object comes first, as above it, where a\n"
            "        ;; walk spends its time, nothing more is tested.\n"
            "        local.get $ptr\n"
            "        global.get $gc_rs_stop\n"
            "        i32.lt_u\n"
            "        if\n"
            "          local.get $ptr\n"
            "          global.get $gc_rs_below\n"
            "          i32.gt_u\n"
            "          if\n"
            "            global.get $gc_rs_stop\n"
            "            local.set $ptr\n"
            "          end\n"
            "        end\n"
            "        br $rw_loop\n"
            "      end\n"
            "      end\n"
            "      br $mk_loop\n"
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
