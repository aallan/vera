"""Mixin for closure lifting.

Compiles anonymous functions (closures) created during body compilation
to module-level WASM functions with explicit environment parameters.
"""

from __future__ import annotations

from collections import deque

from vera import ast
from vera.codegen.memory import ConstructorLayout, _align_up
from vera.skip import CodegenInvariantError, CodegenSkip
from vera.wasm import WasmContext, WasmSlotEnv
from vera.wasm.helpers import _is_host_handle_type, gc_shadow_push


class ClosureLiftingMixin:
    """Methods for lifting closures to module-level functions."""

    def _lift_pending_closures(self, ctx: WasmContext) -> bool:
        """Lift all anonymous functions created during body compilation.

        Each pending closure is compiled to a module-level WASM function
        and added to the function table.

        **Worklist pattern (#514).**  ``_compile_lifted_closure`` creates
        a fresh ``WasmContext`` to translate the closure body.  Any
        ``fn { ... }`` discovered *inside* that body registers on the
        new context's ``_pending_closures`` list — never on ``ctx`` here.
        Pre-#514 this list was thrown away when the inner ctx went out of
        scope, so nested closures (e.g. ``array_map(rows, fn(row) {
        array_map(cols, fn(col) { ... }) })``) emitted only the outer
        function and the inner's call_indirect targeted a missing table
        entry.  The worklist below collects each lift's inner-pending
        list and feeds it back, lifting to arbitrary depth.

        Returns ``True`` if **any** closure body in the worklist
        failed to compile (``_compile_lifted_closure`` returned
        ``None``).  The caller (``_compile_fn``) uses this to drop
        the enclosing top-level function rather than emitting a
        module with a ``call_indirect`` to a missing function-table
        entry — closes #636.  Pre-this-fix the failed closure was
        silently dropped from the table while the parent fn's WAT
        (containing the now-dangling ``call_indirect``) was still
        emitted, producing a WASM-validation trap with no
        source-located parent-fn diagnostic.
        """
        # ``deque`` (rather than a plain list) because ``popleft`` is
        # O(1) where ``list.pop(0)`` would shift every remaining entry.
        # Closure worklists are typically tiny in practice, but the
        # deque is the right idiom for FIFO and removes the need to
        # reason about list-pop costs as the depth of nesting grows.
        worklist: deque[
            tuple[ast.AnonFn, list[tuple[str, int, str]], int]
        ] = deque(ctx._pending_closures)
        # Snapshot `_next_closure_id` BEFORE this fn's worklist so we
        # can recycle the consumed range on failure.  closure_id is
        # module-monotonic and is stored as `func_table_idx` in each
        # closure struct's body emit — it must equal the closure's
        # eventual position in `_closure_table`.  When this fn's
        # worklist fails, the parent fn is dropped (#636) and its
        # closure structs aren't emitted, so the consumed closure_ids
        # are observably free; recycling them keeps the next fn's
        # closure_id ↔ table_index correspondence intact.
        prev_next_closure_id = self._next_closure_id
        # Sync forward from the ctx so the worklist sees the correct
        # current id counter; we'll restore on failure.
        self._next_closure_id = ctx._next_closure_id
        for sig_content, sig_name in ctx._closure_sigs.items():
            if sig_content not in self._closure_sigs:
                self._closure_sigs[sig_content] = sig_name

        # Accumulate successful lifts in local buffers; commit to
        # module-level state only if the entire worklist succeeds.
        # If any closure body fails, the parent fn will be dropped
        # (#636) and these would be orphan dead code in the output
        # module — but more critically, they'd shift table indices
        # for *subsequent* top-level fns' closures, breaking the
        # closure_id ↔ table_index correspondence for the rest of
        # the module (closure_id is a monotonic module-wide counter
        # while table position is determined by appending order in
        # `_closure_table`; a gap in successful lifts within one
        # fn's worklist desyncs the two for everything that follows).
        # Snapshot + commit-on-success preserves the invariant.
        new_closure_fns_wat: list[str] = []
        new_closure_table: list[str] = []
        new_source_map: list[tuple[str, tuple[str, int, int]]] = []
        new_sigs: list[tuple[str, str]] = []
        any_failed = False
        while worklist:
            anon_fn, captures, closure_id = worklist.popleft()
            inner_pending: list[tuple[ast.AnonFn, list[tuple[str, int, str]], int]] = []
            lifted_wat = self._compile_lifted_closure(
                closure_id, anon_fn, captures,
                collect_pending=inner_pending,
            )
            if lifted_wat is None:
                # Closure body failed — diagnostics already emitted by
                # `_compile_lifted_closure`'s harvest.  Record the
                # failure so the caller can drop the enclosing fn (#636).
                any_failed = True
                continue
            new_closure_fns_wat.append(lifted_wat)
            new_closure_table.append(f"$anon_{closure_id}")

            # #516 Stage 2 — record source location for trap mapping.
            # The lifted WAT name is `$anon_N`; trap frames will see
            # `anon_N` (no leading `$`) in func_name.  Use the source
            # span of the original `fn(...) { ... }` expression so a
            # trap inside a closure points back to the syntactic
            # `fn` site, not to the synthetic top-level wrapper.
            if anon_fn.span is not None:
                new_source_map.append((
                    f"anon_{closure_id}",
                    (
                        self.file or "<unknown>",
                        anon_fn.span.line,
                        anon_fn.span.end_line,
                    ),
                ))

            # Register the closure signature for call_indirect
            param_wasm: list[str] = ["i32"]  # env param
            for p in anon_fn.params:
                pwt = self._type_expr_to_wasm_type(p)
                if pwt == "i32_pair":  # pragma: no cover — String/Array closure params
                    param_wasm.extend(["i32", "i32"])
                elif pwt and pwt != "unsupported":
                    param_wasm.append(pwt)
            ret_wt = self._type_expr_to_wasm_type(anon_fn.return_type)
            param_part = " ".join(
                f"(param {wt})" for wt in param_wasm
            )
            if ret_wt == "i32_pair":
                result_part = " (result i32 i32)"
            elif ret_wt:
                result_part = f" (result {ret_wt})"
            else:
                result_part = ""  # pragma: no cover — Unit closure returns
            sig_content = f"{param_part}{result_part}"
            if sig_content not in self._closure_sigs:
                # Pre-compute the index outside the f-string so the
                # whole expression fits on one line — Python 3.11
                # doesn't support multi-line f-string interpolations
                # (only 3.12+ does).
                sig_idx = len(self._closure_sigs) + len(new_sigs)
                sig_name = f"$closure_sig_{sig_idx}"
                new_sigs.append((sig_content, sig_name))

            # Bubble up nested closures + any new sigs / IDs the
            # inner ctx registered while translating this body.
            worklist.extend(inner_pending)

        # Commit-on-success: only extend module-level state if every
        # closure in the worklist succeeded.  On failure, the parent
        # fn is dropped (#636) and these locals are discarded along
        # with the would-be orphans; `_next_closure_id` rolls back so
        # subsequent fns recycle the consumed range.
        if any_failed:
            self._next_closure_id = prev_next_closure_id
        else:
            self._closure_fns_wat.extend(new_closure_fns_wat)
            self._closure_table.extend(new_closure_table)
            for fn_name, span_info in new_source_map:
                self._fn_source_map[fn_name] = span_info
            for sig_content, sig_name in new_sigs:
                if sig_content not in self._closure_sigs:
                    self._closure_sigs[sig_content] = sig_name
            if new_closure_fns_wat:
                self._needs_table = True
                self._needs_alloc = True
                self._needs_memory = True

        return any_failed

    def _compile_lifted_closure(
        self,
        closure_id: int,
        anon_fn: ast.AnonFn,
        captures: list[tuple[str, int, str]],
        collect_pending: (
            list[tuple[ast.AnonFn, list[tuple[str, int, str]], int]]
            | None
        ) = None,
    ) -> str | None:
        """Compile an anonymous function to a module-level WASM function.

        The lifted function signature:
          (func $anon_N (param $env i32) (param ...) (result ...))

        The first parameter is the closure environment pointer.
        Captured values are loaded from the environment into locals.

        ``collect_pending`` is the worklist hook used by
        ``_lift_pending_closures`` to bubble up nested closures (#514).
        Translating this body in a fresh ``WasmContext`` may register
        more closures on that inner ctx; without this hook they would be
        dropped on the floor when the inner ctx goes out of scope.
        """
        # Flatten ADT layouts for context
        ctor_layouts: dict[str, ConstructorLayout] = {}
        ctor_to_adt: dict[str, str] = {}
        for adt_name, layouts in self._adt_layouts.items():
            ctor_layouts.update(layouts)
            for ctor_name in layouts:
                ctor_to_adt[ctor_name] = adt_name

        ctx = WasmContext(
            self.string_pool,
            ctor_layouts=ctor_layouts,
            adt_type_names=set(self._adt_layouts.keys()),
            ctor_to_adt=ctor_to_adt,
            ctor_adt_tp_indices=getattr(self, "_ctor_adt_tp_indices", None),
            adt_tp_counts=getattr(self, "_adt_tp_counts", None),
        )
        # #514: share the module-level sig dict and closure-ID counter
        # with the inner ctx so that any new sigs / IDs it registers
        # get module-unique names (avoids ``$closure_sig_0`` /
        # ``$anon_0`` collisions when nested closures are lifted).
        # Sigs are by-reference: writes inside the inner ctx land
        # directly in the module-level dict, no merge needed.
        ctx._closure_sigs = self._closure_sigs
        ctx._next_closure_id = self._next_closure_id
        fn_ret_types: dict[str, str | None] = {}
        for fn_name, (_, ret_wt) in self._fn_sigs.items():
            if ret_wt != "unsupported":
                fn_ret_types[fn_name] = ret_wt
        ctx.set_fn_ret_types(fn_ret_types)
        # #614: closure body may contain `fn_call(...)[i]` patterns
        # whose element-type inference needs the full return TypeExpr,
        # not just the WAT type — same propagation as the per-function
        # ctx in `functions.py`.
        ctx.set_fn_ret_type_exprs(self._fn_ret_type_exprs)
        # #798: resolved-type side-table for the integer-overflow guard's
        # Int/Nat operand classifier, inside closure bodies too.
        ctx.set_expr_semantic_types(self._expr_semantic_types)
        # #747: per-parameter concrete-@Nat flags for the call-site
        # runtime narrowing guard inside closure bodies too.
        ctx.set_fn_nat_params(self._fn_nat_params)
        # #813: per-parameter concrete-@Int flags for the call-site
        # runtime @Nat -> @Int widening guard inside closure bodies too.
        ctx.set_fn_int_params(self._fn_int_params)
        ctx.set_type_aliases(self._type_aliases)
        ctx.set_type_alias_params(self._type_alias_params)
        env = WasmSlotEnv()

        # Parameter 0: $env (i32 — closure environment pointer)
        env_idx = ctx.alloc_param()
        param_parts = ["(param $env i32)"]

        # Allocate ALL function parameters BEFORE any locals.
        # WASM requires params to be contiguous at indices 0..N-1,
        # with locals following at N, N+1, etc.
        param_info: list[tuple[int, ast.TypeExpr, int]] = []
        gc_pointer_params: list[int] = [env_idx]  # env is always a pointer
        for i, param_te in enumerate(anon_fn.params):
            wt = self._type_expr_to_wasm_type(param_te)
            if wt is None:  # pragma: no cover — Unit closure param
                continue  # Unit param, skip
            if wt == "unsupported":  # pragma: no cover — defensive
                return None
            if wt == "i32_pair":
                # String/Array params need two consecutive i32 slots (ptr, len).
                # The pair convention uses ptr_idx and ptr_idx+1 implicitly, so
                # env.push(type_name, ptr_idx) is sufficient for slot resolution.
                ptr_idx = ctx.alloc_param()
                ctx.alloc_param()  # len slot — consecutive with ptr_idx
                param_parts.append(f"(param $p{i}_ptr i32)")
                param_parts.append(f"(param $p{i}_len i32)")
                param_info.append((i, param_te, ptr_idx))
                gc_pointer_params.append(ptr_idx)
            else:
                local_idx = ctx.alloc_param()
                param_parts.append(f"(param $p{i} {wt})")
                param_info.append((i, param_te, local_idx))
                # Track pointer params for GC.  #347: opaque host
                # handles (Map / Set / Decimal) are i32 indices into
                # Python-side stores, not Vera-heap pointers — exclude
                # from rooting (see `_is_host_handle_type` for full
                # rationale).
                type_name = self._type_expr_to_slot_name(param_te)
                if (
                    wt == "i32"
                    and type_name not in ("Bool", "Byte", None)
                    and not _is_host_handle_type(type_name)
                ):
                    gc_pointer_params.append(local_idx)

        # Compute capture layout (must match _translate_anon_fn).
        # Pair-type captures (#535) take 8 bytes: ptr (i32) + len (i32),
        # two consecutive 4-byte fields.  The matching emit in
        # `_translate_anon_fn` writes both halves; we read both halves
        # here into two consecutive i32 locals so the closure body can
        # resolve the pair as if it were a parameter or let-binding.
        cap_offsets: list[tuple[int, str]] = []
        offset = 4  # skip func_table_idx
        for _tname, _cidx, cap_wt in captures:
            if cap_wt == "i32_pair":
                offset = _align_up(offset, 4)
                cap_offsets.append((offset, cap_wt))
                offset += 8
            elif cap_wt in ("i64", "f64"):
                offset = _align_up(offset, 8)
                cap_offsets.append((offset, cap_wt))
                offset += 8
            else:  # i32
                offset = _align_up(offset, 4)
                cap_offsets.append((offset, cap_wt))
                offset += 4

        # Load captured values from env into locals (allocated AFTER params)
        cap_locals: list[tuple[str, int]] = []  # (type_name, ptr_or_only_local)
        cap_local_kinds: list[str] = []  # parallel: cap_wt for each entry
        load_instrs: list[str] = []
        for i, (tname, _cidx, cap_wt) in enumerate(captures):
            cap_offset, _ = cap_offsets[i]
            if cap_wt == "i32_pair":
                # Allocate two consecutive i32 locals (ptr, len).  The
                # SlotEnv convention pushes only `ptr_idx`; the body
                # reads `local.get ptr_idx` for the ptr and
                # `local.get ptr_idx + 1` for the len, matching the
                # let-binding and parameter conventions.
                ptr_local = ctx.alloc_local("i32")
                len_local = ctx.alloc_local("i32")
                # Sanity: the two locals must be consecutive.  Both
                # `alloc_local("i32")` calls go to the same i32 pool,
                # so consecutive allocation is guaranteed by the
                # WasmContext implementation.  An explicit raise (vs.
                # `assert`) so the check survives `python -O`
                # (ruff S101).
                if len_local != ptr_local + 1:  # pragma: no cover
                    raise RuntimeError(
                        f"pair capture locals must be consecutive: "
                        f"ptr={ptr_local} len={len_local}"
                    )
                load_instrs.append(f"local.get {env_idx}")
                load_instrs.append(f"i32.load offset={cap_offset}")
                load_instrs.append(f"local.set {ptr_local}")
                load_instrs.append(f"local.get {env_idx}")
                load_instrs.append(f"i32.load offset={cap_offset + 4}")
                load_instrs.append(f"local.set {len_local}")
                cap_locals.append((tname, ptr_local))
                cap_local_kinds.append("i32_pair")
            else:
                cap_local = ctx.alloc_local(cap_wt)
                load_op = (
                    "i64.load" if cap_wt == "i64"
                    else "f64.load" if cap_wt == "f64"
                    else "i32.load"
                )
                load_instrs.append(f"local.get {env_idx}")
                load_instrs.append(f"{load_op} offset={cap_offset}")
                load_instrs.append(f"local.set {cap_local}")
                cap_locals.append((tname, cap_local))
                cap_local_kinds.append(cap_wt)

        # Build slot environment: captures first (outer scope, higher
        # De Bruijn indices), then function params on top (most recent).
        for tname, local_idx in cap_locals:
            env = env.push(tname, local_idx)
        for _i, param_te, local_idx in param_info:
            type_name = self._type_expr_to_slot_name(param_te)
            if type_name:
                env = env.push(type_name, local_idx)

        # Return type
        ret_wt = self._type_expr_to_wasm_type(anon_fn.return_type)
        if ret_wt == "unsupported":  # pragma: no cover — defensive
            return None
        if ret_wt == "i32_pair":
            result_part = " (result i32 i32)"
        elif ret_wt:
            result_part = f" (result {ret_wt})"
        else:
            result_part = ""  # pragma: no cover — Unit closure return

        # Compile the body.  Three failure modes are handled:
        #   1. CodegenSkip — translator hit unsupported shape (#626 L3)
        #   2. CodegenInvariantError — codegen bug (#626 L3)
        #   3. body_instrs is None — legacy silent-skip return
        # See the parallel block in vera/codegen/functions.py::_compile_fn
        # for the matching catch in the non-closure path.
        try:
            body_instrs = ctx.translate_block(anon_fn.body, env)
        except CodegenSkip as skip:
            # Closure-body skips emit their own structured [E602]
            # pointing at the unsupported node, then return None so
            # the parent function's _lift_pending_closures path
            # (vera/codegen/closures.py::_lift_pending_closures, the
            # Layer 2 commit-on-success site from #636) drops the
            # enclosing fn with its own dropped-parent [E602].
            self._harvest_interp_inference_failures(ctx)
            self._warning(
                skip.node if getattr(skip.node, "span", None) else anon_fn,
                f"Closure body contains unsupported "
                f"{type(skip.node).__name__}: {skip.reason} — "
                f"closure skipped.",
                rationale="The WASM backend does not yet support all "
                "Vera expression types. The enclosing function will "
                "also be dropped to avoid a missing function-table "
                "entry.",
                error_code="E602",
            )
            return None
        except CodegenInvariantError as inv:  # pragma: no cover — no production code raises CodegenInvariantError yet; the handler is the catch-side contract for future raises tracked in #657 (Track 2: INVARIANT_DEFENSIVE conversions).
            # Closure-body invariant violation — codegen bug.
            # Surfaced as [E699] at severity="error" so `vera compile`
            # exits non-zero.  Symmetric with the parent-boundary
            # handler in `vera/codegen/functions.py::_compile_fn`.
            #
            # Harvest interpolation failures before the [E699] for the
            # same reason the CodegenSkip handler above does — symmetry
            # insurance against future raise sites that fire mid-
            # interpolation-translation.
            self._harvest_interp_inference_failures(ctx)
            self._error(
                inv.node if inv.node is not None else anon_fn,
                f"Internal compiler error in closure body: {inv.msg}",
                rationale="This is a codegen invariant violation. "
                "Please file a bug report with the offending program.",
                error_code="E699",
            )
            return None

        if body_instrs is None:
            # #630 Tier 2 — closure-body parallel of the harvest in
            # `_compile_fn` (functions.py).  Without this, an
            # interpolation segment in a closure body whose Vera type
            # couldn't be inferred populated `ctx._interp_inference_failures`
            # but the failures were silently dropped on the closure-
            # path return-None — the closure_id was still registered
            # at the call site, so `call_indirect` referenced a missing
            # function-table entry and WASM validation rejected the
            # module with no source-located diagnostic.  Same
            # silent-drop shape that #614/#615 fixed for translation
            # failures; this closes the parallel for the post-#630
            # interpolation-failure path.  (silent-failure-hunter
            # finding C1 on PR #631.)  Pre-this-fix the line below
            # carried a `# pragma: no cover — defensive` claim that
            # was empirically disproved as soon as #630's Tier 2
            # added a non-defensive None-return path through
            # `_translate_interpolated_string`.
            self._harvest_interp_inference_failures(ctx)
            return None

        # Propagate host-import tracking from closure ctx to module level
        self._map_ops_used.update(ctx._map_ops_used)
        self._map_imports.update(ctx._map_imports)
        self._set_ops_used.update(ctx._set_ops_used)
        self._set_imports.update(ctx._set_imports)
        self._decimal_ops_used.update(ctx._decimal_ops_used)
        self._decimal_imports.update(ctx._decimal_imports)
        self._json_ops_used.update(ctx._json_ops_used)
        self._html_ops_used.update(ctx._html_ops_used)

        # Build GC prologue/epilogue (only when closure body allocates).
        # Two-phase prologue: ``gc_prologue`` runs before ``load_instrs``
        # (saves the GC sp and roots pointer-typed parameters, which are
        # already populated by WASM's call ABI); ``gc_capture_pushes``
        # runs *after* ``load_instrs`` (CodeRabbit on PR #569 — captures
        # are still 0 in the prologue because the env-loads haven't run
        # yet, so ``gc_shadow_push`` would write zero to the shadow
        # stack and any captured heap pointer reachable only through
        # the closure could be GC'd while in use).  Splitting the
        # prologue lets us push capture roots once the loads have
        # populated their locals.
        gc_prologue: list[str] = []
        gc_capture_pushes: list[str] = []
        gc_epilogue: list[str] = []

        # Determine if the return type is a heap pointer.  Computed
        # unconditionally — not just inside ``if ctx.needs_alloc:`` —
        # because ``_translate_array_map`` and ``_translate_array_mapi``
        # always emit a per-iteration ``gc_sp -= 4`` pop after each
        # ``call_indirect`` when the element type is heap-pointer-like
        # (the ``b_needs_unwind`` flag).  That pop assumes the callee
        # pushed a return-value root.  Pre-#593 the push was gated on
        # ``ctx.needs_alloc``: a closure body like
        # ``fn(@Bool -> @String) { render_cell(@Bool.0) }`` (where
        # ``render_cell`` returns String literals from the data segment,
        # so the closure itself doesn't allocate) emitted no push, but
        # the array_map loop popped anyway — dropping ``$gc_sp`` BELOW
        # the caller's prologue baseline and corrupting earlier roots.
        # Manifested as silent string corruption (Conway's Life rendering
        # — the original #593 symptom) or ``call_indirect`` table-OOB at
        # smaller scales.  Fix: emit the return-value push even when
        # ``needs_alloc=False`` so the array_map pop is always balanced.
        ret_is_pointer = False
        if ret_wt == "i32":
            ret_type_name = self._type_expr_to_slot_name(
                anon_fn.return_type,
            )
            if (
                ret_type_name not in ("Bool", "Byte", None)
                and not _is_host_handle_type(ret_type_name)
            ):
                # #347: opaque host handles aren't Vera-heap pointers;
                # same exclusion as param/capture cases.
                ret_is_pointer = True
        elif ret_wt == "i32_pair":
            ret_is_pointer = True

        if ctx.needs_alloc:
            gc_sp_save = ctx.alloc_local("i32")
            gc_prologue.append("global.get $gc_sp")
            gc_prologue.append(f"local.set {gc_sp_save}")
            for pidx in gc_pointer_params:
                gc_prologue.extend(gc_shadow_push(pidx))
            # Capture roots: pair captures (#535) have their ptr field
            # at ``cap_local`` and len at ``cap_local + 1``; we root the
            # ptr but not the len (len is an i32 byte count, never a
            # heap pointer).  Emitted into ``gc_capture_pushes`` so
            # they run after the env-loads have populated the locals.
            for (tname, cap_local), kind in zip(cap_locals, cap_local_kinds):
                if kind == "i32_pair":
                    gc_capture_pushes.extend(gc_shadow_push(cap_local))
                elif (
                    kind == "i32"
                    and tname not in ("Bool", "Byte")
                    and not _is_host_handle_type(tname)
                ):
                    # #347: same exclusion as the param case above —
                    # opaque host handles are i32 indices, not Vera-
                    # heap pointers.
                    gc_capture_pushes.extend(gc_shadow_push(cap_local))

            if ret_wt == "i32_pair":
                gc_ret_ptr = ctx.alloc_local("i32")
                gc_ret_len = ctx.alloc_local("i32")
                gc_epilogue.append(f"local.set {gc_ret_len}")
                gc_epilogue.append(f"local.set {gc_ret_ptr}")
                gc_epilogue.append(f"local.get {gc_sp_save}")
                gc_epilogue.append("global.set $gc_sp")
                if ret_is_pointer:
                    gc_epilogue.extend(gc_shadow_push(gc_ret_ptr))
                gc_epilogue.append(f"local.get {gc_ret_ptr}")
                gc_epilogue.append(f"local.get {gc_ret_len}")
            elif ret_wt is not None:
                gc_ret = ctx.alloc_local(ret_wt)
                gc_epilogue.append(f"local.set {gc_ret}")
                gc_epilogue.append(f"local.get {gc_sp_save}")
                gc_epilogue.append("global.set $gc_sp")
                if ret_is_pointer:
                    gc_epilogue.extend(gc_shadow_push(gc_ret))
                gc_epilogue.append(f"local.get {gc_ret}")
            else:  # pragma: no cover — Unit closure return with allocation
                gc_epilogue.append(f"local.get {gc_sp_save}")
                gc_epilogue.append("global.set $gc_sp")
        elif ret_is_pointer:
            # Non-allocating body, heap-pointer return: emit only the
            # return-value root push (no ``gc_sp`` save/restore — the
            # body has no pushes to clean up).  Balances the caller's
            # ``b_needs_unwind`` pop.  See the comment block above.
            if ret_wt == "i32_pair":
                gc_ret_ptr = ctx.alloc_local("i32")
                gc_ret_len = ctx.alloc_local("i32")
                gc_epilogue.append(f"local.set {gc_ret_len}")
                gc_epilogue.append(f"local.set {gc_ret_ptr}")
                gc_epilogue.extend(gc_shadow_push(gc_ret_ptr))
                gc_epilogue.append(f"local.get {gc_ret_ptr}")
                gc_epilogue.append(f"local.get {gc_ret_len}")
            else:  # ret_wt == "i32" ADT
                gc_ret = ctx.alloc_local("i32")
                gc_epilogue.append(f"local.set {gc_ret}")
                gc_epilogue.extend(gc_shadow_push(gc_ret))
                gc_epilogue.append(f"local.get {gc_ret}")

        # Assemble the lifted function WAT (not exported)
        fn_name = f"$anon_{closure_id}"
        header = f"  (func {fn_name}"
        if param_parts:
            header += " " + " ".join(param_parts)
        header += result_part

        lines = [header]
        for local_decl in ctx.extra_locals_wat():
            lines.append(f"    {local_decl}")
        for instr in gc_prologue:
            lines.append(f"    {instr}")
        for instr in load_instrs:
            lines.append(f"    {instr}")
        # Capture roots are pushed AFTER load_instrs so the locals
        # contain the loaded ptr (not the default 0) when shadow_push
        # snapshots their value — see the gc_prologue/gc_capture_pushes
        # split above for the rationale.
        for instr in gc_capture_pushes:
            lines.append(f"    {instr}")
        for instr in body_instrs:
            lines.append(f"    {instr}")
        for instr in gc_epilogue:
            lines.append(f"    {instr}")
        lines.append("  )")

        # #514: bubble inner-ctx state back to the worklist.
        # ``_closure_sigs`` is the module-level dict (shared by reference
        # at ctx-construction above), so new sigs are already visible.
        # ``_next_closure_id`` and any inner ``_pending_closures`` need
        # explicit propagation.
        if collect_pending is not None:
            collect_pending.extend(ctx._pending_closures)
        self._next_closure_id = ctx._next_closure_id

        return "\n".join(lines)
