"""Mixin for function body compilation (Pass 2).

Compiles individual function declarations to WAT text, including
parameter allocation, body translation, and function assembly.
"""

from __future__ import annotations

from vera import ast
from vera.codegen.tail_position import compute_tail_call_sites
from vera.wasm import WasmContext, WasmSlotEnv
from vera.wasm.helpers import gc_shadow_push


class FunctionCompilationMixin:
    """Methods for compiling function bodies to WAT."""

    def _compile_fn(
        self, decl: ast.FnDecl, *, export: bool = True
    ) -> str | None:
        """Compile a single function to WAT.

        Returns the WAT function string, or None if not compilable
        (with a warning diagnostic).
        """
        # Check if function is compilable
        if not self._is_compilable(decl):
            return None

        # Build effect_ops mapping for State<T> and Exn<E> operations
        effect_ops: dict[str, tuple[str, bool]] = {}
        if isinstance(decl.effect, ast.EffectSet):
            for eff in decl.effect.effects:
                if (isinstance(eff, ast.EffectRef) and eff.name == "State"
                        and eff.type_args and len(eff.type_args) == 1):
                    type_name = self._type_expr_to_slot_name(eff.type_args[0])
                    if type_name:
                        # Only map if no user-defined function shadows the op
                        if "get" not in self._fn_sigs:
                            effect_ops["get"] = (
                                f"$vera.state_get_{type_name}", False
                            )
                        if "put" not in self._fn_sigs:
                            effect_ops["put"] = (
                                f"$vera.state_put_{type_name}", True
                            )
                elif (isinstance(eff, ast.EffectRef) and eff.name == "Exn"
                        and eff.type_args and len(eff.type_args) == 1):
                    type_name = self._type_expr_to_slot_name(eff.type_args[0])
                    if type_name and "throw" not in self._fn_sigs:
                        effect_ops["throw"] = (
                            f"$exn_{type_name}", False
                        )

        # Flatten ADT layouts into ctor_name -> layout for WasmContext
        ctor_layouts = {}
        ctor_to_adt: dict[str, str] = {}
        for adt_name, layouts in self._adt_layouts.items():
            ctor_layouts.update(layouts)
            for ctor_name in layouts:
                ctor_to_adt[ctor_name] = adt_name
        adt_type_names = set(self._adt_layouts.keys())

        ctx = WasmContext(
            self.string_pool,
            effect_ops=effect_ops,
            ctor_layouts=ctor_layouts,
            adt_type_names=adt_type_names,
            generic_fn_info=getattr(self, "_generic_fn_info", None),
            ctor_to_adt=ctor_to_adt,
            known_fns=set(self._fn_sigs.keys()),
            ctor_adt_tp_indices=getattr(self, "_ctor_adt_tp_indices", None),
            adt_tp_counts=getattr(self, "_adt_tp_counts", None),
        )
        # Build function return type map for FnCall type inference
        fn_ret_types: dict[str, str | None] = {}
        for fn_name, (_, ret_wt) in self._fn_sigs.items():
            if ret_wt and ret_wt != "unsupported":
                fn_ret_types[fn_name] = ret_wt
        ctx.set_fn_ret_types(fn_ret_types)
        # Provide type aliases so closures can resolve FnType return types
        ctx.set_type_aliases(self._type_aliases)
        ctx.set_type_alias_params(self._type_alias_params)
        ctx.set_closure_id_start(self._next_closure_id)
        ctx.set_closure_sigs(self._closure_sigs)
        env = WasmSlotEnv()

        # Allocate parameters and track pointer params for GC prologue
        param_parts: list[str] = []
        gc_pointer_params: list[int] = []
        for i, param_te in enumerate(decl.params):
            wt = self._type_expr_to_wasm_type(param_te)
            if wt is None:
                # Unit parameter — skip in WASM signature
                continue
            if wt == "unsupported":
                self._warning(
                    decl,
                    f"Function '{decl.name}' has unsupported parameter type.",
                    rationale="Only Int, Nat, Float64, Bool, and Unit types "
                    "are compilable in the current WASM backend.",
                    error_code="E600",
                )
                return None
            if wt == "i32_pair":
                # String/Array types use two consecutive i32 params (ptr, len)
                ptr_idx = ctx.alloc_param()
                _len_idx = ctx.alloc_param()
                param_parts.append(f"(param $p{i}_ptr i32)")
                param_parts.append(f"(param $p{i}_len i32)")
                type_name = self._type_expr_to_slot_name(param_te)
                if type_name:
                    env = env.push(type_name, ptr_idx)
                gc_pointer_params.append(ptr_idx)
                continue
            local_idx = ctx.alloc_param()
            param_parts.append(f"(param $p{i} {wt})")
            # Push into slot environment
            type_name = self._type_expr_to_slot_name(param_te)
            if type_name:
                env = env.push(type_name, local_idx)
            # Track i32 pointer params (ADT/closure, not Bool/Byte)
            if wt == "i32" and type_name not in ("Bool", "Byte", None):
                gc_pointer_params.append(local_idx)

        # Return type
        ret_wt = self._type_expr_to_wasm_type(decl.return_type)
        if ret_wt == "unsupported":
            self._warning(
                decl,
                f"Function '{decl.name}' has unsupported return type.",
                rationale="Only Int, Nat, Bool, and Unit types are "
                "compilable in the current WASM backend.",
                error_code="E601",
            )
            return None
        if ret_wt == "i32_pair":
            result_part = " (result i32 i32)"
        elif ret_wt:
            result_part = f" (result {ret_wt})"
        else:
            result_part = ""

        # Scan body for handle[State<T>] expressions to register imports
        self._scan_body_for_state_handlers(decl.body)

        # Scan body for IO qualified calls to register per-op imports
        self._scan_io_ops(decl.body)

        # #517 — configure tail-call optimization for this function.
        # The analyzer marks `id(FnCall)` for every call in syntactic
        # tail position; ``_translate_call`` checks membership +
        # type match before emitting ``return_call $foo``.  The
        # ``self_ret_wt`` argument is the function's WASM return
        # type, used by the translator's type-match guard to ensure
        # WASM ``return_call`` semantics are valid (callee signature
        # must match caller).  See ``vera/codegen/tail_position.py``
        # for the analyzer rules and ``_translate_call`` in
        # ``vera/wasm/calls.py`` for the emit site.
        tail_sites = compute_tail_call_sites(decl)
        ctx.set_tail_call_context(
            tail_sites,
            self_ret_wt=ret_wt if ret_wt != "unsupported" else None,
        )

        # Compile precondition checks
        pre_instrs = self._compile_preconditions(ctx, decl, env)

        # Snapshot old state for postcondition old() references
        snapshot_instrs = self._snapshot_old_state(ctx, decl)

        # Compile body
        body_instrs = ctx.translate_block(decl.body, env)
        if body_instrs is None:
            self._warning(
                decl,
                f"Function '{decl.name}' body contains unsupported "
                f"expressions — skipped.",
                rationale="The WASM backend does not yet support all "
                "Vera expression types. This function will not appear "
                "in the compiled output.",
                error_code="E602",
            )
            return None

        # Propagate resource flags from WasmContext (e.g. array allocation)
        if ctx.needs_alloc:
            self._needs_alloc = True
            self._needs_memory = True
        # Propagate Map host-import tracking
        self._map_imports.update(ctx._map_imports)
        self._map_ops_used.update(ctx._map_ops_used)
        # Propagate Set host-import tracking
        self._set_imports.update(ctx._set_imports)
        self._set_ops_used.update(ctx._set_ops_used)
        # Propagate Decimal host-import tracking
        self._decimal_imports.update(ctx._decimal_imports)
        self._decimal_ops_used.update(ctx._decimal_ops_used)
        # Propagate Json host-import tracking
        self._json_ops_used.update(ctx._json_ops_used)
        # Propagate Html host-import tracking
        self._html_ops_used.update(ctx._html_ops_used)
        # Propagate Http host-import tracking
        self._http_ops_used.update(ctx._http_ops_used)
        # Propagate Inference host-import tracking
        self._inference_ops_used.update(ctx._inference_ops_used)
        # Propagate Random host-import tracking (#465)
        self._random_ops_used.update(ctx._random_ops_used)
        # Propagate Math host-import tracking (#467)
        self._math_ops_used.update(ctx._math_ops_used)

        # Coerce body result if return type is i32 but body produces i64
        # (e.g. IntLit in a Byte-returning function)
        if ret_wt == "i32":
            body_result_type = ctx._infer_block_result_type(decl.body)
            if body_result_type == "i64":
                body_instrs.append("i32.wrap_i64")

        # Collect closures created during body compilation and lift them
        self._lift_pending_closures(ctx)

        # Compile postcondition checks (wrap around body result)
        post_instrs = self._compile_postconditions(ctx, decl, env, ret_wt)

        # #517 — tail-call optimization fallback for functions whose
        # bodies are followed by post-body work that must run before
        # the function returns.  WASM ``return_call`` discards the
        # current frame and jumps straight to the callee, so any
        # instructions emitted AFTER ``body_instrs`` in the WAT
        # assembly (postcondition checks, GC epilogue) are silently
        # skipped.  The two known sources of post-body work:
        #
        # 1. ``post_instrs`` — postcondition checks (``ensures(...)``
        #    clauses) emitted by ``_compile_postconditions``.  A
        #    non-empty ``post_instrs`` means the function has a
        #    non-trivial postcondition that must be checked at
        #    runtime; ``return_call`` would skip the check and
        #    silently violate the contract.
        #
        # 2. ``ctx.needs_alloc`` — the GC epilogue (restore
        #    ``$gc_sp``, unwind shadow-stack pointer slots) runs
        #    only for allocating functions.  ``return_call`` would
        #    leak shadow-stack slots once per iteration and
        #    eventually trap on the next ``$alloc`` (#549 tracks
        #    GC-aware TCO as a follow-up).
        #
        # When either condition holds, revert every ``return_call``
        # in ``body_instrs`` to plain ``call``.  Allocating /
        # postcondition-bearing functions pay the WASM frame cost in
        # exchange for correctness; non-allocating, postcondition-
        # free functions keep the optimization (the common
        # iteration-style tail recursion case from ``SKILL.md``'s
        # "Iteration" section).
        if ctx.needs_alloc or post_instrs:
            body_instrs = [
                instr.replace("return_call ", "call ", 1)
                if instr.lstrip().startswith("return_call ")
                else instr
                for instr in body_instrs
            ]

        # Build GC prologue/epilogue (only when function allocates)
        gc_prologue: list[str] = []
        gc_epilogue: list[str] = []
        if ctx.needs_alloc:
            gc_sp_save = ctx.alloc_local("i32")
            gc_prologue.append("global.get $gc_sp")
            gc_prologue.append(f"local.set {gc_sp_save}")
            for pidx in gc_pointer_params:
                gc_prologue.extend(gc_shadow_push(pidx))

            # Determine if return type is a heap pointer
            ret_type_name = self._type_expr_to_slot_name(decl.return_type)
            ret_is_pointer = False
            if ret_wt == "i32" and ret_type_name not in (
                "Bool", "Byte", None,
            ):
                ret_is_pointer = True
            elif ret_wt == "i32_pair":
                ret_is_pointer = True

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
            else:
                # Void/Unit — no return value to save
                gc_epilogue.append(f"local.get {gc_sp_save}")
                gc_epilogue.append("global.set $gc_sp")

        # Assemble function WAT
        export_part = f' (export "{decl.name}")' if export else ""
        header = f"  (func ${decl.name}{export_part}"
        if param_parts:
            header += " " + " ".join(param_parts)
        header += result_part

        lines = [header]

        # Extra locals (from let bindings + contract temps + GC saves)
        for local_decl in ctx.extra_locals_wat():
            lines.append(f"    {local_decl}")

        # GC prologue: save gc_sp, push pointer params
        for instr in gc_prologue:
            lines.append(f"    {instr}")

        # Precondition checks (at function entry)
        for instr in pre_instrs:
            lines.append(f"    {instr}")

        # Old state snapshots (for postcondition old() references)
        for instr in snapshot_instrs:
            lines.append(f"    {instr}")

        # Body instructions
        for instr in body_instrs:
            lines.append(f"    {instr}")

        # Postcondition checks (after body, wraps result)
        for instr in post_instrs:
            lines.append(f"    {instr}")

        # GC epilogue: save result, restore gc_sp, push result, return
        for instr in gc_epilogue:
            lines.append(f"    {instr}")

        lines.append("  )")
        return "\n".join(lines)
