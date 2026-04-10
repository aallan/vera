"""Mixin for closure lifting.

Compiles anonymous functions (closures) created during body compilation
to module-level WASM functions with explicit environment parameters.
"""

from __future__ import annotations

from vera import ast
from vera.codegen.api import ConstructorLayout, _align_up
from vera.wasm import WasmContext, WasmSlotEnv
from vera.wasm.helpers import gc_shadow_push


class ClosureLiftingMixin:
    """Methods for lifting closures to module-level functions."""

    def _lift_pending_closures(self, ctx: WasmContext) -> None:
        """Lift all anonymous functions created during body compilation.

        Each pending closure is compiled to a module-level WASM function
        and added to the function table.
        """
        for anon_fn, captures, closure_id in ctx._pending_closures:
            lifted_wat = self._compile_lifted_closure(
                closure_id, anon_fn, captures,
            )
            if lifted_wat is not None:
                self._closure_fns_wat.append(lifted_wat)
                self._closure_table.append(f"$anon_{closure_id}")
                self._needs_table = True
                self._needs_alloc = True
                self._needs_memory = True

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
                if ret_wt == "i32_pair":  # pragma: no cover — String/Array closure returns
                    result_part = " (result i32 i32)"
                elif ret_wt:
                    result_part = f" (result {ret_wt})"
                else:
                    result_part = ""  # pragma: no cover — Unit closure returns
                sig_content = f"{param_part}{result_part}"
                if sig_content not in self._closure_sigs:
                    sig_name = (
                        f"$closure_sig_{len(self._closure_sigs)}"
                    )
                    self._closure_sigs[sig_content] = sig_name

        # Update next closure ID for subsequent functions
        self._next_closure_id = ctx._next_closure_id
        # Merge closure sigs from the context (content → name)
        for sig_content, sig_name in ctx._closure_sigs.items():
            if sig_content not in self._closure_sigs:
                self._closure_sigs[sig_content] = sig_name

    def _compile_lifted_closure(
        self,
        closure_id: int,
        anon_fn: ast.AnonFn,
        captures: list[tuple[str, int, str]],
    ) -> str | None:
        """Compile an anonymous function to a module-level WASM function.

        The lifted function signature:
          (func $anon_N (param $env i32) (param ...) (result ...))

        The first parameter is the closure environment pointer.
        Captured values are loaded from the environment into locals.
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
        fn_ret_types: dict[str, str | None] = {}
        for fn_name, (_, ret_wt) in self._fn_sigs.items():
            if ret_wt != "unsupported":
                fn_ret_types[fn_name] = ret_wt
        ctx.set_fn_ret_types(fn_ret_types)
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
                # Track pointer params for GC
                type_name = self._type_expr_to_slot_name(param_te)
                if wt == "i32" and type_name not in ("Bool", "Byte", None):
                    gc_pointer_params.append(local_idx)

        # Compute capture layout (must match _translate_anon_fn)
        cap_offsets: list[tuple[int, str]] = []
        offset = 4  # skip func_table_idx
        for _tname, _cidx, cap_wt in captures:
            align = 8 if cap_wt in ("i64", "f64") else 4
            offset = _align_up(offset, align)
            cap_offsets.append((offset, cap_wt))
            offset += 8 if cap_wt in ("i64", "f64") else 4

        # Load captured values from env into locals (allocated AFTER params)
        cap_locals: list[tuple[str, int]] = []  # (type_name, local_idx)
        load_instrs: list[str] = []
        for i, (tname, _cidx, cap_wt) in enumerate(captures):
            cap_local = ctx.alloc_local(cap_wt)
            cap_offset, _ = cap_offsets[i]
            load_op = (
                "i64.load" if cap_wt == "i64"
                else "f64.load" if cap_wt == "f64"
                else "i32.load"
            )
            load_instrs.append(f"local.get {env_idx}")
            load_instrs.append(f"{load_op} offset={cap_offset}")
            load_instrs.append(f"local.set {cap_local}")
            cap_locals.append((tname, cap_local))

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

        # Compile the body
        body_instrs = ctx.translate_block(anon_fn.body, env)
        if body_instrs is None:  # pragma: no cover — defensive
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

        # Build GC prologue/epilogue (only when closure body allocates)
        gc_prologue: list[str] = []
        gc_epilogue: list[str] = []
        if ctx.needs_alloc:
            gc_sp_save = ctx.alloc_local("i32")
            gc_prologue.append("global.get $gc_sp")
            gc_prologue.append(f"local.set {gc_sp_save}")
            for pidx in gc_pointer_params:
                gc_prologue.extend(gc_shadow_push(pidx))
            # Also push captured pointer locals
            for tname, cap_local in cap_locals:
                gc_cap_wt: str | None = None
                for _tn, _ci, cwt in captures:
                    if _tn == tname:
                        gc_cap_wt = cwt
                        break
                if gc_cap_wt == "i32" and tname not in ("Bool", "Byte"):
                    gc_prologue.extend(gc_shadow_push(cap_local))

            # Determine if return type is a heap pointer
            ret_is_pointer = False
            if ret_wt == "i32":
                ret_type_name = self._type_expr_to_slot_name(
                    anon_fn.return_type,
                )
                if ret_type_name not in ("Bool", "Byte", None):
                    ret_is_pointer = True
            elif ret_wt == "i32_pair":  # pragma: no cover — String/Array closure return
                ret_is_pointer = True

            if ret_wt == "i32_pair":  # pragma: no cover — String/Array closure return
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
        for instr in body_instrs:
            lines.append(f"    {instr}")
        for instr in gc_epilogue:
            lines.append(f"    {instr}")
        lines.append("  )")
        return "\n".join(lines)
