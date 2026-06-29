"""Mixin for function body compilation (Pass 2).

Compiles individual function declarations to WAT text, including
parameter allocation, body translation, and function assembly.
"""

from __future__ import annotations

from vera import ast
from vera.skip import CodegenInvariantError, CodegenSkip
from vera.codegen.tail_position import compute_tail_call_sites
from vera.wasm import WasmContext, WasmSlotEnv
from vera.wasm.helpers import _is_host_handle_type, gc_shadow_push


class FunctionCompilationMixin:
    """Methods for compiling function bodies to WAT."""

    def _compile_fn(
        self, decl: ast.FnDecl, *, export: bool = True,
        module_renames: dict[str, str] | None = None,
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
        # Build function return type map for FnCall type inference.
        # Include Unit-returning fns explicitly with None so `_is_void_expr`
        # in vera/wasm/context.py can distinguish "Unit return" (key present,
        # value is None) from "unknown function" (key absent).  Without this,
        # a user @Unit fn called in non-tail block-statement position fell
        # through to "produces a value", emitting a stray drop and breaking
        # WASM validation (#584).
        fn_ret_types: dict[str, str | None] = {}
        for fn_name, (_, ret_wt) in self._fn_sigs.items():
            if ret_wt != "unsupported":
                fn_ret_types[fn_name] = ret_wt
        ctx.set_fn_ret_types(fn_ret_types)
        # #614: full Vera return-type expressions, paired with the WAT-
        # types above.  Used by `_infer_index_element_type_expr` to
        # resolve the element type of `f()[i]` when `f` returns
        # `Array<T>`.
        ctx.set_fn_ret_type_exprs(self._fn_ret_type_exprs)
        # #798: resolved-type side-table for the integer-overflow guard's
        # Int/Nat operand classifier (kept in lockstep with the verifier).
        ctx.set_expr_semantic_types(self._expr_semantic_types)
        # #747: per-parameter concrete-@Nat flags for the call-site
        # runtime narrowing guard.
        ctx.set_fn_nat_params(self._fn_nat_params)
        # #813: per-parameter concrete-@Int flags for the call-site
        # runtime @Nat -> @Int widening guard.
        ctx.set_fn_int_params(self._fn_int_params)
        # Provide type aliases so closures can resolve FnType return types
        ctx.set_type_aliases(self._type_aliases)
        ctx.set_type_alias_params(self._type_alias_params)
        ctx.set_closure_id_start(self._next_closure_id)
        ctx.set_closure_sigs(self._closure_sigs)
        # #814 §8.5.3: module-qualified call target table, so a ``m::f`` call
        # whose bare name is shadowed by a local resolves to the module's
        # body (emitted under a distinct ``mod$…`` name) rather than the local.
        ctx.set_module_qualified_targets(self._module_qualified_targets)
        # #814 C2: intra-module call renames, set ONLY when compiling a
        # ``mod$…`` body, so a bare sibling call inside it reaches the
        # module's version rather than the main program's local shadow.
        ctx.set_intra_module_renames(module_renames or {})
        env = WasmSlotEnv()

        # Allocate parameters and track pointer params for GC prologue
        param_parts: list[str] = []
        gc_pointer_params: list[int] = []
        # #746: refined params get a runtime predicate guard at entry (the
        # value's local + its type expr), emitted *before* the preconditions
        # (a `requires(...)` may depend on the refined invariant — see the
        # emission site below).
        refined_param_checks: list[tuple[int, ast.TypeExpr]] = []
        # #746 PR-review: a tuple param whose *components* are refined / @Nat
        # carries no top-level refinement, so it needs per-component boundary
        # guards (the FFI gap the projection-fact assumption opened — see
        # `_emit_component_refinement_guards`).  Collected alongside the
        # directly-refined params and emitted in the same pre-body block.
        component_param_checks: list[tuple[int, ast.TypeExpr]] = []
        for i, param_te in enumerate(decl.params):
            wt = self._type_expr_to_wasm_type(param_te)
            if wt is None:
                # Unit parameter — skipped in the WASM signature (zero-size).
                # A `@Unit` refinement is codegen-UNguardable: its binder is
                # erased, so there is no local to check a boundary predicate
                # against.  `_refinement_guard_parts` returns None for a `@Unit`
                # base and the verifier records such a narrowing
                # `tier3_unguarded` (an honest E506, not a claimed guard), so
                # there is nothing to emit here.  Fail loud rather than silently
                # drop a declared boundary invariant should a future change ever
                # make a `@Unit` param carry guard parts (CR 8afb51a/e6f17b7).
                if self._refinement_guard_parts(param_te) is not None:
                    raise ValueError(  # pragma: no cover — invariant guard
                        f"refined @Unit parameter in '{decl.name}' carries "
                        "runtime guard parts but has no WASM local to check "
                        "them against; a @Unit refinement must be recorded "
                        "tier3_unguarded, not guarded"
                    )
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
                if self._refinement_guard_parts(param_te) is not None:
                    refined_param_checks.append((ptr_idx, param_te))
                gc_pointer_params.append(ptr_idx)
                continue
            local_idx = ctx.alloc_param()
            param_parts.append(f"(param $p{i} {wt})")
            # Push into slot environment
            type_name = self._type_expr_to_slot_name(param_te)
            if type_name:
                env = env.push(type_name, local_idx)
            if self._refinement_guard_parts(param_te) is not None:
                refined_param_checks.append((local_idx, param_te))
            # Component guards for a tuple param (heap pointer, wt == "i32") OR a
            # refinement OVER a tuple (`{ @Tuple<PosInt, Int> | P }`) —
            # `_resolve_tuple_type` unwraps both.  A refinement-over-tuple gets
            # BOTH its top-level guard (above) and per-component guards; an
            # ordinary ADT / closure param resolves to None and is skipped (CR
            # PR-review).
            if self._resolve_tuple_type(param_te) is not None:
                component_param_checks.append((local_idx, param_te))
            # Track i32 pointer params (ADT/closure, not Bool/Byte,
            # not opaque host handles — Map/Set/Decimal are i32
            # indices into Python-side stores, not Vera-heap
            # pointers; pushing them onto the GC shadow stack wastes
            # space and a handle value that lands in the heap-pointer
            # range with valid alignment would spuriously mark an
            # unrelated heap object as live (#347).
            if (
                wt == "i32"
                and type_name not in ("Bool", "Byte", None)
                and not _is_host_handle_type(type_name)
            ):
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

        # Compile precondition checks.  A `requires(...)` may *assume* the
        # refined parameters' invariants, so it runs after the refinement
        # guards emitted below (the call stays here so its ctx side effects
        # are unchanged; only the emitted-instruction order is reversed).
        precond_instrs = self._compile_preconditions(ctx, decl, env)

        # #746: refined parameters carry a runtime predicate guard at entry —
        # a refinement is the parameter's *type* invariant, so an untrusted
        # (incl. FFI/public) caller passing a violating value traps via
        # $vera.contract_fail rather than the function relying on an invariant
        # the value never established.  Emitted *before* the explicit
        # preconditions: a `requires(...)` may itself depend on the invariant
        # (e.g. `requires(10 / @NonZero.0 > 0)` would trap on the division
        # before the guard could report the boundary violation), so the guard
        # must establish the refinement first.
        refine_guard_instrs: list[str] = []
        # #746 PR-review: per-component boundary guards for tuple params — a
        # `Tuple<PosInt, Int>` carries no top-level refinement, so an FFI caller
        # passing a refinement-violating component would otherwise slip past the
        # callee's entry checks (the verifier *assumes* the component holds).
        # Emitted BEFORE the top-level refined guard below: a refinement OVER a
        # tuple (`{ @Tuple<PosInt, Int> | P }`) has P potentially read the
        # components, so the components must be established first (CR PR-review).
        for value_local, param_te in component_param_checks:
            refine_guard_instrs.extend(
                self._emit_component_refinement_guards(
                    ctx, decl, param_te, value_local, env, "parameter"))

        for value_local, param_te in refined_param_checks:
            parts = self._refinement_guard_parts(param_te)
            if parts is None:  # pragma: no cover — collected only when not None
                continue
            predicate, base_name = parts
            msg = self._format_refinement_message(decl, param_te, "parameter")
            guard = self._emit_refinement_check(
                ctx, predicate, base_name, value_local, msg, env)
            if guard is not None:
                refine_guard_instrs.extend(guard)

        pre_instrs = refine_guard_instrs + precond_instrs

        # Snapshot old state for postcondition old() references
        snapshot_instrs = self._snapshot_old_state(ctx, decl)

        # Compile body.
        #
        # Two failure modes are handled here:
        #
        # 1. ``CodegenSkip`` — a translator hit an AST shape it
        #    recognises but doesn't yet support.  We attach the
        #    unsupported-node's span to the [E602] diagnostic so the
        #    user sees exactly which expression we couldn't compile,
        #    rather than just "function 'foo' has an unsupported
        #    expression somewhere".  This is the #626 Layer 3 path:
        #    new translator code raises ``CodegenSkip``; old translator
        #    code still returns None and falls through to the legacy
        #    branch below.  See vera/skip.py.
        # 2. ``body_instrs is None`` — legacy silent-skip return.
        #    Pre-#626-Layer-3 every unsupported shape went this way.
        #    The audit-and-convert pass (Phase 3, tracked in #657) is
        #    migrating these sites to ``raise CodegenSkip``; until
        #    that's complete this branch stays as the catch-all.
        try:
            body_instrs = ctx.translate_block(decl.body, env)
        except CodegenSkip as skip:
            # #626 Layer 3 — structured skip with node-level span.
            self._harvest_interp_inference_failures(ctx)
            self._warning(
                skip.node if getattr(skip.node, "span", None) else decl,
                f"Function '{decl.name}' body contains unsupported "
                f"{type(skip.node).__name__}: {skip.reason} — "
                f"function skipped.",
                rationale="The WASM backend does not yet support all "
                "Vera expression types. This function will not appear "
                "in the compiled output.",
                error_code="E602",
            )
            return None
        except CodegenInvariantError as inv:  # pragma: no cover — no production code raises CodegenInvariantError yet; the handler is the catch-side contract for future raises tracked in #657 (Track 2: INVARIANT_DEFENSIVE conversions).
            # #626 Layer 3 — compiler bug, not a user error.  Surface
            # as [E699] at severity="error" so `vera compile` exits
            # non-zero — these should never fire in production; if
            # you see one, file a bug, and don't let CI mask it as a
            # warning.
            #
            # Harvest interpolation failures before the [E699] for the
            # same reason the CodegenSkip handler does: if the invariant
            # fires after some interp segments have already populated
            # `ctx._interp_inference_failures`, those would otherwise be
            # silently dropped.  Empirically invariants fire early
            # (before interp translation runs) so this is mostly
            # symmetry insurance — CodeRabbit nitpick on #658.
            self._harvest_interp_inference_failures(ctx)
            self._error(
                inv.node if inv.node is not None else decl,
                f"Internal compiler error while compiling "
                f"'{decl.name}': {inv.msg}",
                rationale="This is a codegen invariant violation — "
                "the type checker should have rejected the input "
                "before it reached this point.  Please file a bug "
                "report with the offending program.",
                error_code="E699",
            )
            return None

        if body_instrs is None:
            # #630 Tier 2 — surface a specific [E615] for each
            # interpolation segment whose Vera type couldn't be
            # inferred (see `_translate_interpolated_string` in
            # `vera/wasm/operators.py`), then fall through to the
            # generic [E602] function-skip.  Pre-#630 those segments
            # silently fell through to `to_string(...)` which reads
            # i64; an i32_pair value (String/Array) then tripped
            # `expected i64, found i32` at WASM validation, decoupled
            # from any source location.  Post-#630 the failure is
            # loud, source-located, and points at the specific
            # `\(...)` segment whose inference returned None.
            self._harvest_interp_inference_failures(ctx)
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

        # #813: guard a @Nat -> @Int widening at the return position.  A @Nat
        # result above i64.MAX reinterprets to a negative @Int (u64.MAX -> -1),
        # so trap rather than silently return it — the runtime backstop for the
        # verifier's nat_to_int_coerce obligation (7c).  @Int is i64, so this
        # runs before (and is unaffected by) the i32 coercion below.
        if (self._type_expr_to_slot_name(decl.return_type) == "Int"
                and ctx._result_is_nat(decl.body)):
            body_instrs = ctx._emit_int_widen_guard(body_instrs)

        # Coerce body result if return type is i32 but body produces i64
        # (e.g. IntLit in a Byte-returning function)
        if ret_wt == "i32":
            body_result_type = ctx._infer_block_result_type(decl.body)
            if body_result_type == "i64":
                body_instrs.append("i32.wrap_i64")

        # Collect closures created during body compilation and lift them.
        # If any closure body failed to compile, drop the enclosing fn
        # rather than emit a module with a `call_indirect` to a missing
        # function-table entry — closes #636.  The closure body's own
        # diagnostics (E615 from interpolation failures, generic E602
        # from translation failures) were already emitted by
        # `_compile_lifted_closure`'s harvest; here we add a specific
        # E602 noting that the parent is being dropped *because* of
        # the closure failure, so the user can correlate the cause
        # diagnostic with the effect.
        closure_failed = self._lift_pending_closures(ctx)
        if closure_failed:
            self._warning(
                decl,
                f"Function '{decl.name}' contains a closure whose "
                f"body failed to compile — skipped to avoid emitting "
                f"an invalid module.",
                rationale="A closure body inside this function failed "
                "to translate (see preceding diagnostics for the "
                "specific cause). The closure was dropped from the "
                "function table; the enclosing function references it "
                "via call_indirect, which would fail at WASM "
                "validation. Dropping the enclosing function lets the "
                "build complete with diagnostics only, no invalid "
                "module emission.",
                error_code="E602",
            )
            return None

        # Compile postcondition checks (wrap around body result)
        post_instrs = self._compile_postconditions(ctx, decl, env, ret_wt)

        # #517 — tail-call optimization fallback for functions whose
        # bodies are followed by post-body work that must run before
        # the function returns.  WASM ``return_call`` discards the
        # current frame and jumps straight to the callee, so any
        # instructions emitted AFTER ``body_instrs`` in the WAT
        # assembly (postcondition checks, GC epilogue) are silently
        # skipped.  Three outcomes (precedence: 1 > 2 > 3):
        #
        # 1. ``post_instrs`` non-empty — postcondition checks
        #    (``ensures(...)`` clauses) emitted by
        #    ``_compile_postconditions``.  A non-empty
        #    ``post_instrs`` means the function has a non-trivial
        #    postcondition that must be checked at runtime;
        #    ``return_call`` would skip the check and silently
        #    violate the contract.  REVERTED to plain ``call`` —
        #    no way to TCO and still run the check.
        #
        # 2. ``ctx.needs_alloc`` and no ``post_instrs`` — the GC
        #    epilogue (restore ``$gc_sp``, unwind shadow-stack
        #    pointer slots) runs only for allocating functions.
        #    ``return_call`` would leak shadow-stack slots once per
        #    iteration and eventually trap on the next ``$alloc``.
        #    Pre-#549 this fell to the same revert-to-call path as
        #    postcondition-bearing functions; post-#549 we instead
        #    PATCH every ``return_call`` site to restore ``$gc_sp``
        #    to its entry value immediately before the jump.  The
        #    callee's prologue then saves a clean baseline and the
        #    chain continues without unbounded shadow-stack growth.
        #
        # 3. Neither condition holds — leave ``return_call``
        #    untouched.  This is the common non-allocating tail-
        #    recursion case (the ``Iteration is tail recursion``
        #    idiom from ``SKILL.md``).
        #
        # ``gc_sp_save`` is pre-allocated before the dispatch so
        # both the per-return_call restore (in branch 2) AND the
        # function's GC prologue/epilogue below share the same
        # local index.
        gc_sp_save: int | None = (
            ctx.alloc_local("i32") if ctx.needs_alloc else None
        )

        if post_instrs:
            # Postcondition checks must run; return_call would skip
            # them.  Revert every return_call to plain call.
            body_instrs = [
                instr.replace("return_call ", "call ", 1)
                if instr.lstrip().startswith("return_call ")
                else instr
                for instr in body_instrs
            ]
        elif ctx.needs_alloc:
            # #549: GC-aware TCO.  Prepend a ``$gc_sp`` restore
            # immediately before each ``return_call`` so the
            # callee's prologue saves a clean baseline rather than
            # inheriting the leaked shadow-stack slots from this
            # frame's arg-evaluation leg.  Args are already on the
            # WASM operand stack at the return_call site; the
            # restore touches only the ``$gc_sp`` global, not the
            # operand stack, so args transfer atomically to the
            # callee.  Pre-#549 this revert-to-plain-call path also
            # fired for allocating fns; closing #549 lets allocating
            # tail-recursive fns iterate indefinitely without
            # unbounded shadow-stack growth.
            assert gc_sp_save is not None  # noqa: S101 - narrows int | None for mypy
            patched: list[str] = []
            for instr in body_instrs:
                if instr.lstrip().startswith("return_call "):
                    # Preserve the return_call line's leading
                    # whitespace so the inserted restore visually
                    # nests at the same depth.  Without this, an
                    # `if/else`-nested ``return_call`` (which carries
                    # an inline 2-space indent from
                    # ``vera/wasm/operators.py``'s if/else emission)
                    # ends up with `local.get N` / `global.set $gc_sp`
                    # lines rendered 2 spaces shallower in the WAT.
                    # Functionally inert (WAT is whitespace-
                    # insensitive) but visually misleading.  Tracked
                    # for principled fixup in #672.
                    prefix = instr[: len(instr) - len(instr.lstrip())]
                    patched.append(f"{prefix}local.get {gc_sp_save}")
                    patched.append(f"{prefix}global.set $gc_sp")
                patched.append(instr)
            body_instrs = patched

        # Build GC prologue/epilogue (only when function allocates)
        gc_prologue: list[str] = []
        gc_epilogue: list[str] = []
        if ctx.needs_alloc:
            assert gc_sp_save is not None  # noqa: S101 - narrows int | None for mypy
            gc_prologue.append("global.get $gc_sp")
            gc_prologue.append(f"local.set {gc_sp_save}")
            for pidx in gc_pointer_params:
                gc_prologue.extend(gc_shadow_push(pidx))

            # Determine if return type is a heap pointer
            ret_type_name = self._type_expr_to_slot_name(decl.return_type)
            ret_is_pointer = False
            if (
                ret_wt == "i32"
                and ret_type_name not in ("Bool", "Byte", None)
                and not _is_host_handle_type(ret_type_name)
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
