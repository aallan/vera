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
from vera.wasm.helpers import gc_shadow_push, is_gc_pointer_base


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

        **Called more than once per context (#1245).**  ``_compile_fn``
        drives a lift after the body AND a second one after
        ``_compile_postconditions``, because a closure created while
        lowering a refined-RETURN guard, a tuple return's component
        guards, or an ``ensures(...)`` predicate is registered on this
        same ``ctx`` only at that later point.  The pending list is
        therefore CONSUMED here (not merely read) so the second pass sees
        exactly the newly-registered closures, and ``ctx``'s closure-id
        counter is re-synced on the way out so a closure registered after
        this pass takes the next free id — the ``closure_id`` ↔
        ``_closure_table`` position correspondence is what a closure
        struct's stored ``func_table_idx`` relies on.
        """
        # ``deque`` (rather than a plain list) because ``popleft`` is
        # O(1) where ``list.pop(0)`` would shift every remaining entry.
        # Closure worklists are typically tiny in practice, but the
        # deque is the right idiom for FIFO and removes the need to
        # reason about list-pop costs as the depth of nesting grows.
        #
        # Each entry carries the ANCESTRY of `AnonFn` identities that led
        # to it (#1234): a lift whose own boundary guard re-queues a
        # closure already on its lift chain is a cycle, and the worklist
        # would otherwise grow for ever.  See the pop below.
        worklist: deque[
            tuple[ast.AnonFn, list[tuple[str, int, str]], int, frozenset[int]]
        ] = deque(
            (anon_fn, captures, closure_id, frozenset())
            for anon_fn, captures, closure_id in ctx._pending_closures
        )
        ctx._pending_closures = []
        # INVARIANT: the ancestry keys are `id()` values, so every node they
        # name must stay strongly referenced for as long as its key is in
        # play.  It is not the worklist entries that guarantee that — an
        # ancestry names ANCESTORS, which have already been popped — but the
        # AST itself: every `AnonFn` an ancestry can name is a node of the
        # `Program` this compilation is walking, reachable from the declaration
        # being compiled, from an alias table entry (a refinement predicate's
        # stored type expression, the #1234 cycle's own source), or from the
        # `mono_decls` clones Pass 2 holds across the whole run.  All three
        # outlive the lift, so an id here cannot be recycled while its key is
        # live.  Never retain an ancestry (or any set of these ids) beyond
        # THAT lifetime: CPython reuses an id once its object is collected,
        # and a recycled id silently reads as a cycle in a set that outlived
        # its referents.
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
            anon_fn, captures, closure_id, ancestry = worklist.popleft()
            if id(anon_fn) in ancestry:
                # #1234: lifting this closure lowers its refined-formal /
                # refined-return guard, whose predicate leads back to THIS
                # closure, so the lift queues it again — `type SelfRef =
                # { @Int | … fn(@SelfRef -> @Int) … }` used in a signature
                # made `vera compile` run for ever on a check-green program
                # with no diagnostic and no bound.  Refuse the lift loudly
                # and let the #636 path drop the enclosing function,
                # mirroring the registration pre-scan's
                # `_anon_sig_scan_stack` guard (compilability.py), which
                # made the REGISTRATION walk immune to the same cycle.
                #
                # Keyed on the `AnonFn` node identity along the current lift
                # CHAIN, not a module-wide seen-set.  The distinction is
                # load-bearing in both directions and is pinned by
                # `tests/test_closure_lift_boundaries_1234_1235_1245.py`:
                # a seen-set refuses the SECOND legitimate lift of one
                # predicate's closure — `fn f(@R, @R -> @Int)` guards two
                # formals of the same refined type, and a diamond reaches
                # one refinement by two routes — while the chain still
                # catches a cycle of ANY length, self-reference and mutual
                # A -> B -> A and longer alike.
                param_sig = ", ".join(
                    ast.format_type_expr(p) for p in anon_fn.params)
                ret_sig = ast.format_type_expr(anon_fn.return_type)
                self._warning(
                    anon_fn,
                    f"Closure fn({param_sig} -> {ret_sig}) is refined by a "
                    "type whose refinement chain leads back to this same "
                    "closure — a cyclic refinement, whose boundary guard "
                    "cannot be lowered without unbounded expansion; "
                    "closure skipped.",
                    rationale="A refined closure formal or return is "
                    "guarded at the boundary by lowering the refinement's "
                    "predicate.  When that predicate contains a closure "
                    "whose own refinement leads back here — directly, or "
                    "around a cycle of two or more types — each lift queues "
                    "another closure and codegen would never terminate.  "
                    "The enclosing function is dropped too, to avoid a "
                    "missing function-table entry.",
                    error_code="E602",
                )
                any_failed = True
                continue
            inner_pending: list[tuple[ast.AnonFn, list[tuple[str, int, str]], int]] = []
            try:
                lifted_wat = self._compile_lifted_closure(
                    closure_id, anon_fn, captures,
                    collect_pending=inner_pending,
                    # #1299: a closure body is lexically INSIDE the function
                    # being compiled, so it resolves bare names in that
                    # function's scope.  Carried from the parent context
                    # rather than rebuilt: the lift has no declaration to
                    # derive it from, and a rebuilt copy could drift.
                    scoped_fns=ctx._scoped_fns,
                )
            except CodegenInvariantError:
                # #657: a closure-body invariant (codegen bug) aborts the
                # worklist mid-way.  Restore `_next_closure_id` — mirroring the
                # `any_failed` rollback below — so the consumed range is recycled
                # and subsequent top-level fns keep their closure_id ↔
                # table_index correspondence, then re-raise so `_compile_fn`
                # surfaces a single [E699].  (Local buffers are discarded with
                # the stack frame; module-level state is committed only on the
                # all-success path below, so nothing else needs rolling back.)
                self._next_closure_id = prev_next_closure_id
                raise
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
                if pwt == "i32_pair":
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
            # inner ctx registered while translating this body, each
            # tagged with THIS closure added to the lift chain (#1234).
            descendant_ancestry = ancestry | {id(anon_fn)}
            worklist.extend(
                (inner_fn, inner_caps, inner_id, descendant_ancestry)
                for inner_fn, inner_caps, inner_id in inner_pending
            )

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

        # #1245: hand the id counter back to the context.  A closure this
        # function registers LATER — while `_compile_postconditions` lowers
        # a refined-return guard or an `ensures(...)` predicate — allocates
        # its `closure_id` from `ctx._next_closure_id`, and the second lift
        # pass appends it to `_closure_table` at exactly that index.  Without
        # the resync it would reuse an id this pass already committed, and
        # the closure struct's stored `func_table_idx` would address another
        # closure's table entry.
        ctx._next_closure_id = self._next_closure_id

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
        scoped_fns: set[str] | None = None,
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
            # #1253/#1316: the namespace's data types, as in `functions.py`
            # — a lifted closure body belongs to the declaration that
            # contains it, so it resolves names in that declaration's scope.
            adt_type_names=set(self._alias_env.data_types),
            # #873: a generic called ONLY from inside a closure body must be
            # rewritten to its monomorphized clone here too — mono discovery
            # already walks closure bodies (the total AST walk) and emits the
            # clone, but without `generic_fn_info` the lifted closure body left
            # the call on the bare generic name (`call $are_equal`), which has
            # no implementation → WASM validation failure at run.  `known_fns`
            # rides along so the same cross-module guard rail the per-function
            # context uses (functions.py) also protects closure bodies.
            generic_fn_info=getattr(self, "_generic_fn_info", None),
            ctor_to_adt=ctor_to_adt,
            known_fns=set(self._fn_sigs.keys()),
            # #1299: the enclosing function's lexical scope, threaded from
            # its context by `_lift_pending_closures`.  ``None`` (a caller
            # that lifts outside a function compile) falls back to the flat
            # registry inside `WasmContext`, which is the pre-#1299 answer.
            scoped_fns=scoped_fns,
            ctor_adt_tp_indices=getattr(self, "_ctor_adt_tp_indices", None),
            adt_tp_counts=getattr(self, "_adt_tp_counts", None),
            adt_tp_param_names=getattr(self, "_adt_tp_param_names", None),
        )
        # #773 / PR #870 review: direct `==` derivability gate inside closure
        # bodies — same oracle as the per-function ctx in functions.py.
        ctx.set_adt_eq_derivable(self._adt_satisfies_eq)
        # #932: share the truncated→full constrained-var name map (see
        # functions.py) so a generic clone's direct `==` inside a closure body
        # resolves a truncated slot type on its fully-nested name.
        ctx.set_eq_full_type_names(getattr(self, "_eq_full_type_names", {}))
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
        # #841: Future<Result<String, String>>-returning fn names, so an
        # await inside a closure body gets the fused-handle check too.
        ctx.set_future_ret_fns(
            self._future_ret_fns, self._future_ret_module_fns,
        )
        # #798: resolved-type side-table for the integer-overflow guard's
        # Int/Nat operand classifier, inside closure bodies too.
        ctx.set_expr_semantic_types(self._expr_semantic_types)
        # #820: target-type side-table for the @Nat -> @Int widening guard's
        # per-component target-type recovery, inside closure bodies too.
        ctx.set_expr_target_types(self._expr_target_types)
        # #747: per-parameter concrete-@Nat flags for the call-site
        # runtime narrowing guard inside closure bodies too.
        ctx.set_fn_nat_params(self._fn_nat_params)
        # #813: per-parameter concrete-@Int flags for the call-site
        # runtime @Nat -> @Int widening guard inside closure bodies too.
        ctx.set_fn_int_params(self._fn_int_params)
        # #865: per-parameter concrete-@Byte flags for the call-site
        # int-literal → i32.const coercion inside closure bodies too.
        ctx.set_fn_byte_params(self._fn_byte_params)
        ctx.set_alias_env(self._alias_env)
        # No `set_refinement_guard_emitter` here (#1268), deliberately: this
        # context is built with no `effect_op_cells`, so a `throw` in a
        # closure body reaches no cell and is not a write boundary the guard
        # could key on — it does not compile at all today (`call target
        # 'throw' not registered in this module`, a closure skip).  Threading
        # the op registries in is what would make the boundary real, and the
        # emitter's absence then fails CLOSED at a loud skip rather than
        # emitting an unguarded payload the verifier records as guarded.
        # #814/#774: a qualified call inside a closure body must resolve the
        # same way it does in a top-level body — to the module's function
        # (`mod$…` for a shadowed fn) and, for a shadowed imported generic, to
        # the module generic's clone rather than the local shadow.
        ctx.set_module_qualified_targets(self._module_qualified_targets)
        ctx.set_module_qualified_generic_bases(
            self._module_qualified_generic_bases,
        )
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
            if wt == "unsupported":
                # #913: a bare type variable (`@T` inside a `forall<T>` body)
                # is `"unsupported"` here — but it is NOT a codegen bug.  The
                # generic TEMPLATE is body-compiled to draw its skip-warning
                # surface (E602/E604/E605), exactly as a template's own bare
                # `@T` *parameter* draws E604 via `_is_compilable`; only the
                # monomorphized clone (whose closure param is the concrete
                # type) is ever run.  So drop THIS closure cleanly — a
                # user-facing skip that returns None, routing through
                # `_lift_pending_closures` to `_compile_fn`'s droppable
                # dropped-parent E602 — rather than raising the hard E699 that
                # reported a valid generic as an internal compiler error.  Both
                # this closure-level E602 and the function-level wrapper are
                # suppressed once a clone compiles: the wrapper by the #604
                # description-prefix filter, THIS one by that filter's #913
                # forall-origin arm (`vera/codegen/core.py`), which matches a
                # template-body E602 by its source line falling inside a
                # compiled-clone template's span (its description names the
                # closure, not the enclosing fn, so the prefix match misses it).
                self._harvest_interp_inference_failures(ctx)
                self._warning(
                    anon_fn,
                    "Closure parameter has unsupported WASM type — "
                    "closure skipped.",
                    rationale="A closure parameter typed as an unsubstituted "
                    "type variable has no monomorphic WASM representation. "
                    "This occurs only in an uninstantiated generic template "
                    "body; the enclosing function is dropped, and each "
                    "concrete instantiation compiles its own clone.",
                    error_code="E602",
                )
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
                # Track pointer params for GC.  The classification is
                # `is_gc_pointer_base` over the formal's REPRESENTATION
                # base (#1255): the slot name is the SYNTACTIC head, so a
                # refined or aliased `@Byte` formal was rooted here as a
                # heap pointer.  `_family_base_te` is the same resolution
                # the width above (`_type_expr_to_wasm_type`) already
                # performs, so the two conjuncts describe one type.
                if wt == "i32" and is_gc_pointer_base(
                    self._family_base_te(param_te)
                ):
                    gc_pointer_params.append(local_idx)

        # #1024: a REFINED closure formal carries a runtime predicate guard at
        # the lifted body's prologue — the closure-side dual of `_compile_fn`'s
        # `refined_param_checks` (functions.py).  The verifier obligates the
        # apply_fn ARGUMENT against this formal's full predicate (verifier.py
        # apply_fn branch, fix site 1) and records it `guarded=True` on the
        # strength of THIS guard: without it, `apply_fn(clo, 0)` into a
        # `{ @Nat | @Nat.0 > 0 }` formal narrowed a violating value in
        # unchecked (the #1017 apply_fn arm's `>= 0` proved nothing about the
        # strict predicate).  Derived from `param_info`, whose stored index is
        # already the value local the guard checks (the ptr half for an
        # i32_pair String/Array param, exactly as `_compile_fn` collects) — the
        # @Unit param is `continue`d above and never enters `param_info`, which
        # matches the codegen-unguardable @Unit refinement (the verifier records
        # that narrowing `tier3_unguarded`, claiming no runtime guard).
        refined_param_checks: list[
            tuple[int, tuple[ast.Expr, str]]
        ] = [
            (value_local, parts)
            for _i, param_te, value_local in param_info
            if (parts := self._refinement_guard_parts(param_te)) is not None
        ]
        # #1235: a closure formal whose TUPLE COMPONENTS are refined / @Nat
        # carries no top-level refinement, so the guards above see nothing —
        # the named path's `component_param_checks` (functions.py) is what
        # catches that, and the closure path had no equivalent.  A
        # `Tuple<PosInt, Int>` reaching an `AnonFn` through `apply_fn` or a
        # collection combinator therefore crossed unguarded where the same
        # formal on a named function traps: inconsistent enforcement of a
        # designed guard surface.  Collected here from the same `param_info`
        # and lowered through the same `_tuple_component_guard_sites`
        # decomposition the named path uses, so the closure and named
        # boundaries check the same set — which is also what lets
        # `_signature_refinement_predicates` decompose an `AnonFn`'s
        # signature: emitter and registration flip together.
        component_param_checks: list[tuple[int, ast.TypeExpr]] = [
            (value_local, param_te)
            for _i, param_te, value_local in param_info
            if self._resolve_tuple_type(param_te) is not None
        ]

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
        if ret_wt == "unsupported":
            # #913: same as the closure-parameter case above — an unsubstituted
            # type variable (`-> @T`) in an uninstantiated generic template body
            # is a clean skip, not an internal compiler error.  Drop the closure
            # so the enclosing fn is dropped droppably (E602); the clone whose
            # return type is concrete compiles normally.
            self._harvest_interp_inference_failures(ctx)
            self._warning(
                anon_fn,
                "Closure return type has unsupported WASM type — "
                "closure skipped.",
                rationale="A closure return typed as an unsubstituted type "
                "variable has no monomorphic WASM representation. This occurs "
                "only in an uninstantiated generic template body; the enclosing "
                "function is dropped, and each concrete instantiation compiles "
                "its own clone.",
                error_code="E602",
            )
            return None
        if ret_wt == "i32_pair":
            result_part = " (result i32 i32)"
        elif ret_wt:
            result_part = f" (result {ret_wt})"
        else:
            result_part = ""  # pragma: no cover — Unit closure return

        # #984: an @Int body narrowing into a @Nat closure RETURN can be
        # negative (`fn(@Int -> @Nat) { @Int.0 }` applied to -5 returned -5
        # through the @Nat slot on a verify-clean program — the #758 return
        # nat-bind hole reachable only through this closure path).  Guard it
        # PER NARROWING LEAF, exactly as `_compile_fn` does for the top-level
        # return (`_nat_return_leaf_ids` threaded into the body translation,
        # applied by `_guard_nat_return_leaf` at each Block / if-branch / match
        # arm leaf): a whole-body wrap would false-trap a legitimate @Nat leaf
        # of a heterogeneous body (a captured @Nat above i64.MAX reads as a
        # negative i64), and closures emit no `return_call` so no TCO revert is
        # needed.  Alias-aware + refinement-excluded gate: a refinement over
        # @Nat is guarded by the #1032 refined-RETURN guard emitted after the
        # body below — its predicate conjoins the @Nat base's `>= 0`
        # (`_refinement_guard_parts`), so adding the leaf guard here would be a
        # redundant second sign check.  Mirrors the top-level narrow-return
        # gate.  MUST run before `translate_block` so the leaf ids are in
        # place when the body is lowered.  `ret_refined_parts` is computed
        # ONCE and reused by the #1032 guard: `_refinement_guard_parts`
        # emits a loud E618 for a nested-refinement base, and calling it
        # twice would double that diagnostic.
        ret_refined_parts = self._refinement_guard_parts(anon_fn.return_type)
        if (ctx._type_expr_base_is_nat(anon_fn.return_type)
                and ret_refined_parts is None):
            ctx._nat_return_leaf_ids = ctx._collect_narrowing_return_leaves(
                anon_fn.body)
        else:
            # Reset unconditionally, as `_compile_fn` does for the top-level
            # return: each closure gets a fresh WasmContext today, so this
            # branch is insurance against a future shared-ctx refactor
            # leaking a @Nat closure's leaf set into a non-@Nat sibling.
            ctx._nat_return_leaf_ids = set()

        # Compile the body.  Three failure modes are handled:
        #   1. CodegenSkip — translator hit unsupported shape (#626 L3)
        #   2. CodegenInvariantError — codegen bug (#626 L3)
        #   3. body_instrs is None — legacy silent-skip return
        # See the parallel block in vera/codegen/functions.py::_compile_fn
        # for the matching catch in the non-closure path.
        try:
            # #1212: the closure's RETURN is a `@Byte` write boundary, so
            # its body's literal leaves are marked before translation —
            # the same call `_compile_fn` makes, which is what keeps a
            # heterogeneous join lowering identically on both paths.  MUST
            # precede `translate_block`; the `i32.wrap_i64` mirror below
            # only rescues a body the decider calls i64 WHOLE.
            self._mark_byte_return_leaves(
                ctx, anon_fn.return_type, anon_fn.body)
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
        except RecursionError:
            # #933 belt-and-suspenders (see the parallel catch in
            # functions.py::_compile_fn): a derived-helper generator whose
            # per-level frame cost outruns `DERIVED_HELPER_DEPTH_CAP` must not
            # surface a raw traceback from a check-green program.  Degrade to
            # the clean [E602] skip the closure-skip path already emits, which
            # drops the enclosing function too.
            self._harvest_interp_inference_failures(ctx)
            self._warning(
                anon_fn,
                "Closure body exceeded the codegen recursion bound (a deeply "
                "/ non-uniformly recursive type) — closure skipped.",
                rationale="Rendering / comparing a polymorphically-recursive "
                "type would expand without bound at compile time. The "
                "enclosing function will also be dropped to avoid a missing "
                "function-table entry.",
                error_code="E602",
            )
            return None
        # #657: a CodegenInvariantError from the closure body is NOT caught
        # here — it propagates to `_compile_fn`'s handler around
        # `_lift_pending_closures`, which surfaces a single [E699] for the whole
        # function.  Catching it here (the previous behaviour) emitted [E699]
        # AND returned None, so the enclosing fn then also emitted a spurious
        # [E602] "closure skipped" — mixing the compiler-bug and user-skip
        # signals.  See vera/codegen/functions.py and tests/test_codegen_invariant_e699.py.

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

        # Coerce body result if return type is i32 but body produces i64
        # (e.g. an IntLit in a @Byte-returning closure) — the closure-side
        # mirror of `_compile_fn`'s return-boundary coercion (functions.py),
        # and the NINTH @Byte write boundary (#1212).  A closure's return is
        # a Byte write exactly as a named function's is, and only the named
        # path coerced it: `fn(@Bool -> @Byte) { 207 }` behind an `apply_fn`
        # emitted `i64.const 207` into an `(result i32)` and the lifted
        # `$anon_0` failed WASM validation, on a check-green program, while
        # its named twin `fn g(@Bool -> @Byte) { 207 }` ran.  Same gate, same
        # place in the sequence: after the body, before anything that reads
        # the result at `ret_wt` (the #1032 refined-return guard below saves
        # it into an `ret_wt` local, which an i64 result would make
        # ill-typed too).  MUST NOT move above `translate_block`.
        if ret_wt == "i32":
            body_result_type = ctx._infer_block_result_type(anon_fn.body)
            if body_result_type == "i64":
                body_instrs.append("i32.wrap_i64")

        # #1024: emit the refined-formal prologue guards now — AFTER the body
        # compiles (so the `_nat_return_leaf_ids` setup that MUST precede
        # `translate_block` is untouched) and BEFORE the host-import propagation
        # block below, so any ctx state a predicate translation registers (an
        # overflow guard, a Map/Set op) rides the SAME merge the body's does (the
        # #808 fan-in rule).  `_emit_refinement_check` allocs no locals for the
        # predicate, but `ctx.translate_expr` may, so this must also precede the
        # `ctx.extra_locals_wat()` read in the assembly below.  A CodegenSkip
        # while lowering a predicate is caught inside `_emit_refinement_check`
        # (E617, no guard); an AdtEq/CodegenInvariant escape propagates to
        # `_lift_pending_closures` -> a single [E699], exactly as the closure
        # body's own uncaught invariants do (no extra try/except is layered here,
        # matching the closure's existing return-side guards).  The AnonFn has no
        # `decl`, so the trap message is built from its own signature — the shape
        # `_format_refinement_message` produces for a named fn.
        #
        # #1235: the per-COMPONENT guards for a tuple formal / return are
        # emitted here too, from the same `_tuple_component_guard_sites`
        # decomposition the named path reads — see `component_param_checks`
        # above.  Component guards precede their boundary's top-level guard
        # on both sides, exactly as `_compile_fn` and `_compile_postconditions`
        # order them: a refinement OVER a tuple may have its predicate read
        # the components, so those are established first.
        ret_has_components = self._has_guardable_tuple_components(
            anon_fn.return_type)
        refine_guard_instrs: list[str] = []
        if (refined_param_checks or component_param_checks
                or ret_refined_parts is not None or ret_has_components):
            param_sig = ", ".join(
                ast.format_type_expr(p) for p in anon_fn.params)
            ret_sig = ast.format_type_expr(anon_fn.return_type)
            closure_sig = f"fn({param_sig} -> {ret_sig})"
            for value_local, param_te in component_param_checks:
                refine_guard_instrs.extend(
                    self._emit_component_refinement_guards(
                        ctx, closure_sig, param_te, value_local, env,
                        "parameter"))
            for value_local, parts in refined_param_checks:
                predicate, base_name = parts
                msg = (
                    f"Refinement violation in {closure_sig}\n"
                    f"  parameter: {ast.format_expr(predicate)} failed"
                )
                guard = self._emit_refinement_check(
                    ctx, predicate, base_name, value_local, msg, env)
                if guard is not None:
                    refine_guard_instrs.extend(guard)
            # #1032: a REFINED closure RETURN carries a runtime predicate guard
            # over the body's result — the return-side dual of the formal
            # guards above and the closure mirror of the named path's
            # refined-return guard (`_compile_postconditions`, contracts.py):
            # save the result to locals, check the predicate over it, push it
            # back.  The verifier records the refined closure return `tier3`
            # guarded on the strength of THIS guard (the AnonFn refined arm in
            # `_walk_for_nat_binding_obligations`); without it,
            # `fn(@Int -> @Pos) { @Int.0 }` returned -5 — or 0, which clears
            # the @Nat base's `>= 0` — out through the refined slot silently.
            # An i32_pair result (String/Array base) saves both halves and
            # checks over the ptr, exactly as the named i32_pair return guard
            # does; a `@Unit`-based refinement never reaches here
            # (`_refinement_guard_parts` returns None for an erased base, and
            # the verifier records it tier3_unguarded).  Appended to
            # `body_instrs` so the check runs before the GC epilogue re-roots
            # the (now-checked) value.
            if ret_refined_parts is not None or ret_has_components:
                msg = (
                    f"Refinement violation in {closure_sig}\n"
                    f"  return value: "
                    f"{ast.format_expr(ret_refined_parts[0])} failed"
                ) if ret_refined_parts is not None else ""
                if ret_wt == "i32_pair":
                    ptr_l = ctx.alloc_local("i32")
                    len_l = ctx.alloc_local("i32")
                    ret_guard = self._emit_component_refinement_guards(
                        ctx, closure_sig, anon_fn.return_type, ptr_l, env,
                        "return value")
                    if ret_refined_parts is not None:
                        predicate, base_name = ret_refined_parts
                        guard = self._emit_refinement_check(
                            ctx, predicate, base_name, ptr_l, msg, env)
                        if guard is not None:
                            ret_guard.extend(guard)
                    if ret_guard:
                        body_instrs = [
                            *body_instrs,
                            f"local.set {len_l}",
                            f"local.set {ptr_l}",
                            *ret_guard,
                            f"local.get {ptr_l}",
                            f"local.get {len_l}",
                        ]
                elif ret_wt:
                    ret_local = ctx.alloc_local(ret_wt)
                    ret_guard = self._emit_component_refinement_guards(
                        ctx, closure_sig, anon_fn.return_type, ret_local, env,
                        "return value")
                    if ret_refined_parts is not None:
                        predicate, base_name = ret_refined_parts
                        guard = self._emit_refinement_check(
                            ctx, predicate, base_name, ret_local, msg, env)
                        if guard is not None:
                            ret_guard.extend(guard)
                    if ret_guard:
                        body_instrs = [
                            *body_instrs,
                            f"local.set {ret_local}",
                            *ret_guard,
                            f"local.get {ret_local}",
                        ]

        # #820: a @Nat closure body widening into an @Int closure RETURN
        # reinterprets above i64.MAX (u64.MAX -> -1) — the definition-side dual
        # of the closure-argument guard (`_translate_apply_fn`).  The verifier
        # obligates this shallow-syntactically (the AnonFn body is opaque to its
        # SMT layer, so it records tier3), and codegen guards the body's @Int
        # return value here.  Fires only when the declared return is @Int and the
        # body is intrinsically @Nat (`_result_is_nat`) — never a genuine @Int
        # body (which may be legitimately negative).  The #984 narrowing dual
        # is guarded per-leaf during body translation above (`_nat_return_leaf_ids`),
        # not as a whole-body wrap here — see that block for why.
        if (ctx._type_expr_base_is_int(anon_fn.return_type)
                and ctx._result_is_nat(anon_fn.body)):
            body_instrs = ctx._emit_int_widen_guard(body_instrs)

        # Propagate host-import tracking from closure ctx to module level
        self._map_ops_used.update(ctx._map_ops_used)
        self._map_imports.update(ctx._map_imports)
        self._set_ops_used.update(ctx._set_ops_used)
        self._set_imports.update(ctx._set_imports)
        self._decimal_ops_used.update(ctx._decimal_ops_used)
        self._decimal_imports.update(ctx._decimal_imports)
        self._json_ops_used.update(ctx._json_ops_used)
        self._html_ops_used.update(ctx._html_ops_used)
        # #841: fused async/await inside a lifted closure body registers
        # its host imports on the closure ctx (the _scan_io_ops AnonFn
        # branch also covers these — same belt-and-braces as #808).
        self._async_ops_used.update(ctx._async_ops_used)
        # #808: a #798 integer-overflow guard inside a lifted closure body sets
        # this on the closure ctx; OR it into the module ``self`` so
        # ``_assemble_module`` emits the ``vera.overflow_trap`` import (same
        # propagation the per-function merge does in functions.py).
        self._needs_overflow_trap = (
            self._needs_overflow_trap or ctx._needs_overflow_trap
        )
        # #773: structural-Eq helpers generated inside a lifted closure body.
        self._adt_eq_helpers.update(ctx._adt_eq_helpers)
        # #924: recursive show/hash helpers generated inside a lifted closure.
        self._show_hash_helpers.update(ctx._show_hash_helpers)

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
            # #1255: the REPRESENTATION base, as at the param case above —
            # `fn(… -> @SmallByte)` under `type SmallByte = { @Byte | … }`
            # returns a Byte, and pushing it rooted a 0..255 value.
            ret_is_pointer = is_gc_pointer_base(
                self._family_base_te(anon_fn.return_type),
            )
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
                elif kind == "i32" and is_gc_pointer_base(
                    # #1255: a capture is carried by its SLOT NAME (a free
                    # variable has no type expression here), so the
                    # representation base comes from the name resolver
                    # rather than from `_family_base_te` — the same hop
                    # `_slot_name_to_wasm_type` took to decide `kind`, so
                    # the two conjuncts again describe one type.
                    ctx._resolve_base_type_name(tname)
                ):
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
        # #1024: refined-formal prologue guards run after all prologue setup (GC
        # roots + capture loads) and BEFORE the body, so a refinement-violating
        # argument traps at closure entry — the closure-side analogue of
        # `_compile_fn` prepending its refined-param guards to the body.
        for instr in refine_guard_instrs:
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
