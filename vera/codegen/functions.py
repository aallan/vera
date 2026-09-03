"""Mixin for function body compilation (Pass 2).

Compiles individual function declarations to WAT text, including
parameter allocation, body translation, and function assembly.
"""

from __future__ import annotations

import functools
from typing import TYPE_CHECKING, cast

from vera import ast
from vera.skip import AdtEqNotDerivableError, CodegenInvariantError, CodegenSkip
from vera.codegen.compilability import contract_exprs
from vera.codegen.tail_position import compute_tail_call_sites
from vera.monomorphize import mangle_type_name
from vera.slots import effect_op_result_names, type_expr_slot_name
from vera.wasm import WasmContext, WasmSlotEnv
from vera.wasm.helpers import (
    CellNames,
    gc_shadow_push,
    is_gc_pointer_base,
)

if TYPE_CHECKING:
    from vera.types import SpanTypeTable


class FunctionCompilationMixin:
    """Methods for compiling function bodies to WAT."""

    def _emit_adt_eq_not_derivable(
        self, ctx: WasmContext, nde: AdtEqNotDerivableError,
        decl: ast.FnDecl,
    ) -> None:
        """Emit the E613 diagnostic for a direct `==` on a non-Eq ADT.

        Shared by the function-body and closure-lift catch sites so the
        user-facing message cannot drift between the two (#773 / PR #870
        review).
        """
        from vera.errors import Diagnostic

        self._harvest_interp_inference_failures(ctx)
        loc, source_line = self._diag_location(
            nde.node if nde.node is not None else decl
        )
        self.diagnostics.append(Diagnostic(
            description=(
                f"Type '{nde.type_name}' does not satisfy ability 'Eq'; "
                f"`==` requires both operands to be Eq."
            ),
            location=loc,
            source_line=source_line,
            rationale=(
                "Structural Eq derivation requires every constructor "
                "field to be itself Eq; this type has a field with no "
                "Eq semantics (or an unresolved type argument), so no "
                "equality can be generated."
            ),
            fix=(
                f"Compare Eq-derivable values instead. An ADT derives Eq "
                f"structurally when every constructor field is itself Eq "
                f"— restructure '{nde.type_name}' so its fields are Eq "
                f"primitives or Eq ADTs (Array/Map/handle fields are "
                f"not Eq)."
            ),
            spec_ref='Chapter 9, Section 9.8 "Abilities"',
            severity="error",
            error_code="E613",
        ))

    def _emit_contract_predicate_skip(
        self, ctx: WasmContext, skip: CodegenSkip, decl: ast.FnDecl,
    ) -> None:
        """Emit the E602 warning for a ``CodegenSkip`` in a contract predicate.

        A ``hash`` / ``show`` (or any other unsupported construct) inside a
        ``requires`` / ``ensures`` / refinement guard raises ``CodegenSkip``
        during predicate lowering.  Surface the SAME clean E602 "function
        skipped" warning the body path emits (line ~414), pointing at the
        unsupported node's span, instead of letting the exception escape as a
        Python traceback on a ``check``-green program (#922).
        """
        self._harvest_interp_inference_failures(ctx)
        self._warning(
            skip.node if getattr(skip.node, "span", None) else decl,
            f"Function '{decl.name}' contract predicate contains unsupported "
            f"{type(skip.node).__name__}: {skip.reason} — function skipped.",
            rationale="The WASM backend does not yet support lowering all "
            "Vera expressions to a runtime contract check. This function "
            "will not appear in the compiled output.",
            error_code="E602",
        )

    def _emit_contract_predicate_degradation(
        self, ctx: WasmContext,
        exc: AdtEqNotDerivableError | CodegenSkip,
        decl: ast.FnDecl,
    ) -> None:
        """Dispatch a contract-predicate degradation to its clean diagnostic.

        An ``AdtEqNotDerivableError`` (a non-Eq composite ``==``) becomes the
        E613 the body / closure / postcondition paths emit; a ``CodegenSkip``
        (an unsupported ``hash`` / ``show`` / …) becomes the E602 the body path
        emits.  Shared by every contract-predicate catch site — precondition,
        refinement-parameter guard, and postcondition — so a user program can
        NEVER surface a Python traceback from a contract predicate (#922,
        contract §516 / §522 / §589).
        """
        if isinstance(exc, AdtEqNotDerivableError):
            self._emit_adt_eq_not_derivable(ctx, exc, decl)
        else:
            self._emit_contract_predicate_skip(ctx, exc, decl)

    def _mark_byte_return_leaves(
        self, ctx: WasmContext, return_type: ast.TypeExpr, body: ast.Block,
    ) -> None:
        """Mark *body*'s literal leaves when the return resolves to `@Byte`.

        The return-boundary arm of #1212's ONE marking, shared by the named
        path (`_compile_fn`) and the closure path
        (`_compile_lifted_closure`) so the two cannot decide a return width
        differently — which is exactly what the ninth and tenth shapes were.
        The declared return resolves through `WasmContext._boundary_base`,
        the ONE representation-base derivation every #1212 boundary now
        shares (#1256), so a refined `@Byte` alias is a Byte boundary here
        as it is at the `apply_fn` argument and the `throw` payload.
        """
        ctx._mark_byte_write_value(body, ctx._boundary_base(return_type))

    def _lift_closures_or_drop(
        self, ctx: WasmContext, decl: ast.FnDecl,
    ) -> bool:
        """Lift *ctx*'s pending closures; True means drop the function.

        The ONE degradation net around ``_lift_pending_closures``, driven
        TWICE per function (#1245): once after the body, once after
        ``_compile_postconditions`` — which lowers the refined-RETURN guard,
        a tuple return's component guards and every ``ensures(...)``
        predicate, any of which may construct a closure that registers on
        ``ctx`` only at that point.  Both passes need the identical
        treatment of a failed lift, so the handling lives here rather than
        being written out twice.

        If any closure body failed to compile, the enclosing fn is dropped
        rather than emitting a module with a ``call_indirect`` to a missing
        function-table entry — closes #636.  The closure body's own
        diagnostics (E615 from interpolation failures, generic E602 from
        translation failures) were already emitted by
        ``_compile_lifted_closure``'s harvest; a specific E602 is added here
        noting that the parent is being dropped *because* of the closure
        failure, so the user can correlate the cause with the effect.
        """
        try:
            closure_failed = self._lift_pending_closures(ctx)
        except (AdtEqNotDerivableError, CodegenSkip) as exc:
            # #773 / PR #870 review: a direct `==` on a non-Eq-derivable ADT
            # inside a CLOSURE body — same clean E613 as the function-body
            # catch (a user error, not a compiler bug).  MUST precede the
            # parent CodegenInvariantError catch below (subclass).
            # #922: also degrade a `CodegenSkip` (an unsupported `hash`/`show`
            # inside a closure) to a clean E602 rather than an uncaught
            # traceback, via the shared contract-predicate dispatcher.
            # #1185 (PR #1192 review): record the failed lift here too — an
            # escape from `_lift_pending_closures` leaves `_closure_table`
            # empty exactly as the rolled-back `closure_failed` path below
            # does, so the orphan-carrier blame chain must be able to select
            # THIS function as the [E602] root; without the record, the
            # carrier's [E620] falls back to the no-closure-in-program
            # wording, which is false for this shape.  No check-green
            # program reaches this branch today (a closure-body skip is
            # caught inside `_compile_lifted_closure`, and non-Eq `==` is
            # E243-gated in body and refinement position since #928) — it
            # is the defensive sibling of the append below, pinned by the
            # stubbed-lift regression in
            # tests/test_codegen_orphan_call_indirect_1185.py.
            self._closure_lift_skips.append(decl.name)
            self._emit_contract_predicate_degradation(ctx, exc, decl)
            return True
        except CodegenInvariantError as inv:  # #657: a closure-body invariant
            # violation (a codegen bug) propagates out of
            # `_compile_lifted_closure` to here and surfaces as ONE [E699] for
            # the whole function — NOT the [E602] "closure skipped" warning
            # below, which is reserved for a user-facing unsupported-construct
            # skip.  Swallowing it in the closure helper (its previous
            # behaviour) mixed the compiler-bug and user-skip signals: the
            # helper emitted [E699] AND returned None, so this path then also
            # emitted [E602].  Covered by tests/test_codegen_invariant_e699.py.
            # #1185 (PR #1192 review, outside-diff): record the failed lift
            # on THIS route too — the [E699] is an error, but the module is
            # still assembled (compilation degrades, it does not abort), so
            # the orphan-carrier blame chain runs and must be able to name
            # this function as the root instead of falling back to the
            # false no-closure-in-program wording.  Pinned by the
            # `invariant_error` leg of the stubbed-lift regression in
            # tests/test_codegen_orphan_call_indirect_1185.py.
            self._closure_lift_skips.append(decl.name)
            self._harvest_interp_inference_failures(ctx)
            self._error(
                inv.node if inv.node is not None else decl,
                f"Internal compiler error while compiling '{decl.name}': "
                f"{inv.msg}",
                rationale="This is a codegen invariant violation — the type "
                "checker should have rejected the input before it reached this "
                "point.  Please file a bug report with the offending program.",
                error_code="E699",
            )
            return True
        if closure_failed:
            # #1185: record the rolled-back lift.  A lift that rolls back
            # is what leaves `_closure_table` empty, and an empty table
            # orphans every `call_indirect` elsewhere in the module — the
            # drop-propagation pass blames this function for those
            # carriers, so the user gets one root cause, not two.
            self._closure_lift_skips.append(decl.name)
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
            return True
        return False

    def _compile_fn(
        self, decl: ast.FnDecl, *, export: bool = True,
        module_renames: dict[str, str] | None = None,
        imported: bool = False,
        module_tables: (
            tuple[SpanTypeTable | None, SpanTypeTable | None] | None
        ) = None,
        where_scope: frozenset[str] = frozenset(),
    ) -> str | None:
        """Compile a single function to WAT.

        Returns the WAT function string, or None if not compilable
        (with a warning diagnostic).

        *where_scope* (#1299) is the ``where``-helper names lexically in
        scope in *decl*'s body; with the namespace this compile is running
        under it decides which bare names the emitted body may treat as
        denoting a user declaration.  See ``_scoped_fn_names``.

        *imported* is True when *decl* is an imported module body compiled into
        this flat WASM module (Pass 2.5 / 2.6).  The checker's resolved- /
        target-type side-tables are keyed by span alone (``(line, col, end_line,
        end_col)`` — no file identity), so the MAIN-file tables
        (``self._expr_semantic_types`` / ``self._expr_target_types``) must NOT be
        consulted for an imported body: an imported expression whose span
        coincides with a main-file entry would pick up the WRONG type and, at a
        tuple/array widen site, emit a SPURIOUS @Nat -> @Int guard that traps a
        legal @Nat (confirmed cross-module collision, #986 review).

        *module_tables* (#987) is the imported module's OWN
        ``(expr_semantic_types, expr_target_types)`` pair, keyed by that module's
        node spans — so looking *decl*'s spans up in it is correct, not a
        cross-file collision.  When supplied (the normal path from Pass 2.5 / 2.6
        via ``CheckArtifacts.module_artifacts``), the imported body gets the same
        per-component target-type recovery a same-file body does, so its
        array-element / tuple-construction @Nat -> @Int widening guard fires
        through the import door.  When absent (a caller that threaded no module
        artifacts), we fall back to suppression (both tables ``None``) — the
        pre-#987 behaviour: those component sites stay unguarded, never
        false-guarded.  Fn-type-based recovery (closure formal / return types) is
        NOT span-keyed and is unaffected either way.
        """
        # #987: an imported body's span-keyed tables are ITS module's own (or
        # None when none were threaded) — never the main-file tables, whose
        # colliding span would mis-key an imported operand.  Bound here so the
        # two ``ctx.set_expr_*`` calls below stay readable.  Cast to the
        # ``object``-valued shape the ``WasmContext`` setters expect: a ``Type``
        # dict is not a ``dict[..., object]`` under mypy's dict invariance, but
        # the values genuinely are ``Type`` instances (which ARE objects), so
        # the widening is sound.
        imported_semantic = cast(
            "dict[tuple[int, int, int, int], object] | None",
            module_tables[0] if module_tables is not None else None,
        )
        imported_target = cast(
            "dict[tuple[int, int, int, int], object] | None",
            module_tables[1] if module_tables is not None else None,
        )
        # #851 — diagnostics emitted while compiling a prelude-injected
        # function (or a mono clone of one — the mangler's `base$Types`
        # names strip back to a prelude base) must resolve their spans
        # against the prelude buffer, not the user's file.  Every
        # `_compile_fn` entry overwrites the flag, so it is always
        # current for the function whose diagnostics are being emitted;
        # the Pass-2 loops in `compile_program` reset it when done.
        self._in_prelude_fn = (
            decl.name.split("$")[0] in self._prelude_fn_names
        )

        # Check if function is compilable
        if not self._is_compilable(decl):
            return None

        # Build effect_ops mapping for State<T> and Exn<E> operations.
        # `effect_op_result_wt` records each value-producing op's result WAT
        # type (its State<T> parameter's WAT type) so `_infer_expr_wasm_type`
        # can type a bare `get(())` in constructor-arg / match-scrutinee
        # position (#914 A1/A2).  Composite type args (`Tuple<Int, Int>`,
        # `Option<Int>`) are routed through the injective `mangle_type_name`
        # escaper (#775/#914 B) so the `state_*`/`exn_*` WAT identifiers stay
        # legal — raw `<`, `>`, `,`, ` ` are illegal in a WAT identifier.
        effect_ops: dict[str, tuple[str, bool]] = {}
        effect_op_result_wt: dict[str, str | None] = {}
        effect_op_result_vera: dict[str, str | None] = {}
        effect_op_cells: dict[str, CellNames] = {}
        # #1285: cell family -> getter import, for `new(State<T>)`.
        state_getters: dict[str, str] = {}
        # #1207: the op → Vera result-type table, from the ONE derivation
        # mono discovery also reads.  Source-order-first-wins and the
        # unnameable-argument skip live in the shared builder, so the two
        # consultors cannot drift.  Shadowing is NOT filtered into these
        # registries (#1284): they record which cell each op name reaches,
        # and whether a given call site IS the op is asked at that site,
        # through `_bare_call_denotes_op`.  Withholding the entry here
        # answered both questions with one table and made the second answer
        # unavailable — `State.get(())` in a function that also declares
        # `fn get` compiled to `call $vera.get` and failed to link.
        row_op_results = (
            effect_op_result_names(decl.effect.effects)
            if isinstance(decl.effect, ast.EffectSet) else {}
        )
        if isinstance(decl.effect, ast.EffectSet):
            # SOURCE ORDER, first wins — the checker's rule for a bare op
            # (spec §7.4) and for its type arguments, so the two agree on
            # which cell a bare `get`/`put` names.  A row may legitimately
            # carry two instantiations of one effect (§7.3.3:
            # `effects(<State<Int>, State<Bool>>)` is two independent
            # cells); this loop used to let the LAST one overwrite the
            # first, emitting `state_get_Bool` (i32) where the checker had
            # typed the call `Int` (i64) — invalid WASM from a check-green
            # program.  Every assignment below is therefore guarded on the
            # op name not already being mapped.
            for eff in decl.effect.effects:
                if (isinstance(eff, ast.EffectRef) and eff.name == "State"
                        and eff.type_args and len(eff.type_args) == 1):
                    # The alias-OPAQUE source spelling, kept for exactly one
                    # role: the #1006 Vera-name mirror below.
                    type_name = type_expr_slot_name(eff.type_args[0])
                    if type_name:
                        # The import NAME keys on the resolved cell FAMILY
                        # (matching `_check_state_type` registration, #1205
                        # / #1209); the Vera-name mirror below stays the
                        # SOURCE name (note it also feeds the #1006/#914-A2
                        # clone-naming contract for a `get(())` array
                        # element driving a generic instantiation — see the
                        # tracked mono discovery desync).
                        # IDENTITY names the import; REPRESENTATION is
                        # recorded beside it so a `put` call site can
                        # pick its #1203 write guard without slicing
                        # the family back out of the mangled name
                        # (#1218).
                        cell = CellNames(
                            family=self._family_name_te(eff.type_args[0]),
                            base=self._family_base_te(eff.type_args[0]),
                        )
                        mangled = mangle_type_name(cell.family)
                        # #1285: the family-keyed getter, recorded for EVERY
                        # State in the row rather than only the first.  A
                        # `new(State<T>)` in a postcondition names its family
                        # the way `old(State<T>)` does, so it reads this
                        # table; the name-keyed `effect_ops["get"]` beside it
                        # stays source-order-first-wins, which is the right
                        # rule for a bare `get(())` that names no family and
                        # the wrong one for a contract that does.
                        state_getters.setdefault(
                            cell.family, f"$vera.state_get_{mangled}")
                        if "get" not in effect_ops:
                            effect_ops["get"] = (
                                f"$vera.state_get_{mangled}", False
                            )
                            # State<T>'s T is validated non-pair /
                            # non-unsupported by `_check_state_type` (E607),
                            # so this yields a scalar (i64/f64/i32) or an
                            # ADT-pointer (i32) — exactly the op's result WT.
                            effect_op_result_wt["get"] = (
                                self._type_expr_to_wasm_type(eff.type_args[0])
                            )
                            # #1006: the VERA-name mirror — `_infer_vera_type`
                            # needs it to type a `get(())` array-literal
                            # element (the WAT type above is layout-ambiguous).
                            # #1207: read from the shared table rather than
                            # re-derived here, so mono discovery's copy of
                            # this answer is the SAME answer.
                            effect_op_result_vera["get"] = row_op_results.get(
                                "get")
                            effect_op_cells["get"] = cell
                        if "put" not in effect_ops:
                            effect_ops["put"] = (
                                f"$vera.state_put_{mangled}", True
                            )
                            effect_op_cells["put"] = cell
                elif (isinstance(eff, ast.EffectRef) and eff.name == "Exn"
                        and eff.type_args and len(eff.type_args) == 1):
                    type_name = type_expr_slot_name(eff.type_args[0])
                    if type_name and "throw" not in effect_ops:
                        # The tag name resolves like the State import
                        # family (matching `_check_exn_type`, #1205/#1209).
                        # IDENTITY names the tag; REPRESENTATION rides
                        # beside it in `effect_op_cells` exactly as the
                        # State pair above (#1218), because the throw call
                        # site is a WRITE boundary and needs the payload's
                        # width: `throw(5)` into `Exn<{ @Byte | … }>` put an
                        # `i64.const` under an i32 tag and the module failed
                        # WASM validation (#1269).
                        # The payload's TYPE EXPRESSION rides along (#1268):
                        # the throw call site guards a refined payload by
                        # lowering its predicate, which neither name carries.
                        exn_cell = CellNames(
                            family=self._family_name_te(eff.type_args[0]),
                            base=self._family_base_te(eff.type_args[0]),
                            type_expr=eff.type_args[0],
                        )
                        effect_ops["throw"] = (
                            f"$exn_{mangle_type_name(exn_cell.family)}",
                            False,
                        )
                        effect_op_cells["throw"] = exn_cell

        # Flatten ADT layouts into ctor_name -> layout for WasmContext
        ctor_layouts = {}
        ctor_to_adt: dict[str, str] = {}
        for adt_name, layouts in self._adt_layouts.items():
            ctor_layouts.update(layouts)
            for ctor_name in layouts:
                ctor_to_adt[ctor_name] = adt_name
        # #1253/#1316: the NAMESPACE's data types, not every layout this
        # compilation registered.  `_adt_layouts` is one map across every
        # absorbed namespace; `_alias_env.data_types` is the set
        # `_adt_members_in_scope` scoped to the module (or the prelude) whose
        # declaration is compiling, which is what the checker saw.  Handing
        # the wasm layer the flat map made its `base in _adt_type_names`
        # tests answer over a larger set than `naming._resolve_named` does.
        adt_type_names = set(self._alias_env.data_types)

        ctx = WasmContext(
            self.string_pool,
            effect_ops=effect_ops,
            effect_op_result_wt=effect_op_result_wt,
            effect_op_result_vera=effect_op_result_vera,
            effect_op_cells=effect_op_cells,
            state_getters=state_getters,
            ctor_layouts=ctor_layouts,
            adt_type_names=adt_type_names,
            generic_fn_info=getattr(self, "_generic_fn_info", None),
            generic_constrained_vars=getattr(
                self, "_generic_constrained_vars", None),
            ctor_to_adt=ctor_to_adt,
            known_fns=set(self._fn_sigs.keys()),
            # #1299: the ownership predicate's table is the LEXICAL one —
            # `known_fns` above stays flat for the guard rail, which asks
            # whether a resolved target has a symbol, not whose name it is.
            scoped_fns=self._scoped_fn_names(where_scope, decl.name),
            ctor_adt_tp_indices=getattr(self, "_ctor_adt_tp_indices", None),
            adt_tp_counts=getattr(self, "_adt_tp_counts", None),
            adt_tp_param_names=getattr(self, "_adt_tp_param_names", None),
        )
        # #773 / PR #870 review: the direct `==` path checks structural-Eq
        # derivability through the SAME gate the generic constraint path uses.
        ctx.set_adt_eq_derivable(self._adt_satisfies_eq)
        # #932: share the truncated→full constrained-var name map so the direct
        # `==` path inside a generic clone body resolves a truncated slot type
        # (`List<List>`) on its fully-nested name for the derivability decision.
        ctx.set_eq_full_type_names(getattr(self, "_eq_full_type_names", {}))
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
        # #841: Future<Result<String, String>>-returning fn names, for the
        # await lowering's directly-awaited-call check (computed once in
        # core.py, shared with the _scan_io_ops pre-scan).
        ctx.set_future_ret_fns(
            self._future_ret_fns, self._future_ret_module_fns,
        )
        # #798: resolved-type side-table for the integer-overflow guard's
        # Int/Nat operand classifier (kept in lockstep with the verifier).
        # #987: for an imported body this is ITS module's table (correct spans)
        # or None — never the main-file table, whose colliding span would
        # mis-classify an imported operand (see the *imported* note above).
        ctx.set_expr_semantic_types(
            imported_semantic if imported else self._expr_semantic_types)
        # #820: target-type side-table for the @Nat -> @Int widening guard's
        # per-component target-type recovery (tuple component / array element
        # / heterogeneous if-arm), the codegen dual of ``_target_type_of``.
        # #987: an imported body uses its own module's table (so its widen guard
        # fires through the import door) or None; the main-file table would
        # false-guard a colliding span.
        ctx.set_expr_target_types(
            imported_target if imported else self._expr_target_types)
        # #747: per-parameter concrete-@Nat flags for the call-site
        # runtime narrowing guard.
        ctx.set_fn_nat_params(self._fn_nat_params)
        # #813: per-parameter concrete-@Int flags for the call-site
        # runtime @Nat -> @Int widening guard.
        ctx.set_fn_int_params(self._fn_int_params)
        # #865: per-parameter concrete-@Byte flags for the call-site
        # int-literal → i32.const coercion.
        ctx.set_fn_byte_params(self._fn_byte_params)
        # Provide the naming environment so closures can resolve FnType
        # return types.  One value, so the alias bodies and their parameter
        # lists cannot be handed over half-updated (#1184 / #1208).
        ctx.set_alias_env(self._alias_env)
        # #1268: the §2.6.5 predicate lowering, bound to THIS context, for
        # the boundaries the context discovers mid-expression (a `throw`
        # payload).  Installed here rather than passed per call so the two
        # halves of a guard — representation and lowering — cannot be paired
        # with different contexts.
        ctx.set_refinement_guard_emitter(
            functools.partial(self._emit_boundary_refinement_guard, ctx),
        )
        ctx.set_closure_id_start(self._next_closure_id)
        ctx.set_closure_sigs(self._closure_sigs)
        # #814 §8.5.3: module-qualified call target table, so a ``m::f`` call
        # whose bare name is shadowed by a local resolves to the module's
        # body (emitted under a distinct ``mod$…`` name) rather than the local.
        ctx.set_module_qualified_targets(self._module_qualified_targets)
        # #814/#774: shadowed imported-generic qualified-call bases, so a
        # `m::gen(…)` whose bare name a local shadows resolves to the module
        # generic's clone rather than the local shadow.
        ctx.set_module_qualified_generic_bases(
            self._module_qualified_generic_bases,
        )
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
            # Track i32 pointer params.  `is_gc_pointer_base` over the
            # formal's REPRESENTATION base (#1255) — the closure path's
            # twin, and the slot name pushed above is deliberately NOT the
            # input: that one is the syntactic head (it has to be, it keys
            # the binding table), which classified a refined or aliased
            # `@Byte` formal as a heap pointer.
            if wt == "i32" and is_gc_pointer_base(
                self._family_base_te(param_te)
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

        # Scan the function for handle[State<T>] / handle[Exn<E>] expressions
        # to register imports and tags.  #1210: a handler naming a cell or
        # payload type the backend cannot compile drops the function here with
        # its own [E607] / [E612], the same verdict the declared-effect gate
        # reaches — the walk used to skip such a type in silence and leave the
        # lowering to emit calls to imports that were never declared.  The
        # walk covers the contract predicates too (round 2): they are lowered
        # code, so a handler in one is emitted like any other.
        if not self._scan_body_for_state_handlers(decl.body, decl):
            return None

        # Scan body for IO qualified calls to register per-op imports
        self._scan_io_ops(decl.body)
        # #823: also scan the contract predicates.  Markdown / regex host
        # imports are registered ONLY by this scan (they have no per-function
        # `ctx` set-site, unlike map/set/http/…), and the scan is otherwise
        # body-only — so an `md_*` / `regex_*` builtin inside a runtime-checked
        # `requires(...)` / `ensures(...)` would emit an orphaned
        # `call $vera.<name>` with no import declaration and fail WAT
        # compilation.  Contracts are pure, so the QualifiedCall (IO / Http /
        # Inference / Random) branches of the scan never fire here — except
        # through a handler clause body, which is ordinary code.
        # `contract_exprs` is the shared enumeration (#1210 round 2): the
        # `getattr(c, "expr")` shortcut this replaced skipped `decreases`,
        # whose measure lives in `exprs`.
        for _pred in contract_exprs(decl.contracts):
            self._scan_io_ops(_pred)
        # #1210 round 5: and the SIGNATURE's refinement predicates, which are
        # lowered as boundary guards in this function's prologue/epilogue.
        # They are reached through the alias table, not structurally from the
        # body, so nothing the recursion does can find them.
        for _pred in self._signature_refinement_predicates(decl):
            self._scan_io_ops(_pred)

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

        # #758/#983 — per-narrowing-leaf @Int->@Nat return guard.  Collect the
        # tail-position return leaves that narrow into a bare @Nat return so
        # each is guarded inline at emission (mirroring the verifier 7d leaf
        # descent), instead of wrapping the WHOLE body — which reverted EVERY
        # `return_call` and broke TCO for a non-narrowing @Nat->@Nat recursive
        # tail call (`drain`, which stack-exhausted at depth).  Alias-aware
        # (`type Count = Nat`) via `_boundary_base` — the ONE representation-base
        # derivation the `throw` payload and the `apply_fn` signature also ask
        # (#1256).  It resolves the type EXPRESSION, where the
        # `_resolve_base_type_name(_type_expr_to_slot_name(...))` spelling it
        # replaces chased the alias by NAME and dropped its type arguments:
        # `type Ident<T> = T; type Count = Ident<Nat>;` answered the bare head
        # `Ident`, this gate stayed shut, and `f(0 - 5)` returned -5 through the
        # `@Nat` slot — the #983 silent negative, one spelling over.  Still
        # refined-excluded (`{ @Nat | P }` / an alias to one stays on the 7b
        # refinement-boundary path) via `_refinement_guard_parts`, a SEPARATE
        # conjunct untouched by the base swap even though `_boundary_base`
        # strips the refinement wrapper.  Exactly as the whole-body
        # narrow-return gate below.  A narrowing leaf that is itself a tail call
        # (an @Int-returning call) is removed from `tail_sites` so it lowers to
        # a plain `call` — the appended guard runs AFTER it, which `return_call`
        # would skip.
        nat_leaf_ids: set[int] = set()
        if (decl.body is not None
                and ctx._boundary_base(decl.return_type) == "Nat"
                and self._refinement_guard_parts(decl.return_type) is None):
            nat_leaf_ids = ctx._collect_narrowing_return_leaves(decl.body)
        ctx._nat_return_leaf_ids = nat_leaf_ids

        # #820 FIX-1 — a @Nat arm of a heterogeneous @Int-join if/match is
        # widen-guarded PER-ARM (`_emit_int_widen_guard`, appended AFTER the arm
        # body).  A call inside such an arm that lowered to `return_call` would
        # return before the appended guard runs, leaving it DEAD (a @Nat above
        # i64.MAX silently reinterprets to a negative @Int) — the widen sibling
        # of the #983 narrowing-leaf hazard.  Subtract those call ids from
        # `tail_sites` so they lower to a plain `call` the guard can follow.  The
        # collector uses the SAME `_is_hetero_int_widen_join` gate as the emitters,
        # so a call is only stripped if its arm is actually guarded.
        hetero_widen_ids: set[int] = set()
        if decl.body is not None:
            hetero_widen_ids = ctx._collect_hetero_widen_arm_calls(decl.body)

        ctx.set_tail_call_context(
            tail_sites - nat_leaf_ids - hetero_widen_ids,
            self_ret_wt=ret_wt if ret_wt != "unsupported" else None,
        )

        # Compile precondition checks + refinement-parameter entry guards.
        #
        # #922: BOTH the precondition (`_compile_preconditions`) and the
        # refinement-guard (`_emit_refinement_check` /
        # `_emit_component_refinement_guards`) lower a contract-position
        # predicate via `translate_expr`, so a non-Eq composite `==` raises
        # `AdtEqNotDerivableError` and an unsupported `hash`/`show` raises
        # `CodegenSkip` — exactly as the body / closure / postcondition paths do.
        # These sites sat OUTSIDE any degradation try/except, so the exception
        # escaped uncaught (a Python traceback on a `check`-green program).
        # Wrap them in the SAME `(AdtEqNotDerivableError, CodegenSkip)`
        # degradation the postcondition path uses: an `AdtEqNotDerivableError`
        # becomes a clean E613, a `CodegenSkip` a clean E602, and the function
        # is dropped.  A `requires(...)` may *assume* the refined parameters'
        # invariants, so it runs after the refinement guards emitted below (the
        # call stays here so its ctx side effects are unchanged; only the
        # emitted-instruction order is reversed).
        try:
            precond_instrs = self._compile_preconditions(ctx, decl, env)

            # #746: refined parameters carry a runtime predicate guard at
            # entry — a refinement is the parameter's *type* invariant, so an
            # untrusted (incl. FFI/public) caller passing a violating value traps
            # via $vera.contract_fail rather than the function relying on an
            # invariant the value never established.  Emitted *before* the
            # explicit preconditions: a `requires(...)` may itself depend on the
            # invariant (e.g. `requires(10 / @NonZero.0 > 0)` would trap on the
            # division before the guard could report the boundary violation), so
            # the guard must establish the refinement first.
            refine_guard_instrs: list[str] = []
            # #746 PR-review: per-component boundary guards for tuple params — a
            # `Tuple<PosInt, Int>` carries no top-level refinement, so an FFI
            # caller passing a refinement-violating component would otherwise
            # slip past the callee's entry checks (the verifier *assumes* the
            # component holds).  Emitted BEFORE the top-level refined guard
            # below: a refinement OVER a tuple (`{ @Tuple<PosInt, Int> | P }`)
            # has P potentially read the components, so the components must be
            # established first (CR PR-review).
            for value_local, param_te in component_param_checks:
                refine_guard_instrs.extend(
                    self._emit_component_refinement_guards(
                        ctx, ast.format_fn_signature(decl), param_te,
                        value_local, env, "parameter"))

            for value_local, param_te in refined_param_checks:
                parts = self._refinement_guard_parts(param_te)
                if parts is None:  # pragma: no cover — collected only when not None
                    continue
                predicate, base_name = parts
                msg = self._format_refinement_message(
                    decl, param_te, "parameter")
                guard = self._emit_refinement_check(
                    ctx, predicate, base_name, value_local, msg, env)
                if guard is not None:
                    refine_guard_instrs.extend(guard)
        except (AdtEqNotDerivableError, CodegenSkip) as exc:
            self._emit_contract_predicate_degradation(ctx, exc, decl)
            return None
        except CodegenInvariantError as inv:  # #939: complete the #922 net.
            # A `@T.n` read in a `requires(...)` clause of a generic
            # instantiated at Unit hits the dangling-slot invariant in
            # `_translate_slot_ref`; pre-#939 this precond `try` caught only
            # `(AdtEqNotDerivableError, CodegenSkip)`, so it escaped `_compile_fn`
            # as a raw traceback on a `check`-green program.  Mirror the body /
            # closure / postcondition paths: surface ONE loud [E699] (a compiler
            # bug — E206 should have rejected it at check).  MUST follow the
            # `(AdtEqNotDerivableError, CodegenSkip)` catch above (subclass).
            # Covered by tests/test_codegen_invariant_e699.py.
            self._harvest_interp_inference_failures(ctx)
            self._error(
                inv.node if inv.node is not None else decl,
                f"Internal compiler error while compiling '{decl.name}': "
                f"{inv.msg}",
                rationale="This is a codegen invariant violation — the type "
                "checker should have rejected the input before it reached this "
                "point.  Please file a bug report with the offending program.",
                error_code="E699",
            )
            return None

        pre_instrs = refine_guard_instrs + precond_instrs

        # #1172: the runtime decreases guard.  The entry sequence saves
        # this function's chain state, evaluates the measure components,
        # traps (via $vera.contract_fail) when a live previous activation's
        # measure fails to lexicographically decrease while staying
        # non-negative, and records the new baseline; the restores are
        # emitted at the function's exit (after the postconditions,
        # below).  Placed after the preconditions: the measure may rely
        # on the invariants requires() establishes (e.g. a division), and
        # spec §5.6.1(1) has the measure evaluated at entry over the
        # parameters, which the body cannot mutate.
        try:
            dec_entry_instrs, dec_restore_instrs, dec_self_tail = (
                self._compile_decreases_entry(ctx, decl, env)
            )
        except (AdtEqNotDerivableError, CodegenSkip) as exc:
            # The measure is a contract predicate: degrade through the
            # same net as the pre/postcondition paths — a check-green
            # program must never surface a raw traceback (#922).
            self._emit_contract_predicate_degradation(ctx, exc, decl)
            return None
        except CodegenInvariantError as inv:
            # Mirror the precondition net's #939 arm: one loud [E699].
            self._harvest_interp_inference_failures(ctx)
            self._error(
                inv.node if inv.node is not None else decl,
                f"Internal compiler error while compiling '{decl.name}': "
                f"{inv.msg}",
                rationale="This is a codegen invariant violation — the type "
                "checker should have rejected the input before it reached "
                "this point.  Please file a bug report with the offending "
                "program.",
                error_code="E699",
            )
            return None
        pre_instrs = pre_instrs + dec_entry_instrs

        # Snapshot old state for postcondition old() references.  This call
        # sits OUTSIDE the body's CodegenSkip net (round-7 review, F2: a
        # raise from the snapshot's family resolution escaped as a crash on
        # a check-green program), so it carries its own — kept as
        # defence-in-depth now that `_family_name_te` is total (#1209), for
        # the same reason the boundary had a net at all: nothing else here
        # would degrade a skip to a diagnostic.
        try:
            snapshot_instrs = self._snapshot_old_state(ctx, decl)
        except CodegenInvariantError as inv:  # PR #1283 review
            # The arm this boundary was missing.  `state_type_arg` raises
            # `CodegenInvariantError`, not `CodegenSkip`, for an `old(E)`
            # whose `E` is not `State<T>` — and the checker types `old(E)`
            # as `UnknownType`, which satisfies a `Bool` postcondition, so
            # `ensures(old(IO))` is check-green and reached this raise.  A
            # `CodegenSkip`-only net let it escape `_compile_fn` as a raw
            # traceback: exactly the #939 gap, one boundary over.  Mirrors
            # the precondition and `decreases` arms above — one loud [E699],
            # attributed as a compiler bug.  MUST precede the `CodegenSkip`
            # catch below only if it were a subclass; it is not, so order is
            # free and this reads in raise-severity order.
            self._harvest_interp_inference_failures(ctx)
            self._error(
                inv.node if inv.node is not None else decl,
                f"Internal compiler error while compiling '{decl.name}': "
                f"{inv.msg}",
                rationale="This is a codegen invariant violation — the type "
                "checker should have rejected the input before it reached "
                "this point.  Please file a bug report with the offending "
                "program.",
                error_code="E699",
            )
            return None
        except CodegenSkip as skip:
            self._harvest_interp_inference_failures(ctx)
            self._warning(
                skip.node if getattr(skip.node, "span", None) else decl,
                f"Function '{decl.name}' postcondition old(State<T>) "
                f"snapshot contains unsupported "
                f"{type(skip.node).__name__}: {skip.reason} — function "
                f"skipped.",
                rationale="The WASM backend could not resolve the "
                "old-state snapshot's State<T> family. This function "
                "will not appear in the compiled output.",
                error_code="E602",
            )
            return None

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
        # #1212: the RETURN is a `@Byte` write boundary like any other, so
        # mark the body's literal leaves before translating it.  The
        # whole-body `i32.wrap_i64` below cannot cover a HETEROGENEOUS join
        # — `_infer_block_result_type` reads the then-branch / first arm
        # only, so a join whose read arm is an i32 `@Byte` slot and whose
        # sibling is a bare literal was annotated from one arm while the
        # other lowered at its own width, and ARM ORDER decided which way
        # the module failed to validate.  Marking makes every arm i32, after
        # which whichever arm the decider reads gives the same answer; a
        # decider taught to read every arm would not have helped, since the
        # literal arm would still emit `i64.const`.  Alias-aware, so a
        # refined `@Byte` alias return marks too.
        self._mark_byte_return_leaves(ctx, decl.return_type, decl.body)
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
        except RecursionError:
            # #933 belt-and-suspenders: the structural derived-helper
            # generators (show/hash/eq) bound their DISTINCT-type descent on
            # `DERIVED_HELPER_DEPTH_CAP` (see vera/skip.py), which fires on a
            # non-uniform ADT like `Box<Box<T>>` long before the interpreter's
            # recursion limit.  This catch is the last-resort backstop for a
            # future generator whose per-level frame cost outruns that cap: a
            # check-green program must NEVER surface a raw Python traceback
            # (DESIGN.md principle 1).  Degrade to the same clean [E602] skip a
            # structurally-unsupported body already takes — the function is
            # dropped with a loud diagnostic, not a crash.
            self._harvest_interp_inference_failures(ctx)
            self._warning(
                decl,
                f"Function '{decl.name}' body exceeded the codegen recursion "
                f"bound (a deeply / non-uniformly recursive type) — "
                f"function skipped.",
                rationale="Rendering / comparing a polymorphically-recursive "
                "type (e.g. `Box<T>` with a `Box<Box<T>>` field) would expand "
                "without bound at compile time. This function will not appear "
                "in the compiled output.",
                error_code="E602",
            )
            return None
        except AdtEqNotDerivableError as nde:
            # #773 / PR #870 review: a direct `==` on an ADT whose Eq is not
            # structurally derivable — a USER error, not a compiler bug.
            # Surface the same E613 the generic constraint path emits, with
            # the comparison's own span.  MUST precede the parent
            # CodegenInvariantError catch below (subclass).
            self._emit_adt_eq_not_derivable(ctx, nde, decl)
            return None
        except CodegenInvariantError as inv:  # #657: reachable — operators.py / closures.py raise this for type-check-impossible states; covered by tests/test_codegen_invariant_e699.py.
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

        # NOTE: resource / host-import flags accumulated on ``ctx`` are
        # propagated to the module ``self`` *after* ``_compile_postconditions``
        # below — not here — so a builtin or allocation used only inside an
        # ``ensures(...)`` predicate (lowered after this point) still gets its
        # import / memory declaration.  See the propagation block after the
        # postcondition compile (#808 / #823).

        # #813: guard a @Nat -> @Int widening at the return position.  A @Nat
        # result above i64.MAX reinterprets to a negative @Int (u64.MAX -> -1),
        # so trap rather than silently return it — the runtime backstop for the
        # verifier's nat_to_int_coerce obligation (7c).  @Int is i64, so this
        # runs before (and is unaffected by) the i32 coercion below.
        # Alias-aware via `_boundary_base` so an alias-typed @Int return is
        # guarded too — matching the verifier's 7c gate (`_is_int_type` over the
        # *resolved* return type).  The raw `_type_expr_to_slot_name` returned
        # the opaque alias name and missed `type MyInt = Int` entirely (#983
        # review, the widen sibling of the alias-blind narrow gate); the
        # name-only chase that replaced it still dropped an APPLICATION's type
        # arguments, so `type MyInt = Ident<Int>` answered the head `Ident` and
        # the widen guard went missing again (#1256, measured against the plain
        # spelling's).  `_boundary_base` resolves the type expression, so both
        # spellings answer `Int` — the same derivation the narrow gate above,
        # the `throw` payload and the `apply_fn` signature ask.  A refinement
        # over @Int stays here (the verifier's 7c fires on refined @Int too: the
        # `<= i64.MAX` bound is not subsumed by the predicate), which the
        # wrapper-stripping resolution preserves rather than changes.
        widen_guarded = (
            ctx._boundary_base(decl.return_type) == "Int"
            and ctx._result_is_nat(decl.body)
        )
        if widen_guarded:
            body_instrs = ctx._emit_int_widen_guard(body_instrs)

        # #758/#983: an @Int body narrowing into a @Nat return can be negative
        # (`to_nat(0 - 5)` = -5), so trap rather than store a negative in the
        # @Nat slot — the runtime backstop for the verifier's return nat_bind
        # obligation (7d), the dual of the #813 widen guard above.  This is
        # emitted PER NARROWING LEAF during body translation (via the
        # `_nat_return_leaf_ids` set threaded above), NOT as a whole-body wrap:
        # the whole-body wrap appended the guard after the entire body and so
        # reverted EVERY `return_call`, losing TCO for a non-narrowing
        # @Nat->@Nat recursive tail call (`drain`) that then stack-exhausted at
        # depth (#983 regression).  Guarding only the genuine narrowing leaves
        # inline leaves the recursive tail call's `return_call` structurally
        # intact — nothing is appended after the body — so, unlike the widen
        # guard, this no longer forces a revert below.  The alias-aware +
        # refinement-excluded gate lives where `nat_leaf_ids` is computed.

        # Coerce body result if return type is i32 but body produces i64
        # (e.g. IntLit in a Byte-returning function)
        if ret_wt == "i32":
            body_result_type = ctx._infer_block_result_type(decl.body)
            if body_result_type == "i64":
                body_instrs.append("i32.wrap_i64")

        # Collect closures created during body compilation and lift them.
        # #1245: this is the FIRST of two lift passes — the second runs
        # after `_compile_postconditions` below, which is where a closure
        # written in a refined RETURN's predicate, a tuple return's
        # component guards, or an `ensures(...)` clause is registered.
        if self._lift_closures_or_drop(ctx, decl):
            return None

        # Compile postcondition checks (wrap around body result).
        # #912: a composite `==` on a genuinely non-Eq-derivable operand
        # (a `Tuple`, or an ADT with an `Array`/`Map` field) in an `ensures`
        # clause raises `AdtEqNotDerivableError` from the structural-Eq dispatch,
        # exactly as the body path does — but `_compile_postconditions` runs
        # OUTSIDE the body/closure try blocks above, so the exception escaped
        # uncaught (a Python traceback on a `check`-green program).  Catch it
        # here with the SAME clean E613 the body (line 407) and closure (line
        # 504) paths emit, dropping the function.  The *provable* free-type-var
        # shape (`@Box<T>.result == @Box<T>.0`) never reaches here — it is routed
        # to the scalar lowering by `_is_lost_type_arg_clone` before dispatch —
        # so this backstop only fires on operands the checker's own Eq gate
        # would reject (it does not yet gate contract position; a distinct gap).
        # #922: the catch also covers `CodegenSkip` — an unsupported `hash`/`show`
        # on a composite (e.g. `ensures(hash(recursiveADT) == 0)`) raises
        # `CodegenSkip`, not `AdtEqNotDerivableError`, and the pre-#922 narrow
        # catch let it escape uncaught.  It now degrades to a clean E602 via the
        # shared contract-predicate dispatcher.
        try:
            post_instrs = self._compile_postconditions(ctx, decl, env, ret_wt)
        except (AdtEqNotDerivableError, CodegenSkip) as exc:
            self._emit_contract_predicate_degradation(ctx, exc, decl)
            return None
        except CodegenInvariantError as inv:  # #939: complete the net here too.
            # The last of the four contract-lowering paths to gain the
            # `CodegenInvariantError` net (body / closure had it pre-#939; the
            # precondition path gained it in #939's first commit).  A `@T.n`
            # read in an `ensures(...)` clause of a generic instantiated at a
            # zero-size type (`Unit`, `Future<Unit>`) dangles in
            # `_translate_slot_ref`; without this catch it escaped `_compile_fn`
            # as a raw traceback on a `check`-green program (the #939-review
            # crash).  E206's `erases_to_unit` broadening now rejects that at
            # check, so this is the defensive backstop — but it MUST exist for
            # symmetry, exactly as the body/closure/precondition catches do.
            # MUST follow the `(AdtEqNotDerivableError, CodegenSkip)` catch
            # above (subclass).  Covered by tests/test_codegen_invariant_e699.py.
            self._harvest_interp_inference_failures(ctx)
            self._error(
                inv.node if inv.node is not None else decl,
                f"Internal compiler error while compiling '{decl.name}': "
                f"{inv.msg}",
                rationale="This is a codegen invariant violation — the type "
                "checker should have rejected the input before it reached this "
                "point.  Please file a bug report with the offending program.",
                error_code="E699",
            )
            return None

        # #1245: the SECOND lift pass.  `_compile_postconditions` lowers the
        # refined-RETURN guard, a tuple return's per-component guards, and
        # every `ensures(...)` predicate — all of which may construct a
        # closure, which registers on `ctx` only now.  With one pass, that
        # closure was created and never lifted: the module's function table
        # stayed empty, the `call_indirect` its construction emits was
        # orphaned, and the #1185 propagation dropped the function and every
        # caller — a check-green, verify-clean program compiling to ZERO
        # exports.  `_lift_pending_closures` consumes the pending list and
        # re-syncs the id counter, so this pass sees exactly the closures the
        # postcondition phase added.
        #
        # The two passes are deliberately NOT one transaction (PR #1250
        # review).  When this one reports a failed lift the function is
        # dropped while the FIRST pass's lifted closures stay committed, so
        # the module carries them as dead code.  Measured on a stubbed
        # second-pass failure: `$anon_0`/`$anon_1` and their `elem` entries
        # remain, contiguous and still aligned with their `closure_id`s, the
        # parent and its callers drop with the usual [E602]/[E620] chain, and
        # the module VALIDATES — so the cost is output size in a path no
        # check-green program reaches (every catch in
        # `_lift_closures_or_drop` is defensive; a closure-body failure is
        # caught inside `_compile_lifted_closure`), not a correctness one.
        # Deferring pass 1's commit would mean holding its four output
        # buffers uncommitted across the whole postcondition phase to buy
        # that back.
        if self._lift_closures_or_drop(ctx, decl):
            return None

        # Propagate resource / host-import flags from ``ctx`` to the module
        # ``self`` that ``_assemble_module`` reads.  This runs HERE — after the
        # precondition (`_compile_preconditions`), body (`translate_block`),
        # lifted-closure, AND postcondition (`_compile_postconditions`) lowering
        # — because ``ctx`` accumulates these flags across every one of those
        # phases.  Propagating earlier (the historical position, before
        # postconditions) dropped any flag a builtin or allocation set while
        # lowering an ``ensures(...)`` predicate, so the import / memory / GC
        # declaration was omitted and the orphaned `call`/`global.get` failed
        # WAT compilation (#808 for `vera.overflow_trap`; #823 for the other
        # host-import families and `$alloc`/`$gc_sp`).  Nothing between the old
        # position and here reads these flags — they are consumed only at module
        # assembly — so the move is purely additive in correctness.
        if ctx.needs_alloc:
            self._needs_alloc = True
            self._needs_memory = True
        self._map_imports.update(ctx._map_imports)
        self._map_ops_used.update(ctx._map_ops_used)
        self._set_imports.update(ctx._set_imports)
        self._set_ops_used.update(ctx._set_ops_used)
        self._decimal_imports.update(ctx._decimal_imports)
        self._decimal_ops_used.update(ctx._decimal_ops_used)
        self._json_ops_used.update(ctx._json_ops_used)
        self._html_ops_used.update(ctx._html_ops_used)
        self._http_ops_used.update(ctx._http_ops_used)
        self._async_ops_used.update(ctx._async_ops_used)
        self._inference_ops_used.update(ctx._inference_ops_used)
        self._db_ops_used.update(ctx._db_ops_used)  # #229
        self._random_ops_used.update(ctx._random_ops_used)
        self._math_ops_used.update(ctx._math_ops_used)
        self._needs_overflow_trap = (
            self._needs_overflow_trap or ctx._needs_overflow_trap
        )
        # #773: structural-Eq helper functions generated while lowering this
        # body (deduped by name across the whole module at assembly).
        self._adt_eq_helpers.update(ctx._adt_eq_helpers)
        # #924: recursive show/hash helper functions generated while lowering
        # this body (deduped by name across the whole module at assembly).
        self._show_hash_helpers.update(ctx._show_hash_helpers)

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

        if post_instrs or widen_guarded:
            # Postcondition checks must run; return_call would skip them.  The
            # #813 @Nat->@Int return widen guard is the same case: it is appended
            # *after* the trailing tail call (whole-body wrap), so a
            # `return_call` would return before the guard runs, silently leaking
            # a reinterpreted negative @Int (e.g. `fn f(@Nat -> @Int) {
            # make_nat(@Nat.0) }`).  Revert every return_call to plain call so
            # the guard is reached.  The #758 @Int->@Nat narrow guard is NOT
            # here: it is emitted per narrowing LEAF during body translation, so
            # a non-narrowing @Nat->@Nat recursive tail call keeps its
            # `return_call` (a narrowing-leaf call was already excluded from
            # `tail_sites` above, so it lowers to a plain `call` reached by its
            # own inline guard) — this is what restores TCO for `drain` (#983).
            body_instrs = [
                instr.replace("return_call ", "call ", 1)
                if instr.lstrip().startswith("return_call ")
                else instr
                for instr in body_instrs
            ]
        elif dec_restore_instrs:
            # #1172: the decreases guard's tail-call discipline — TCO is
            # PRESERVED for the dominant self-recursive case, which #517
            # exists for (`decreases` is mandatory on pure recursion, so
            # demoting guarded functions would have un-fixed the
            # documented iteration idiom's 1M-depth property).  Per
            # surviving ``return_call`` in this guarded function:
            #   - self-recursive: prepend the site check + state restore
            #     built by `_dec_self_tail_prefix` (capture args, verify
            #     the hop decreases against the live chain globals, close
            #     out this activation's state, re-push) and keep the
            #     ``return_call`` — the chain rides the site checks;
            #   - a DIFFERENT guarded target: demote to a plain ``call``
            #     (the mutual-tail corner: with the frame elided, no
            #     restore placement both preserves the chain and unwinds
            #     it; the entry check then covers every hop, at
            #     native-stack depth);
            #   - an unguarded target: prepend the restores only (this
            #     activation ends here; the callee never touches this
            #     function's chain state).
            # An untranslatable self-tail prefix demotes that site the
            # same way — the check is never partially emitted.  The GC
            # prepend below composes: it touches only ``$gc_sp``.
            patched_dec: list[str] = []
            for instr in body_instrs:
                stripped = instr.lstrip()
                if not stripped.startswith("return_call "):
                    patched_dec.append(instr)
                    continue
                target = stripped.split()[1].lstrip("$")
                ws = instr[: len(instr) - len(stripped)]
                if target == decl.name:
                    if dec_self_tail is not None:
                        patched_dec.extend(
                            ws + part for part in dec_self_tail)
                        patched_dec.append(instr)
                    else:
                        patched_dec.append(
                            instr.replace("return_call ", "call ", 1))
                elif target in self._dec_guarded_names:
                    patched_dec.append(
                        instr.replace("return_call ", "call ", 1))
                else:
                    # PR #1179 review F2: an UNGUARDED tail target can
                    # trampoline straight back into this function; the
                    # old prepend-restores-then-transfer sequence zeroed
                    # the chain first, so every re-entry re-baselined
                    # and a constant measure looped forever.  Demote
                    # like the mutual-tail case: plain-call semantics
                    # keep the chain live across the callee, and the
                    # single exit's restores run when the value returns.
                    patched_dec.append(
                        instr.replace("return_call ", "call ", 1))
            body_instrs = patched_dec

        if (
            not (post_instrs or widen_guarded)
            and ctx.needs_alloc
        ):
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

            # Determine if return type is a heap pointer (#1255: from the
            # REPRESENTATION base, the closure return's twin).
            ret_is_pointer = False
            if ret_wt == "i32":
                ret_is_pointer = is_gc_pointer_base(
                    self._family_base_te(decl.return_type),
                )
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

        # #1172: decreases-guard restores — every non-trap exit puts the
        # function's chain state back to what this activation saved, so a
        # finished call leaves no residue that would spuriously trap a
        # sibling call.  Trap paths need no restore (the instance dies).
        # A `return_call` CAN survive in a guarded function — the
        # self-recursive and unguarded-target tail sites keep TCO — but
        # those sites carry their restores inline (the `dec_self_tail`
        # prefix / `dec_restore_instrs` prepend), so together with this
        # single fall-through exit every live return is covered.  An
        # unwinding `throw` covers nothing, which is why an
        # Exn-declaring function gets no guard at all (see
        # `_compile_decreases_entry`).
        for instr in dec_restore_instrs:
            lines.append(f"    {instr}")

        # GC epilogue: save result, restore gc_sp, push result, return
        for instr in gc_epilogue:
            lines.append(f"    {instr}")

        lines.append("  )")
        return "\n".join(lines)
