"""Vera WASM translation layer — AST to WAT bridge.

Translates Vera AST expressions into WebAssembly Text format (WAT)
instructions for compilation to WASM binary.  Manages slot environments,
local variable allocation, string pool, and instruction generation.

The ``WasmContext`` class is composed from several mixin modules that
each handle a specific concern:

* :mod:`~vera.wasm.inference` — type inference and utility methods
* :mod:`~vera.wasm.operators` — binary/unary operators, control flow,
  quantifiers, assert/assume, old/new
* :mod:`~vera.wasm.calls` — function calls, generic resolution, handle
* :mod:`~vera.wasm.closures` — closures and free variable analysis
* :mod:`~vera.wasm.data` — constructors, match, arrays, indexing

See spec/11-compilation.md for the compilation specification.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from vera import ast
from vera.skip import CodegenSkip

if TYPE_CHECKING:
    from vera.codegen import ConstructorLayout

from vera.wasm.helpers import (  # noqa: F401 — re-exported for consumers
    _INLINE_I32_TYPES,
    StringPool,
    WasmSlotEnv,
    gc_shadow_push,
    wasm_type,
)
from vera.wasm.inference import InferenceMixin
from vera.wasm.operators import OperatorsMixin
from vera.wasm.calls import CallsMixin
from vera.wasm.calls_arrays import CallsArraysMixin
from vera.wasm.calls_containers import CallsContainersMixin
from vera.wasm.calls_encoding import CallsEncodingMixin
from vera.wasm.calls_handlers import CallsHandlersMixin
from vera.wasm.calls_markup import CallsMarkupMixin
from vera.wasm.calls_math import CallsMathMixin
from vera.wasm.calls_parsing import CallsParsingMixin
from vera.wasm.calls_strings import CallsStringsMixin
from vera.wasm.closures import ClosuresMixin
from vera.wasm.data import DataMixin


# =====================================================================
# WASM translation context
# =====================================================================

class WasmContext(
    InferenceMixin,
    OperatorsMixin,
    CallsMixin,
    CallsArraysMixin,
    CallsContainersMixin,
    CallsEncodingMixin,
    CallsHandlersMixin,
    CallsMarkupMixin,
    CallsMathMixin,
    CallsParsingMixin,
    CallsStringsMixin,
    ClosuresMixin,
    DataMixin,
):
    """Generates WAT instructions for a single function body.

    Manages local variable allocation and dispatches expression
    translation.  Mirrors SmtContext in smt.py.

    Composed from five mixin classes, each in its own module.
    This class provides __init__, configuration setters, local
    allocation, the expression dispatcher (translate_expr), and
    block translation (translate_block).
    """

    def __init__(
        self,
        string_pool: StringPool,
        effect_ops: dict[str, tuple[str, bool]] | None = None,
        ctor_layouts: dict[str, ConstructorLayout] | None = None,
        adt_type_names: set[str] | None = None,
        generic_fn_info: (
            dict[str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]] | None
        ) = None,
        ctor_to_adt: dict[str, str] | None = None,
        known_fns: set[str] | None = None,
        ctor_adt_tp_indices: dict[str, tuple[int | None, ...]] | None = None,
        adt_tp_counts: dict[str, int] | None = None,
    ) -> None:
        self.string_pool = string_pool
        self._next_local: int = 0
        self._locals: list[tuple[str, str]] = []  # (name, wat_type)
        self._result_local: int | None = None
        # Effect operation mapping: op_name -> (wasm_call_target, is_void)
        # e.g. {"get": ("$vera.state_get_Int", False),
        #        "put": ("$vera.state_put_Int", True)}
        self._effect_ops = effect_ops or {}
        # Constructor layout mapping: ctor_name -> ConstructorLayout
        self._ctor_layouts: dict[str, ConstructorLayout] = ctor_layouts or {}
        # ADT type names for slot/param type resolution
        self._adt_type_names: set[str] = adt_type_names or set()
        # Generic function info for call rewriting:
        # fn_name -> (forall_vars, param_type_exprs)
        self._generic_fn_info: dict[
            str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]
        ] = generic_fn_info or {}
        # Constructor name → ADT name reverse mapping
        self._ctor_to_adt: dict[str, str] = ctor_to_adt or {}
        # Known locally-defined function names (for cross-module guard rail)
        self._known_fns: set[str] = known_fns or set()
        # Per-field ADT type-param indices for sparse constructors (e.g. Err → (1,))
        self._ctor_adt_tp_indices: dict[str, tuple[int | None, ...]] = (
            ctor_adt_tp_indices or {}
        )
        # Maps ADT name → number of type parameters
        self._adt_tp_counts: dict[str, int] = adt_tp_counts or {}
        # Map host-import tracking (propagated to codegen core)
        self._map_imports: set[str] = set()
        self._map_ops_used: set[str] = set()
        # #573: wrap-table flag — set when any host-handle type
        # migrates to the heap-wrap-as-ADT scheme so the GC
        # sweep can reclaim host-side store entries.  Currently
        # set by Map operations (phase 1 of #573).  Set / Decimal
        # / JSON / HTML migrations track this same flag in
        # follow-ups.  When true, `assembly.py` allocates a
        # 64 KiB wrap-table region in linear memory, emits the
        # `$register_wrapper` helper, and adds a Phase-2c walk
        # to `$gc_collect` that fires `host_decref_handle` for
        # unmarked wrappers.
        self._needs_wrap_table: bool = False
        # Set host-import tracking (propagated to codegen core)
        self._set_imports: set[str] = set()
        self._set_ops_used: set[str] = set()
        # Decimal host-import tracking (propagated to codegen core)
        self._decimal_imports: set[str] = set()
        self._decimal_ops_used: set[str] = set()
        # Json host-import tracking (propagated to codegen core)
        self._json_ops_used: set[str] = set()
        # Html host-import tracking (propagated to codegen core)
        self._html_ops_used: set[str] = set()
        # Http host-import tracking (propagated to codegen core)
        self._http_ops_used: set[str] = set()
        # Inference host-import tracking (propagated to codegen core)
        self._inference_ops_used: set[str] = set()
        # Random host-import tracking (propagated to codegen core, #465)
        self._random_ops_used: set[str] = set()
        # Math host-import tracking (propagated to codegen core, #467)
        self._math_ops_used: set[str] = set()
        # Function return WASM types for type inference:
        # fn_name → return_wasm_type (str | None)
        self._fn_ret_types: dict[str, str | None] = {}
        # #814 §8.5.3: (module path, fn name) → WASM target name for a
        # module-qualified call.  Lets `m::f` bypass a local shadow.
        self._module_qualified_targets: dict[
            tuple[tuple[str, ...], str], str
        ] = {}
        # #814 C2: bare name → mod$ name, set only while compiling a `mod$…`
        # body so an intra-module sibling call reaches the module's version.
        self._intra_module_renames: dict[str, str] = {}
        # Function return *Vera* type expressions, retained alongside
        # `_fn_ret_types` because some inference paths need the full
        # NamedType (with type_args) — e.g. resolving the element type
        # of an Array returned from a function call so `f()[i]` can
        # type-infer (#614).  Pre-fix this dict didn't exist and
        # `_infer_index_element_type_expr` only handled SlotRef and
        # nested-IndexExpr collections, silently returning None for
        # FnCall collections — `_translate_index_expr` then returned
        # None too, causing the enclosing function (or closure) to
        # be dropped from the output.
        self._fn_ret_type_exprs: dict[str, ast.TypeExpr] = {}
        # #747: per-parameter concrete-@Nat flags per function, for the
        # runtime @Int -> @Nat narrowing guard at call sites.
        self._fn_nat_params: dict[str, tuple[bool, ...]] = {}
        # Closure compilation state — accumulated during translation
        # Each entry: (anon_fn, captures, closure_id)
        # captures: list of (type_name, outer_de_bruijn, wasm_type)
        self._pending_closures: list[
            tuple[ast.AnonFn, list[tuple[str, int, str]], int]
        ] = []
        # Type aliases: alias_name -> TypeExpr (for FnType resolution)
        self._type_aliases: dict[str, ast.TypeExpr] = {}
        # Type alias parameters: alias_name -> param names (for generic aliases)
        self._type_alias_params: dict[str, tuple[str, ...]] = {}
        # Closure signature registry: sig_key -> (type_name, param/result WAT)
        self._closure_sigs: dict[str, str] = {}
        # Flags for resource requirements detected during translation
        self.needs_alloc: bool = False
        # Next closure id (may be overwritten by codegen)
        self._next_closure_id: int = 0
        # Next quantifier label id (for unique block/loop labels)
        self._next_quant_id: int = 0
        # Next handle expression label id (for unique try_table labels)
        self._next_handle_id: int = 0
        # Old state snapshots: type_name -> local_idx (for old() in postconditions)
        self._old_state_locals: dict[str, int] = {}
        # #517 — WASM tail-call optimization.  Populated by
        # ``set_tail_call_context`` from the per-fn analyzer in
        # ``vera/codegen/tail_position.py``: the set of ``id(FnCall)``
        # AST nodes that are syntactically in tail position.  The
        # ``_translate_call`` site emits ``return_call $foo`` instead
        # of ``call $foo`` when the call's id is in this set AND its
        # WASM return type matches ``_self_ret_wt`` (return_call
        # requires the callee's signature to match the caller's).
        # ``_self_ret_wt`` is the current function's WASM return type
        # — needed for the type-match check.  Both default to "no
        # tail-call optimization" so ``WasmContext`` instances created
        # without these set (e.g. closure bodies — see
        # ``vera/codegen/closures.py``) emit plain ``call``.
        self._tail_call_sites: set[int] = set()
        self._self_ret_wt: str | None = None
        # #630 Tier 2 — interpolation-segment inference failures.
        # When `_translate_interpolated_string` can't classify a segment's
        # Vera type, it appends the offending `Expr` here and returns
        # None.  `CodeGenerator._compile_fn` harvests these and emits a
        # specific [E615] diagnostic before the fall-through [E602].
        # Pre-#630 the same path silently wrapped the segment in
        # `to_string(...)` which reads `i64` — an `i32_pair` value
        # (String/Array) would then trip `expected i64, found i32` at
        # WASM validation.  Converting the silent miscompilation into a
        # loud compile-time skip closes the ten triggers of the #602
        # bug class against any future inference gap (ADT types in
        # interpolation, novel composite kinds, etc.).
        self._interp_inference_failures: list[ast.Expr] = []
        # #632 — apply_fn closure-arg shapes that the inference
        # dispatcher in `_infer_apply_fn_return_type` doesn't
        # recognise (today: anything other than SlotRef-into-FnType
        # alias or AnonFn — e.g. `apply_fn(make_mapper(), 7)` where
        # `make_mapper` is a FnCall returning a closure).  Pre-#632
        # the apply_fn translation site silently used the `"i64"`
        # default for the call_indirect sig, producing a WASM
        # validation trap with no source-located diagnostic.
        # Post-#632 the failing closure_arg is appended here and the
        # codegen base's `_harvest_inference_failures` emits a
        # specific [E616] before falling through to [E602].
        self._apply_fn_inference_failures: list[ast.Expr] = []
        # #798: the checker's resolved-type side-table (keyed by
        # ``ast.span_key``), threaded from the CodeGenerator.  The
        # integer-overflow guard reads it to classify an arithmetic operand
        # as @Int (i64) vs @Nat (u64) using the SAME resolved type the
        # verifier's ``int_overflow`` obligation uses, so codegen guards
        # exactly the sites — at exactly the range — the verifier obligates.
        # ``None`` when typecheck was skipped (AST-only fallback).
        self._expr_semantic_types: (
            dict[tuple[int, int, int, int], object] | None
        ) = None

    def set_expr_semantic_types(
        self,
        types: dict[tuple[int, int, int, int], object] | None,
    ) -> None:
        """Seed the checker's resolved-type side-table for the #798 overflow
        guard's Int/Nat operand classifier (mirrors the verifier's
        ``_resolved_type_of`` / ``_overflow_int_type``)."""
        self._expr_semantic_types = types

    def set_fn_ret_types(
        self, ret_types: dict[str, str | None],
    ) -> None:
        """Set function return WASM types for FnCall type inference."""
        self._fn_ret_types = ret_types

    def set_module_qualified_targets(
        self, targets: dict[tuple[tuple[str, ...], str], str],
    ) -> None:
        """Set the (module path, fn name) → WASM target map (#814 §8.5.3)."""
        self._module_qualified_targets = targets

    def set_intra_module_renames(self, renames: dict[str, str]) -> None:
        """Set the intra-module bare-call rename map (#814 C2).

        Non-empty only while compiling a ``mod$…`` body; redirects a bare
        call to a locally-shadowed same-module function to the module's
        ``mod$`` version instead of the main program's local shadow.
        """
        self._intra_module_renames = renames

    def set_fn_ret_type_exprs(
        self, ret_type_exprs: dict[str, ast.TypeExpr],
    ) -> None:
        """Set function return Vera-type exprs for richer inference (#614)."""
        self._fn_ret_type_exprs = ret_type_exprs

    def set_fn_nat_params(
        self, nat_params: dict[str, tuple[bool, ...]],
    ) -> None:
        """Set per-parameter concrete-@Nat flags for the call-site
        runtime narrowing guard (#747)."""
        self._fn_nat_params = nat_params

    def set_type_aliases(
        self, aliases: dict[str, ast.TypeExpr],
    ) -> None:
        """Set type alias mappings for FnType resolution."""
        self._type_aliases = aliases

    def set_type_alias_params(
        self, params: dict[str, tuple[str, ...]],
    ) -> None:
        """Set type alias parameter names for generic alias resolution."""
        self._type_alias_params = params

    def set_closure_id_start(self, start: int) -> None:
        """Set the starting closure ID for this context."""
        self._next_closure_id = start

    def set_closure_sigs(self, sigs: dict[str, str]) -> None:
        """Seed with accumulated module-level closure signatures.

        Each context independently numbers ``$closure_sig_N`` from zero.
        When multiple functions use closures with different signatures,
        the names collide after module-level merge.  By seeding the
        context with signatures already registered at module level, new
        signatures get unique numbers and existing ones reuse their names.
        """
        self._closure_sigs = dict(sigs)

    def set_result_local(self, local_idx: int) -> None:
        """Set the local index used for @T.result in postconditions."""
        self._result_local = local_idx

    def set_old_state_locals(
        self, locals_map: dict[str, int],
    ) -> None:
        """Set old-state snapshot locals for old() in postconditions."""
        self._old_state_locals = locals_map

    def set_tail_call_context(
        self, sites: set[int], self_ret_wt: str | None,
    ) -> None:
        """Configure tail-call optimization for the function being compiled.

        ``sites`` is the set of ``id(ast.FnCall)`` AST nodes the
        per-fn analyzer in ``vera/codegen/tail_position.py``
        identified as syntactically in tail position.  At translate
        time, ``_translate_call`` checks ``id(call) in sites`` plus
        the type-match condition (callee's WASM return type ==
        ``self_ret_wt``) before emitting ``return_call $foo``
        instead of ``call $foo``.

        Both arguments default to "no TCO" if never called — this
        is the right default for closure bodies and other contexts
        where the caller hasn't pre-computed tail-call sites.
        """
        self._tail_call_sites = sites
        self._self_ret_wt = self_ret_wt

    def get_old_state_local(self, type_name: str) -> int | None:
        """Get the local index holding the old() snapshot for a State type."""
        return self._old_state_locals.get(type_name)

    def alloc_param(self) -> int:
        """Allocate a parameter slot (already in WASM signature).

        Returns the local index for this parameter.
        """
        idx = self._next_local
        self._next_local += 1
        return idx

    def alloc_local(self, wat_type: str) -> int:
        """Allocate a new local variable.  Returns local index."""
        idx = self._next_local
        name = f"$l{idx}"
        self._locals.append((name, wat_type))
        self._next_local += 1
        return idx

    def extra_locals_wat(self) -> list[str]:
        """Return WAT local declarations for non-parameter locals."""
        return [f"(local {name} {wt})" for name, wt in self._locals]

    # -----------------------------------------------------------------
    # Expression translation
    # -----------------------------------------------------------------

    def translate_expr(
        self, expr: ast.Expr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a Vera AST expression to WAT instructions.

        Returns a list of WAT instruction strings, or None if the
        expression contains unsupported constructs (function skipped).

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.)
        #
        # Handled (explicit isinstance branch — codegen produces WAT):
        #   IntLit            → i64.const
        #   FloatLit          → f64.const
        #   BoolLit           → i32.const 0/1
        #   UnitLit           → empty (no stack value)
        #   StringLit         → string-pool index pair
        #   InterpolatedString → string-builder sequence
        #   SlotRef           → local.get
        #   ResultRef         → local.get (postcondition checks)
        #   BinaryExpr        → operand translations + binop
        #   UnaryExpr         → operand + unop
        #   IndexExpr         → bounds check + load
        #   ArrayLit          → alloc + element stores
        #   FnCall            → call
        #   QualifiedCall     → effect-op dispatch
        #   ModuleCall        → desugared to FnCall
        #   ConstructorCall   → ADT layout alloc + field stores
        #   NullaryConstructor → tag-only ADT alloc
        #   AnonFn            → closure-lift dispatch (closures.py)
        #   IfExpr            → block + br_if
        #   MatchExpr         → pattern dispatch + arm bodies
        #   Block             → statement sequence + trailing expr
        #   HandleExpr        → handler installation + body
        #   AssertExpr        → predicate + trap on false
        #   AssumeExpr        → predicate + trap on false
        #   ForallExpr        → quantifier dispatch (verifier-only at runtime)
        #   ExistsExpr        → quantifier dispatch
        #   OldExpr           → snapshot lookup (postcondition contexts)
        #   NewExpr           → snapshot lookup (postcondition contexts)
        #
        # Cannot occur (rejected before reaching codegen):
        #   HoleExpr          → parser placeholder; check time rejects
        """
        if isinstance(expr, ast.IntLit):
            return [f"i64.const {expr.value}"]

        if isinstance(expr, ast.BoolLit):
            return [f"i32.const {1 if expr.value else 0}"]

        if isinstance(expr, ast.FloatLit):
            return [f"f64.const {expr.value}"]

        if isinstance(expr, ast.UnitLit):
            return []  # Unit produces no value on the stack

        if isinstance(expr, ast.SlotRef):
            return self._translate_slot_ref(expr, env)

        if isinstance(expr, ast.BinaryExpr):
            return self._translate_binary(expr, env)

        if isinstance(expr, ast.UnaryExpr):
            return self._translate_unary(expr, env)

        if isinstance(expr, ast.IfExpr):
            return self._translate_if(expr, env)

        if isinstance(expr, ast.Block):
            return self.translate_block(expr, env)

        if isinstance(expr, ast.FnCall):
            return self._translate_call(expr, env)

        if isinstance(expr, ast.QualifiedCall):
            return self._translate_qualified_call(expr, env)

        if isinstance(expr, ast.ModuleCall):
            # C7e: desugar to flat FnCall — imported function is compiled
            # into the same WASM module via flattening.  #814 §8.5.3: a
            # module-qualified call MUST reach the module's function even
            # when a local shadows its bare name, so resolve the WASM target
            # via the qualified-target table (mod$… name for a shadowed fn,
            # else the bare name) rather than blindly dropping the path.
            target = self._module_qualified_targets.get(
                (tuple(expr.path), expr.name), expr.name,
            )
            desugared = ast.FnCall(
                name=target,
                args=expr.args,
                span=expr.span,
            )
            return self._translate_call(desugared, env)

        if isinstance(expr, ast.StringLit):
            return self._translate_string_lit(expr)

        if isinstance(expr, ast.InterpolatedString):
            return self._translate_interpolated_string(expr, env)

        if isinstance(expr, ast.ResultRef):
            return self._translate_result_ref()

        if isinstance(expr, ast.ConstructorCall):
            return self._translate_constructor_call(expr, env)

        if isinstance(expr, ast.NullaryConstructor):
            return self._translate_nullary_constructor(expr)

        if isinstance(expr, ast.MatchExpr):
            return self._translate_match(expr, env)

        if isinstance(expr, ast.AnonFn):
            return self._translate_anon_fn(expr, env)

        if isinstance(expr, ast.HandleExpr):
            return self._translate_handle_expr(expr, env)

        if isinstance(expr, ast.ArrayLit):
            return self._translate_array_lit(expr, env)

        if isinstance(expr, ast.IndexExpr):
            return self._translate_index_expr(expr, env)

        if isinstance(expr, ast.AssertExpr):
            return self._translate_assert(expr, env)

        if isinstance(expr, ast.AssumeExpr):
            return self._translate_assume()

        if isinstance(expr, ast.ForallExpr):
            return self._translate_forall(expr, env)

        if isinstance(expr, ast.ExistsExpr):
            return self._translate_exists(expr, env)

        if isinstance(expr, ast.OldExpr):
            return self._translate_old_expr(expr)

        if isinstance(expr, ast.NewExpr):
            return self._translate_new_expr(expr)

        raise CodegenSkip(
            expr, f"no translator for expression type {type(expr).__name__}"
        )

    # -----------------------------------------------------------------
    # Blocks and statements
    # -----------------------------------------------------------------

    def translate_block(
        self, block: ast.Block, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a block: process statements, then final expression."""
        current_env = env
        instructions: list[str] = []

        for stmt in block.statements:
            if isinstance(stmt, ast.LetStmt):
                val_instrs = self.translate_expr(stmt.value, current_env)
                if val_instrs is None:
                    return None
                # Determine WAT type for this let binding
                type_name = self._type_expr_to_slot_name(stmt.type_expr)
                if type_name is None:
                    raise CodegenSkip(
                        stmt, "let binding type has no slot name"
                    )
                # Pair bindings (String, Array<T>) need two locals: (ptr, len)
                if self._is_pair_type_name(type_name):
                    ptr_idx = self.alloc_local("i32")
                    len_idx = self.alloc_local("i32")
                    instructions.extend(val_instrs)
                    instructions.append(f"local.set {len_idx}")
                    instructions.append(f"local.set {ptr_idx}")
                    current_env = current_env.push(type_name, ptr_idx)
                    continue
                wat_t = self._slot_name_to_wasm_type(type_name)
                if wat_t is None:
                    raise CodegenSkip(
                        stmt,
                        f"let binding type {type_name!r} has no WASM representation",
                    )
                local_idx = self.alloc_local(wat_t)
                # #552: guard an @Int -> @Nat let narrowing at runtime
                # when the verifier could not discharge `value >= 0`
                # statically (Tier 3), or when codegen runs without
                # `vera verify`.  The guard never trips on a provably-@Nat
                # value, mirroring the #520 subtraction guard's
                # belt-and-suspenders role.  Alias-aware (`type Age = Nat`)
                # via `_resolve_base_type_name` so an alias/refined @Nat let
                # target is guarded too (CR #756).
                if (self._resolve_base_type_name(type_name) == "Nat"
                        and self._narrows_into_nat(stmt.value)):
                    instructions.extend(
                        self._emit_nat_bind_guard(val_instrs))
                else:
                    instructions.extend(val_instrs)
                instructions.append(f"local.set {local_idx}")
                # #705: shadow-push heap-pointer let bindings so
                # subsequent allocations in the same block (e.g. a
                # ``set_to_array`` host call after ``let @Set =
                # build_set()``) can't reclaim them.  Bool / Byte /
                # Unit are inline i32s that don't need rooting; any
                # other i32 slot is a heap-pointer ADT.  The function
                # epilogue's ``$gc_sp`` restore pops these on exit.
                # Setting ``needs_alloc`` here ensures the GC
                # infrastructure (``$gc_sp``, ``$gc_stack_limit``)
                # gets emitted even for functions that don't otherwise
                # allocate; without it the WAT references unknown
                # globals.
                if wat_t == "i32" and type_name not in _INLINE_I32_TYPES:
                    self.needs_alloc = True
                    instructions.extend(gc_shadow_push(local_idx))
                current_env = current_env.push(type_name, local_idx)
            elif isinstance(stmt, ast.ExprStmt):
                stmt_instrs = self.translate_expr(stmt.expr, current_env)
                if stmt_instrs is None:
                    return None
                instructions.extend(stmt_instrs)
                # Drop the value if the expression produces one.
                # QualifiedCalls (effect ops like IO.print) return void.
                # UnitLit produces nothing.
                if stmt_instrs and not self._is_void_expr(stmt.expr):
                    if self._is_pair_result_expr(stmt.expr):
                        instructions.extend(["drop", "drop"])
                    else:
                        instructions.append("drop")
            elif isinstance(stmt, ast.LetDestruct):
                result = self._translate_let_destruct(stmt, current_env)
                if result is None:
                    return None
                destr_instrs, current_env = result
                instructions.extend(destr_instrs)
            else:
                # Unknown statement type
                raise CodegenSkip(
                    stmt,
                    f"unsupported statement type {type(stmt).__name__}",
                )

        # Final expression
        expr_instrs = self.translate_expr(block.expr, current_env)
        if expr_instrs is None:
            return None
        instructions.extend(expr_instrs)
        return instructions

    # -----------------------------------------------------------------
    # Helpers
    # -----------------------------------------------------------------

    def _is_void_expr(self, expr: ast.Expr) -> bool:
        """Check if an expression produces no value on the WASM stack.

        QualifiedCalls (effect operations like IO.print) return Unit
        and produce no stack value.  UnitLit also produces nothing.
        Effect op calls like put() are also void.
        Compound expressions (match, if, block) are void when all
        branches/the final expression are void.

        # WALKER_COVERAGE: (#597 — positive-filter walker; default
        # `return False` is correct for every Expr that produces a
        # value.  Every Expr below has a disposition.)
        #
        # Handled (may be void; checked explicitly):
        #   QualifiedCall     → True for void IO ops (print/exit/sleep/stderr)
        #   UnitLit           → always True
        #   FnCall            → True if user fn declared @Unit return
        #   AssertExpr        → always True (returns Unit)
        #   AssumeExpr        → always True (returns Unit)
        #   MatchExpr         → True if all arm bodies are void
        #   IfExpr            → True if both branches are void
        #   Block             → True if trailing expr is void
        #   HandleExpr        → True if body is void
        #
        # Intentionally ignored (default `return False` = produces value):
        #   IntLit            → always Int (i64) on stack
        #   FloatLit          → always Float64 (f64) on stack
        #   BoolLit           → always Bool (i32) on stack
        #   StringLit         → always String (i32 pair) on stack
        #   InterpolatedString → always String (i32 pair) on stack
        #   SlotRef           → always type-matched value on stack
        #   ResultRef         → always type-matched value on stack
        #   BinaryExpr        → arith/cmp/logic — always produces value
        #   UnaryExpr         → neg/not — always produces value
        #   IndexExpr         → element value on stack
        #   ArrayLit          → Array (i32 pair) on stack
        #   ConstructorCall   → ADT (i32) on stack
        #   NullaryConstructor → ADT (i32) on stack
        #   AnonFn            → closure handle (i32) on stack
        #   ModuleCall        → return value on stack
        #   ForallExpr        → Bool (i32) on stack
        #   ExistsExpr        → Bool (i32) on stack
        #
        # Cannot occur (rejected before reaching codegen):
        #   HoleExpr          → parser placeholder; check time rejects
        #   OldExpr           → contract-only
        #   NewExpr           → contract-only
        """
        if isinstance(expr, ast.QualifiedCall):
            # IO.print/sleep/stderr return Unit (void);
            # IO.exit never returns (unreachable);
            # Other IO ops (read_line, read_file, time, args, get_env)
            # produce values.
            if expr.qualifier == "IO":
                return expr.name in ("print", "exit", "sleep", "stderr")
            # Http ops return Result<String, String> — not void
            if expr.qualifier == "Http":
                return False
            # Inference.complete returns Result<String, String> — not void
            if expr.qualifier == "Inference":
                return False
            # All Random ops produce values (Int, Float64, or Bool); never void. (#465)
            if expr.qualifier == "Random":
                return False
            # State ops are desugared to FnCall, not QualifiedCall.
            # Future qualified effects should be added explicitly above.
            # Default to void for unknown qualified calls as a safe
            # fallback — WASM validation will catch mismatches.
            return True
        if isinstance(expr, ast.UnitLit):
            return True
        if isinstance(expr, ast.FnCall) and expr.name in self._effect_ops:
            _name, is_void = self._effect_ops[expr.name]
            return is_void
        # User-defined fns declared with @Unit return type — registry stores
        # them with value None alongside non-void returns.  Without this
        # clause a `helper(); next_expr` block where `helper` is a user
        # @Unit fn fell through to "produces a value", got a stray `drop`
        # appended, and failed WASM validation with "expected a type but
        # nothing on stack" (#584).
        if isinstance(expr, ast.FnCall) and expr.name in self._fn_ret_types:
            return self._fn_ret_types[expr.name] is None
        if isinstance(expr, (ast.AssertExpr, ast.AssumeExpr)):
            return True  # assert/assume return Unit (void)
        # Compound expressions: void if all branches are void
        if isinstance(expr, ast.MatchExpr):
            return all(self._is_void_expr(arm.body) for arm in expr.arms)
        if isinstance(expr, ast.IfExpr):
            return (self._is_void_expr(expr.then_branch)
                    and self._is_void_expr(expr.else_branch))
        if isinstance(expr, ast.Block):
            return self._is_void_expr(expr.expr)
        if isinstance(expr, ast.HandleExpr):
            return self._is_void_expr(expr.body)
        return False

    def _is_pair_result_expr(self, expr: ast.Expr) -> bool:
        """Check if an expression produces two values (ptr, len) on the stack.

        String literals, array literals, pair-type slot refs, and function
        calls returning i32_pair all produce two values.
        """
        if isinstance(expr, ast.StringLit):
            return True
        if isinstance(expr, ast.InterpolatedString):
            return True
        if isinstance(expr, ast.ArrayLit):
            return True
        if isinstance(expr, ast.SlotRef):
            name = self._resolve_base_type_name(expr.type_name)
            return self._is_pair_type_name(name)
        if isinstance(expr, ast.FnCall):
            ret = self._infer_fncall_wasm_type(expr)
            return ret == "i32_pair"
        if isinstance(expr, ast.QualifiedCall):
            ret = self._infer_qualified_call_wasm_type(expr)
            return ret == "i32_pair"
        return False
