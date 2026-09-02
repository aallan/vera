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

from typing import TYPE_CHECKING, Callable

from vera import ast
from vera.naming import EMPTY_ALIAS_ENV, AliasEnv
from vera.skip import (
    DERIVED_HELPER_DEPTH_CAP,
    CodegenInvariantError,
    CodegenSkip,
)
from vera.slots import bare_call_denotes_user_fn

if TYPE_CHECKING:
    from vera.codegen import ConstructorLayout

from vera.wasm.helpers import (  # noqa: F401 — re-exported for consumers
    _INLINE_I32_TYPES,
    CellNames,
    StateClauseEntry,
    StringPool,
    WasmSlotEnv,
    contains_shadow_push,
    gc_shadow_push,
    is_gc_pointer_base,
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
        effect_op_result_wt: dict[str, str | None] | None = None,
        effect_op_result_vera: dict[str, str | None] | None = None,
        effect_op_cells: dict[str, CellNames] | None = None,
        state_getters: dict[str, str] | None = None,
        ctor_layouts: dict[str, ConstructorLayout] | None = None,
        adt_type_names: set[str] | None = None,
        generic_fn_info: (
            dict[str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]] | None
        ) = None,
        generic_constrained_vars: dict[str, frozenset[str]] | None = None,
        ctor_to_adt: dict[str, str] | None = None,
        known_fns: set[str] | None = None,
        scoped_fns: set[str] | None = None,
        ctor_adt_tp_indices: dict[str, tuple[int | None, ...]] | None = None,
        adt_tp_counts: dict[str, int] | None = None,
        adt_tp_param_names: dict[str, tuple[str, ...]] | None = None,
    ) -> None:
        self.string_pool = string_pool
        self._next_local: int = 0
        self._locals: list[tuple[str, str]] = []  # (name, wat_type)
        self._result_local: int | None = None
        # Effect operation mapping: op_name -> (wasm_call_target, is_void)
        # e.g. {"get": ("$vera.state_get_Int", False),
        #        "put": ("$vera.state_put_Int", True)}
        self._effect_ops = effect_ops or {}
        # #914: op_name -> the op's RESULT WAT type (e.g. "get" -> "i64" for
        # State<Int>, "i32" for State<Box>).  `_effect_ops` carries only the
        # dispatch target + void-ness, not the value-producing op's result
        # type, which `_infer_expr_wasm_type` needs when a bare `get(())`
        # sits in a constructor-argument or match-scrutinee position (A1/A2).
        # Populated in lock-step with `_effect_ops` at every injection site
        # (the declared-effect path in codegen/functions.py and the handler-
        # body path in wasm/calls_handlers.py) so the two never drift.
        self._effect_op_result_wt: dict[str, str | None] = (
            effect_op_result_wt or {}
        )
        # #1006: op_name -> the op's RESULT VERA type name (e.g. "get" ->
        # "Int" for State<Int>).  The WAT-type mirror above cannot serve
        # `_infer_vera_type` (i32 is Bool/pointer/…-ambiguous), which needs
        # the Vera name when a bare `get(())` sits in an array-literal
        # ELEMENT position — the element layout is chosen from the Vera
        # type.  Populated in lock-step with `_effect_op_result_wt` at both
        # injection sites (codegen/functions.py declared-effect path and
        # wasm/calls_handlers.py handler-body path) and saved/restored the
        # same way, so the three op registries never drift.
        self._effect_op_result_vera: dict[str, str | None] = (
            effect_op_result_vera or {}
        )
        # #1218: op_name -> the CELL that op dispatches to, as the canonical
        # pair :class:`CellNames` (identity + representation).  The fourth
        # registry in the lock-step set, populated at the same two injection
        # sites and saved/restored the same way.  It exists so a call site
        # can ask "which cell is this?" from the canonical side: the answers
        # used to be recovered by slicing the mangled family back out of the
        # op's own `$vera.state_put_…` dispatch target, which is a SECOND
        # derivation of the family — and re-mangling an already-mangled name
        # is the exact non-idempotence trap #1233's round-5 review found.
        # Only State get/put have entries; `throw` and user-effect ops reach
        # no host cell and are absent.
        self._effect_op_cells: dict[str, CellNames] = effect_op_cells or {}
        # #1285: cell FAMILY -> that cell's `$vera.state_get_<T>` import.
        # The four registries above are keyed by op NAME, which is the right
        # key for a call site (`get(())` names no family, so it means
        # whichever cell the row or the enclosing handler binds) and the
        # wrong key for a contract: `new(State<Bool>)` names its family
        # explicitly, exactly as `old(State<Bool>)` does.  Reading the
        # name-keyed registry gave `new()` whichever family's getter was
        # installed LAST, so under `effects(<State<Int>, State<Bool>>)` a
        # `new(State<Bool>)` read `state_get_Int` — an i64 into the Bool
        # comparison's `i32.eq`, check-green and verify-green, dead at load.
        # Keyed and populated so `new()` resolves the way `old()` already
        # did (`_state_effect_family` on both sides), and NOT filtered by
        # bare-call ownership (#1284): a contract form names the effect, so
        # a user `fn get` cannot shadow it.
        self._state_getters: dict[str, str] = state_getters or {}
        # #976 option C: op_name -> :class:`StateClauseEntry` for the
        # innermost enclosing ``handle[State<T>]``.  When a get/put call site
        # has an entry here, the clause BODY is inlined at the site
        # (intrinsic-hybrid semantics: intrinsic store/read, clause executes,
        # ``resume(v)`` is the op's result, ``with`` overrides the store).
        # Empty for a declared-``effects(<State<T>>)`` function with no
        # handler — those keep the bare host-cell call.  Saved/restored
        # around each handler body exactly like ``_effect_ops`` (nested
        # handlers).  The entry carries the handler-DECLARATION scope the
        # clause compiles in: see :class:`StateClauseEntry`.
        self._state_clause_ops: dict[str, StateClauseEntry] = {}
        # True while translating an inlined State clause body/`with` expr —
        # gates the ``resume(v)`` lowering (v IS the op's result value).
        self._in_state_clause: bool = False
        # The active clause's cell REPRESENTATION name while translating
        # it — lets the resume lowering apply the #865 Byte-literal width
        # coercion (`resume(0)` in a `State<Byte>` get clause is the
        # op's i32 result).  The BASE rather than the family (#1218): a
        # refined `Byte` cell has its own family and the same i32 width.
        self._state_clause_family_base: str | None = None
        # #1233: the host cell stack, as FAMILIES, at the current emission
        # point — one entry per enclosing `handle[State<T>]` whose
        # `state_push_T` has run, innermost last.  Maintained by
        # `_translate_handle_state` around its handled body.
        self._pushed_cell_families: list[str] = []
        # The index into `_pushed_cell_families` from which the cells are
        # SHADOWS of the scope the current op registries belong to.  Equal to
        # `len(_pushed_cell_families)` inside a handled body (an op there
        # reaches the innermost cell, which is its own handler's); rolled back
        # to the handler's DECLARATION-time value while an inlined clause body
        # is translated, because a bare op there resolves into that
        # declaration scope (#1211) while the intrinsics still address the
        # innermost cell of the family.  A family occurring in
        # `_pushed_cell_families[_addressable_from:]` is therefore
        # unreachable — refused loudly rather than compiled to hybrid
        # semantics (see `_reject_unaddressable_clause_op`).
        self._addressable_from: int = 0
        # #1211: how many clause bodies are being inlined into one another
        # right now.  Each outward re-entry re-expands another clause, so the
        # emitted code is exponential in this depth — bounded by
        # `STATE_CLAUSE_INLINE_DEPTH_CAP`.
        self._clause_inline_depth: int = 0
        # Constructor layout mapping: ctor_name -> ConstructorLayout
        self._ctor_layouts: dict[str, ConstructorLayout] = ctor_layouts or {}
        # ADT type names for slot/param type resolution
        self._adt_type_names: set[str] = adt_type_names or set()
        # Generic function info for call rewriting:
        # fn_name -> (forall_vars, param_type_exprs)
        self._generic_fn_info: dict[
            str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]
        ] = generic_fn_info or {}
        # Per-generic set of type vars carrying an ability bound (`where Eq<T>`).
        # Used by `_unify_param_arg_wasm` to keep a `ConstructorCall`'s type
        # argument when rewriting the call site, so the mangled call name matches
        # the parameterized clone Pass 1.5 emitted (#772).
        self._generic_constrained_vars: dict[str, frozenset[str]] = (
            generic_constrained_vars or {}
        )
        # Constructor name → ADT name reverse mapping
        self._ctor_to_adt: dict[str, str] = ctor_to_adt or {}
        # Every WASM symbol this compilation registered — the REGISTRATION
        # question, and only that: `_translate_call`'s guard rail asks whether
        # a RESOLVED call target (already mono-mangled, already `mod$…`
        # rerouted) has an implementation to land on.  Flat by nature; a
        # symbol emitted for some other namespace is still a symbol.
        self._known_fns: set[str] = known_fns or set()
        # The names visible in the compiling declaration's LEXICAL scope —
        # #1284's ownership question, which is a different one (#1299).
        # Splitting them is the fix: one table answers "does this symbol
        # exist?", the other "whose declaration does this bare name denote
        # HERE?", and answering the second with the first is what let an
        # invisible import claim a call site's `get`.  Defaults to
        # ``known_fns`` so a context built without one keeps the flat
        # answer rather than silently owning NO name — an empty scope would
        # route every bare call to the op registries, which is the opposite
        # error and a far louder one.
        # Stack shapes recorded by a lowering that installs its own
        # scope, keyed by expression id (#1371).  See `_stack_shape_of`.
        self._scoped_expr_shape: dict[int, str] = {}
        self._scoped_fns: set[str] = (
            self._known_fns if scoped_fns is None else scoped_fns
        )
        # Per-field ADT type-param indices for sparse constructors (e.g. Err → (1,))
        self._ctor_adt_tp_indices: dict[str, tuple[int | None, ...]] = (
            ctor_adt_tp_indices or {}
        )
        # Maps ADT name → number of type parameters
        self._adt_tp_counts: dict[str, int] = adt_tp_counts or {}
        # #773: ADT name → ordered type-parameter NAMES, for structural-Eq
        # substitution inside parameterized field types (`List<T>` → `List<Int>`)
        self._adt_tp_param_names: dict[str, tuple[str, ...]] = (
            adt_tp_param_names or {}
        )
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
        # #841: fused-async host-import tracking (async_http_get /
        # async_http_post / async_await; propagated to codegen core)
        self._async_ops_used: set[str] = set()
        # #841: names of functions whose declared return type is
        # exactly Future<Result<String, String>> — the await lowering
        # consults this to decide whether a directly-awaited call
        # result needs the fused-handle runtime check.  Computed once
        # in vera/codegen/core.py (compute_future_ret_fns) and shared
        # with the compilability pre-scan; set via set_future_ret_fns.
        self._future_ret_fns: frozenset[str] = frozenset()
        # #841 round 2: qualified companion for ModuleCall awaits.
        self._future_ret_module_fns: frozenset[
            tuple[tuple[str, ...], str]
        ] = frozenset()
        # Inference host-import tracking (propagated to codegen core)
        self._inference_ops_used: set[str] = set()
        # DB host-import tracking (#229; propagated to codegen core)
        self._db_ops_used: set[str] = set()
        # Random host-import tracking (propagated to codegen core, #465)
        self._random_ops_used: set[str] = set()
        # Math host-import tracking (propagated to codegen core, #467)
        self._math_ops_used: set[str] = set()
        # #808: the #798 integer-overflow guard calls $vera.overflow_trap so the
        # trap classifies as kind="overflow" rather than bare "unreachable".
        # Set in operators._emit_overflow_guard; merged into codegen core (which
        # emits the import) in functions.py after each function is compiled (and
        # in closures.py for lifted-closure bodies).
        self._needs_overflow_trap: bool = False
        # #773: structural-Eq helper functions this context generated, keyed by
        # the mangled `$eq_<type>` function name → its full WAT text.  Each
        # helper takes two i32 ADT pointers and returns i32 (1 = equal).  A
        # nested-ADT field recurses by calling another entry here (generated on
        # demand, deduped by name so a recursive/self-referential ADT emits one
        # function).  Merged into the CodeGenerator core after each function /
        # closure body compiles (functions.py / closures.py), then emitted once
        # at module assembly (assembly.py) — the same propagate-then-emit shape
        # as the host-import "needs" families.
        self._adt_eq_helpers: dict[str, str] = {}
        # Names of eq-helpers already requested (guards recursion during
        # generation before the body is stored in ``_adt_eq_helpers``).
        self._adt_eq_pending: set[str] = set()
        # #773 / PR #870 review: derivability oracle for the DIRECT `==` path
        # — the CodeGenerator's `_adt_satisfies_eq` bound method (the same
        # E613 gate the generic constraint path consults), injected via
        # `set_adt_eq_derivable` in functions.py / closures.py so there is
        # exactly ONE derivability implementation.  When None (a bare
        # WasmContext in unit tests), the gate is skipped and generation
        # proceeds as before.
        self._adt_eq_derivable: Callable[[str], bool] | None = None
        # #932: TRUNCATED one-level constrained-var name → FULLY-recovered nested
        # name (`List<List>` → `List<List<Int>>`).  Populated by Pass 1.5
        # monomorphization (`_collect_eq_full_type_names`) and consulted for the
        # Eq-derivability DECISION only — by the constraint gate
        # (`_check_constraints`) and by the direct-`==` path inside a clone body
        # (`_translate_binary`).  Never keys a clone symbol, so the clone-mangling
        # contract stays the truncated one-level name (the #772 hard constraint).
        # Empty for a bare WasmContext (no mono pass) — a plain dict lookup then
        # leaves every name unchanged.
        self._eq_full_type_names: dict[str, str] = {}
        # #924: generated recursive show/hash helper functions, keyed by the
        # mangled `$show_<type>` / `$hash_<type>` function name → its full WAT
        # text.  A directly- (or mutually-) recursive ADT's `show`/`hash`
        # cannot render inline (unbounded depth), so it emits a self-calling
        # helper — one per recursive type — that recurses over the finite
        # value.  Mirrors `_adt_eq_helpers` (#773): merged into the
        # CodeGenerator core after each body compiles, emitted once at module
        # assembly, and guarded against re-entry via `_show_hash_pending`.
        self._show_hash_helpers: dict[str, str] = {}
        self._show_hash_pending: set[str] = set()
        # #933: nesting-depth bound for the derived-helper generators
        # (`$show_<type>` / `$hash_<type>` / `$eq_<type>`).  A UNIFORMLY-
        # recursive ADT (`List<T>` whose tail is again `List<T>`) recurs on the
        # SAME parameterized type and is caught by the per-generator `_seen` /
        # `_..._pending` guards at generation depth 1 — one helper per type.  A
        # POLYMORPHICALLY-recursive (non-uniform) ADT
        # (`Box<T>` with a `Box<Box<T>>` field) mints a DISTINCT, strictly
        # deeper type at every descent (`Box<Box<Int>>`, `Box<Box<Box<Int>>>`,
        # …), so those guards never fire and generation recurs unboundedly into
        # a raw Python ``RecursionError`` on a check-green program — the exact
        # traceback-on-valid-input DESIGN.md principle 1 forbids.  These fields
        # cap the distinct-ptype expansion: on exceeding the cap the generator
        # returns the same "unsupported" signal an unrenderable field produces,
        # so the enclosing helper falls back to the clean E602 (show/hash) /
        # E613 (eq) skip that non-recursive-unsupported types already take.  The
        # cap sits far above every legitimate uniform shape (measured max
        # generation depth 1) yet far below Python's recursion limit, so the
        # bound degrades DETERMINISTICALLY regardless of that limit.  The cap
        # itself is shared with the Eq-derivability gate (see
        # ``vera.skip.DERIVED_HELPER_DEPTH_CAP``) so all three derived-helper
        # walks bound at the same depth.
        self._derived_helper_depth: int = 0
        self._derived_helper_depth_cap: int = DERIVED_HELPER_DEPTH_CAP
        # Function return WASM types for type inference:
        # fn_name → return_wasm_type (str | None)
        self._fn_ret_types: dict[str, str | None] = {}
        # #814 §8.5.3: (module path, fn name) → WASM target name for a
        # module-qualified call.  Lets `m::f` bypass a local shadow.
        self._module_qualified_targets: dict[
            tuple[tuple[str, ...], str], str
        ] = {}
        # #814/#774: (module path, generic name) → the ``mod$…`` mono BASE for
        # an imported generic whose bare name a local shadows.  The ModuleCall
        # desugar rewrites `m::gen(…)` to a FnCall on this base, which is a key
        # in `_generic_fn_info`, so `_resolve_generic_call` mangles it to the
        # emitted clone (`mod$m$gen$Int`) instead of the local shadow's bare
        # `gen`.  Empty unless the program qualified-calls a shadowed generic.
        self._module_qualified_generic_bases: dict[
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
        # #813: per-parameter concrete-@Int flags, the dual, for the runtime
        # @Nat -> @Int widening guard at call sites.
        self._fn_int_params: dict[str, tuple[bool, ...]] = {}
        # #865: per-parameter concrete-@Byte flags, for the call-site
        # int-literal → i32.const coercion (spec §11 — @Byte is i32).
        self._fn_byte_params: dict[str, tuple[bool, ...]] = {}
        # #1212: `IntLit` nodes this context lowers at the i32 Byte width.
        # Populated by `_mark_byte_literal_leaves`, the ONE branch descent
        # every #865 arm drives through `_mark_byte_write_value`; read by
        # the `IntLit` lowering and by the two join result-type deciders, so
        # a marked leaf and the `(result …)` annotation over it agree.
        self._byte_literal_ids: set[int] = set()
        # Closure compilation state — accumulated during translation
        # Each entry: (anon_fn, captures, closure_id)
        # captures: list of (type_name, outer_de_bruijn, wasm_type)
        self._pending_closures: list[
            tuple[ast.AnonFn, list[tuple[str, int, str]], int]
        ] = []
        # #1208: the naming environment — alias name -> body TypeExpr (for
        # FnType resolution) and alias name -> declared parameter names (for
        # generic aliases), as ONE value instead of two maps that could be
        # swapped independently and fall out of step (the #1184 mispairing).
        # Seeded empty; codegen calls `set_alias_env` before translation.
        self._alias_env: AliasEnv = EMPTY_ALIAS_ENV
        # #1268: lower a refinement predicate to a boundary guard over a
        # value already in a local.  Injected by codegen via
        # `set_refinement_guard_emitter`, because the two halves of a §2.6.5
        # guard live on opposite sides of this seam: the REPRESENTATION half
        # — which local, at what width, in what order relative to the value
        # on the stack — is this context's, while lowering it needs the string
        # pool's trap message, the `$vera.contract_fail` import flag and the
        # E617/E618 diagnostics, all of which are the generator's.  The same
        # injection shape as `set_adt_eq_derivable`.  `None` until installed:
        # a context translating a `throw` without it FAILS CLOSED (a loud
        # skip), never silently unguarded — see
        # `_emit_exn_payload_refine_guard`.  A lifted-closure context is
        # deliberately left at `None`: it carries no `effect_op_cells`, so no
        # `throw` there is a write boundary this could guard (it does not
        # compile at all today), and the closed failure is what a future
        # thread-through would meet rather than a silently unguarded payload.
        self._refinement_guard_emitter: (
            Callable[[ast.TypeExpr, int, str, WasmSlotEnv], list[str] | None]
            | None
        ) = None
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
        # #758/#983 — per-narrowing-leaf @Int->@Nat return guard.  The set of
        # ``id(leaf)`` tail-position return leaves that narrow into a @Nat
        # return, so ``translate_expr`` / the block-trailing / match-arm
        # emission sites wrap EACH such leaf with ``_emit_nat_bind_guard``
        # inline (mirroring the verifier 7d leaf descent) rather than wrapping
        # the whole body.  The whole-body wrap reverted EVERY ``return_call`` —
        # breaking TCO for a non-narrowing @Nat->@Nat recursive tail call
        # (`drain`) that stack-exhausted at depth (the #983 regression).
        # Populated per-fn by ``CodeGenerator._compile_fn``; defaults empty so
        # closure bodies and untargeted contexts guard nothing.
        self._nat_return_leaf_ids: set[int] = set()
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
        # #820: the checker's TARGET-type side-table (``expected`` per expr
        # span).  Consulted by ``_target_codegen_type`` — the codegen dual of
        # the verifier's ``_target_type_of`` — so the @Nat -> @Int widening
        # guard fires at a tuple component / array element / heterogeneous
        # if-arm exactly where the verifier obligates it.  ``None`` when
        # typecheck was skipped (those component sites stay E531-disclosed).
        self._expr_target_types: (
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

    def set_expr_target_types(
        self,
        types: dict[tuple[int, int, int, int], object] | None,
    ) -> None:
        """Seed the checker's TARGET-type side-table (#820) for the
        @Nat -> @Int widening guard's per-component target-type recovery
        (``_target_codegen_type`` — the dual of the verifier's
        ``_target_type_of``)."""
        self._expr_target_types = types

    def set_fn_ret_types(
        self, ret_types: dict[str, str | None],
    ) -> None:
        """Set function return WASM types for FnCall type inference."""
        self._fn_ret_types = ret_types

    def set_adt_eq_derivable(
        self, oracle: Callable[[str], bool],
    ) -> None:
        """Set the structural-Eq derivability oracle for direct `==` (#773).

        ``oracle`` is the CodeGenerator's ``_adt_satisfies_eq`` bound method —
        the SAME gate the generic constraint path consults — so the direct
        comparison path rejects exactly the set the E613 gate rejects.
        """
        self._adt_eq_derivable = oracle

    def set_eq_full_type_names(self, full_names: dict[str, str]) -> None:
        """Share the truncated→full constrained-var name map (#932).

        ``full_names`` is the CodeGenerator's ``_eq_full_type_names``, populated
        by Pass 1.5 monomorphization BEFORE any body is translated.  The direct
        ``==`` path inside a generic clone body (`_translate_binary`) consults it
        so a `@T` slot whose substituted type is the TRUNCATED one-level clone
        name (`List<List>`) resolves its Eq derivability and its `$eq_<type>`
        helper on the FULLY-nested name (`List<List<Int>>`) — matching the
        constraint gate.  The clone SYMBOL stays the truncated name (#772).
        """
        self._eq_full_type_names = full_names

    def set_future_ret_fns(
        self,
        names: frozenset[str],
        module_fns: frozenset[tuple[tuple[str, ...], str]] = frozenset(),
    ) -> None:
        """Set the Future<Result<String, String>>-returning fn sets (#841)."""
        self._future_ret_fns = names
        self._future_ret_module_fns = module_fns

    def set_module_qualified_targets(
        self, targets: dict[tuple[tuple[str, ...], str], str],
    ) -> None:
        """Set the (module path, fn name) → WASM target map (#814 §8.5.3)."""
        self._module_qualified_targets = targets

    def set_module_qualified_generic_bases(
        self, bases: dict[tuple[tuple[str, ...], str], str],
    ) -> None:
        """Set the (module path, generic name) → ``mod$…`` mono base map
        for a shadowed imported generic reached via ``m::gen`` (#814/#774)."""
        self._module_qualified_generic_bases = bases

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

    def set_fn_int_params(
        self, int_params: dict[str, tuple[bool, ...]],
    ) -> None:
        """Set per-parameter concrete-@Int flags for the call-site
        runtime @Nat -> @Int widening guard (#813)."""
        self._fn_int_params = int_params

    def set_fn_byte_params(
        self, byte_params: dict[str, tuple[bool, ...]],
    ) -> None:
        """Set per-parameter concrete-@Byte flags for the call-site
        int-literal → i32.const coercion (#865)."""
        self._fn_byte_params = byte_params

    def set_alias_env(self, env: AliasEnv) -> None:
        """Set the naming environment for alias resolution (#1208).

        Replaces the former ``set_type_aliases`` / ``set_type_alias_params``
        pair.  The two maps have to be overlaid together — a module alias
        shadowing a *parameterised* prelude alias with a *non*-parameterised
        one must not inherit the prelude's parameter list (#1184) — so they
        travel as one value that cannot be half-updated.
        """
        self._alias_env = env

    def set_refinement_guard_emitter(
        self,
        emitter: Callable[
            [ast.TypeExpr, int, str, WasmSlotEnv], list[str] | None
        ],
    ) -> None:
        """Install the §2.6.5 refinement-predicate guard lowering (#1268).

        *emitter* takes ``(type_expr, value_local, message, env)`` and returns
        the WAT that traps via ``$vera.contract_fail`` when the value in
        *value_local* violates *type_expr*'s predicate — or ``None`` when the
        type is unrefined, or refined over a base codegen emits no guard for
        (an erased ``@Unit``, a nested refinement).  Codegen binds it to
        ``CodeGenerator._emit_boundary_refinement_guard`` for THIS context, so
        the trap message interns into the shared string pool and the
        contract-fail import flag is raised on the generator that assembles
        the module.
        """
        self._refinement_guard_emitter = emitter

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

    def _bare_call_denotes_op(self, name: str) -> bool:
        """Is a BARE call to *name* here the effect operation? (#1284)

        Codegen's leg of :func:`~vera.slots.bare_call_denotes_user_fn`, over
        ``_scoped_fns`` — the names visible in the compiling declaration's
        LEXICAL scope, which is the table the checker resolves against.
        Every bare-call site that consults an op registry asks this first,
        so a name the checker resolved to a user declaration is lowered as
        the ordinary call the checker typed: the clause-inline dispatch, the
        host-cell intrinsics, the #1233 addressability gate, the three
        result-type inference sites, and ``_handle_exn_always_throws``'s
        ``throw_installed`` question, which is the same one for ``Exn``'s
        operation.

        Not for the QUALIFIED spelling: ``State.get(())`` names the effect,
        so no declaration can shadow it and the registries answer directly.

        NOT ``_known_fns`` (#1299).  That set is the registration table the
        guard rail reads, and it is flat by construction — every symbol the
        whole compilation absorbed, including a module's ``private fn get``,
        a public one a selective import excludes, and the bare key a
        ``forall<T>`` parent's ``where`` helper keeps beside its
        clone-qualified one.  Asked over it, this predicate answered
        "user-owned" at a site where the checker had resolved the operation:
        check-green source ran the invisible declaration's body where the
        widths agreed, and failed to load where they did not.
        """
        return not bare_call_denotes_user_fn(name, self._scoped_fns)

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
    # #1212 — the @Byte write boundary's literal width
    # -----------------------------------------------------------------

    def _mark_byte_literal_leaves(self, value: ast.Expr) -> bool:
        """Mark every value-position ``IntLit`` LEAF of *value* as i32.

        THE branch descent for the ``@Byte`` write boundaries (#1212).
        ``@Byte`` is i32 (spec §11) but an int literal defaults to
        ``i64.const``, and #865 coerced a literal only when it was the whole
        written value.  The checker's bidirectional coercion types a branch
        literal as ``@Byte`` just as happily, so ``let @Byte = if c then { 1 }
        else { 2 }`` — and its init / put / ``with`` / resume / argument /
        constructor-field twins — were check-green programs that failed WASM
        validation with ``type mismatch: expected i32, found i64``.

        Descends exactly the JOIN positions whose arms carry the boundary's
        own type: a ``Block``'s trailing expression, both branches of an
        ``IfExpr``, and every arm body of a ``MatchExpr`` (single- and
        multi-arm alike).  Everything else is a leaf that is not a literal
        and already lowers at i32 in a Byte context, so it is left alone.

        Returns True iff at least one literal was marked, which is what tells
        the caller the join lowers at i32 — a join with no literal arm
        (``if c then { @Byte.0 } else { @Byte.1 }``) already did, and is
        deliberately not claimed here.

        One descent shared by every #865 arm, rather than an ``isinstance``
        test repeated per site: a site that tested for a bare ``IntLit`` was
        precisely a site that emitted invalid WASM for the branch spelling.
        """
        if isinstance(value, ast.IntLit):
            self._byte_literal_ids.add(id(value))
            return True
        if isinstance(value, ast.Block):
            return self._mark_byte_literal_leaves(value.expr)
        if isinstance(value, ast.IfExpr):
            marked = self._mark_byte_literal_leaves(value.then_branch)
            if value.else_branch is not None:
                marked = self._mark_byte_literal_leaves(
                    value.else_branch) or marked
            return marked
        if isinstance(value, ast.MatchExpr):
            marked = False
            for arm in value.arms:
                marked = self._mark_byte_literal_leaves(arm.body) or marked
            return marked
        return False

    def _mark_byte_write_value(
        self, value: ast.Expr, target_base: str | None,
    ) -> bool:
        """Prepare *value* to be translated into a ``@Byte`` boundary.

        THE entry every #865 arm calls — the `let` binding, the five
        State-cell writes, the constructor field and the call argument —
        BEFORE it translates *value*, so the marks are in place when the
        ``IntLit`` lowering and the join result-type deciders read them.
        Marking rather than returning instructions is what keeps the value
        translated exactly ONCE: the arms that used to overwrite an
        already-translated ``i64`` lowering with a coerced one discarded a
        whole join's translation (and the locals and pending closures it
        registered) to do it.

        *target_base* is the boundary's resolved REPRESENTATION name; a
        non-``Byte`` boundary marks nothing and returns False.
        """
        if target_base != "Byte":
            return False
        return self._mark_byte_literal_leaves(value)

    # -----------------------------------------------------------------
    # Expression translation
    # -----------------------------------------------------------------

    def translate_expr(
        self, expr: ast.Expr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a Vera AST expression, scoping its GC shadow roots.

        THE root-lifetime rule (#1371), stated once: an expression's shadow
        roots live exactly as long as the expression is forming its value.
        Lower the expression, restore ``$gc_sp`` to where it stood before,
        and re-root the value itself when the value is a heap pointer — so
        what survives an expression is the one thing it produced, and its
        temporaries are gone.

        Before this, every root a lowering made lived for the FRAME: the only
        reclamation was the function epilogue's ``$gc_sp`` restore, which runs
        once, on the way out.  So a frame's shadow use grew with the number of
        pointer-producing expressions its body contained, whether or not any
        of them were still live — ``string_length(string_concat(s, "y"))``
        repeated K times cost K permanent roots for K values that died
        immediately.  With the shadow stack at 4 096 roots, the depth a
        recursion could reach was a function of how much its body allocated
        on the way past, and overflow is a bare ``unreachable``.  #1322 was
        this defect in its match-shaped form; ``_scope_match_shadow_roots``
        was its match-shaped fix, and this is that fix generalised — one
        discipline, one place, with the match as an ordinary case of it.

        Returns a list of WAT instruction strings, or None if the
        expression contains unsupported constructs (function skipped).
        """
        instructions = self._translate_expr_unscoped(expr, env)
        if instructions is None:
            return None
        return self._scope_shadow_roots(expr, instructions)

    def _scope_shadow_roots(
        self, expr: ast.Expr, instructions: list[str]
    ) -> list[str]:
        """Wrap *instructions* in a ``$gc_sp`` save / restore / re-root.

        The emission discipline is the function epilogue's, verbatim
        (``gc_prologue`` / ``gc_epilogue`` in ``vera/codegen/functions.py``):
        save, lower, restore, push the result back if it is a pointer.

        Emitted ONLY when this expression's lowering actually pushed
        (:func:`contains_shadow_push`).  That is not an optimisation.  A
        function whose lowering never sets ``needs_alloc`` gets no ``$gc_sp``
        global at all, so an unconditional wrapper would read a global that
        does not exist; and gating on the push keeps the emitted WAT of every
        non-rooting expression — every literal, every slot reference, every
        scalar arithmetic tree — byte-identical.

        The re-root is load-bearing, and measured rather than asserted:
        delete it and ``TestMatchResultReRootIsLoadBearing1322`` reads back a
        freed-and-reused block.  The cells that show it need all three of a
        result that is NOT ``let``-bound (a ``let`` roots what it binds and
        supplies the missing root), a sibling call argument that allocates
        while the result sits on the operand stack, and an assertion on
        CONTENT — a freed block nothing has overwritten yet still reads back
        correctly, so a length check passes on a real use-after-free.  Those
        cells are this change's canary in the other direction too: a restore
        placed too EAGERLY fails them the same way.

        Declines, leaving the instructions untouched, when the expression's
        stack shape is unrecoverable.  Guessing it wrong is not a missed
        reclamation but invalid WASM (a ``local.set`` against an empty
        operand stack), so an unknown shape keeps the pre-#1371 behaviour:
        the root outlives its value, which is wasteful and sound.
        """
        if not contains_shadow_push(instructions):
            return instructions
        if not self.needs_alloc:
            # A push was emitted, so `$gc_sp` must have been declared.  Every
            # producer sets the flag beside its push; a new one that forgets
            # would emit a module referencing an undeclared global, and this
            # says so at the seam rather than at WAT assembly.
            raise CodegenInvariantError(
                f"{type(expr).__name__} lowering emitted a GC shadow push "
                "without setting needs_alloc, so `$gc_sp` would not be "
                "declared"
            )
        shape = self._stack_shape_of(expr)
        if shape == "unknown":
            return instructions
        save_local = self.alloc_local("i32")
        scoped = ["global.get $gc_sp", f"local.set {save_local}"]
        scoped.extend(instructions)
        restore = [f"local.get {save_local}", "global.set $gc_sp"]
        if shape == "void":
            scoped.extend(restore)
            return scoped
        if shape == "i32_pair":
            # (ptr, len): the pointer half is a heap pointer by construction
            # — the pair convention has no non-pointer form.
            ret_ptr = self.alloc_local("i32")
            ret_len = self.alloc_local("i32")
            scoped.append(f"local.set {ret_len}")
            scoped.append(f"local.set {ret_ptr}")
            scoped.extend(restore)
            scoped.extend(gc_shadow_push(ret_ptr))
            scoped.append(f"local.get {ret_ptr}")
            scoped.append(f"local.get {ret_len}")
            return scoped
        ret_local = self.alloc_local(shape)
        scoped.append(f"local.set {ret_local}")
        scoped.extend(restore)
        if shape == "i32" and self._expr_result_is_pointer(expr):
            scoped.extend(gc_shadow_push(ret_local))
        scoped.append(f"local.get {ret_local}")
        return scoped

    def _scope_statement_roots(
        self,
        stmt_instrs: list[str],
        before_env: WasmSlotEnv,
        after_env: WasmSlotEnv,
        save_local: Callable[[], int],
    ) -> list[str]:
        """Give one statement's GC shadow roots STATEMENT lifetime (#1371).

        Restores ``$gc_sp`` to where the statement found it and then roots
        what the statement BOUND — the environment delta — so a statement
        leaves behind exactly its bindings and none of the temporaries that
        produced them.  An expression statement binds nothing, so its value
        and every intermediate that built it are reclaimed; a `let` leaves
        one root per heap-pointer binding, which is correct, since a binding
        is live to the end of its block.

        Which bindings are heap pointers is the rule the producers used
        before this consolidated them: a pair binding roots its pointer half,
        and any other ``i32`` binding whose type is not an inline scalar
        roots its local.  Reading it off the delta means a binding is rooted
        once, by one rule, wherever it came from — `let`, pair-`let` or
        `let`-destructure.

        Nothing allocates between the restore and the pushes that follow it,
        so the bindings are never unrooted across a collection point.
        """
        roots = self._binding_roots(before_env, after_env)
        if not contains_shadow_push(stmt_instrs):
            # No temporaries to reclaim.  A binding may still need its root
            # — `let @String = "literal";` roots a pointer without having
            # pushed anything to get it.
            if not roots:
                return stmt_instrs
            scoped = list(stmt_instrs)
            self.needs_alloc = True
            for local_idx in roots:
                scoped.extend(gc_shadow_push(local_idx))
            return scoped
        save = save_local()
        scoped = ["global.get $gc_sp", f"local.set {save}"]
        scoped.extend(stmt_instrs)
        scoped.append(f"local.get {save}")
        scoped.append("global.set $gc_sp")
        for local_idx in roots:
            scoped.extend(gc_shadow_push(local_idx))
        return scoped

    def _binding_roots(
        self, before_env: WasmSlotEnv, after_env: WasmSlotEnv
    ) -> list[int]:
        """The WASM locals a statement bound that hold heap pointers.

        A pair binding (`String` / `Array<T>`) contributes its POINTER half,
        which is the local the environment carries; the length lives at
        ``local + 1`` and is a byte count, not a reference.  Any other
        ``i32`` binding is a heap pointer unless its type is one of the
        inline scalars — the `_INLINE_I32_TYPES` question, deliberately, and
        not `is_gc_pointer_base`: rooting a host handle is what the `let`
        rooting has always done, and narrowing that here would be a
        reachability change riding a lifetime change.
        """
        roots: list[int] = []
        for type_name, local_idx in after_env.bindings_added_since(before_env):
            if self._is_pair_type_name(type_name):
                roots.append(local_idx)
                continue
            if (self._slot_name_to_wasm_type(type_name) == "i32"
                    and type_name not in _INLINE_I32_TYPES):
                roots.append(local_idx)
        return roots

    def _stack_shape_of(self, expr: ast.Expr) -> str:
        """What *expr*'s lowering leaves on the operand stack.

        A shape recorded BY the lowering wins (#1371).  Most kinds answer the
        same in any context, but a ``handle`` expression's value is its
        body's, and the body's ops resolve through the effect-op registries
        that handler installs — which exist only while it is being lowered,
        and are keyed by bare op name, so two nested handlers' ``get``s are
        indistinguishable once the inner one is popped.  Asked from here,
        afterwards, a ``handle[State<Nat>]`` nested in a
        ``handle[State<Option<Int>>]`` answered with the OUTER ``get``:
        ``i32`` for a body worth ``i64``, and the wrapper then emitted
        ``local.set`` at the wrong width.  So the lowering records the answer
        at the one moment it is computable and this reads the record, rather
        than re-deriving it in a context that no longer holds.
        """
        recorded = self._scoped_expr_shape.get(id(expr))
        if recorded is not None:
            return recorded
        return self._compute_stack_shape(expr)

    def _compute_stack_shape(self, expr: ast.Expr) -> str:
        """Derive *expr*'s operand-stack shape from the CURRENT context.

        One of ``"void"``, ``"i32_pair"``, a WAT value type, or
        ``"unknown"``.  Reads the two predicates the rest of codegen already
        decides stack shape with — ``_is_void_expr`` and
        ``_is_pair_result_expr``, the pair that ``translate_block`` consults
        to decide how many ``drop``s an expression statement needs — before
        falling back to the width inferencer, so the scoping wrapper and the
        drop it may sit beside can never disagree about how many words are
        there.
        """
        if self._is_void_expr(expr):
            return "void"
        if self._is_pair_result_expr(expr):
            return "i32_pair"
        width = self._infer_expr_wasm_type(expr)
        if width in ("i32", "i64", "f64"):
            return width
        if width == "i32_pair":
            return "i32_pair"
        return "unknown"

    def _expr_result_is_pointer(self, expr: ast.Expr) -> bool:
        """Whether an ``i32``-lowered result must be re-rooted (#1371).

        Decided by :func:`is_gc_pointer_base` over the REPRESENTATION base of
        the expression's Vera type — the same rule, from the same function,
        that the function and closure epilogues use for their return values.

        Defaults to ``True`` when the Vera type is unrecoverable.  The two
        errors are not symmetric: re-rooting a non-pointer costs one shadow
        slot and one candidate the mark phase's heap-range guard rejects,
        while failing to re-root a pointer hands the value to the next
        collection.  An unknown type takes the inert error.
        """
        vera_type = self._infer_vera_type(expr)
        if vera_type is None:
            return True
        head = vera_type.split("<", 1)[0]
        return is_gc_pointer_base(self._resolve_base_type_name(head))

    def _translate_expr_unscoped(
        self, expr: ast.Expr, env: WasmSlotEnv
    ) -> list[str] | None:
        """Translate a Vera AST expression to WAT instructions.

        The per-kind dispatch.  Callers go through
        :meth:`translate_expr`, which adds the #1371 root scoping around
        whatever this returns.

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
            # #1212: a literal a @Byte write boundary marked (directly, or as
            # a leaf of an `if` / `match` join flowing into one) lowers at the
            # i32 Byte width — see `_mark_byte_literal_leaves`.
            if id(expr) in self._byte_literal_ids:
                return [f"i32.const {expr.value}"]
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
            #
            # #814/#774: an imported GENERIC whose bare name a local shadows
            # resolves through a separate table to its ``mod$…`` mono BASE; the
            # base is a `_generic_fn_info` key, so the resulting FnCall is
            # rewritten by `_resolve_generic_call` to the per-instantiation clone
            # (`mod$m$gen$Int`) rather than the local shadow's bare `gen`.
            #
            # The desugar and the statement-position result-shape predicates
            # (`_is_void_expr` / `_is_pair_result_expr`) share ONE target
            # resolver so they can never disagree on which function is called
            # (CR 3518737022): `_resolve_module_call_wasm_name` returns a shadowed
            # generic's fully-resolved clone (`mod$m$gen$Int`, which
            # `_translate_call` then calls directly) or the bare name of an
            # UNshadowed generic (which `_translate_call` mangles itself).
            target = self._resolve_module_call_wasm_name(expr)
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
        """Translate a block: process statements, then final expression.

        Each statement is a GC root scope (#1371).  A statement's lowering
        may root any number of temporaries — the allocations inside a `let`'s
        right-hand side, the intermediates of an expression statement whose
        value is dropped — and every one of them is dead the moment the
        statement ends.  What outlives a statement is exactly what it BOUND,
        so the statement restores ``$gc_sp`` to where it stood on entry and
        then roots its new bindings, read from the environment delta.

        That delta is why the producers no longer root their own bindings:
        one rule decides which of a statement's bindings are heap pointers
        and roots each exactly once, where before `let`, pair-`let` and
        `let`-destructure each pushed for themselves — and a scoped restore
        would have had to know, per producer, what to put back.
        """
        current_env = env
        instructions: list[str] = []
        # One save local for the whole block: each statement re-snapshots it,
        # so the K statements of a block share a local rather than each
        # taking one.  Allocated on the first statement that needs it, so a
        # block whose statements root nothing declares no extra local and its
        # emitted WAT is unchanged.
        stmt_save: int | None = None

        def save_local() -> int:
            """The block's shared ``$gc_sp`` snapshot local, allocated once.

            Called only by a statement scope that is actually emitting a
            restore, so a block whose statements root nothing declares no
            extra local.
            """
            nonlocal stmt_save
            if stmt_save is None:
                stmt_save = self.alloc_local("i32")
            return stmt_save

        for stmt in block.statements:
            stmt_env = current_env
            stmt_instrs: list[str] = []
            if isinstance(stmt, ast.LetStmt):
                # Determine WAT type for this let binding.  Resolved BEFORE
                # the value is translated because a `@Byte` target changes how
                # the value's int literals lower (#865 / #1212) — see the
                # `_mark_byte_write_value` call below.
                type_name = self._type_expr_to_slot_name(stmt.type_expr)
                if type_name is None:
                    raise CodegenSkip(
                        stmt, "let binding type has no slot name"
                    )
                # #865: `@Byte` is i32 (spec §11), but an int literal defaults
                # to `i64.const`.  The bidirectional checker accepts a 0..255
                # literal bound to a `@Byte` (incl. a `{ @Byte | P }`
                # refinement) let target — mark it so it lowers at i32 and
                # matches the i32 Byte local.  Sibling of the call-argument
                # coercion; a non-literal Byte value already yields i32.
                # #1212: the marking descends `if` / `match` / `Block` joins to
                # their literal LEAVES, so `let @Byte = if c then { 1 } else
                # { 2 }` — check-green, and invalid WASM while only a top-level
                # literal was coerced — lowers at i32 in every arm.
                self._mark_byte_write_value(
                    stmt.value, self._resolve_base_type_name(type_name))
                val_instrs = self.translate_expr(stmt.value, current_env)
                if val_instrs is None:
                    return None
                # Pair bindings (String, Array<T>) need two locals: (ptr, len)
                if self._is_pair_type_name(type_name):
                    ptr_idx = self.alloc_local("i32")
                    len_idx = self.alloc_local("i32")
                    stmt_instrs.extend(val_instrs)
                    stmt_instrs.append(f"local.set {len_idx}")
                    stmt_instrs.append(f"local.set {ptr_idx}")
                    # #846: a host-import pair (``IO.args`` → Array<String>,
                    # ``IO.read_line`` → String) is rooted only host-side
                    # during construction, so without a root here the next
                    # alloc sweeps the block while the (ptr, len) locals still
                    # point at it.  The root is now planted by the statement
                    # scope below, from the environment delta, alongside every
                    # other binding's (#1371) — pushing here as well would
                    # root one address twice and hold the duplicate for the
                    # rest of the frame.
                    current_env = current_env.push(type_name, ptr_idx)
                    instructions.extend(self._scope_statement_roots(
                        stmt_instrs, stmt_env, current_env, save_local))
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
                    stmt_instrs.extend(
                        self._emit_nat_bind_guard(val_instrs))
                elif (self._resolve_base_type_name(type_name) == "Int"
                        and self._result_is_nat(stmt.value)):
                    # #813: guard a @Nat -> @Int let widening — a @Nat value
                    # above i64.MAX reinterprets to a negative @Int.
                    stmt_instrs.extend(
                        self._emit_int_widen_guard(val_instrs))
                else:
                    # A `@Byte` target's literals were already marked before
                    # the translation above, so `val_instrs` is the i32
                    # lowering — nothing to override here (#865 / #1212).
                    stmt_instrs.extend(val_instrs)
                stmt_instrs.append(f"local.set {local_idx}")
                # #705: a heap-pointer let binding must be rooted, or a
                # later allocation in the same block (a ``set_to_array``
                # host call after ``let @Set = build_set()``) reclaims it.
                # The root is planted by the statement scope below, from the
                # environment delta (#1371); rooting here as well would hold
                # a duplicate of the same address for the rest of the frame.
                current_env = current_env.push(type_name, local_idx)
            elif isinstance(stmt, ast.ExprStmt):
                value_instrs = self.translate_expr(stmt.expr, current_env)
                if value_instrs is None:
                    return None
                stmt_instrs.extend(value_instrs)
                # Drop the value if the expression produces one.
                # QualifiedCalls (effect ops like IO.print) return void.
                # UnitLit produces nothing.
                if stmt_instrs and not self._is_void_expr(stmt.expr):
                    if self._is_pair_result_expr(stmt.expr):
                        stmt_instrs.extend(["drop", "drop"])
                    else:
                        stmt_instrs.append("drop")
            elif isinstance(stmt, ast.LetDestruct):
                result = self._translate_let_destruct(stmt, current_env)
                if result is None:
                    return None
                destr_instrs, current_env = result
                stmt_instrs.extend(destr_instrs)
            else:
                # Unknown statement type
                raise CodegenSkip(
                    stmt,
                    f"unsupported statement type {type(stmt).__name__}",
                )
            instructions.extend(self._scope_statement_roots(
                stmt_instrs, stmt_env, current_env, save_local))

        # Final expression
        expr_instrs = self.translate_expr(block.expr, current_env)
        if expr_instrs is None:
            return None
        # #758/#983 — guard a narrowing @Nat-return leaf inline (per-leaf, not
        # whole-body).  A no-op unless this exact trailing expr is a collected
        # narrowing return leaf; this covers the top-level body's trailing expr
        # AND every if-branch trailing expr (branches are Blocks routed here by
        # `_translate_if`).
        expr_instrs = self._guard_nat_return_leaf(block.expr, expr_instrs)
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
        #   ModuleCall        → True if resolved target fn returns @Unit
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
            # DB.query / DB.execute both return a Result — not void (#229)
            if expr.qualifier == "DB":
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
        # #1284: bare form, so the ownership predicate decides whether the
        # op registry answers at all — a user `fn put` returning a value is
        # not void just because the handler's `put` is.
        if (isinstance(expr, ast.FnCall)
                and self._bare_call_denotes_op(expr.name)
                and expr.name in self._effect_ops):
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
        # A module-qualified call is void iff its resolved target returns
        # @Unit — mirror the FnCall clause on the resolved WASM target (bare
        # name, the ``mod$…`` name when the bare name is locally shadowed, or a
        # shadowed generic's per-instantiation clone), so a unit-returning
        # ``m::f()`` in statement position gets no stray drop (#814; same class
        # as the user-@Unit-fn case #584).
        if isinstance(expr, ast.ModuleCall):
            target = self._resolve_module_call_wasm_name(expr)
            if target in self._fn_ret_types:
                return self._fn_ret_types[target] is None
            return False
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
        if isinstance(expr, ast.ModuleCall):
            # Resolve the qualified target (bare name, the ``mod$…`` name when
            # shadowed, or a shadowed generic's per-instantiation clone) and
            # reuse the FnCall inference so a String/Array-returning ``m::f()``
            # in statement position drops both stack values, not one (#814).
            target = self._resolve_module_call_wasm_name(expr)
            ret = self._infer_fncall_wasm_type(
                ast.FnCall(name=target, args=expr.args, span=expr.span))
            return ret == "i32_pair"
        return False

    def _resolve_module_call_wasm_name(self, expr: ast.ModuleCall) -> str:
        """Resolve a ``ast.ModuleCall`` to the WASM function name it will call.

        The single target-resolution consulted by BOTH the desugar
        (``translate_expr``) and the statement-position result-shape predicates
        (``_is_void_expr`` / ``_is_pair_result_expr``), so they can never
        disagree on which function ``m::f(...)`` reaches (the #774 review, CR
        3518737022): if the result-shape checks resolved differently from the
        desugar, a shadowed generic's ``String``/``@Unit`` clone could drop the
        wrong number of stack values → a WASM validation failure on a
        check-green program.

        Order mirrors the desugar exactly:
          1. a shadowed imported GENERIC (``_module_qualified_generic_bases``) →
             its per-instantiation clone (via ``_resolve_generic_call`` on the
             ``mod$…`` base, which mangles in the inferred type args);
          2. a shadowed NON-generic (``_module_qualified_targets``) → its
             ``mod$…`` name;
          3. otherwise the bare name.
        """
        qkey = (tuple(expr.path), expr.name)
        gen_base = self._module_qualified_generic_bases.get(qkey)
        if gen_base is not None:
            resolved = self._resolve_generic_call(
                ast.FnCall(name=gen_base, args=expr.args, span=expr.span))
            if resolved is not None:
                return resolved
            return gen_base
        return self._module_qualified_targets.get(qkey, expr.name)
