"""Vera code generator — composed CodeGenerator class.

The ``CodeGenerator`` class is composed from several mixin modules that
each handle a specific concern:

* :mod:`~vera.codegen.modules` — cross-module registration (C7e)
* :mod:`~vera.codegen.registration` — Pass 1 forward declarations
* :mod:`~vera.codegen.monomorphize` — generic instantiation (Pass 1.5)
* :mod:`~vera.codegen.functions` — function body compilation (Pass 2)
* :mod:`~vera.codegen.closures` — closure lifting
* :mod:`~vera.codegen.contracts` — runtime contract insertion
* :mod:`~vera.codegen.assembly` — WAT module assembly
* :mod:`~vera.codegen.compilability` — compilability checks
"""

from __future__ import annotations

import contextlib
import dataclasses
import re
from collections.abc import Iterator
from typing import TYPE_CHECKING

import wasmtime

from vera import ast, naming
from vera.codegen.api import CompileResult
from vera.codegen.memory import ConstructorLayout
from vera.errors import Diagnostic, SourceLocation
from vera.monomorphize import (
    NamespaceFnNames,
    canonicalize_type_aliases,
    qualify_nested_generic_decls,
)
from vera.naming import EMPTY_ALIAS_ENV, AliasEnv
from vera.prelude import (
    PRELUDE_FILE,
    PRELUDE_NAMESPACE,
    data_decl_shape,
    mentioned_fn_names,
    prelude_adt_names,
)
from vera.slots import family_fallback_name
from vera.wasm import StringPool
from vera.wasm.helpers import CellNames
from vera.wasm.async_fusion import (
    compute_future_ret_fns,
    compute_future_ret_module_fns,
)
from vera.codegen.modules import CrossModuleMixin
from vera.codegen.registration import RegistrationMixin
from vera.codegen.monomorphize import MonomorphizationMixin
from vera.codegen.functions import FunctionCompilationMixin
from vera.codegen.closures import ClosureLiftingMixin
from vera.codegen.contracts import ContractsMixin
from vera.codegen.assembly import AssemblyMixin
from vera.codegen.compilability import CompilabilityMixin

if TYPE_CHECKING:
    from vera.resolver import ResolvedModule
    from vera.types import ModuleArtifacts, SpanTypeTable, Type
    from vera.wasm.context import WasmContext


# #1100: WAT-text scanning for the skip-propagation pass
# (`_drop_dangling_callers`).  The emitted WAT is the exact symbol stream
# wasmtime resolves, so scanning it needs no re-derivation of mono/module
# renaming.  `_WAT_FN_NAME_RE` reads the defined symbol out of a
# `  (func $name ...` emission; `_WAT_CALL_RE` collects every direct call
# target (`call $f` / `return_call $f`).  `call_indirect` never matches
# (`_` is a word character, and its operand is a `(type $sig)`, not a
# function symbol); `throw $tag` references an exception tag, not a
# function; `ref.func` is never emitted.
_WAT_FN_NAME_RE = re.compile(r"\s*\(func \$([^\s()]+)")
_WAT_CALL_RE = re.compile(r"\b(?:return_call|call)\s+\$([^\s()]+)")
# #1185: an INDIRECT call names no function symbol at all — it dispatches
# on the module's function table — so `_WAT_CALL_RE` is blind to it and
# the propagation needs its own probe.  Anchored at line start so a `;;`
# comment naming the instruction can never be read as an emission.
_WAT_CALL_INDIRECT_RE = re.compile(r"(?m)^\s*call_indirect\b")

# #1208: the two reserved floors of the shared declaration-index space (see
# `CodeGenerator._decl_order`).  A built-in ADT precedes every declaration,
# including the prelude's; the prelude block sits between it and the user's,
# with room for far more injected declarations than the prelude has.
_BUILTIN_DECL_INDEX = -(1 << 30)
_PRELUDE_DECL_BASE = -(1 << 20)

# The WAT width of each `vera.types.PRIMITIVES` member — one entry per key of
# that registry, which `tests/test_name_resolution_spine_1316.py` asserts
# directly, since the spine answers PRIMITIVE for every one of them and this
# table is where the width is stated.  `Never` is the one
# primitive with no representation — no value of it exists, so a parameter or
# return of that type has no word to occupy and the compilability check refuses
# it, exactly as it did before the spine (#1309) routed primitives here.
_PRIMITIVE_WASM_TYPES: dict[str, str | None] = {
    "Int": "i64",
    "Nat": "i64",
    "Float64": "f64",
    "Bool": "i32",
    "Byte": "i32",
    "Unit": None,
    "String": "i32_pair",
    "Never": "unsupported",
}


def _find_holes(program: ast.Program) -> list[ast.HoleExpr]:
    """Walk the AST and return all HoleExpr nodes."""
    holes: list[ast.HoleExpr] = []
    _walk_node(program, holes)
    return holes


def _walk_node(node: object, holes: list[ast.HoleExpr]) -> None:
    """Recursively walk AST nodes collecting HoleExpr instances."""
    if isinstance(node, ast.HoleExpr):
        holes.append(node)
        return
    if isinstance(node, ast.Node):
        for field_val in vars(node).values():
            _walk_node(field_val, holes)
    elif isinstance(node, (list, tuple)):
        for item in node:
            _walk_node(item, holes)


class CodeGenerator(
    CrossModuleMixin,
    RegistrationMixin,
    MonomorphizationMixin,
    FunctionCompilationMixin,
    ClosureLiftingMixin,
    ContractsMixin,
    AssemblyMixin,
    CompilabilityMixin,
):
    """Compiles a Vera Program AST to WebAssembly.

    Two-pass approach:
    1. Registration: collect function signatures for forward references
    2. Compilation: generate WAT for each compilable function
    """

    def __init__(
        self,
        source: str = "",
        file: str | None = None,
        resolved_modules: list[ResolvedModule] | None = None,
        expr_semantic_types: (
            dict[tuple[int, int, int, int], Type] | None
        ) = None,
        expr_target_types: (
            dict[tuple[int, int, int, int], Type] | None
        ) = None,
        module_artifacts: ModuleArtifacts | None = None,
    ) -> None:
        self.source = source
        self.file = file
        self.diagnostics: list[Diagnostic] = []
        self.string_pool = StringPool()
        # #798: the checker's resolved-type side-table (keyed by
        # ``ast.span_key``).  Threaded into every ``WasmContext`` so the
        # integer-overflow guard classifies an arithmetic operand's Int/Nat
        # type the same way the verifier's ``int_overflow`` obligation does.
        # ``None`` when a caller skipped typecheck (the guard then falls back
        # to the AST-only classifier).
        self._expr_semantic_types: (
            dict[tuple[int, int, int, int], Type] | None
        ) = expr_semantic_types
        # #820: the checker's TARGET-type side-table (``expected`` per expr
        # span).  Threaded into every ``WasmContext`` so the @Nat -> @Int
        # widening guard can recover the per-component target type at a tuple
        # component / array element / heterogeneous if-arm — the codegen dual
        # of the verifier's ``_target_type_of``.  ``None`` when a caller
        # skipped typecheck (those component sites then stay E531-disclosed).
        self._expr_target_types: (
            dict[tuple[int, int, int, int], Type] | None
        ) = expr_target_types
        # #987: per-resolved-module span-keyed side-tables, keyed by module path
        # (``CheckArtifacts.module_artifacts``).  The two tables above hold
        # MAIN-file entries only, so an imported body compiled in Pass 2.5 / 2.6
        # cannot recover its component targets from them.  ``_compile_fn``
        # selects the entry for the module being compiled — via the ``path`` its
        # ``_imported_fn_decls`` / ``_shadowed_module_fns`` entry carries — so the
        # imported body's array-element / tuple-construction @Nat -> @Int
        # widening guard fires exactly as the module's standalone compile emits
        # it.  Empty when a caller skipped ``typecheck_with_artifacts`` (or has no
        # imports); the imported body then falls back to suppressed lookups
        # (#986), never a wrong-file-keyed guard.
        self._module_artifacts: dict[
            tuple[str, ...],
            tuple[SpanTypeTable | None, SpanTypeTable | None],
        ] = dict(module_artifacts or {})

        # Registered function signatures: name -> (param_types, return_type)
        self._fn_sigs: dict[str, tuple[list[str | None], str | None]] = {}
        # Registered function return Vera-type expressions (#614).
        # Carries the full NamedType (with type_args) alongside the WAT
        # type kept in `_fn_sigs`, so inference paths that need to
        # extract the element type of e.g. `Array<Int>` returned from
        # a call (`f()[i]`) can reach into the type_args.
        self._fn_ret_type_exprs: dict[str, ast.TypeExpr] = {}
        # #747: per-parameter "is a concrete @Nat formal" flags, for the
        # runtime @Int -> @Nat narrowing guard at call sites.  Generic
        # formals fixed to @Nat at the call site erase to i64 here, so they
        # stay statically-only (verifier-obligated).
        self._fn_nat_params: dict[str, tuple[bool, ...]] = {}
        # #813: per-parameter "is a concrete @Int formal" flags, the dual of
        # `_fn_nat_params`, for the runtime @Nat -> @Int widening guard at
        # call sites.
        self._fn_int_params: dict[str, tuple[bool, ...]] = {}
        # #865: per-parameter "is a concrete @Byte formal" flags.  `@Byte` is
        # i32 (spec §11) but an int-literal argument defaults to `i64.const`;
        # a Byte-typed formal makes the call site coerce a literal argument to
        # `i32.const`, mirroring the #766 binop-operand fix at the call-arg
        # position.  Disjoint from the @Nat/@Int bitmaps (a formal resolves to
        # one primitive base or neither).
        self._fn_byte_params: dict[str, tuple[bool, ...]] = {}
        # Track which effect operations are needed
        self._io_ops_used: set[str] = set()
        self._needs_contract_fail: bool = False
        # #808: set when an overflow guard emits a `vera.overflow_trap` call,
        # so assembly.py declares the host import.
        self._needs_overflow_trap: bool = False
        self._needs_memory: bool = False
        # (cell, wasm_type).  `CellNames` rather than a bare family
        # (#1238 review F2): the wasi target names the unsupported
        # families in a user-facing error, and since #1218 a refined
        # cell's IDENTITY carries its whole predicate — a
        # discriminator, not something to read.  The base travels
        # with it so a message can say `state (Byte)`.
        self._state_types: list[tuple[CellNames, str]] = []
        self._exn_types: list[tuple[str, str]] = []  # (type_name, wasm_type)
        # #1210: State cell types and Exn payload types the handler walk
        # found and could NOT register.  Reset by
        # `_scan_body_for_state_handlers` — the walk's entry point — at the
        # start of each per-function walk, and read by it immediately after,
        # so neither list outlives one function.  Declared here as well so
        # the two siblings are visible together and neither depends on the
        # walk having run for the attribute to exist.
        self._unregistrable_state_cells: list[tuple[ast.TypeExpr, str]] = []
        self._unregistrable_exn_tags: list[tuple[ast.TypeExpr, str]] = []
        self._md_ops_used: set[str] = set()  # Markdown host-import builtins
        self._regex_ops_used: set[str] = set()  # Regex host-import builtins
        self._map_ops_used: set[str] = set()  # Map host-import builtins
        self._map_imports: set[str] = set()  # Map WAT import declarations
        self._set_ops_used: set[str] = set()  # Set host-import builtins
        self._set_imports: set[str] = set()  # Set WAT import declarations
        self._decimal_ops_used: set[str] = set()  # Decimal host-import builtins
        self._decimal_imports: set[str] = set()  # Decimal WAT import declarations
        self._json_ops_used: set[str] = set()  # Json host-import builtins
        self._html_ops_used: set[str] = set()  # Html host-import builtins
        self._http_ops_used: set[str] = set()  # Http host-import builtins
        # #841: fused-async host-import builtins (async_http_get /
        # async_http_post / async_await)
        self._async_ops_used: set[str] = set()
        # #841: fns declared to return Future<Result<String, String>>,
        # shared by the _scan_io_ops pre-scan and the WasmContext await
        # lowering (computed in compile() from the program decls).
        self._future_ret_fns: frozenset[str] = frozenset()
        # #841 round 2: (module path, name) → return TypeExpr for every
        # imported module fn (harvested in modules.py), and the derived
        # qualified future-return set for ModuleCall awaits.
        self._module_fn_ret_type_exprs: dict[
            tuple[tuple[str, ...], str], ast.TypeExpr
        ] = {}
        self._future_ret_module_fns: frozenset[
            tuple[tuple[str, ...], str]
        ] = frozenset()
        self._inference_ops_used: set[str] = set()  # Inference host-import builtins
        self._db_ops_used: set[str] = set()  # #229 DB host-import builtins
        self._random_ops_used: set[str] = set()  # Random host-import builtins (#465)
        self._math_ops_used: set[str] = set()  # Math host-import builtins (#467)

        # ADT layout metadata (populated during registration)
        self._adt_layouts: dict[str, dict[str, ConstructorLayout]] = {}
        # #1227: the namespace each absorbed ADT was DECLARED in.  The layout
        # map above is one space across every module — layouts are structural,
        # and a module's own bodies compile against this generator's copy — but
        # the declaration-index space is per namespace (§8.4.1, PR #1224), so
        # an imported ADT has to be ordered where its own module declared it.
        # Only module-owned ADTs are recorded; a main-file declaration is in
        # `_decl_order` and a built-in or prelude ADT takes the reserved floor.
        self._adt_layout_owners: dict[str, tuple[str, ...]] = {}
        self._needs_alloc: bool = False
        # Constructor type-param index mapping: ctor_name → tuple of ADT type-param
        # indices (or None for concrete fields).  Used by the monomorphizer and WASM
        # type inference to correctly bind forall vars from sparse constructors like
        # Err(e) whose single field maps to Result's *second* type param (E), not T.
        self._ctor_adt_tp_indices: dict[str, tuple[int | None, ...]] = {}
        # Maps ADT name → number of type parameters (needed to produce full-length
        # type-arg tuples with None placeholders for unknown positions).
        self._adt_tp_counts: dict[str, int] = {}
        # #773: ADT name → ordered type-parameter NAMES, for structural-Eq
        # substitution of params nested inside parameterized field types
        # (`Cons(T, List<T>)` under a `List<Int>` comparison).
        self._adt_tp_param_names: dict[str, tuple[str, ...]] = {}

        # Type aliases (populated during registration)
        # Maps alias name -> TypeExpr (for resolving function type aliases)
        self._type_aliases: dict[str, ast.TypeExpr] = {}
        # Type alias parameters: alias name -> param names
        # Needed for generic type alias resolution in closure codegen
        self._type_alias_params: dict[str, tuple[str, ...]] = {}
        # #1111: per-module alias namespaces.  Spec §8.4.1 makes type
        # aliases module-local (not importable), so each imported
        # module's aliases are captured under its path here — NEVER
        # merged into the flat maps above, which hold only the main
        # file's (and the prelude's non-shadowed) aliases.  While a
        # module-provenance declaration compiles / registers,
        # `_module_alias_scope` swaps the flat maps for
        # ``{prelude, **module_own}`` so every alias consumer resolves
        # against the defining module's namespace.
        self._module_type_aliases: dict[
            tuple[str, ...], dict[str, ast.TypeExpr]] = {}
        self._module_type_alias_params: dict[
            tuple[str, ...], dict[str, tuple[str, ...]]] = {}
        # #1111: the prelude's own alias definitions, captured
        # unconditionally at injection (even when a main-file alias
        # shadows the name in the flat map) — module namespaces overlay
        # onto THESE, never onto the main file's aliases.
        self._prelude_type_aliases: dict[str, ast.TypeExpr] = {}
        self._prelude_type_alias_params: dict[str, tuple[str, ...]] = {}
        # #1208: the SHARED declaration-index space over aliases AND ADTs, the
        # codegen-side counterpart of ``TypeEnv.next_decl_index``.  An alias
        # body sees only what was declared before it, and "before" has to
        # order the two registries against EACH OTHER — a `data Decimal`
        # declared below `type M = Decimal<Int>` is invisible to that body,
        # exactly as at check.
        #
        # Three blocks, ordered as the checker sees them: built-ins first
        # (unstamped, they read ``_BUILTIN_DECL_INDEX``), then the prelude
        # (a NEGATIVE block, because `inject_prelude` PREPENDS its
        # declarations while codegen registers the main file before injecting
        # them — without the block a main-file alias over a prelude alias
        # would resolve opaquely here and fully at check), then that
        # namespace's own declarations from 0 up.
        #
        # PER NAMESPACE, exactly like ``_type_aliases`` and for the same
        # reason (§8.4.1, #1111): ``_decl_order`` holds the ACTIVE namespace
        # — the main file's — and ``_module_alias_scope`` swaps in the
        # compiling module's own space beside its alias maps.  A single
        # shared space was a silent MISCOMPILE (PR #1224 review): modules
        # register at Pass 0.5 and the main file at Pass 1, and
        # ``_stamp_decl_order`` is idempotent by name, so a name a module had
        # already stamped kept that EARLIER index inside the main file's
        # namespace — turning the main file's forward reference into a
        # backward one.  `import lib;` (declaring `data X`) + `type Z = X;
        # type X = Nat;` then resolved `Z` to `Nat` here and to the opaque
        # ADT `X` at check, merging two parameter stacks the checker kept
        # apart, and a check-clean verify-clean program read the wrong
        # parameter.  Only names in the ACTIVE namespace are stamped, so
        # relative order within it is exact — which is all the bound reads.
        self._decl_order: dict[str, int] = {}
        self._decl_order_next: int = 0
        self._prelude_decl_order_next: int = _PRELUDE_DECL_BASE
        # The prelude's negative block, kept separately so a module's
        # namespace can be rebuilt as {prelude, **module_own} — the same
        # overlay ``_module_alias_scope`` performs on the alias maps.
        self._prelude_decl_order: dict[str, int] = {}
        # Each imported module's OWN 0-based space, captured at absorb time
        # (`_register_modules`) and installed by ``_module_alias_scope``.
        self._module_decl_order: dict[tuple[str, ...], dict[str, int]] = {}
        # #1208: the naming environment the ONE renderer (:mod:`vera.naming`)
        # resolves against, held as the single value the flat maps above
        # describe.  DERIVED from those maps rather than adopted from another
        # phase's per-module registration (the verifier keeps its own,
        # ``ContractVerifier._module_alias_envs``): codegen's alias view is not
        # the checker's — it is the prelude's aliases overlaid by the main
        # file's (and, inside ``_module_alias_scope``, by the compiling
        # module's), and it is built from the TRANSFORMED, monomorphized AST.
        # Sourcing it from the check would name against a table codegen does
        # not otherwise use, which is exactly the mint-one-way /
        # look-up-another split #1208 closes.  `_sync_alias_env` re-derives it
        # wherever the maps change.
        self._alias_env: AliasEnv = EMPTY_ALIAS_ENV
        # #1253: which ADT NAMES are members of each namespace — the module
        # path (``None`` = this program) → the names visible there.
        # ``_adt_layouts`` is one map across every absorbed namespace, so
        # deriving the naming env's `data_types` set from all of it made a
        # sibling module's ADTs members of a module that never imported them,
        # where the checker keeps the name opaque: the two sides then disagree
        # about what a NAME MEANS.  Membership is the owning namespace plus
        # that namespace's OWN imports (public and in-filter, the checker's
        # view), computed once in `_register_modules`.  Empty until then, and
        # empty for a single-file program — `_adt_members_in_scope` reads that
        # as "no module structure", which is the whole map.
        self._adt_namespace_members: dict[
            tuple[str, ...] | None, frozenset[str]
        ] = {}
        # The builtin ADTs, members of every namespace (they are global
        # infrastructure, owned by no module — the same set `_register_modules`
        # exempts from the E609/E610 collision rails).  A FLOOR, not the whole
        # infrastructure set: it is snapshotted in Pass 0.5, and the PRELUDE's
        # own ADTs register in Pass 1.2, so `_adt_members_in_scope` completes
        # it with `prelude.prelude_adt_names()` (#1277) and derives whatever
        # remains by subtracting what the namespaces declare.
        self._builtin_adt_names: frozenset[str] = frozenset()
        # Every ADT name SOME namespace declares — the main program's and each
        # module's own declarations.  Whatever `_adt_layouts` holds beyond this
        # is global infrastructure and belongs to every namespace.
        self._namespace_declared_adts: frozenset[str] = frozenset()
        # #1277: ADT name → EVERY module that declares it, in resolution
        # order, read from the declarations rather than from the registered
        # layouts, so the Pass-1.2 contention rail sees a module's `data
        # Option` as well as its `data Json` — and sees the second declarer
        # as well as the first.  Distinct from `_adt_layout_owners`, which
        # records which namespace's LAYOUT won the flat slot and is read for
        # declaration ordering: that one is first-wins because a slot has
        # one winner, while contention is a property of each declaration.
        self._module_adt_declarers: dict[str, tuple[tuple[str, ...], ...]] = {}
        # The namespace `_module_alias_scope` currently has installed, so
        # `_sync_alias_env` knows whose membership to apply.
        self._active_module_path: tuple[str, ...] | None = None

        # Diagnostics already reported by `_error_once` (PR #1224 review).  The
        # boundary-guard layer's errors fire from several call sites per
        # declaration and once per monomorphized clone, all from the same
        # spans; the set keeps one declaration to one diagnostic.  Keyed by
        # (code, message, resolved file, line, column), so a same-position
        # declaration in a different module — or a genuinely different error at
        # one position — still reports.
        self._error_once_sites: set[
            tuple[str, str, str | None, int, int]] = set()

        # #1210 round 7: AnonFn signatures currently being expanded by
        # `_scan_anon_fn_signature`.  A refinement's predicate may itself
        # contain a closure whose formal is refined by the SAME alias
        # (`type R = { @Int | … fn(@R -> @Int) … }` type-checks), so the
        # signature leg of the pre-scan walkers is cycle-guarded the way
        # every other alias walk here is.  A stack, not a memo: entries are
        # discarded on the way out, so a second function meeting the same
        # closure still gets its own registration verdict.
        self._anon_sig_scan_stack: set[int] = set()

        # #1172: runtime decreases-guard state.  ``_dec_guard_fns`` maps
        # each guarded function's WAT name -> lexicographic component
        # count, driving the per-function ``$dec_prev_<f>_<k>`` /
        # ``$dec_active_<f>`` globals emission in assembly;
        # ``_dec_rank_helpers`` collects the per-ADT structural-size
        # functions (``$dec_size_<T>``) the ADT-measure comparisons call.
        self._dec_guard_fns: dict[str, int] = {}
        self._dec_rank_helpers: dict[str, str] = {}
        # #1172: names of EVERY decreases-carrying function that can be a
        # ``return_call`` target — locals (with where-helpers), imported
        # bodies, mono clones, and shadowed ``mod$…`` emissions — built
        # by the pre-pass in ``compile_program`` before Pass 2, so the
        # tail-call discipline can classify a target that compiles later.
        self._dec_guarded_names: set[str] = set()

        # Closure compilation state
        self._closure_table: list[str] = []  # lifted fn names for table
        self._closure_sigs: dict[str, str] = {}  # sig_key -> WAT type decl
        self._closure_fns_wat: list[str] = []  # WAT for lifted closures
        self._needs_table: bool = False
        # #1100: skip-propagation bookkeeping, populated by
        # `_compile_fn_tracked` and consumed by `_drop_dangling_callers`
        # just before module assembly.
        #   _skipped_fn_roots: WAT symbol name of every function
        #     `_compile_fn` DROPPED -> the diagnostic that explains the
        #     drop (None when no E6xx diagnostic was emitted — a
        #     defensive fallback, no known path).  Call sites emit
        #     `call $name` for exactly these names, so any emitted body
        #     referencing one would dangle at WAT assembly.
        #   _fn_decl_by_wat_name: WAT symbol name -> FnDecl for every
        #     compile attempt, so a dropped caller's [E620] warning can
        #     point at the caller's own declaration.
        #   _closure_parents: lifted-closure WAT name ($anon_N) -> the
        #     top-level WAT symbol whose compile committed it.  A parent
        #     references its closures only via a function-table INDEX
        #     (never by `$anon_N` name), so the caller-drop scan needs
        #     this explicit construction edge.
        #   _closure_lift_skips (#1185): WAT symbol names of the functions
        #     `_compile_fn` dropped because their closure LIFT rolled back.
        #     Those rollbacks are what leave `_closure_table` empty, so an
        #     orphaned `call_indirect` elsewhere in the module is
        #     attributed to the first of them.
        self._skipped_fn_roots: dict[str, Diagnostic | None] = {}
        self._fn_decl_by_wat_name: dict[str, ast.FnDecl] = {}
        self._closure_parents: dict[str, str] = {}
        # #1183: every function absent from the emitted module -> the
        # diagnostic that explains its absence (its own root skip for a
        # directly-dropped function, its [E620] for a dangling caller).
        # Seeded from `_skipped_fn_roots` and extended in
        # `_drop_dangling_callers`; surfaced as `CompileResult.dropped_fns`
        # so `execute()` and the CLI can tell "this entry was DECLARED and
        # dropped" from "this entry was never written" instead of silently
        # substituting whatever export happens to be first.
        self._dropped_fn_diags: dict[str, Diagnostic | None] = {}
        # #1185: WAT names of functions whose closure lift rolled back —
        # the blame chain for orphaned `call_indirect` carriers when the
        # table is suppressed (see `_drop_dangling_callers`).
        self._closure_lift_skips: list[str] = []
        # #773: generated structural-Eq helper functions, keyed by their
        # `$eq_<type>` name → WAT text.  Accumulated across every function /
        # closure body (merged from each WasmContext) and emitted once at
        # module assembly.
        self._adt_eq_helpers: dict[str, str] = {}
        # #924: generated recursive show/hash helper functions ($show_<type> /
        # $hash_<type>), merged from each WasmContext and emitted once at
        # module assembly — the same propagate-then-emit shape as _adt_eq_helpers.
        self._show_hash_helpers: dict[str, str] = {}
        # #573: wrap-table flag — see ``WasmContext`` for the long
        # description.  Set in ``_assemble_module`` whenever a
        # host-handle type that has migrated to heap-wrap-as-ADT is
        # in use (currently just Map; Set / Decimal extend the
        # gating in their own follow-ups).  When true, the WAT
        # module gets a 64 KiB wrap-table region, the
        # ``$register_wrapper`` helper, and Phase 2c of
        # ``$gc_collect``.
        self._needs_wrap_table: bool = False
        self._next_closure_id: int = 0

        # #516 Stage 2 — runtime-trap source mapping.
        # Maps WAT function name (without leading `$`) → (file, start_line,
        # end_line) so wasmtime trap frames can be resolved to a source
        # location at runtime.  Populated by `_register_fn` for top-level
        # user functions (including monomorphized clones, registered in
        # Pass 1.5) and by the closure-lifting pass for `$anon_N`
        # helpers; entries for prelude-injected FnDecls are removed
        # immediately after registration in `compile_program` (see the
        # post-`inject_prelude` loop) and migrated to
        # `_prelude_fn_names`.  #1189: IMPORTED functions never reach this
        # generator's `_register_fn` at all — Pass 0.5 registers each
        # module's declarations into a throwaway `CodeGenerator` — so
        # `_register_modules` harvests that generator's map (stamped with
        # the MODULE's own file), and `_register_shadowed_import` mirrors
        # the entry onto the `mod$…` name a locally-shadowed import is
        # emitted under.  Every other mangled name — a mono clone whose
        # own entry was dropped, say — falls back at trap time: the
        # resolver (`_resolve_trap_frames` in `vera/runtime/traps.py`)
        # strips the rightmost `$` suffix and looks up the base name,
        # since `$` cannot appear in user-written Vera identifiers and so
        # any `$` in a WAT name was inserted by the compiler's manglers.
        # Built-in WASM helpers (`$alloc`, `$gc_collect`,
        # `$contract_fail`, `$exn_*`, `$vera.*`) never appear here at
        # all — they're emitted directly into WAT by the assembly
        # module without going through `_register_fn`, and the
        # resolver tags them as `<builtin>`.
        self._fn_source_map: dict[str, tuple[str, int, int]] = {}

        # #516 Stage 2 — positive source-of-truth for prelude / built-in
        # function classification.  Populated by the post-`inject_prelude`
        # registration loop in `compile_program`: any FnDecl that wasn't
        # in `_fn_sigs` before the prelude pass but is registered after
        # is by definition a prelude / built-in injection, not user
        # code.  Detection is by **registration-flow position**, NOT by
        # `decl.span` being None — `inject_prelude` calls
        # `parse_to_ast` on inline Vera source so its synthetic FnDecls
        # do have spans (just spans pointing into that synthetic
        # source's line numbers, which would otherwise land entirely
        # bogus coordinates in `_fn_source_map` and surface them on a
        # trap as e.g. "in option_unwrap_or (/tmp/foo.vera:9-18)" for
        # a 3-line user file).
        #
        # The trap-frame resolver consults this alongside the runtime-
        # helper allowlist to recognise trap frames inside prelude
        # functions (`option_unwrap_or`, the option/result combinators,
        # ADT auto-derived methods, …) as built-ins rather than mis-
        # classifying them as `<unknown>` user code — without this, the
        # CLI's suppression-marker collapse cannot fire for traps that
        # go through prelude functions, and the user sees a confusing
        # "in option_unwrap_or (<unknown>)" entry at the top of their
        # backtrace.
        self._prelude_fn_names: set[str] = set()

        # #851 — the concatenated prelude source buffer that injected
        # declarations' spans index into.  Captured from
        # `inject_prelude()` in Pass 1.2 so `_warning` / `_error` can
        # quote the *prelude's* source line for prelude-origin
        # diagnostics instead of resolving the span's line number
        # against the user's file (which rendered unrelated user code
        # under the caret, or nothing when out of range).
        self._prelude_source: str = ""
        # #851 — True while `_compile_fn` is compiling a prelude-
        # injected function (or a mono clone of one), so diagnostics
        # anchored to *body* nodes (whose spans also index the prelude
        # buffer) resolve against the prelude origin too.  Set at
        # `_compile_fn` entry; every entry overwrites it, and the
        # Pass-2 loops reset it to False when they finish.
        self._in_prelude_fn: bool = False

        # Cross-module state (C7e)
        self._resolved_modules: list[ResolvedModule] = (
            resolved_modules or []
        )
        # Imported (module path, FnDecl) to compile in Pass 2.5.  The path is
        # carried so Pass 2.5 can apply that module's intra-rename map (#814
        # C2): a bare sibling call inside an imported body must reach the
        # module's version, not a local shadow of that name.
        self._imported_fn_decls: list[tuple[tuple[str, ...], ast.FnDecl]] = []
        # #814 §8.5.3: WASM target name for a module-qualified call
        # ``m::f`` keyed by (module path, fn name).  Normally the bare name;
        # for a module fn whose bare name is shadowed by a LOCAL definition
        # it is a distinct ``mod$…`` name so the qualified call reaches the
        # module's body while bare calls keep resolving to the local shadow.
        self._module_qualified_targets: dict[
            tuple[tuple[str, ...], str], str
        ] = {}
        # (module path, mangled name, FnDecl) of shadowed module fns to emit
        # in Pass 2.6.
        self._shadowed_module_fns: list[
            tuple[tuple[str, ...], str, ast.FnDecl]
        ] = []
        # Per-module intra-module call rename map: module path → {bare name →
        # mod$ name} for that module's locally-shadowed functions.  Applied
        # ONLY inside an emitted ``mod$…`` body so an intra-module call lands
        # on the module's version, not the main program's local shadow (#814
        # C2 — the residual the verifier↔codegen review found).
        self._module_intra_renames: dict[
            tuple[str, ...], dict[str, str]
        ] = {}
        # Names of ALL local functions (top-level + recursive where-fns) that
        # shadow the importer's flat namespace.  Populated by _register_modules;
        # Pass 2.5 consults it so an imported fn shadowed by a local where-fn is
        # not emitted under a clashing bare name (#814).
        self._local_shadowed_fn_names: set[str] = set()
        # #890: fn/ADT/ctor names contributed ONLY by a transitively-reached
        # module (imported by an imported module, not by this program).  Their
        # bodies ARE compiled into the flat WASM module so an imported body can
        # call them, but the top-level program's own bodies must not reach them
        # (spec §8.6.4 — a transitive module's declarations are not visible to
        # the original importer).  The guard rail (`_check_cross_module_calls`)
        # subtracts these from its "known" set, so a bare/qualified call to a
        # transitive symbol from a *main-program* body fails loudly at compile
        # instead of silently resolving to the emitted-for-a-sibling body.
        self._transitive_only_names: set[str] = set()
        # #1299: namespace path (``None`` = the main program) → the bare
        # SOURCE function names a body compiled in that namespace can NAME.
        # Codegen absorbs every module into one flat WASM namespace, so
        # `_fn_sigs` cannot answer "whose declaration is this bare `get`?" —
        # it holds a module's private helpers, the public ones an import
        # filter excluded, and every transitive module's declarations, none
        # of which the checker resolved against.  This map is what
        # `_scoped_fn_names` narrows `_fn_sigs` down to before the #1284
        # ownership predicate reads it.  Computed once in
        # `_collect_namespace_fn_names`, after the Pass-0 transforms.
        self._namespace_fn_names: dict[
            tuple[str, ...] | None, frozenset[str]
        ] = {}
        # The same tables as the shared value `MonoContext` carries, so Pass
        # 1.5's discovery narrows against exactly what `_scoped_fn_names`
        # narrows against (#1299).
        self._namespace_tables: NamespaceFnNames | None = None
        # #1281: bare names some namespace could resolve to more than one
        # module's declaration — a module importing two dependencies that
        # each export `gen`, and declaring no `gen` of its own.  Spec §8.5
        # refuses that name in the namespace holding the clash rather than
        # ordering the two imports (#1304), and the CHECKER reports it
        # (E155), so a program reaching this pass with the name still
        # ambiguous has bypassed the checker.  The E608 relaxation therefore
        # fires only for names OUTSIDE this set, and the shape keeps its
        # refusal here too instead of compiling against whichever body the
        # positional reroute map favoured.  Filled beside
        # `_namespace_fn_names`, from the same walk as the checker's.
        self._ambiguous_imported_fn_names: frozenset[str] = frozenset()
        # #774: imported PUBLIC generic (`forall`) FnDecls the importer must
        # monomorphize itself — cross-module generic monomorphization.  The
        # importer discovers instantiations from ITS OWN call sites and emits
        # the clones into its own (flat) WASM module, since the defining module
        # only monomorphizes its own instantiations (and never calls a generic
        # it merely exports).  Keyed by bare name (first-seen wins, public +
        # import-filtered), split by whether a LOCAL shadows the bare name:
        #   * `_imported_generic_decls` — UNshadowed: merged into
        #     `generic_decls` in `_monomorphize`, so both a bare call `gid(…)`
        #     and a qualified `m::gid(…)` (which desugars to the bare target)
        #     route through `_generic_fn_info` to the emitted clone.
        #   * `_shadowed_imported_generic_decls` — a local non-generic shadows
        #     the bare name (#814 asymmetric variant), so ONLY the qualified
        #     form may reach the module's generic; the bare name stays on the
        #     local.  These are monomorphized under a distinct ``mod$…$`` mono
        #     prefix and reached via `_module_qualified_generic_targets`.
        self._imported_generic_decls: dict[str, ast.FnDecl] = {}
        self._shadowed_imported_generic_decls: dict[
            tuple[str, ...], dict[str, ast.FnDecl]
        ] = {}
        # #998: bare name → origin module path for `_imported_generic_decls`
        # entries (same first-seen-wins order), and clone WASM name → origin
        # module path for every emitted clone of an imported generic
        # (unshadowed, shadowed `mod$…`, and their hoisted where-helpers).
        # Monomorphization preserves node spans, so a clone's body is keyed by
        # its TEMPLATE module's span tables — the mono compile loop threads
        # `_module_artifacts[origin]` for these so the #820 widen guards fire
        # (a local generic's clones are absent and keep the main-file tables).
        self._imported_generic_origins: dict[str, tuple[str, ...]] = {}
        self._mono_clone_origins: dict[str, tuple[str, ...]] = {}
        # #1002: every emitted mono clone name → the concrete-FREE chain base
        # key of the generic it clones (a top-level generic's own name, or a
        # ``<parent-chain>$where$<helper>`` chain for a nested generic).  The
        # per-clone where-tree hoister reads it to key a generic-under-generic
        # helper's ``_emitted_instances`` entry the SAME way the verifier's
        # `_verify_fn` reconstructs it from its lexical enclosing chain (both
        # concrete-free), so the #732 differential stays in lockstep even though
        # the EMITTED WASM clone carries a per-instantiation concrete-including
        # name (``outer$Int$where$ginner$Int``) to avoid a cross-instantiation
        # collision.
        self._clone_base_chain: dict[str, str] = {}
        # Reset per-`_monomorphize` run; declared here so the type is stated
        # once (imported bases that actually entered `generic_decls`).
        self._imported_generic_base_origins: dict[str, tuple[str, ...]] = {}
        # #814/#774: (module path, generic name) → mono base name the qualified
        # call must mangle against, for a generic whose bare name a local
        # shadows.  The ModuleCall desugar consults this so `m::gen(5)` resolves
        # to the module generic's clone (`mod$m$gen$Int`) instead of falling
        # back to the local shadow's bare `gen`.
        self._module_qualified_generic_bases: dict[
            tuple[tuple[str, ...], str], str
        ] = {}

    def _family_name_te(self, te: ast.TypeExpr) -> str:
        """The ``State<T>``/``Exn<E>`` host-import/tag FAMILY name for a
        type argument (#1209) — the CodeGenerator twin of
        ``WasmContext._family_name``, over ``_alias_env``: the aliases of
        the module whose declaration is compiling, kept current by
        ``_sync_alias_env`` / ``_module_alias_scope``.

        Registration (``_check_state_type`` / ``_check_exn_type`` / the body
        scan) and per-function lowering resolve through the SAME
        :func:`vera.naming.family_name`, so the declared import families and
        the call sites that target them cannot diverge (the #914 bug class)
        — and both now name the CELL the checker typed, so a composite or
        parameterised alias joins the family its resolution names instead of
        minting a second one beside it (#1209)."""
        return naming.family_name(
            te, self._alias_env, family_fallback_name(te))

    def _family_base_te(self, te: ast.TypeExpr) -> str:
        """The same cell's REPRESENTATION name (#1218) — the
        ``WasmContext._family_base`` twin.

        :func:`vera.naming.family_base_name` over the same environment: the
        family with its refinements stripped, which is what decides
        i32/i64/f64/pair and which write guard applies.  Never a symbol —
        see the function's own docstring for why the two names are separate.
        """
        return naming.family_base_name(
            te, self._alias_env, family_fallback_name(te))

    # -----------------------------------------------------------------
    # Diagnostics
    # -----------------------------------------------------------------

    def _is_prelude_origin(self, node: ast.Node) -> bool:
        """True when a diagnostic node belongs to prelude-injected code.

        #851 — prelude declarations (and their mono clones, whose
        mangled ``base$Types`` names strip back to a prelude base) carry
        spans indexing the synthetic prelude buffer, not the user's
        file.  Body nodes inside a prelude function are recognised via
        the `_in_prelude_fn` flag `_compile_fn` maintains.
        """
        if isinstance(node, ast.FnDecl):
            if node.name.split("$")[0] in self._prelude_fn_names:
                return True
        return self._in_prelude_fn

    def _diag_location(
        self, node: ast.Node,
    ) -> tuple[SourceLocation, str]:
        """Resolve a diagnostic node to (location, source_line).

        User-origin nodes resolve against the user's file and source
        text as before.  Prelude-origin nodes resolve against the
        synthetic ``<prelude>`` file and the prelude source buffer, so
        a prelude span can never render user source (#851).
        """
        if self._is_prelude_origin(node):
            loc = SourceLocation(file=PRELUDE_FILE)
            source = self._prelude_source
        else:
            loc = SourceLocation(file=self.file)
            source = self.source
        if node.span:
            loc.line = node.span.line
            loc.column = node.span.column
        lines = source.splitlines()
        source_line = (
            lines[loc.line - 1] if 1 <= loc.line <= len(lines) else ""
        )
        return loc, source_line

    def _warning(
        self,
        node: ast.Node,
        description: str,
        *,
        rationale: str = "",
        spec_ref: str = "",
        error_code: str = "",
    ) -> None:
        """Record a compilation warning (function skipped)."""
        loc, source_line = self._diag_location(node)
        self.diagnostics.append(Diagnostic(
            description=description,
            location=loc,
            source_line=source_line,
            rationale=rationale,
            spec_ref=spec_ref,
            severity="warning",
            error_code=error_code,
        ))

    def _error(
        self,
        node: ast.Node,
        description: str,
        *,
        rationale: str = "",
        error_code: str = "",
    ) -> None:
        """Record a compilation error (compiler bug / fatal).

        Unlike `_warning`, an error makes the overall compile
        non-zero-exit at the CLI boundary.  Used for [E699]
        "internal compiler error" diagnostics where the type
        checker should have rejected the input before reaching
        codegen — these indicate a compiler bug, not a user
        limitation, and the user-visible signal needs to be
        loud enough that CI logs can't mask it.  See
        `vera/skip.py::CodegenInvariantError` for the raise
        contract.
        """
        loc, source_line = self._diag_location(node)
        self.diagnostics.append(Diagnostic(
            description=description,
            location=loc,
            source_line=source_line,
            rationale=rationale,
            severity="error",
            error_code=error_code,
        ))

    def _error_once(
        self,
        node: ast.Node,
        description: str,
        *,
        rationale: str = "",
        error_code: str = "",
    ) -> None:
        """`_error`, but at most one such diagnostic per source position.

        For the errors raised by a helper the compile CONSULTS repeatedly —
        the boundary-guard layer's nested-refinement rejection (E618) and its
        tuple-depth fail-closed (E617).  Both are properties of a
        DECLARATION, and both are now derived once and read by three
        consumers (the guard emitters, the has-guardable predicate, and the
        host-import pre-scan), plus once more per monomorphized clone — every
        one of them from the same spans.  Reporting per visit turned one
        declaration into three identical diagnostics.

        Keyed on the resolved location AND the message, so the dedup can only
        ever swallow a repeat of the same finding: two library modules whose
        declarations share a line/column still report (the location carries
        its own file, PR #1224 review), and two DIFFERENT errors that happen
        to land on one span both survive.
        """
        loc, _source_line = self._diag_location(node)
        key = (error_code, description, loc.file, loc.line, loc.column)
        if key in self._error_once_sites:
            return
        self._error_once_sites.add(key)
        self._error(
            node, description, rationale=rationale, error_code=error_code)

    def _get_source_line(self, line: int) -> str:
        """Extract a line from the source text."""
        lines = self.source.splitlines()
        if 1 <= line <= len(lines):
            return lines[line - 1]
        return ""

    def _referenced_prelude_fns(self, program: ast.Program) -> set[str]:
        """Prelude-injected function names the program references (#851).

        A transitive call-target scan: the roots are every non-prelude
        declaration (all user decls — including generic ones the mono
        collector never scans — plus imported module fns and their
        Pass-2.6 shadowed variants); a prelude fn is referenced when a
        root (or the body of an already-referenced prelude fn, e.g.
        ``json_get_string`` calling ``json_get``) names it as a call
        target.  Feeds the unreferenced-prelude warning suppression in
        ``compile_program``.
        """
        targets = frozenset(self._prelude_fn_names)
        if not targets:
            return set()  # pragma: no cover — guarded by the caller
        prelude_decls: dict[str, ast.FnDecl] = {}
        roots: list[object] = []
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and decl.name in targets:
                prelude_decls[decl.name] = decl
            else:
                roots.append(decl)
        roots.extend(idecl for _path, idecl in self._imported_fn_decls)
        roots.extend(idecl for _p, _m, idecl in self._shadowed_module_fns)
        referenced: set[str] = set()
        work = roots
        while work:
            node = work.pop()
            for name in mentioned_fn_names(node, targets):
                if name not in referenced:
                    referenced.add(name)
                    # Transitive: a referenced prelude fn's own body
                    # can reference further prelude fns.
                    called = prelude_decls.get(name)
                    if called is not None:
                        work.append(called)
        return referenced

    def _harvest_interp_inference_failures(
        self,
        ctx: WasmContext,
    ) -> None:
        """Emit specific diagnostics for each inference-failure list
        recorded on `ctx`, before the caller emits the generic
        `[E602]` skip / drops the closure from the function table.

        Two lists are harvested:

        - `_interp_inference_failures` → `[E615]` per segment.
          Populated by `_translate_interpolated_string` when a
          `\\(...)` segment's Vera type can't be classified
          (#630 Tier 2).
        - `_apply_fn_inference_failures` → `[E616]` per closure_arg.
          Populated by `_translate_apply_fn` when the closure-arg
          shape isn't one the dispatcher recognises (#632).

        Both `_compile_fn` (top-level functions) and
        `_compile_lifted_closure` (lifted closure bodies) construct
        a fresh `WasmContext` and call this helper before their
        own None-return paths, so the centralised harvest stays in
        lock-step across both call sites — a future change to
        either E615 or E616 semantics (richer source ranges,
        suggested fixes) lands in one place.
        """
        for failed_part in ctx._interp_inference_failures:
            self._warning(
                failed_part,
                "Cannot interpolate value of unknown type — "
                "the compiler couldn't determine the Vera type of "
                "this expression, so it can't choose the right "
                "to_string conversion.",
                rationale="Interpolation inserts a `to_string`-style "
                "wrapper based on the segment's Vera type. When type "
                "inference returns None or an unrecognised name, the "
                "wrapper would generate invalid WASM at validation "
                "time. Likely cause: a function or expression whose "
                "return-type shape isn't yet handled by the "
                "canonicaliser in `vera/wasm/inference.py`. See #630.",
                error_code="E615",
            )
        for closure_arg in ctx._apply_fn_inference_failures:
            self._warning(
                closure_arg,
                "Cannot infer closure return type for call_indirect — "
                "the apply_fn dispatcher doesn't recognise this "
                "argument shape, so it can't construct the right "
                "call_indirect signature.",
                rationale="apply_fn's call_indirect emission needs the "
                "closure's return type to construct a matching WASM "
                "signature. Today the dispatcher recognises SlotRef "
                "into a FnType alias and inline AnonFn literals; "
                "other expression shapes (e.g. a FnCall returning a "
                "closure) fall through. Without this guard, the "
                "default 'i64' signature mismatches the actual i32_pair "
                "/ other return at WASM validation. See #632.",
                error_code="E616",
            )

    # -----------------------------------------------------------------
    # Skip propagation (#1100)
    # -----------------------------------------------------------------

    def _compile_fn_tracked(
        self, decl: ast.FnDecl, *, export: bool = True,
        module_renames: dict[str, str] | None = None,
        imported: bool = False,
        module_tables: (
            tuple[SpanTypeTable | None, SpanTypeTable | None] | None
        ) = None,
        where_scope: frozenset[str] = frozenset(),
    ) -> str | None:
        """`_compile_fn` plus the #1100 skip/closure bookkeeping.

        Every Pass 2/2.5/2.6/mono compile goes through here so
        `_drop_dangling_callers` can later see (a) which WAT symbol
        names were DROPPED (a caller's `call $name` to one would fail
        WAT assembly with a raw `unknown func`), with the diagnostic
        that explains each drop, and (b) which lifted closures belong
        to which parent (a parent holds only a table index, so the
        construction edge is invisible to a WAT-text scan).

        *where_scope* (#1299) is the ``where``-helper names lexically in
        scope in *decl*'s body — the direct helpers of every enclosing
        function, plus *decl*'s own.  It cannot be recovered from *decl*: a
        helper node carries no parent link, and the ancestors' helpers are
        exactly what the checker's ``_lookup_function_scoped`` walks.  The
        default is right for a top-level declaration with no helpers, which
        is every caller that omits it.
        """
        diags_before = len(self.diagnostics)
        closures_before = len(self._closure_fns_wat)
        self._fn_decl_by_wat_name[decl.name] = decl
        # #1208: the one door every emission passes, so the function's own
        # type-parameter narrowing is applied here rather than at each caller.
        with self._fn_alias_scope(decl):
            fn_wat = self._compile_fn(
                decl, export=export, module_renames=module_renames,
                imported=imported, module_tables=module_tables,
                where_scope=where_scope,
            )
        if fn_wat is None:
            # The LAST codegen diagnostic emitted during this compile is
            # the one that explains the drop (a closure-level skip is
            # followed by the parent-level drop warning, so "last" picks
            # the function-level explanation).  Restricted to E6xx so an
            # unrelated interleaved diagnostic can never be mistaken for
            # the root cause.
            root = next(
                (
                    d for d in reversed(self.diagnostics[diags_before:])
                    if d.error_code.startswith("E6")
                ),
                None,
            )
            self._skipped_fn_roots[decl.name] = root
        else:
            for closure_wat in self._closure_fns_wat[closures_before:]:
                match = _WAT_FN_NAME_RE.match(closure_wat)
                if match:
                    self._closure_parents[match.group(1)] = decl.name
        return fn_wat

    def _drop_dangling_callers(
        self, functions_wat: list[str], exports: list[str],
    ) -> list[str]:
        """Drop every function whose (transitive) callee was skipped (#1100).

        An `[E602]`-class skip removes a function from the emitted module,
        but its callers' `call $f` / `return_call $f` instructions were
        still emitted — so a check-clean program whose skipped construct
        sits in a *called* helper failed WAT assembly with a raw wasmtime
        ``unknown func: failed to find name $f`` instead of a
        source-located diagnostic.  This pass runs after all function
        compilation and prunes the whole unreachable caller subgraph, so
        the module always assembles and every dropped caller carries its
        own [E620] warning naming the ROOT skipped function and its skip
        location (DESIGN.md principle 1: the diagnostic is an instruction
        pointing at the construct to fix, not a WAT internals dump).

        Mechanics: the scan works on the emitted WAT text — the exact
        symbol stream wasmtime resolves — so mono-mangled (`f$Int`),
        module-qualified (`mod$f`), and where-helper (`p$where$h`)
        call targets are matched without re-deriving any renaming logic.
        Lifted closures are nodes too: a closure body holding the only
        `call $skipped` dooms its parent through the `_closure_parents`
        construction edge, and the doomed closure's body is replaced by
        an `unreachable` stub RATHER than removed — later closures'
        `closure_id` ↔ table-index correspondence depends on every
        earlier `(elem ...)` slot staying occupied.  The worklist reaches
        a fixed point because `doomed` only grows and is bounded by the
        node count, so call-graph cycles (mutual recursion) terminate.

        **Indirect calls (#1185).**  A `call_indirect` names no symbol, so
        the scan below cannot see it: it dispatches on the module's
        function table, which `_assemble_module` emits only when at least
        one closure lift committed.  When an [E602] skip swallowed a
        module's ONLY closure the lift rolled back, the `(table)`/`(elem)`
        sections were suppressed, and every surviving carrier — an
        `apply_fn` on a closure-typed parameter, or a monomorphized clone
        of a prelude combinator — kept an indirect call into a table that
        no longer existed.  That module assembled with zero error
        diagnostics and then failed to load with a raw
        ``unknown table 0`` as soon as ANY unrelated export ran.  Such a
        carrier can only ever have targeted a dropped closure, so it is
        seeded into the same fixed point as an ordinary dangling caller
        and dropped with its own [E620] naming the [E602] root.  Emitting
        an empty table instead would trade a located compile-time refusal
        for an opaque runtime trap (DESIGN.md: fail loud).

        Functions outside the doomed subgraph — including their exports —
        are untouched.  Mutates *exports* in place; returns the pruned
        *functions_wat*.
        """
        # #1183: a directly-skipped function is already absent from the
        # module — record it before the early return so a program whose
        # ONLY drop is the root still reports it.
        self._dropped_fn_diags.update(self._skipped_fn_roots)
        # #1185: `_needs_table` is set in the same commit block that
        # extends `_closure_table` / `_closure_fns_wat`, so "the table is
        # suppressed" and "no closure survived the lift" are the same
        # condition — which also means no *closure* body can be carrying
        # an orphaned indirect call, and scanning `functions_wat` is
        # complete.  The cheap substring pre-check keeps the common
        # closure-free program on the existing early-out.  The early
        # return fires only when NEITHER mechanism has work: no skipped
        # roots to propagate and no orphaned indirect calls to seed.
        table_suppressed = not (self._needs_table and self._closure_table)
        maybe_orphaned = table_suppressed and any(
            "call_indirect" in fn_wat for fn_wat in functions_wat
        )
        if not self._skipped_fn_roots and not maybe_orphaned:
            return functions_wat

        # Node tables: WAT symbol name -> referenced symbol names, in
        # first-reference order (kept deterministic — diagnostics and
        # drop order must not depend on set iteration).
        top_names: list[str] = []       # functions_wat order
        refs_by_name: dict[str, list[str]] = {}
        closure_names: set[str] = set()
        indirect_carriers: list[str] = []   # #1185, emission order
        for fn_wat in functions_wat:
            match = _WAT_FN_NAME_RE.match(fn_wat)
            if match is None:  # pragma: no cover — every emission is a (func
                continue
            name = match.group(1)
            top_names.append(name)
            refs_by_name[name] = list(
                dict.fromkeys(_WAT_CALL_RE.findall(fn_wat))
            )
            if maybe_orphaned and _WAT_CALL_INDIRECT_RE.search(fn_wat):
                indirect_carriers.append(name)
        for closure_wat in self._closure_fns_wat:
            match = _WAT_FN_NAME_RE.match(closure_wat)
            if match is None:  # pragma: no cover — every lift is a (func
                continue
            name = match.group(1)
            closure_names.add(name)
            refs_by_name[name] = list(
                dict.fromkeys(_WAT_CALL_RE.findall(closure_wat))
            )
        # The construction edge: a parent "references" each closure its
        # compile committed (the WAT itself only carries the table index).
        for anon_name, parent in self._closure_parents.items():
            if parent in refs_by_name and anon_name not in refs_by_name[parent]:
                refs_by_name[parent].append(anon_name)

        # Fixed point: doomed maps each dropped symbol to the ROOT skip
        # diagnostic; direct_cause remembers the reference that doomed it
        # (for the "calls X, which was dropped because Y" wording).
        doomed: dict[str, Diagnostic | None] = dict(self._skipped_fn_roots)
        root_of: dict[str, str] = {
            name: name for name in self._skipped_fn_roots
        }
        direct_cause: dict[str, str] = {}
        # #1185: seed the orphaned `call_indirect` carriers BEFORE the
        # fixed point, so their own callers drop transitively through the
        # ordinary `call $carrier` edge.  Every such carrier is doomed by
        # the same absent table, and the blame is the first closure lift
        # that rolled back — the skip that emptied it.  With no lift
        # failure at all (a program that applies a closure-typed parameter
        # but never writes a closure) there is no root to name, and the
        # carrier is its own root.
        orphaned: dict[str, None] = {}
        if indirect_carriers:
            blame = next(
                (n for n in self._closure_lift_skips if n in doomed), None,
            )
            for name in indirect_carriers:
                if name in doomed:
                    continue  # already dropped for a direct-call reason
                doomed[name] = doomed[blame] if blame is not None else None
                root_of[name] = root_of[blame] if blame is not None else name
                orphaned[name] = None
        changed = True
        while changed:
            changed = False
            for name, refs in refs_by_name.items():
                if name in doomed:
                    continue
                hit = next((r for r in refs if r in doomed), None)
                if hit is None:
                    continue
                doomed[name] = doomed[hit]
                root_of[name] = root_of[hit]
                direct_cause[name] = hit
                changed = True

        dropped_tops = [
            n for n in top_names if n in direct_cause or n in orphaned
        ]
        if not dropped_tops and not (closure_names & direct_cause.keys()):
            return functions_wat

        def _where(diag: Diagnostic) -> str:
            """Render a root diagnostic's position for an [E620] chain."""
            at = f"line {diag.location.line}, column {diag.location.column}"
            return (
                at if diag.location.file == self.file
                else f"{diag.location.file}, {at}"
            )

        # Emit one [E620] per dropped top-level function, in emission
        # order.  Closures carry no separate diagnostic — the parent's
        # warning covers the drop (the closure is not a user-named unit).
        for name in dropped_tops:
            decl = self._fn_decl_by_wat_name.get(name)
            if decl is None:  # pragma: no cover — tracked at every compile
                continue
            if name in orphaned:
                # #1185: no callee to name — this function reaches its
                # target through the function table, and there is no table.
                orphan_diag = doomed[name]
                if orphan_diag is not None:
                    # `table_suppressed` means NO lift committed, so "no
                    # closure survived" is exact; the named function is
                    # one of the rolled-back lifts, not necessarily the
                    # only one — hence the parenthetical rather than a
                    # "because X" claim.
                    why = (
                        f"the module's function table is empty: no "
                        f"closure survived codegen (function "
                        f"'{root_of[name]}' was skipped — see the "
                        f"[{orphan_diag.error_code}] diagnostic at "
                        f"{_where(orphan_diag)})"
                    )
                else:
                    why = (
                        "the module declares no function table: this "
                        "program creates no closure for it to hold"
                    )
                self._warning(
                    decl,
                    f"Function '{name}' applies a closure via "
                    f"call_indirect, but {why} — function dropped from "
                    f"the compiled output.",
                    rationale="An indirect call dispatches through the "
                    "module's function table. With no closure in the "
                    "table, the table is not emitted and this function's "
                    "call_indirect has no target — the module would fail "
                    "to load with a raw WebAssembly 'unknown table' error "
                    "naming no Vera source, on the first call to ANY "
                    "export. It is dropped with this diagnostic instead. "
                    "Fix the root cause at the referenced location, or "
                    "pass this function a closure the compiler can lift, "
                    "to restore it and its callers.",
                    spec_ref='Chapter 11, Section 11.4.1 "Compilable Subset"',
                    error_code="E620",
                )
                # #1183: the [E620] just appended IS this carrier's
                # explanation — record it so `vera run --fn <carrier>`
                # refuses with it instead of falling back to the
                # silent-substitution class (PR #1192 review).
                self._dropped_fn_diags[name] = self.diagnostics[-1]
                continue
            cause = direct_cause[name]
            via_closure = cause in closure_names
            if via_closure:
                # A closure's own refs never include `$anon` names (those
                # travel as table indices), so one hop lands on a real
                # function symbol.
                cause = direct_cause[cause]
            root_name = root_of[name]
            root_diag = doomed[name]
            if root_diag is not None:
                where = _where(root_diag)
                root_part = (
                    f"which was skipped by codegen (see the "
                    f"[{root_diag.error_code}] diagnostic at {where})"
                )
            else:
                root_part = (
                    "which could not be compiled (see the earlier "
                    "diagnostics)"
                )
            if cause == root_name:
                chain = f"function '{root_name}', {root_part}"
            else:
                chain = (
                    f"function '{cause}', which was dropped because "
                    f"function '{root_name}' was skipped"
                    if root_diag is None else
                    f"function '{cause}', which was dropped because "
                    f"function '{root_name}' was skipped by codegen (see "
                    f"the [{root_diag.error_code}] diagnostic at {where})"
                )
            verb = (
                "contains a closure that calls" if via_closure else "calls"
            )
            self._warning(
                decl,
                f"Function '{name}' {verb} {chain} — "
                f"function dropped from the compiled output.",
                rationale="The skipped function is absent from the "
                "emitted WASM module, so this function's call to it "
                "cannot be assembled — it is dropped with this "
                "diagnostic instead of failing module assembly with a "
                "raw WebAssembly error naming a missing symbol. Fix "
                "the root cause at the referenced location to restore "
                "this function and its callers.",
                spec_ref='Chapter 11, Section 11.4.1 "Compilable Subset"',
                error_code="E620",
            )
            # #1183: the [E620] just appended IS this function's
            # explanation — a caller drop has no root skip of its own.
            self._dropped_fn_diags[name] = self.diagnostics[-1]

        # Prune the doomed top-level functions and their exports; stub
        # the doomed closure bodies in place (table slots must survive).
        dropped_set = set(dropped_tops)
        exports[:] = [e for e in exports if e not in dropped_set]
        self._closure_fns_wat = [
            (
                f"  (func ${match.group(1)} unreachable)"
                if (match := _WAT_FN_NAME_RE.match(closure_wat)) is not None
                and match.group(1) in direct_cause
                else closure_wat
            )
            for closure_wat in self._closure_fns_wat
        ]
        return [
            fn_wat for fn_wat in functions_wat
            if (m := _WAT_FN_NAME_RE.match(fn_wat)) is None
            or m.group(1) not in dropped_set
        ]

    # -----------------------------------------------------------------
    # Compilation entry point
    # -----------------------------------------------------------------

    @contextlib.contextmanager
    def _fn_alias_scope(self, decl: ast.FnDecl) -> Iterator[None]:
        """Name *decl*'s own scope for the duration of its compile (#1208).

        A ``forall`` variable SHADOWS a same-named module alias over the whole
        signature and body — the checker binds it before it binds any slot — so
        the parameter names, refinement binders and slot-reference keys emitted
        for a generic TEMPLATE have to be rendered with it in scope.  Almost
        every function codegen compiles is already concrete (a mono clone
        carries ``forall_vars=None``, and this is then the identity), but the
        uninstantiated template is emitted and EXPORTED too: named against the
        bare module env, ``forall<T> fn f(@Option<T>, @Option<Int>)`` under
        ``type T = Int`` collapses two parameter stacks the checker kept apart,
        and the exported body reads the wrong parameter.

        Narrows only ``_alias_env`` — the flat alias maps are unchanged, since
        a type parameter is not an alias — so it composes with
        ``_module_alias_scope``, which the emission doors enter outside it.
        """
        if not decl.forall_vars:
            yield
            return
        saved = self._alias_env
        self._alias_env = naming.with_type_params(saved, decl.forall_vars)
        try:
            yield
        finally:
            self._alias_env = saved

    def _declaration_namespace(
        self, name: str, origin: tuple[str, ...] | None = None,
    ) -> tuple[str, ...] | None:
        """The namespace the declaration emitted as *name* was DECLARED in.

        The one predicate every registration and emission door asks before
        entering ``_module_alias_scope``, so a body is always named, resolved
        and measured in the namespace that wrote it (#1111, #1316).  Three
        answers, in this order:

        * *origin* when the caller has one — a mono clone of an IMPORTED
          generic records its defining module in ``_mono_clone_origins``, and
          that beats every name-based test.
        * :data:`PRELUDE_NAMESPACE` when the name (or the base a mono clone's
          ``base$Types`` mangling strips back to) is a prelude combinator.
          The same ``split("$")[0]`` test ``_is_prelude_origin`` and
          ``_compile_fn``'s ``_in_prelude_fn`` flag use, so a declaration's
          diagnostics and its type resolution agree about whose code it is.
        * ``None`` — the entry file's own namespace, where
          ``_module_alias_scope`` is a no-op.
        """
        if origin is not None:
            return origin
        if name.split("$")[0] in self._prelude_fn_names:
            return PRELUDE_NAMESPACE
        return None

    def _sync_alias_env(self) -> None:
        """Re-derive ``_alias_env`` from the flat alias maps (#1208).

        The naming environment must describe the SAME aliases every other
        alias consumer reads mid-compile, so it is rebuilt at each point the
        flat maps change: Pass-1 registration, prelude injection, and both
        ends of ``_module_alias_scope``'s swap.  A new mutation site must call
        this too — a stale env renders a name against the wrong namespace, and
        a name minted one way and looked up another misses SILENTLY.

        The type-parameter narrowing a generic TEMPLATE needs is layered on top
        per function by ``_fn_alias_scope``, not stored here: it belongs to one
        declaration, while this describes the module.
        """
        order = self._decl_order
        members = self._adt_members_in_scope()
        self._alias_env = AliasEnv(
            aliases=dict(self._type_aliases),
            alias_params=dict(self._type_alias_params),
            data_types={
                name: self._adt_decl_index(name, order)
                for name in self._adt_layouts
                if members is None or name in members
            },
            _order={
                name: order.get(name, _BUILTIN_DECL_INDEX)
                for name in self._type_aliases
            },
        )

    def _adt_members_in_scope(self) -> frozenset[str] | None:
        """The ADT names visible in the namespace now installed (#1253).

        ``None`` means "no module structure to scope by" — a single-file
        program, or a point before ``_register_modules`` has computed the
        membership sets — and the caller then takes every registered layout,
        which is what codegen did everywhere before this.

        Otherwise it is the owning namespace's own ADTs plus the ones it
        IMPORTS, public and in-filter: the checker's view of that module,
        which is the whole point.  A namespace with no computed entry (a
        module the resolver reached but nothing recorded) falls back to the
        same permissive whole-map answer rather than to an empty set — a
        wrongly-empty membership would silently re-open the divergence in the
        other direction, rendering a name the module DOES own as opaque.

        GLOBAL INFRASTRUCTURE is a member of every namespace, and is derived
        rather than snapshotted: any registered layout that NO namespace
        declares.  The ``_register_builtin_adts`` set (``Option``, ``Result``,
        ``Tuple``, …) is only half of it — ``Json``, ``HtmlNode``, ``Request``
        and ``Response`` are registered by the PRELUDE injection in Pass 1.2,
        after ``_register_modules`` computes these sets in Pass 0.5, so a
        snapshot taken there necessarily misses them (the checker's
        ``TypeEnv`` carries all of them from the start, so the miss was an
        asymmetry between the two sides' notions of "builtin").  Subtracting
        what the namespaces declare cannot go stale with registration order.

        Subtraction alone is sound only while "declared by a namespace" and
        "global infrastructure" are DISJOINT, and §8.4.1 makes them overlap
        on purpose: the prelude's data types are ordinary public
        declarations a program may name and shadow.  So the floor unioned
        in has to state the prelude's names positively rather than let them
        be recovered by elimination (#1277).  Two sets do that, and they
        answer different questions:

        - ``_builtin_adt_names`` — the Pass-0.5 snapshot of
          ``_register_builtin_adts`` (``Option``, ``Result``, ``Tuple``, …),
          which is also the set the E609/E610 collision rails exempt.
        - :func:`~vera.prelude.prelude_adt_names` — every ADT the PRELUDE
          can provide, which is the half the snapshot cannot hold: ``Json``,
          ``HtmlNode``, ``Request`` and ``Response`` register in Pass 1.2,
          after this membership is computed.  Without it, one file's ``data
          Json`` removed ``Json`` from every OTHER namespace's members —
          including the entry program's, which never declared it and
          legitimately sees the prelude's — while the checker's ``TypeEnv``
          carries the name in every namespace unconditionally.

        Naming a prelude ADT the program never demanded is inert, so this
        floor does not condition on demand where the checker does not —
        but the reason is NOT that an unregistered name is filtered out
        downstream.  That is true of a name with no layout at all, and
        false in exactly the case this floor is about: when a module has
        declared the name, a layout IS registered, and it is the module's.
        What makes it inert is narrower and is a property of today's only
        consumer — ``naming._resolve_named`` reads ``data_types`` for the
        index alone, and the index changes a rendering only for
        ``Decimal`` and the single ``REMOVED_ALIASES`` entry ``Float``,
        neither of which the prelude declares.  A future consumer that
        reads the set for anything else would see the module's layout
        under the prelude's name — which is why the Pass-1.2 rail refuses
        that program (E621) rather than leaving the two to disagree.

        THE PRELUDE is a namespace too (#1316), and the only one whose
        membership is stated rather than looked up: it declares no user type
        and imports none, so its members are exactly the global
        infrastructure.  It has to be answered here even for a single-file
        program, where the permissive ``None`` above would otherwise hand the
        prelude's bodies the ENTRY file's declarations — and a
        ``data Array { … }`` in the entry file would then make the prelude's
        own ``Array<T>`` parameters a one-word ADT pointer instead of the
        container's (ptr, len) pair.
        """
        infrastructure = (
            frozenset(self._adt_layouts) - self._namespace_declared_adts
        )
        if self._active_module_path == PRELUDE_NAMESPACE:
            return (
                infrastructure | self._builtin_adt_names | prelude_adt_names()
            )
        if not self._adt_namespace_members:
            return None
        members = self._adt_namespace_members.get(self._active_module_path)
        if members is None:
            return None
        return (
            members | infrastructure
            | self._builtin_adt_names | prelude_adt_names()
        )

    def _adt_decl_index(self, name: str, order: dict[str, int]) -> int:
        """Where *name* sits in the declaration-index space *order* keys (#1227).

        ``_adt_layouts`` is one map across every absorbed namespace, so the
        active space is asked first: a name it stamped is a declaration of
        this namespace, at that position.  A name it did not stamp may still
        be a declaration of ANOTHER module — imported ADTs are visible to the
        importer (the checker registers them, carrying the index their own
        module gave them), and they must arrive with that index or a main-file
        alias naming one resolves through a declaration the checker's binding
        table treats as coming later.  Only what no namespace declared —
        built-ins, and the prelude's own ADTs — takes the reserved floor.
        """
        idx = order.get(name)
        if idx is not None:
            return idx
        owner = self._adt_layout_owners.get(name)
        if owner is not None:
            owner_idx = self._module_decl_order.get(owner, {}).get(name)
            if owner_idx is not None:
                return owner_idx
        return _BUILTIN_DECL_INDEX

    def _stamp_decl_order(self, name: str, *, prelude: bool = False) -> None:
        """Record *name*'s position in the ACTIVE declaration-index space.

        Called once per ``type`` / ``data`` registration, in source order.
        Idempotent by name WITHIN one namespace — a name is stamped where it
        first registers there, and a later re-registration (the prelude pass
        revisits declarations) does not move it.  A module's declarations are
        never stamped here: they are captured into ``_module_decl_order`` in
        the module's own 0-based space and installed by
        ``_module_alias_scope``, so one namespace's stamp can never decide
        another's forward/backward question (PR #1224 review).

        *prelude* draws from the negative block instead, so injected
        declarations precede the main file's whatever order codegen happens to
        walk them in — and, being recorded in ``_prelude_decl_order`` too,
        precede every module's as well.

        That second record is written UNCONDITIONALLY (#1287).
        ``_prelude_decl_order`` is not a namespace: ``_module_alias_scope``
        builds every module's space as ``{**_prelude_decl_order,
        **module_own}``, so it is the base layer under all of them, and its
        contents are a fact about what ``inject_prelude`` laid down.  Keying
        the write on ``_decl_order`` — the ACTIVE, main-file namespace —
        let a main-file declaration decide it: ``type Option = Int`` is
        accepted (§8.4.1 — the prelude's data types are ordinary public
        declarations a program may shadow; only the ``Vera`` prefix is
        reserved, E154) and does NOT suppress the prelude's ``data
        Option<T>``, so the guard fired on the prelude stamp and left
        ``Option`` out of the block entirely — resolving at
        ``_BUILTIN_DECL_INDEX`` inside every module namespace, and shifting
        every later prelude declaration one place earlier because the
        counter never advanced.  That is exactly the cross-namespace leak
        ``_decl_order`` and ``_module_decl_order`` were split apart to
        prevent (PR #1224 review).

        The ACTIVE space still takes the main file's stamp: `setdefault`
        leaves a name the main file already declared where the main file put
        it, so the shadow keeps winning its own namespace.
        """
        if prelude:
            if name not in self._prelude_decl_order:
                self._prelude_decl_order[name] = self._prelude_decl_order_next
                self._prelude_decl_order_next += 1
            self._decl_order.setdefault(name, self._prelude_decl_order[name])
            return
        if name in self._decl_order:
            return
        self._decl_order[name] = self._decl_order_next
        self._decl_order_next += 1

    def _contends_with_prelude(
        self, prelude_decl: ast.DataDecl, owner: tuple[str, ...],
    ) -> bool:
        """Can *owner*'s declaration of this name share the prelude's layout?

        The flat map holds ONE layout per name, so two declarations of a
        prelude name are a contention exactly when they describe different
        layouts (:func:`~vera.prelude.data_decl_shape`).  A module that
        restates the prelude's own type — same constructors, same order,
        same field types, type parameters compared positionally — is not a
        contention: the single registered layout is correct for both, which
        is why such programs compile and run today and must keep doing so.
        `examples/vera/collections.vera` is that shape in this repository:
        it declares `public data Option<T> { None, Some(T) }`, which
        `examples/modules.vera` imports, so a rail keyed on the name alone
        refuses a shipped example.

        A module whose declaration this cannot find (the name is declared,
        but the resolved module's AST no longer holds the node) is treated
        as contending — the safe direction, since the alternative is
        sharing a layout that may not fit.
        """
        module_decl = self._find_module_data_decl(owner, prelude_decl.name)
        if module_decl is None:  # pragma: no cover — defensive
            return True
        # The module's declaration is canonicalized through the MODULE's own
        # alias maps — §8.4.1 makes an alias module-local, so those are the
        # only ones that may answer for it (#1111) — and the prelude's
        # through nothing.  One side only, in that direction: a restatement
        # spelled through a module alias is still a restatement, while
        # resolving the prelude's spelling through a module's aliases would
        # let `type Array<T> = Int;` collapse the prelude's `Array<Json>`
        # onto the module's `Int` and share a layout that does not fit.
        return (
            data_decl_shape(
                module_decl,
                self._module_type_aliases.get(owner, {}),
                self._module_type_alias_params.get(owner, {}),
            )
            != data_decl_shape(prelude_decl)
        )

    def _emit_prelude_adt_contention_error(
        self, name: str, owner: tuple[str, ...],
    ) -> None:
        """Report a module ADT that took a demanded prelude ADT's name (#1277).

        Located at the MODULE's declaration, in the module's own file —
        the declaration the user can act on.  Before this rail the only
        report was the wreckage: an E602 for an unknown constructor inside
        the prelude's own combinator, an E620 cascade behind it, every one
        of them at ``<prelude>`` coordinates and none of them naming
        ``data {name}`` or the module it is in.

        The sibling of E609/E610 (§11.16): one flat WASM namespace, one
        layout per name.  Those rails compare two IMPORTED modules and
        exempt the Pass-0.5 built-in snapshot, which is taken before the
        prelude's own ADTs register — this is the same collision against
        the half of global infrastructure that snapshot cannot hold.

        Both branches of the fix are measured, not supposed.  RENAMING is
        always available.  Matching the prelude's shape works because the
        one registered layout then serves both declarations — the same
        condition :meth:`_contends_with_prelude` tests, so the instruction
        and the rail cannot disagree.  Telling the user to redeclare the
        type in the ENTRY file would not be true: a differently-shaped
        entry declaration suppresses the prelude's injection and silently
        drops the functions that use the module's version instead.
        """
        mod = ".".join(owner)
        decl = self._find_module_data_decl(owner, name)
        loc = SourceLocation(file=self.file)
        source_line = ""
        resolved = next(
            (m for m in self._resolved_modules if m.path == owner), None)
        if resolved is not None:
            loc = SourceLocation(file=str(resolved.file_path))
            if decl is not None and decl.span:
                loc.line = decl.span.line
                loc.column = decl.span.column
                lines = resolved.source.splitlines()
                if 1 <= loc.line <= len(lines):
                    source_line = lines[loc.line - 1]
        self.diagnostics.append(Diagnostic(
            description=(
                f"Imported module '{mod}' declares a data type '{name}' "
                f"whose shape differs from the prelude's '{name}', and "
                f"both are compiled into this program."
            ),
            location=loc,
            source_line=source_line,
            rationale=(
                "The flat compilation strategy (C7e) gives the whole "
                "program one ADT namespace, and the prelude's data types "
                "are compiled into it alongside every imported module's. "
                "One name carries one constructor layout there, so two "
                f"differently-shaped declarations of '{name}' cannot both "
                "be registered: the module's takes the layout, the "
                "prelude's is dropped, and every function that uses the "
                "prelude type is dropped behind it."
            ),
            fix=(
                f"Rename '{name}' in module '{mod}' and update that "
                f"module's uses of it. If the module means the prelude's "
                f"type, give its declaration the prelude's shape instead "
                f"— the same constructors, in the same order, with the "
                f"same field types — and the one layout serves both."
            ),
            spec_ref='Chapter 11, Section 11.16 "Cross-Module Compilation"',
            severity="error",
            error_code="E621",
        ))

    def _check_entry_module_adt_contention(self, program: ast.Program) -> None:
        """Refuse an entry `data` that cannot share a module's layout (#1312).

        The third pair in the one-layout-per-name family, and the one no rail
        could be asked about before.  E609 compares two IMPORTED modules;
        E621 compares an imported module against the PRELUDE — and an
        entry-file declaration SUPPRESSES the prelude's injection outright,
        so the prelude declaration E621 needs never exists and the entry
        versus module pair fell through both.

        What it fell through to was silent.  Pass 1 registers the entry
        file's `data` over the Pass-0.5 module harvest, which only
        ``setdefault``s, so the entry's declaration takes the one flat layout
        slot and the module's own constructors become ``unknown constructor``
        inside the module's own bodies — an ``[E602]`` skip, an ``[E620]``
        cascade behind it, both WARNINGS.  A `vera check`-green program
        compiled with exit 0 to a module whose `main` was simply absent from
        the exports.

        SHAPE decides, exactly as it does for the prelude pair
        (:func:`~vera.prelude.data_decl_shape`): two declarations that
        describe the same layout are served by the one registered slot, and
        an entry file restating a module's public type must keep compiling.
        Each side's field types resolve through the aliases of the namespace
        it was WRITTEN in — the entry's flat maps here, the module's own
        captured maps for the module's — because §8.4.1 makes an alias
        module-local and no other namespace's may answer for it.

        ONE diagnostic, at the ENTRY's declaration: that is the file `vera
        compile` was given and the declaration whose registration wins the
        slot, and it names the module's file and line so the other half is
        reachable.  E608/E609/E610/E621 all report one instruction per
        collision, and reporting the module's declaration as well would say
        the same thing twice.
        """
        if not self._module_adt_declarers:
            return
        for tld in program.declarations:
            decl = tld.decl
            if not isinstance(decl, ast.DataDecl):
                continue
            declarers = self._module_adt_declarers.get(decl.name, ())
            if not declarers:
                continue
            entry_shape = data_decl_shape(
                decl, self._type_aliases, self._type_alias_params,
            )
            for owner in declarers:
                module_decl = self._find_module_data_decl(owner, decl.name)
                if module_decl is not None and entry_shape == data_decl_shape(
                    module_decl,
                    self._module_type_aliases.get(owner, {}),
                    self._module_type_alias_params.get(owner, {}),
                ):
                    continue
                self._emit_entry_adt_contention_error(decl, owner)

    def _emit_entry_adt_contention_error(
        self, decl: ast.DataDecl, owner: tuple[str, ...],
    ) -> None:
        """Report an entry `data` that contends with a module's (#1312).

        Located at the entry declaration, in the entry file, with the
        module's own coordinates named in the description — see
        :meth:`_check_entry_module_adt_contention` for why one diagnostic
        rather than two.  Refused by the same Pass-1.9 severity gate
        E608 / E609 / E610 / E621 take, so there is ONE refusal mechanism.
        """
        mod = ".".join(owner)
        loc = SourceLocation(file=self.file)
        source_line = ""
        if decl.span is not None:
            loc.line = decl.span.line
            loc.column = decl.span.column
            if self.source:
                lines = self.source.splitlines()
                if 1 <= loc.line <= len(lines):
                    source_line = lines[loc.line - 1]
        where = f"module '{mod}'"
        module_decl = self._find_module_data_decl(owner, decl.name)
        resolved = next(
            (m for m in self._resolved_modules if m.path == owner), None)
        if resolved is not None and module_decl is not None and module_decl.span:
            where = (
                f"module '{mod}' ({resolved.file_path}:"
                f"{module_decl.span.line})"
            )
        self.diagnostics.append(Diagnostic(
            description=(
                f"This file declares a data type '{decl.name}' whose shape "
                f"differs from the '{decl.name}' declared by {where}, and "
                f"both are compiled into this program."
            ),
            location=loc,
            source_line=source_line,
            rationale=(
                "The flat compilation strategy (C7e) gives the whole "
                "program one ADT namespace. One name carries one "
                "constructor layout there, so two differently-shaped "
                f"declarations of '{decl.name}' cannot both be registered: "
                "this file's takes the layout, the module's is dropped, and "
                "every function in that module which constructs or matches "
                "its own version is dropped behind it — including any entry "
                "function that calls one."
            ),
            fix=(
                f"Rename '{decl.name}' in this file and update its uses "
                f"here. If this file means the module's type, import it "
                f"instead of redeclaring it — or give this declaration the "
                f"module's shape, the same constructors in the same order "
                f"with the same field types, and the one layout serves both."
            ),
            spec_ref='Chapter 11, Section 11.16 "Cross-Module Compilation"',
            severity="error",
            error_code="E623",
        ))

    def _find_module_data_decl(
        self, mod_path: tuple[str, ...], name: str,
    ) -> ast.DataDecl | None:
        """*mod_path*'s ``data {name}`` declaration, for its span."""
        for mod in self._resolved_modules:
            if mod.path != mod_path:
                continue
            for tld in mod.program.declarations:
                if isinstance(tld.decl, ast.DataDecl) and tld.decl.name == name:
                    return tld.decl
        return None

    def compile_program(self, program: ast.Program) -> CompileResult:
        """Compile a complete Vera program to WebAssembly."""
        # Pass 0a: reject programs with typed holes
        holes = _find_holes(program)
        if holes:
            for hole in holes:
                loc = SourceLocation(file=self.file)
                if hole.span:
                    loc.line = hole.span.line
                    loc.column = hole.span.column
                self.diagnostics.append(Diagnostic(
                    description=(
                        "Program contains a typed hole (?); "
                        "fill all holes before compiling."
                    ),
                    location=loc,
                    rationale=(
                        "Typed holes are placeholders for incomplete "
                        "expressions. They are allowed by vera check but "
                        "cannot be compiled to WebAssembly."
                    ),
                    fix="Replace ? with a complete expression.",
                    spec_ref='Chapter 4, Section 4.17 "Typed Holes"',
                    severity="error",
                    error_code="E614",
                ))
            return CompileResult(
                wat="",
                wasm_bytes=b"",
                exports=[],
                diagnostics=self.diagnostics,
                state_types=[],
                md_ops_used=set(),
                regex_ops_used=set(),
                map_ops_used=set(),
                set_ops_used=set(),
                decimal_ops_used=set(),
                json_ops_used=set(),
                html_ops_used=set(),
                http_ops_used=set(),
                async_ops_used=set(),
                inference_ops_used=set(),
                db_ops_used=set(),
                random_ops_used=set(),
                math_ops_used=set(),
            )

        # Pass 0: hoist non-generic where-helpers to parent-qualified
        # top-level decls (#991) so same-named helpers in different parent trees
        # (or a helper named like a top-level function) don't collide in the
        # flat WAT namespace.  Runs before EVERY other pass — including module
        # registration below, whose `_collect_local_fn_names` shadow set must
        # see the post-hoist program: a hoisted helper no longer occupies its
        # bare source name, so it must no longer suppress a same-named import's
        # bare emission (PR #1013 round 4 — the stale pre-hoist shadow left the
        # import unemitted and the bare call dangling `unknown func`; at base
        # the helper's bare emission silently CAPTURED the import-bound call, a
        # wrong body under spec §5 helper locality).  Codegen-only: the checker
        # and verifier keep the original nested AST (both scope helper
        # resolution lexically, #991).
        # #1014: parent-qualify nested GENERIC where-helper names (and their
        # lexically-visible bare calls) so two same-named ``forall`` helpers
        # under different parents are distinct mono bases (``a$where$g`` /
        # ``b$where$g``) instead of colliding first-seen-wins in the flat
        # base registry (silent wrong body).
        #
        # Runs BEFORE the #991 hoist: a non-generic helper (``flag``) that calls
        # a generic SIBLING (``gid``) must have that bare call qualified while it
        # is still lexically inside the shared ``where`` block — the hoist would
        # otherwise lift ``flag`` to a top-level ``parent$where$flag`` first,
        # putting it out of reach of the parent-scoped qualification and leaving
        # its ``gid`` call bare (a dangling ``unknown func`` at run — the
        # conformance ch09 regression).  Qualification descends into non-generic
        # helpers exactly as the hoist does, so a generic under a hoisted chain
        # (``a$where$leaf$where$g``) still lands on the identical name; the
        # verifier scopes helpers lexically on its un-hoisted copy, so applying
        # the SAME transform there keeps both sides keying instances identically.
        program = qualify_nested_generic_decls(program)

        program = self._hoist_nongeneric_where_helpers(program)

        # #1299 / #1281: record which function names each namespace can NAME
        # — and which of those are ambiguous — before anything registers or
        # compiles against the flat registry.  Not folded into
        # `_register_modules`: that returns early when the program imports
        # nothing, and the entry program still needs its own set (a
        # `forall<T>` parent's `where` helper puts an out-of-scope bare name
        # in `_fn_sigs` with no module in sight).  Ordered BEFORE it because
        # the E608 rail inside reads the ambiguity half.
        self._collect_namespace_fn_names(program)

        # Pass 0.5: register imported module declarations (C7e)
        self._register_modules(program)

        # Pass 1: register local function signatures (shadows imports)
        self._register_all(program)

        # #1312: the ENTRY file's own `data` declarations against the
        # modules'.  Asked here, between the Pass-0.5 module harvest and the
        # Pass-1.2 prelude injection, for two reasons: `_module_adt_declarers`
        # is already built, and `_type_aliases` still holds ONLY the entry
        # file's aliases — which are the ones an entry declaration's field
        # types resolve through (§8.4.1).
        self._check_entry_module_adt_contention(program)

        # #841: Future<Result<String, String>>-returning fn names — one
        # derivation feeds both import-emission passes (pre-scan +
        # WasmContext) so they agree on which awaits need the
        # fused-handle check.  Derived from the return-type registry
        # (local Pass-1 registrations + the Pass-0 cross-module #628
        # harvest), not the local declarations, so imported and
        # module-qualified calls classify too.  #1109: the registry is
        # matched with aliases resolved (an alias-spelled `-> @F`
        # participates like the literal Future spelling) — Pass 0.5/1
        # have already populated _type_aliases/_type_alias_params.
        self._future_ret_fns = compute_future_ret_fns(
            self._fn_ret_type_exprs,
            self._type_aliases,
            self._type_alias_params,
        )
        self._future_ret_module_fns = compute_future_ret_module_fns(
            self._module_fn_ret_type_exprs,
            self._type_aliases,
            self._type_alias_params,
        )

        # Pass 1.2: inject prelude ADTs and combinator implementations
        # Prelude functions are registered as builtins in the type checker
        # (environment.py) but need compilable AST bodies for codegen.
        # inject_prelude prepends DataDecl, FnDecl, and TypeAliasDecl
        # nodes to program.declarations; we register them here.
        existing_fns = set(self._fn_sigs.keys())
        existing_adts = set(self._adt_layouts.keys())
        # #1111: identity snapshot of the pre-injection declaration list,
        # so prelude-injected TypeAliasDecls can be captured by node
        # identity below.  A name-based delta would miss a prelude alias
        # whose name a main-file alias shadows — and module namespaces
        # must overlay onto the PRELUDE's definition of that name, not
        # the main file's.
        pre_inject_ids = {id(tld) for tld in program.declarations}
        from vera.prelude import inject_prelude
        # #851 — keep the synthetic prelude buffer: injected decls'
        # spans index into it, and `_diag_location` quotes it (under
        # the `<prelude>` origin) for prelude-origin diagnostics.
        self._prelude_source = inject_prelude(program)
        # #1277: prelude ADTs whose name an IMPORTED module has already
        # taken in `_adt_layouts`.  One flat layout map, one slot per name,
        # so the two declarations contend and the module's — registered back
        # in Pass 0.5 — wins by arriving first.
        contended: list[tuple[str, tuple[str, ...]]] = []
        for tld in program.declarations:
            if id(tld) in pre_inject_ids:
                continue
            # #1208: stamp every INJECTED declaration into the prelude block
            # of the shared index space, in the order `inject_prelude` laid
            # them down — which is ahead of the main file's, where codegen
            # has already stamped from 0.  Both kinds, because the bound
            # orders aliases and ADTs against each other.
            if isinstance(tld.decl, (ast.TypeAliasDecl, ast.DataDecl)):
                self._stamp_decl_order(tld.decl.name, prelude=True)
            if isinstance(tld.decl, ast.DataDecl):
                # Asked by OBSERVING what `inject_prelude` laid down rather
                # than by re-deriving its demand predicates in Pass 0.5,
                # where the E609/E610 rails live: a second copy of "does
                # this program want Json?" is a second thing to keep in
                # step, and the identity filter above already says exactly
                # what was injected.  A main-file shadow suppresses the
                # injection outright, so it never reaches here — which is
                # what keeps the §8.4.1 entry-file shadow legal.
                #
                # Read off the DECLARATIONS (`_module_adt_declarers`), not
                # the registered layouts: the harvest skips a built-in name,
                # so `_adt_layout_owners` sees `data Json` and never `data
                # Option`, and keying the rail on it covered four of the
                # prelude's eight names while §8.4.1 and §11.16 claim all
                # eight.  EVERY declarer is asked, because each declaration
                # contends on its own — a first-wins lookup let a module
                # that restates the prelude's type answer for a sibling
                # that does not, which made the rail order-dependent.
                for owner in self._module_adt_declarers.get(
                    tld.decl.name, (),
                ):
                    if self._contends_with_prelude(tld.decl, owner):
                        contended.append((tld.decl.name, owner))
            if isinstance(tld.decl, ast.TypeAliasDecl):
                self._prelude_type_aliases[tld.decl.name] = tld.decl.type_expr
                if tld.decl.type_params:
                    self._prelude_type_alias_params[tld.decl.name] = (
                        tld.decl.type_params
                    )
        # Reported at the declaration that caused it, and refused by the
        # Pass-1.9 severity gate below — the route E608 / E609 / E610 take,
        # so there is ONE refusal mechanism rather than a second early
        # return beside it (measured: an early return here changes neither
        # the diagnostics nor the empty exports, including on a shape whose
        # monomorphization runs over the contended type in between).
        # Without the report, registration proceeds against the module's
        # layout: the prelude's own combinators fail on its constructors
        # (an E602 inside `<prelude>`), every user function touching the
        # type is dropped behind an E620 cascade, and all of it is reported
        # as WARNINGS — a zero-exit compile of a module with the functions
        # silently missing.
        for name, owner in contended:
            self._emit_prelude_adt_contention_error(name, owner)
        # TYPES first, then functions — the split `_register_all` makes for
        # the main file, for the same reason: a prelude combinator's signature
        # is derived by asking the spine what its parameter names MEAN, and
        # the prelude's own ADTs have to be in the env before the first such
        # question.  Only the flat-map halves are registered here; the
        # per-namespace `_prelude_type_aliases` capture happened in the
        # identity-filtered walk above.
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.DataDecl):
                if decl.name not in existing_adts:  # pragma: no cover
                    self._register_data(decl)
            elif isinstance(decl, ast.TypeAliasDecl):
                if decl.name not in self._type_aliases:
                    self._stamp_decl_order(decl.name)
                    self._type_aliases[decl.name] = decl.type_expr
                    if decl.type_params:
                        self._type_alias_params[decl.name] = decl.type_params
            else:
                continue
            # #1208: re-derived per TYPE declaration, as in `_register_all`
            # — a prelude constructor field naming an earlier prelude type
            # is measured through this env.
            self._sync_alias_env()
        # #1208: prelude aliases and ADTs are now in the flat maps too.
        self._sync_alias_env()
        # #1316: and the prelude's own FUNCTIONS register in the PRELUDE's
        # namespace.  Their signatures name the prelude's types, and spec
        # §8.4.1 scopes the alias namespace to the declaring module — so an
        # entry-file `type Json = Int;` must not re-type `json_get`'s
        # parameter.  Pre-fix it did: the signature took the alias's i64 while
        # the body built the ADT's i32 pointer, and the module died at load
        # with `expected i32, found i64` inside `json_get` on a check-green,
        # verify-green program.  The same scope is entered again when these
        # bodies are COMPILED (Pass 2) and when their generic clones are
        # registered and emitted, so the signature and the body agree.
        with self._module_alias_scope(PRELUDE_NAMESPACE):
            for tld in program.declarations:
                decl = tld.decl
                if not isinstance(decl, ast.FnDecl):
                    continue
                if decl.name in existing_fns:
                    continue
                self._register_fn(decl)
                # #516 Stage 2 — anything that arrives here through
                # inject_prelude() (i.e. wasn't in `existing_fns` before
                # the prelude pass) is by definition a prelude / built-
                # in injection, not user code.  Move it from
                # `_fn_source_map` to `_prelude_fn_names` so the trap-
                # frame resolver tags traps inside it as `<builtin>`
                # rather than surfacing a misleading file:line that
                # points at the prelude's *embedded* source string
                # (the prelude FnDecls have spans because their bodies
                # come from `parse_to_ast` of synthesised Vera source —
                # the spans point at line N of that synthetic source,
                # which is meaningless coordinates inside the user's
                # actual file).
                self._fn_source_map.pop(decl.name, None)
                self._prelude_fn_names.add(decl.name)

        # #1299: the prelude's FUNCTIONS belong to every
        # namespace.  Rebuild the visibility tables now that
        # `_prelude_fn_names` is populated — Pass 0.5's call could not know
        # them, and the verifier builds ITS tables from a post-injection
        # program, so leaving them out here made the two sides' discovery
        # scopes differ by exactly the five combinators on every
        # module-using program.
        self._collect_namespace_fn_names(program)

        # #305: Pass-1 signatures for USER fns whose params/return
        # reference prelude ADTs (Request/Response/Json/HtmlNode) were
        # computed before the prelude registered those layouts, so they
        # recorded "unsupported" — leaving fn_param_types stale even
        # though the function compiles fine in Pass 2 (the serve
        # driver's handler validation reads fn_param_types).
        # Re-register exactly those now that the layouts exist
        # (_register_fn is overwrite-idempotent).
        for tld in program.declarations:
            decl = tld.decl
            if (
                isinstance(decl, ast.FnDecl)
                and decl.name in existing_fns
                and decl.name in self._fn_sigs
            ):
                params, ret = self._fn_sigs[decl.name]
                if "unsupported" in params or ret == "unsupported":
                    self._register_fn(decl)

        # Pass 1.5: monomorphize generic functions
        mono_decls = self._monomorphize(program)
        for mdecl in mono_decls:
            # #1111: a clone of an IMPORTED generic carries its module's
            # alias-typed params/returns — register its WASM signature
            # under the defining module's alias namespace (a local
            # clone's origin is None and the scope is a no-op).
            # Defence-in-depth: without the scope an alias-typed
            # component registers as "unsupported" (probed: `@G -> @G`
            # under `G = Int` records `(['i64'], 'unsupported')`), a
            # falsehood today's consumers happen to mask — emission
            # derives the true WAT signature under the Pass-2 scope, and
            # `fn_ret_types` consumers fall back to the correctly
            # harvested bare-name entry.  The scope keeps the registry
            # truthful rather than relying on every future consumer to
            # repeat those fallbacks.
            # #1189: the clone's spans are its DEFINING module's coordinates,
            # so `_register_fn` — which stamps `_fn_source_map` with
            # `self.file` — must run under that module's source scope too.
            # Pre-fix the clone's entry paired the importer's path with the
            # module's line range; in the #1189 repro those coordinates named a
            # real-but-unrelated function in the importer, so the backtrace
            # read as correct and was not.  Same `_module_source_scope` (#1190)
            # Pass 2.5/2.6 use, so registration and emission agree; a LOCAL
            # clone has no recorded origin and the scope is a no-op.
            origin_path = self._mono_clone_origins.get(mdecl.name)
            # #1316: a clone of a PRELUDE generic has no recorded origin — it
            # is not imported — but it is still the prelude's declaration, and
            # its signature must be measured in the prelude's namespace, not
            # the entry file's.  `_declaration_namespace` answers the recorded
            # origin when there is one and the prelude otherwise.
            with (
                self._module_alias_scope(
                    self._declaration_namespace(mdecl.name, origin_path)),
                self._module_source_scope(origin_path),
            ):
                self._register_fn(mdecl)
                if origin_path is not None:
                    # #1111 (PR #1175 review): `_register_fn` just stored
                    # the clone's RAW return-type expression under the
                    # CLONE key in the shared bare-name registry — the
                    # third door into `_fn_ret_type_exprs` after the
                    # Pass-0 harvest and the shadowed `mod$…` mirror,
                    # and a main-file consumer resolving the clone key
                    # (index-element inference on a call to the clone,
                    # the fused-await classifier) would do so against
                    # the flat maps.  Canonicalize inside the scope,
                    # where the flat maps ARE the defining module's.
                    self._fn_ret_type_exprs[mdecl.name] = (
                        canonicalize_type_aliases(
                            self._fn_ret_type_exprs[mdecl.name],
                            self._type_aliases,
                            self._type_alias_params,
                        )
                    )
            # #516 Stage 2 — keep monomorphized prelude clones out of
            # `_fn_source_map`.  A clone like `option_unwrap_or$Int`
            # inherits the original generic FnDecl's span, which for a
            # prelude function points at the synthetic source string
            # `inject_prelude` constructed.  Registering it here would
            # re-introduce the same bogus-coordinates problem the
            # post-prelude loop above scrubbed for the base names.
            # The trap-frame resolver already handles monomorphized
            # prelude calls correctly via the rightmost-`$` strip rule
            # (it tags `option_unwrap_or$Int` as `<builtin>` because
            # `option_unwrap_or` is in `prelude_fn_names`), so the
            # entry here was dead weight.  Suffix-strip and check the
            # base name against `_prelude_fn_names` to detect.
            if "$" in mdecl.name:
                base = mdecl.name.rsplit("$", 1)[0]
                if base in self._prelude_fn_names:
                    self._fn_source_map.pop(mdecl.name, None)

        # Pass 1.6: rewrite ability operation calls → concrete expressions
        program, mono_decls = self._rewrite_ability_ops(program, mono_decls)

        # #1172: pre-pass for the tail-call discipline — collect the name
        # of every decreases-carrying function any ``return_call`` might
        # target, before Pass 2 compiles the first body.
        def _dec_collect(fdecl: ast.FnDecl, emit_name: str) -> None:
            if any(
                isinstance(c, ast.Decreases) and c.exprs
                for c in fdecl.contracts
            ) and not self._dec_declares_exn(fdecl):
                # The Exn exclusion mirrors `_compile_decreases_entry`'s
                # guard decline — the set must track functions that
                # actually RECEIVE a guard, or the tail-call patch and
                # the emitted entries desynchronize.
                self._dec_guarded_names.add(emit_name)
            for wfn in fdecl.where_fns or ():
                _dec_collect(wfn, wfn.name)

        for tld in program.declarations:
            if isinstance(tld.decl, ast.FnDecl):
                _dec_collect(tld.decl, tld.decl.name)
        for _path, idecl in self._imported_fn_decls:
            _dec_collect(idecl, idecl.name)
        for mdecl in mono_decls:
            _dec_collect(mdecl, mdecl.name)
        for _path, mangled, idecl in self._shadowed_module_fns:
            _dec_collect(idecl, mangled)

        # Pass 1.9: check for cross-module calls that codegen can't handle
        self._check_cross_module_calls(program)
        if any(d.severity == "error" for d in self.diagnostics):
            return CompileResult(
                wat="",
                wasm_bytes=b"",
                exports=[],
                diagnostics=self.diagnostics,
                state_types=list(self._state_types),
                md_ops_used=set(self._md_ops_used),
                regex_ops_used=set(self._regex_ops_used),
                map_ops_used=set(self._map_ops_used),
                set_ops_used=set(self._set_ops_used),
                decimal_ops_used=set(self._decimal_ops_used),
                json_ops_used=set(self._json_ops_used),
                html_ops_used=set(self._html_ops_used),
                http_ops_used=set(self._http_ops_used),
                async_ops_used=set(self._async_ops_used),
                inference_ops_used=set(self._inference_ops_used),
                db_ops_used=set(self._db_ops_used),
                random_ops_used=set(self._random_ops_used),
                math_ops_used=set(self._math_ops_used),
            )

        # Pass 2: compile function bodies
        functions_wat: list[str] = []
        exports: list[str] = []

        # Build visibility map for export gating
        fn_visibility: dict[str, str] = {}
        for tld in program.declarations:
            if isinstance(tld.decl, ast.FnDecl):
                fn_visibility[tld.decl.name] = tld.visibility or "private"

        # Generic bases with REGISTERED clones (Pass 1.5) — gates the dead
        # T-unused-template emission in the where-fn sweep below (PR #1013
        # review).  Registered, not compiled: the sweep runs before the mono
        # compile loop, and a clone that later fails to compile is a loud
        # diagnostic either way.  The base is the name minus the LAST
        # `$`-suffix (the single type-args vector `_mangle_fn_name` appends;
        # the vector itself can't contain `$` — type names can't lex it), so
        # an entry whose base is itself `$`-qualified (a shadowed module
        # clone `mod$path$gen$Int`, a per-clone hoisted helper
        # `gen$Int$where$h$…`) reduces to that qualified base, which can
        # never equal a bare helper name — a first-`$` split would collapse
        # them all to their first segment and could false-match a bare
        # helper coincidentally named `mod`/`gen` (Greptile PR #1013 review).
        mono_base_names = {m.name.rsplit("$", 1)[0] for m in mono_decls}

        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                is_public = tld.visibility == "public"
                # #1316: a PRELUDE-injected declaration sits in this list but
                # was written in the prelude's namespace, so its body compiles
                # against the prelude's aliases and data types — the same
                # scope its signature was registered in at Pass 1.2.  A
                # user declaration answers `None` and the scope is a no-op.
                with self._module_alias_scope(
                    self._declaration_namespace(decl.name),
                ):
                    fn_wat = self._compile_fn_tracked(
                        decl, export=is_public,
                        where_scope=frozenset(
                            w.name for w in decl.where_fns or ()
                        ),
                    )
                    if fn_wat is not None:
                        functions_wat.append(fn_wat)
                        if is_public:
                            exports.append(decl.name)
                        # Also compile where-block functions — recursively, so a
                        # helper's OWN where-helpers (grandchildren) are emitted
                        # too.  The checker, verifier, and registration paths all
                        # recurse into nested `where` blocks (`_check_fn` /
                        # `_verify_fn` / `_register_fn`), so a grandchild's name is
                        # registered and the parent's body lowers its call to
                        # `$grandchild` — but before #978 only the direct helpers
                        # were emitted, so a nested helper's body dangled
                        # (`unknown func` at WAT assembly).  The generic path
                        # already flattens nested helpers via
                        # `monomorphize._hoist_where_fns_under`.
                        # #1299: paired with the scope each helper's own body
                        # resolves in — its ancestors' direct helpers plus its
                        # own, which is what the checker walks.
                        for wfn, wscope in self._where_fn_scopes(decl):
                            wfn_wat = self._compile_fn_tracked(
                                wfn, export=False, where_scope=wscope,
                            )
                            if wfn_wat is not None:
                                # PR #1013 review: a fully-concrete (T-unused)
                                # generic helper TEMPLATE compiles — unlike a
                                # `@T`-param one — but is dead code once clones are
                                # registered (every call site rewrites to a clone
                                # via `_generic_fn_info`).  Emitting it dangles:
                                # its body's calls to its OWN where-helpers target
                                # per-clone symbols (`gen$Bool$where$shared`) that
                                # exist under no bare name (pre-#991 they resolved
                                # to a same-named ancestor's bare emission only by
                                # collision luck).  Drop the dead WAT; the compile
                                # attempt above keeps the `@T`-template warning
                                # surface intact, and an uninstantiated generic
                                # (no registered clones) still emits so a bare
                                # call has a target.
                                if (wfn.forall_vars
                                        and wfn.name in mono_base_names):
                                    continue
                                functions_wat.append(wfn_wat)

        # Compile monomorphized functions.
        #
        # Track base names whose mono bodies compiled successfully —
        # not merely registered in `_fn_sigs` (which happens earlier in
        # Pass 1.5 for every clone the monomorphizer generates,
        # including ones whose body later fails to compile).  This set
        # feeds the template-warning suppression below: we suppress
        # only when at least one mono clone actually emitted WAT,
        # preserving the diagnostic surface for genuinely-broken
        # generics whose clones all fail.
        compiled_mono_bases: set[str] = set()
        for mdecl in mono_decls:
            # #1014: strip ONE ``$<TypeArgs>`` suffix, keeping the full base —
            # a parent-qualified helper clone (``a$where$g$Int``) must gate its
            # visibility on ``a$where$g`` (absent from ``fn_visibility`` →
            # private), not on ``a`` (``split("$")[0]``), which would wrongly
            # export a private helper clone under its PUBLIC parent's
            # visibility.  Mangled type args never contain ``$``, so one
            # rsplit is exact.
            orig_name = mdecl.name.rsplit("$", 1)[0]
            is_public = fn_visibility.get(orig_name) == "public"
            # #998: a clone of an IMPORTED generic is the module's own code —
            # compile it against that module's span tables (or, absent tables,
            # the #986 suppressed lookups), exactly like Pass 2.5/2.6 bodies.
            # A local generic's clone has no recorded origin and keeps the
            # main-file tables its template spans live in.
            origin = self._mono_clone_origins.get(mdecl.name)
            # #1111: the clone's alias references resolve against its
            # defining module's namespace (no-op for a local clone).
            # #1189 (PR #1224 review): and its spans are that module's
            # coordinates, so the source scope is paired here exactly as at
            # the Pass-1.5 registration above and in Passes 2.5/2.6 — this
            # was the one emission door that entered the alias scope alone,
            # stamping the IMPORTER's path onto module-local line/column.
            # Beyond the misleading location (a line past the importer's EOF
            # renders an empty `source_line`), the E618 dedup keys on the
            # resolved location precisely because it carries the owning file,
            # so two modules declaring a nested refinement at coinciding
            # coordinates collapsed to ONE diagnostic.
            # #1243: and its bare sibling calls belong to that module's
            # namespace.  This was the one emission door that did not thread
            # the intra-rename map Passes 2.5/2.6 thread — so a clone of an
            # imported generic whose body calls one of ITS module's functions
            # by bare name landed on the IMPORTER's same-named function
            # instead: `glib`'s `gen` ran the importer's `need` (999 where
            # glib's returns 111), and on a type-discriminating pair
            # (`@Int` vs `@Bool`) emitted invalid WASM from check-green
            # source.  The map is empty for a local clone (no origin) and for
            # any module name the importer does not shadow, so nothing else
            # moves.
            with (
                self._module_alias_scope(
                    self._declaration_namespace(mdecl.name, origin)),
                self._module_source_scope(origin),
            ):
                fn_wat = self._compile_fn_tracked(
                    mdecl, export=is_public,
                    imported=origin is not None,
                    module_renames=(
                        self._module_intra_renames.get(origin, {})
                        if origin is not None else None
                    ),
                    module_tables=(
                        self._module_artifacts.get(origin)
                        if origin is not None else None
                    ),
                    # #1299: no `where_scope` — a clone reaching here has
                    # none to give.  `_hoist_clone_where_fns` strips
                    # `where_fns` off every clone and re-queues the helpers as
                    # standalone mono decls under clone-qualified names
                    # (`holder$Bool$where$get`), rewriting the clone's own
                    # calls with them, so the bare helper name is gone from
                    # the body before this loop sees it.  Pinned as an
                    # invariant rather than defended with a dead argument:
                    # test_lexical_fn_scope_1299 asserts no mono decl arrives
                    # carrying helpers, and goes red if that ever changes.
                )
            if fn_wat is not None:
                functions_wat.append(fn_wat)
                compiled_mono_bases.add(orig_name)
                if is_public:
                    exports.append(mdecl.name)

        # Pass 2.5: compile imported function bodies (C7e)
        imported_seen: set[str] = set()
        for path, idecl in self._imported_fn_decls:
            if idecl.name in imported_seen:
                continue
            # Skip if a local function already defined this name — a top-level
            # local (fn_visibility) OR a local `where`-fn helper
            # (_local_shadowed_fn_names).  Either flattens to a bare ``$name``
            # that owns the namespace; emitting the imported body under the
            # same bare name would duplicate it (the qualified target reaches
            # the module via its ``mod$…`` emission instead, #814).
            if (idecl.name in fn_visibility
                    or idecl.name in self._local_shadowed_fn_names):
                continue
            imported_seen.add(idecl.name)
            # #814 C2 (Pass 2.5 mirror): pass the originating module's
            # intra-rename map so a bare sibling call inside this imported
            # body resolves to the module's version (its `mod$…` emission)
            # rather than a local shadow of that name.
            # #1111: resolve type aliases against THIS module's own
            # namespace (spec §8.4.1: aliases are module-local) — the flat
            # maps hold only the main file's + prelude's aliases.
            # #1186: and locate any skip diagnostic in the module's OWN
            # file — this body's spans are module-local coordinates.
            with self._module_alias_scope(path), self._module_source_scope(path):
                fn_wat = self._compile_fn_tracked(
                    idecl, export=False,
                    module_renames=self._module_intra_renames.get(path, {}),
                    imported=True,  # #986: don't consult main-file span tables
                    # #987: thread THIS module's own span-keyed tables so the
                    # imported body's @Nat -> @Int widening guard fires.
                    module_tables=self._module_artifacts.get(path),
                    # #1299: no `where_scope`.  This body resolves bare names
                    # in ITS module's namespace, which the alias scope above
                    # already selects, and it brings no bare helper name of
                    # its own: `_register_modules` runs the #991 hoist and the
                    # #1014 qualification over every module AST, so an
                    # imported declaration arriving here carries only
                    # `$`-qualified helpers — admitted unconditionally.  The
                    # door invariant in test_lexical_fn_scope_1299 holds every
                    # emission site to that, and goes red if one stops.
                )
            if fn_wat is not None:
                functions_wat.append(fn_wat)

        # Pass 2.6: emit shadowed module functions under their qualified
        # ('mod$…') WASM name (#814 §8.5.3).  The plain Pass 2.5 above skips
        # any imported fn whose bare name a local redefines (so bare calls
        # resolve to the local, §8.5.2); here we additionally emit the
        # module's body under a distinct name so a module-qualified call
        # ``m::f`` reaches it.  ``dataclasses.replace`` only renames the WASM
        # function; the body's intra-module calls are redirected to their own
        # ``mod$`` targets via ``module_renames`` (C2) so a sibling call
        # inside the body also lands on the module's version, not a local
        # shadow.
        for path, mangled, idecl in self._shadowed_module_fns:
            if mangled in imported_seen:
                continue
            imported_seen.add(mangled)
            # #1111: same per-module alias namespace as Pass 2.5 — the
            # ``mod$…`` rename does not change which module's aliases
            # the body's type expressions belong to.
            # #1186: likewise the ``mod$…`` rename does not move the body's
            # spans, so its diagnostics still belong to the module's file.
            with self._module_alias_scope(path), self._module_source_scope(path):
                fn_wat = self._compile_fn_tracked(
                    dataclasses.replace(idecl, name=mangled),
                    export=False,
                    module_renames=self._module_intra_renames.get(path, {}),
                    imported=True,  # #986: don't consult main-file span tables
                    # #987: the ``mod$…`` rename only changes the WASM
                    # function name; the body's node spans are unchanged, so
                    # THIS module's table still keys them correctly and its
                    # widen guard fires.
                    module_tables=self._module_artifacts.get(path),
                    # #1299: the ``mod$…`` rename moves the body into no other
                    # namespace, and adds no helper — same reasoning, and the
                    # same door invariant, as the Pass-2.5 emission above.
                )
            if fn_wat is not None:
                functions_wat.append(fn_wat)

        # #851 — all function compilation is done; any diagnostic
        # emitted from here on is module-level, not prelude-origin.
        self._in_prelude_fn = False

        # #604 / #655 — suppress spurious template-only warnings.
        #
        # Generic ``forall<T>`` function templates can NEVER be compiled
        # directly (their type vars have no monomorphic WASM
        # representation).  Each call site produces a monomorphized
        # clone that compiles fine in the normal flow.  Emitting
        # `[E604]` / `[E602]` / `[E605]` on the *template* is pure noise
        # in that case — the function works end-to-end via mono, but
        # the user sees a confusing warning about a function that's
        # actually fine.
        #
        # Targeted suppression: drop every E602/E604/E605 diagnostic
        # whose source is a forall-decl IF at least one mono clone of
        # that decl successfully *compiled* (`_compile_fn` returned
        # non-None, recorded in `compiled_mono_bases` above).  CR-3
        # on PR #659: pre-fix this checked `_fn_sigs`, which is
        # populated in Pass 1.5 *before* mono bodies are compiled —
        # so a broken-but-registered clone would have wrongly
        # suppressed its template's diagnostic, hiding the only
        # pre-runtime signal of a broken generic.  Now we track
        # actually-compiled clones explicitly.
        #
        # If no mono clone compiled, the warning stays — that signals
        # either a genuinely-broken generic or an unused declaration
        # the user wanted to compile but couldn't.
        #
        # This is audit recommendation 2 from the #604 investigation
        # comment.  Pre-fix, the warnings were the only signal that
        # `option_map$Int_JBool`-shape mono-suffix bugs existed;
        # post-fix (the mono-suffix bug in monomorphize.py is closed),
        # they're pure noise for the catalogued cases.
        # Why bare-name (vs `(module, name)`) keying is safe here —
        # `#661`:
        #   * `forall_decl_names` is built from the current
        #     `program.declarations` only, NOT from cross-module
        #     imports.  Imported FnDecls flow through Pass 2.5 above
        #     (lines 519-530), which explicitly skips names already
        #     in `fn_visibility` — so an imported forall decl with
        #     the same name as a local one is dropped before its
        #     template warning could be emitted.
        #   * `compiled_mono_bases` is keyed on the mangler's
        #     `<base>$<types>` split — colliding bases across
        #     modules would resolve to the same mono clone.  (#998
        #     added module attribution for span-TABLE selection —
        #     `_mono_clone_origins` — but clone NAMING/resolution is
        #     still bare-name, the latent gap tracked in `#661`.)
        # Net effect: at most one template warning per base name
        # ever lands in `self.diagnostics`, so a bare-name match in
        # the suppression filter cannot cross-suppress between
        # modules.  If Pass 2.5's dedup is ever loosened, or the
        # mono pipeline starts carrying module attribution, this
        # comment is the trigger to re-key the set on
        # `(module, name)`.
        # `tests/test_codegen_modules.py::TestCrossModuleNameCollision661`
        # pins this invariant — the test compiles a cross-module
        # name-shadowing fixture and asserts there's no over-broad
        # suppression.
        forall_decl_names: set[str] = set()
        # #913: name → span of each forall template, so a CLOSURE-level skip
        # warning (whose description is NOT `Function 'NAME' …`-prefixed —
        # it names the closure, not the enclosing fn) can be matched by
        # error_code + forall-origin (the warning's source line falls within
        # the template's declaration span).  Keeps the suppression robust
        # against description wording rather than re-parsing a name out of it.
        forall_decl_spans: dict[str, ast.Span] = {}
        for tld in program.declarations:
            decl = tld.decl
            if not isinstance(decl, ast.FnDecl):
                continue
            if decl.forall_vars:
                forall_decl_names.add(decl.name)
                if decl.span is not None:
                    forall_decl_spans[decl.name] = decl.span
            else:
                # #990: a nested generic where-helper is a mono base too — its
                # template goes through `_compile_fn` in the Pass-2 where-fn
                # sweep and warns exactly like a top-level template, so it
                # joins the same clone-compiled suppression set.
                for wfn in self._flatten_where_fns(decl):
                    if wfn.forall_vars:
                        forall_decl_names.add(wfn.name)
                        if wfn.span is not None:
                            forall_decl_spans[wfn.name] = wfn.span
        if forall_decl_names:
            mono_compiled = compiled_mono_bases & forall_decl_names
            if mono_compiled:
                # Filter out template warnings for fns whose mono
                # clones compiled.  Keep all other diagnostics intact.
                # Two match shapes, both gated on a clone having compiled
                # (so a genuinely-broken generic with NO compilable clone
                # keeps its warning):
                #   1. Description prefix `Function 'NAME' ` — the
                #      function-level [E604]/[E605] (`_is_compilable`,
                #      `vera/codegen/compilability.py`) and the [E602]
                #      dropped-parent warning (`vera/codegen/functions.py`,
                #      reached via `_compile_fn`).
                #   2. #913: a closure-level [E602] emitted while compiling
                #      the template body (`vera/codegen/closures.py`) whose
                #      unsubstituted `@T` param/return type has no WASM
                #      representation.  Its description names the closure, so
                #      the prefix match misses it; suppress it by forall-origin
                #      — its source line sits inside a compiled-clone
                #      template's declaration span.
                suppressible_codes = {"E602", "E604", "E605"}
                kept: list[Diagnostic] = []
                for d in self.diagnostics:
                    if d.error_code in suppressible_codes:
                        suppressed = any(
                            d.description.startswith(f"Function '{name}' ")
                            for name in mono_compiled
                        )
                        if not suppressed and d.error_code == "E602":
                            line = d.location.line
                            suppressed = any(
                                (span := forall_decl_spans.get(name)) is not None
                                and span.line <= line <= span.end_line
                                for name in mono_compiled
                            )
                        if suppressed:
                            continue
                    kept.append(d)
                self.diagnostics = kept

        # #851 — suppress skip-warnings for prelude-injected functions
        # the program never references.
        #
        # The generic Option/Result combinators the prelude injects
        # (`option_unwrap_or`, `option_map`, …) can never compile as
        # templates (forall params / nested binding patterns), so Pass
        # 2 warned and skipped them on EVERY compile — five warnings of
        # pure noise about code the user didn't write and doesn't call.
        # A skip-warning for prelude code is only an honest signal when
        # the program actually references the skipped function; then it
        # survives (attributed to `<prelude>` via `_diag_location`) as
        # the pre-runtime explanation for why the call can't be served.
        #
        # "Referenced" is a transitive call-target scan rooted at every
        # non-prelude declaration (user decls incl. generics the mono
        # collector never visits, plus imported module fns) — see
        # `_referenced_prelude_fns`.  It over-approximates reachability
        # (a call inside dead user code still counts), which is the
        # safe direction: a false "referenced" keeps a warning, never
        # hides one.  User-origin unsupported functions are untouched —
        # only names in `_prelude_fn_names` (which excludes user-
        # shadowed combinators, skipped at injection) are eligible.
        #
        # This filter runs AFTER the #604 mono-compiled suppression
        # above: that pass drops template warnings for combinators the
        # program calls *successfully*; this one drops the rest of the
        # prelude set the program never mentions.  Between them, a
        # program that calls `option_map` end-to-end compiles with zero
        # warnings, and one that references it without a compilable
        # instantiation keeps exactly the option_map warning.
        if self._prelude_fn_names:
            referenced = self._referenced_prelude_fns(program)
            unreferenced = self._prelude_fn_names - referenced
            if unreferenced:
                suppressible_codes = {"E602", "E604", "E605"}
                self.diagnostics = [
                    d for d in self.diagnostics
                    if not (
                        d.severity == "warning"
                        and d.error_code in suppressible_codes
                        and any(
                            d.description.startswith(f"Function '{name}' ")
                            for name in unreferenced
                        )
                    )
                ]

        # #1100: drop the (transitive) callers of every skipped function
        # so no `call $skipped` survives into module assembly.  Runs after
        # the template/prelude warning-suppression passes above (E620
        # warnings name compiled non-template callers, so those filters
        # must not see them) and before the export-driven alloc scan
        # below (a dropped export must not force the allocator in).
        functions_wat = self._drop_dangling_callers(functions_wat, exports)

        # If any exported function takes String/Array (i32_pair) params, ensure
        # the heap allocator is compiled in so CLI callers can allocate args.
        for export_name in exports:
            sig = self._fn_sigs.get(export_name)
            if sig and any(t == "i32_pair" for t in sig[0] if t is not None):
                self._needs_alloc = True
                self._needs_memory = True
                break

        # Assemble the module
        wat = self._assemble_module(functions_wat)

        # Convert WAT to WASM binary
        try:
            wasm_bytes = wasmtime.wat2wasm(wat)
        except Exception as exc:  # noqa: BLE001 — a backend failure becomes a codegen diagnostic
            self.diagnostics.append(Diagnostic(  # diag-fields-exempt: internal wat2wasm backend failure; a code-generation bug, not a user error, so no source-level fix or spec section applies.
                description=f"WAT compilation failed: {exc}",
                location=SourceLocation(file=self.file),
                severity="error",
            ))
            return CompileResult(
                wat=wat,
                wasm_bytes=b"",
                exports=exports,
                diagnostics=self.diagnostics,
                state_types=list(self._state_types),
                md_ops_used=set(self._md_ops_used),
                regex_ops_used=set(self._regex_ops_used),
                map_ops_used=set(self._map_ops_used),
                set_ops_used=set(self._set_ops_used),
                decimal_ops_used=set(self._decimal_ops_used),
                json_ops_used=set(self._json_ops_used),
                html_ops_used=set(self._html_ops_used),
                http_ops_used=set(self._http_ops_used),
                async_ops_used=set(self._async_ops_used),
                inference_ops_used=set(self._inference_ops_used),
                db_ops_used=set(self._db_ops_used),
                random_ops_used=set(self._random_ops_used),
                math_ops_used=set(self._math_ops_used),
            )

        fn_param_types = {
            name: [t for t in params if t is not None]
            for name, (params, _) in self._fn_sigs.items()
        }
        # Collect functions whose Vera return type resolves to `String`
        # so `execute()` can decode their (ptr, len) pair back into a
        # str.  Walks the AST rather than using `_fn_sigs` because
        # `_fn_sigs` carries the WAT type ("i32_pair") which conflates
        # String and Array<T>.  Alias-resolved via `_resolve_named_type`
        # so `type Name = String` participates.
        fn_string_returns: set[str] = set()
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                if self._return_type_is_string(decl.return_type):
                    fn_string_returns.add(decl.name)
        dropped_fns = self._user_dropped_fns(program, exports)
        return CompileResult(
            wat=wat,
            wasm_bytes=bytes(wasm_bytes),
            exports=exports,
            diagnostics=self.diagnostics,
            state_types=list(self._state_types),
            md_ops_used=set(self._md_ops_used),
            regex_ops_used=set(self._regex_ops_used),
            map_ops_used=set(self._map_ops_used),
            set_ops_used=set(self._set_ops_used),
            decimal_ops_used=set(self._decimal_ops_used),
            json_ops_used=set(self._json_ops_used),
            html_ops_used=set(self._html_ops_used),
            http_ops_used=set(self._http_ops_used),
            async_ops_used=set(self._async_ops_used),
            inference_ops_used=set(self._inference_ops_used),
            db_ops_used=set(self._db_ops_used),
            random_ops_used=set(self._random_ops_used),
            math_ops_used=set(self._math_ops_used),
            fn_param_types=fn_param_types,
            fn_string_returns=fn_string_returns,
            adt_layouts={
                name: dict(ctors)
                for name, ctors in self._adt_layouts.items()
            },
            fn_source_map=dict(self._fn_source_map),
            prelude_fn_names=set(self._prelude_fn_names),
            dropped_fns=dropped_fns,
        )

    def _user_dropped_fns(
        self, program: ast.Program, exports: list[str],
    ) -> dict[str, Diagnostic | None]:
        """USER-declared top-level functions absent from the module (#1183).

        ``_dropped_fn_diags`` is the raw codegen bookkeeping: it also holds
        prelude injections and ``forall`` templates, both of which are
        routinely "dropped" on a perfectly healthy compile (an
        uninstantiated template has no monomorphic body; an unreferenced
        prelude combinator is never emitted).  Neither is something a user
        can request as an entry point, and the diagnostics explaining them
        are deliberately suppressed downstream — so surfacing them would
        turn a normal compile into a wall of phantom "dropped" entries.

        The published set is therefore narrowed to names the user wrote in
        THIS program, that did not make it into *exports*, and whose
        explaining diagnostic actually survived suppression (identity, not
        equality — two skips can share a description).  ``forall``
        templates are excluded on the same grounds as the prelude: a
        template has no monomorphic body by construction, so its absence
        from the module is structural, not a failure — a cross-module
        generic library legitimately exports nothing at all.
        """
        surviving = {id(d) for d in self.diagnostics}
        exported = set(exports)
        dropped: dict[str, Diagnostic | None] = {}
        for tld in program.declarations:
            decl = tld.decl
            if not isinstance(decl, ast.FnDecl):
                continue
            name = decl.name
            if decl.forall_vars:
                continue
            if name in exported or name in self._prelude_fn_names:
                continue
            if name not in self._dropped_fn_diags:
                continue
            diag = self._dropped_fn_diags[name]
            if diag is not None and id(diag) not in surviving:
                continue
            dropped[name] = diag
        return dropped

    # -----------------------------------------------------------------
    # Type helpers (used by most mixins)
    # -----------------------------------------------------------------

    def _return_type_is_string(self, te: ast.TypeExpr) -> bool:
        """True iff the Vera return type resolves to ``String`` (post-alias).

        Used to populate ``CompileResult.fn_string_returns`` so
        ``execute()`` knows to decode the (ptr, len) pair into a Python
        ``str`` for display.  Distinguishes ``String`` from ``Array<T>``
        — both share the i32_pair WAT shape but only ``String`` has
        UTF-8 bytes at memory[ptr:ptr+len].

        The BRANCH ORDER is the checker's, for the same reason
        ``_type_expr_to_wasm_type``'s is (#1309, and this is the THIRD
        consumer of that disease), and it is taken by the same spine,
        :func:`vera.naming.classify_named`: ``String`` is a
        ``vera.types.PRIMITIVES`` member and so precedes the alias table,
        while ``Future`` is an ADT name and so must follow it — and follow
        the DECLARED-ADT branch too, since a user ``data Future`` is that
        namespace's own type and carries no transparent payload (#1321).
        Tested the other way round, ``type Future<T> = Array<T>;`` made a
        ``@Future<String>`` return take the transparent-wrapper strip and be
        classified a string, while the width derivation resolved the alias
        and lowered an ``Array<String>`` — so ``vera run`` decoded the
        array's backing bytes as UTF-8 and printed two NULs where the same
        program under a non-ADT alias name printed the pointer.
        """
        if isinstance(te, ast.NamedType):
            sort = naming.classify_named(te, self._alias_env)
            if sort is naming.NameSort.PRIMITIVE:
                return te.name == "String"
            if sort in (
                naming.NameSort.ALIAS,
                naming.NameSort.ALIAS_ARITY_MISMATCH,
            ):
                # Substitute a parameterised alias's own type params with the
                # concrete `te.type_args` BEFORE recursing (the same
                # `naming.alias_body` `_type_expr_to_wasm_type` uses), so
                # `type Deferred<T> = Future<T>` used as `Deferred<String>`
                # resolves to String instead of recursing on the bare `T` and
                # displaying the raw pointer (PR #1041 review).
                return self._return_type_is_string(
                    naming.alias_body(te, self._alias_env))
            if sort is naming.NameSort.DECLARED_ADT:
                return False
            # Future<T> is representation-transparent (#841 / #1047): a bare
            # `Future<String>` return has the same (ptr, len) pair shape as a
            # plain String, so `execute()` must decode it for display too.
            # Without this strip `mk() -> Future<String>` was absent from
            # `fn_string_returns` and `vera run --fn mk` printed the raw
            # pointer instead of the string (the emitted WASM is sound — a
            # caller that awaits gets the value; only top-level display broke).
            if (te.name == "Future" and te.type_args
                    and len(te.type_args) == 1):
                return self._return_type_is_string(te.type_args[0])
        if isinstance(te, ast.RefinementType):
            return self._return_type_is_string(te.base_type)
        return False

    def _type_expr_to_wasm_type(self, te: ast.TypeExpr) -> str | None:
        """Map a Vera TypeExpr to a WAT type string.

        Returns None for Unit, "unsupported" for non-compilable types,
        "i32_pair" for types represented as (i32, i32) pairs (String, Array).

        The BRANCH ORDER is the checker's, not a convenience ordering
        (#1309, #1321, #1331), and it is not restated here: the branch is
        taken by :func:`vera.naming.classify_named`, THE spine, against
        ``_alias_env`` — the aliases and declared ADTs of the namespace whose
        declaration is compiling (``_sync_alias_env`` / ``_module_alias_scope``,
        #1316).  A width derived in any other order — or against any other
        namespace's tables — disagrees with the type the program was checked
        and verified against.  This function has no type-parameter step of its
        own; monomorphization substitutes concrete arguments before it runs.

        What is left here is the REPRESENTATION question the spine
        deliberately does not answer: given that the name is not declared in
        this namespace, which built-in does it denote and how wide is it.
        Spec §8.4.1 permits both a `type` alias and a `data` declaration to
        take a name the prelude or a built-in container already uses, and both
        shadows win over the built-in reading:

        * ``type Option = Int;`` must emit the alias target's i64.  Codegen
          used to test ``_adt_layouts`` (and ``Array`` / ``Map`` / ``Set`` /
          ``Decimal``, none of which are ``vera.types.PRIMITIVES``) first and
          emitted the ADT pointer's i32 instead — loud where the widths
          differ and the target is a scalar (WASM validation: ``expected i64,
          found i32``) and SILENT where the target is a pair, the single i32
          dropping the length word so ``string_concat`` over a shadow-aliased
          ``String`` returned junk bytes at exit 0 (#1309).
        * ``data Array { Mk(Int) }`` must emit the ADT pointer's i32.  The
          container branch used to run first and answer ``i32_pair``, so the
          match over it was refused as a pair scrutinee, its callers dropped,
          and the module shipped with no exports at all (#1321, #1331).

        Only the PRIMITIVES stay ahead of both shadows, because that is where
        the checker puts them: ``type Bool = Int;`` leaves ``@Bool`` a Bool on
        both sides.  ``Never`` is the one primitive with no representation —
        no value of it exists — so it is ``"unsupported"`` rather than a width.
        """
        if isinstance(te, ast.NamedType):
            name = te.name
            sort = naming.classify_named(te, self._alias_env)
            if sort is naming.NameSort.PRIMITIVE:
                # GUARDED, not a direct index (PR #1372 review).  The spine
                # answers PRIMITIVE for every bare key of
                # ``vera.types.PRIMITIVES``, and this table is a separate
                # statement of each one's WAT width — so a primitive added
                # there and not here would raise ``KeyError`` from inside
                # codegen, an internal crash where the compiler owes a
                # diagnostic.  Falling through to ``"unsupported"`` routes it
                # to the existing E605 refusal instead, which is the LOUD
                # answer, not a silent default: an unsupported type is refused
                # with a located diagnostic, never compiled at a guessed
                # width.  ``tests/test_name_resolution_spine_1316.py`` pins
                # the table's keys against the registry so the gap cannot be
                # introduced unnoticed in the first place.
                return _PRIMITIVE_WASM_TYPES.get(name, "unsupported")
            if sort in (
                naming.NameSort.ALIAS,
                naming.NameSort.ALIAS_ARITY_MISMATCH,
            ):
                # Recurse into the alias's body with this application's
                # arguments substituted for the alias's own parameters, so a
                # parameterised alias (`type Box<T> = Array<T>`) does not leak
                # a bare `T` into the width question and get classified
                # "unsupported" (#635).  An arity mismatch takes the same arm
                # deliberately: the checker rejects it (E133) before any
                # program reaches codegen, and `alias_body` then declines to
                # substitute, which is exactly what this walker did before the
                # spine existed.
                return self._type_expr_to_wasm_type(
                    naming.alias_body(te, self._alias_env))
            if sort is naming.NameSort.DECLARED_ADT:
                return "i32"  # heap pointer
            if name == "Array":
                return "i32_pair"
            if name in ("Map", "Set", "Decimal"):
                return "i32"  # opaque host handle
            # Future<T> is transparent — same representation as T
            # (#841: a fused Future<Result<String, String>> is a
            # wrapper pointer, which is repr-compatible with the
            # Result pointer; value-typed futures are their value).
            # Pre-#841 there was no case here, so a function
            # *returning* a Future was E605-skipped.
            if name == "Future" and te.type_args and len(te.type_args) == 1:
                return self._type_expr_to_wasm_type(te.type_args[0])
            return "unsupported"
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_wasm_type(te.base_type)
        # Function types compile to i32 (closure pointer)
        if isinstance(te, ast.FnType):
            return "i32"
        return "unsupported"

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str | None:
        """The slot-binding name of *te*, as the checker binds it (#1208).

        Delegates to :func:`vera.naming.slot_name` against ``_alias_env`` —
        the aliases of the module whose declaration is compiling, kept
        current by ``_sync_alias_env`` / ``_module_alias_scope``.  Syntactic
        head, RESOLVED type arguments: a parameter written ``@Option<Cnt>``
        keys the ``Option<Int>`` stack the checker created, which is the
        stack the reference side (``naming.slot_ref_key``) looks up.  Nested
        composite arguments stay fully qualified (#914 finding 2).
        """
        return naming.slot_name_or_none(te, self._alias_env)

    def _hoist_nongeneric_where_helpers(
        self, program: ast.Program,
    ) -> ast.Program:
        """Hoist every NON-generic ``where``-helper to a parent-qualified
        top-level decl (#991), so same-named helpers in different parent trees
        (or a helper named like a top-level function) never collide in the flat
        WAT namespace.

        This is the non-generic mirror of the generic path's
        ``_hoist_clone_where_fns`` (#904): a helper ``leaf`` under ``branchA``
        becomes ``compute$where$branchA$where$leaf`` and every lexically-visible
        bare call to it — in the parent's body and in any nested helper body that
        can see it — is redirected to the mangled name.  ``$`` cannot appear in a
        source identifier and ``where`` is reserved, so the mangled name collides
        with neither a user function nor a generic clone (``gid$Int``) nor a
        generic helper's per-clone hoist (``gid$Int$where$…``).

        The DESIGN call is mangling, not a checker rejection: spec §5
        (``spec/05-functions.md``) makes where-helpers "always local to the
        parent function", so two same-named helpers under different parents are a
        semantically VALID program — the collision was codegen's flat namespace
        leaking, not a user error — and mangling gives one canonical treatment of
        helper symbols across the generic and non-generic paths (DESIGN
        principle 3).

        GENERIC helpers are left structurally nested: each is a monomorphization
        base whose clones (and their own where-helpers) are emitted and hoisted
        per-instantiation by the mono path, exactly as ``_flatten_where_fns``
        and ``collect_nested_generic_decls`` stop at a generic node.  Their
        BODIES are rewritten, though — shadow-aware
        (``_rewrite_generic_subtree_shadowed``): an ancestor-helper call inside
        one is redirected to the hoisted name, while a name the generic subtree
        re-defines stays bare for the mono path's per-clone redirect (PR #1013
        review).  The hoisted non-generic decls become ordinary top-level
        declarations, so registration, monomorphization discovery, and Pass-2
        emission all handle them uniformly with no special-casing.
        """
        new_tlds: list[ast.TopLevelDecl] = []
        for tld in program.declarations:
            decl = tld.decl
            # Skip GENERIC top-level functions entirely: their where-helpers
            # (non-generic or otherwise) are carried into each clone and hoisted
            # per-instantiation by `_hoist_clone_where_fns` under the
            # clone-qualified prefix (`outer$Int$where$helper`, #904).  Hoisting
            # them here would strip them from the template and dangle the clone's
            # call.
            if (isinstance(decl, ast.FnDecl)
                    and decl.where_fns
                    and not decl.forall_vars):
                hoisted: list[ast.FnDecl] = []
                rewritten = self._hoist_nongeneric_where_fns_under(
                    decl, decl.name, hoisted, {},
                )
                new_tlds.append(dataclasses.replace(tld, decl=rewritten))
                # Hoisted helpers are always private: they are internal to the
                # parent and must never be exported (their bare source name is
                # gone, and only top-level names back exports / `execute` lookup).
                for h in hoisted:
                    new_tlds.append(
                        dataclasses.replace(tld, visibility="private", decl=h)
                    )
            else:
                new_tlds.append(tld)
        return dataclasses.replace(program, declarations=tuple(new_tlds))

    def _hoist_nongeneric_where_fns_under(
        self,
        fn: ast.FnDecl,
        prefix: str,
        hoisted: list[ast.FnDecl],
        scope: dict[str, str],
    ) -> ast.FnDecl:
        """Hoist ``fn``'s NON-generic ``where``-helpers under ``prefix``,
        recursively; return ``fn`` with those helpers stripped and every bare
        call to a lexically-visible helper (in ``fn``'s body and in its retained
        generic helpers' bodies) redirected to the mangled name.

        *scope* is the ``{helper name: mangled name}`` map of every non-generic
        helper visible from ENCLOSING ``where`` scopes (ancestors), so full
        lexical resolution holds: a helper's body resolves a bare call to the
        NEAREST same-named helper in the enclosing tree — its own children first
        (this level), then any ancestor's (a grandchild calling an "aunt" — a
        sibling of its parent — is redirected too), and an inner helper shadows
        an outer same-named one for its subtree.  A name absent from the combined
        scope is a top-level / generic / builtin call and stays bare.  Generic
        helpers are retained structurally nested for the mono path, but their
        bodies ARE rewritten — shadow-aware, via
        ``_rewrite_generic_subtree_shadowed`` — so an ancestor-helper call
        inside one reaches the hoisted name while a name the subtree re-defines
        stays bare for the per-clone redirect.  A generic helper's NAME also
        shadows a same-named ancestor entry for its level's whole subtree (the
        call must route through ``_resolve_generic_call`` to its clone,
        `gid$Int`, not be captured by the ancestor's hoisted helper).
        """
        where_fns = fn.where_fns or ()
        # This level's non-generic helpers map to their mangled names; this
        # level's GENERIC helper names ERASE any same-named ancestor entry —
        # both directions of "inner shadows outer" (PR #1013 review: a shadow
        # map built from non-generic names only captured a call to a nested
        # generic onto the ancestor's hoisted helper — at base a loud
        # duplicate-identifier crash, silently the wrong body here).
        this_level = {
            wfn.name: f"{prefix}$where${wfn.name}"
            for wfn in where_fns
            if not wfn.forall_vars
        }
        generic_names = {wfn.name for wfn in where_fns if wfn.forall_vars}
        combined = {
            k: v for k, v in scope.items() if k not in generic_names
        }
        combined.update(this_level)
        kept_generic: list[ast.FnDecl] = []
        for wfn in where_fns:
            if wfn.forall_vars:
                kept_generic.append(wfn)
                continue
            # The child body sees `combined` (this level + all ancestors); its
            # own nested helpers extend that scope inside the recursion.
            child = self._hoist_nongeneric_where_fns_under(
                wfn, this_level[wfn.name], hoisted, combined,
            )
            hoisted.append(
                dataclasses.replace(child, name=this_level[wfn.name])
            )
        # Rewrite the parent's OWN body/contracts with the full scope, then
        # descend into each retained generic subtree shadow-aware.  A blunt
        # whole-decl rewrite (body + retained generics in one walk) captured a
        # generic helper's call to its OWN nested helper onto the ancestor's
        # mangled name — mono clones the generic with the call already
        # rewritten, so `_hoist_clone_where_fns`'s per-clone redirect never
        # fires: silent wrong body, and a false Tier-1 when contracted (the
        # verifier's scoped lookup resolves the call correctly while the
        # compiled program runs the ancestor's helper) — PR #1013 review.
        body_only = dataclasses.replace(fn, where_fns=None)
        rewritten = self._rewrite_call_names(body_only, combined)
        assert isinstance(rewritten, ast.FnDecl)  # noqa: S101
        new_generic = tuple(
            self._rewrite_generic_subtree_shadowed(gfn, combined)
            for gfn in kept_generic
        )
        return dataclasses.replace(
            rewritten, where_fns=new_generic or None,
        )

    def _rewrite_generic_subtree_shadowed(
        self, fn: ast.FnDecl, rename: dict[str, str],
    ) -> ast.FnDecl:
        """Redirect ancestor-helper calls inside a RETAINED generic subtree,
        honouring the subtree's own shadowing (PR #1013 review).

        A generic helper stays structurally nested for the mono path, but its
        body may legitimately call an ancestor's (now hoisted) non-generic
        helper — that call must be redirected to the mangled name.  A name the
        subtree RE-DEFINES at any level, however, is resolved per-clone by
        ``_hoist_clone_where_fns``, so its ancestor entry must be dropped for
        that level's body and everything below it; rewriting it here would bind
        the call to the ancestor's helper and the per-clone redirect (keyed on
        the bare name) would never fire.
        """
        level_names = {wfn.name for wfn in fn.where_fns or ()}
        visible = {k: v for k, v in rename.items() if k not in level_names}
        body_only = dataclasses.replace(fn, where_fns=None)
        rewritten = self._rewrite_call_names(body_only, visible)
        assert isinstance(rewritten, ast.FnDecl)  # noqa: S101
        new_where = tuple(
            self._rewrite_generic_subtree_shadowed(wfn, visible)
            for wfn in fn.where_fns or ()
        )
        return dataclasses.replace(
            rewritten, where_fns=new_where or None,
        )

    def _scoped_fn_names(
        self, where_scope: frozenset[str], own_name: str,
    ) -> set[str]:
        """The registered names a bare call in this body may DENOTE (#1299).

        ``_fn_sigs`` narrowed to the compiling declaration's lexical scope:
        its namespace's own declarations, visible imports and the prelude
        (:meth:`_collect_namespace_fn_names`, selected by the module scope
        ``_module_alias_scope`` currently has installed), the ``where``
        helpers in scope, and the declaration itself for recursion.
        This is what codegen hands
        :func:`~vera.slots.bare_call_denotes_user_fn`; the flat registry
        stays behind ``_known_fns`` for the guard rail, which asks a
        different question ("is there a symbol here?") that IS flat.

        A strict SUBSET of ``_fn_sigs`` by construction — the comprehension
        iterates the registry — so this can only ever withdraw a name the
        pre-#1299 table wrongly claimed, never introduce one with no
        signature behind it.  ``tests/test_lexical_fn_scope_1299.py`` pins
        that as a property rather than leaving it to the reading.

        Every ``$``-bearing key is admitted unconditionally.  ``$`` cannot
        occur in a Vera identifier (``LOWER_IDENT``), so a mangled name is
        never what a bare source call spells; what admitting it DOES is keep
        a mono clone (``pick$Int``), a rerouted module body (``mod$lib$f``),
        and a hoisted helper (``outer$where$h``) answering "user-owned" at
        the sites that see a call name the rewrite already resolved.

        This implements the SPEC's rule — §7.4 resolves a bare operation only
        for a name no declaration in the call site's scope occupies, and §5
        makes a ``where`` helper local to its parent — rather than reproducing
        what the checker currently computes.  The two coincide everywhere
        except one shape: ``register_fn`` recurses helpers into the flat
        ``TypeEnv``, so the checker also resolves a bare call in a SIBLING
        top-level function to another function's helper, which this set does
        not (#1307).  Where that shape's helper is named after an operation
        the two now disagree in the checker's direction, and closing it is a
        checker change with its own new rejections.
        """
        lexical = set(
            self._namespace_fn_names.get(self._active_module_path, ())
        )
        lexical |= where_scope
        lexical.add(own_name)
        return {
            name for name in self._fn_sigs
            if "$" in name or name in lexical
        }

    @staticmethod
    def _where_fn_scopes(
        decl: ast.FnDecl,
    ) -> list[tuple[ast.FnDecl, frozenset[str]]]:
        """:meth:`_flatten_where_fns`, each helper paired with ITS scope.

        The scope of a helper is the direct ``where`` names of every
        enclosing function up to and including itself — spec §5's helper
        locality, which the checker's ``_lookup_function_scoped`` frame-stack
        walk also implements, so a grandchild helper is NOT in its
        grandparent's scope and a sibling is.  ("Also", not "exactly": the
        checker's env fallback additionally reaches helpers from OUTSIDE the
        frame stack entirely, which is #1307 and not this walk's rule.)

        Same traversal, same skip, same order as :meth:`_flatten_where_fns`;
        the two are asserted to enumerate identically rather than kept in
        step by inspection, because a helper this one missed would compile
        against the wrong scope silently.
        """
        out: list[tuple[ast.FnDecl, frozenset[str]]] = []
        seen: set[int] = set()
        here = frozenset(w.name for w in decl.where_fns or ())
        stack: list[tuple[ast.FnDecl, frozenset[str]]] = [
            (w, here) for w in reversed(decl.where_fns or ())
        ]
        while stack:
            wfn, inherited = stack.pop()
            if id(wfn) in seen:
                continue
            seen.add(id(wfn))
            scope = inherited | {w.name for w in wfn.where_fns or ()}
            out.append((wfn, scope))
            if not wfn.forall_vars:
                stack.extend(
                    (w, scope) for w in reversed(wfn.where_fns or ())
                )
        return out

    @staticmethod
    def _flatten_where_fns(decl: ast.FnDecl) -> list[ast.FnDecl]:
        """Every ``where``-helper reachable from *decl*, at any depth (#978),
        except the subtree of a generic helper (carried per-clone by the mono
        path instead, #990).

        Pre-order, depth-first, so a helper precedes its own nested helpers.
        WAT function order is irrelevant to assembly, but a stable order keeps
        emitted output deterministic.  An ``id``-keyed visited guard makes the
        walk total against a pathological (shared-node) AST shape — a plain
        ``where``-block tree has none, so the guard is pure insurance.
        """
        out: list[ast.FnDecl] = []
        seen: set[int] = set()
        stack: list[ast.FnDecl] = list(reversed(decl.where_fns or ()))
        while stack:
            wfn = stack.pop()
            if id(wfn) in seen:
                continue
            seen.add(id(wfn))
            out.append(wfn)
            # #990: do NOT descend into a GENERIC helper's subtree.  The
            # helper itself is appended so `_compile_fn` surfaces the same
            # template warning a top-level generic gets (suppressed when a
            # clone compiled), but everything under it belongs to the mono
            # path — each clone carries the subtree and
            # `_hoist_clone_where_fns` emits it per-instantiation; emitting
            # the children standalone here would duplicate them (and a
            # T-dependent child is uncompilable outside a clone anyway).
            if not wfn.forall_vars:
                stack.extend(reversed(wfn.where_fns or ()))
        return out

    @staticmethod
    def _escape_wat_string(s: str) -> str:
        """Escape a string for WAT data section literal."""
        result: list[str] = []
        for ch in s:
            code = ord(ch)
            if ch == '"':
                result.append("\\22")
            elif ch == "\\":
                result.append("\\\\")
            elif ch == "\n":
                result.append("\\n")
            elif ch == "\t":
                result.append("\\t")
            elif 0x20 <= code < 0x7F:
                result.append(ch)
            else:
                # Encode as hex bytes
                for b in ch.encode("utf-8"):
                    result.append(f"\\{b:02x}")
        return "".join(result)

    # -----------------------------------------------------------------
    # Pass 1.6: Ability operation rewriting
    # -----------------------------------------------------------------

    def _rewrite_ability_ops(
        self,
        program: ast.Program,
        mono_decls: list[ast.FnDecl],
    ) -> tuple[ast.Program, list[ast.FnDecl]]:
        """Rewrite ability operation calls to concrete expressions.

        Replaces ``eq(a, b)`` with ``BinaryExpr(a, EQ, b)`` in all
        function bodies (regular and monomorphized).
        """
        from dataclasses import replace as _replace

        # Built-in ability operations that need AST-level rewriting.
        # eq(a, b) → BinaryExpr(a, EQ, b)
        # compare(a, b) → if a < b then Less elif a == b then Equal else Greater
        # (show and hash are dispatched at WASM level, not rewritten here)
        ability_ops: dict[str, str] = {"eq": "Eq", "compare": "Ord"}

        # Rewrite program declarations (non-generic only)
        new_tlds: list[ast.TopLevelDecl] = []
        prog_changed = False
        for tld in program.declarations:
            if isinstance(tld.decl, ast.FnDecl) and not tld.decl.forall_vars:
                new_body = self._rewrite_ops_in_expr(
                    tld.decl.body, ability_ops)
                new_where = self._rewrite_where_fns(
                    tld.decl.where_fns, ability_ops)
                new_contracts = self._rewrite_ops_in_contracts(
                    tld.decl.contracts, ability_ops)
                if (new_body is not tld.decl.body
                        or new_where is not tld.decl.where_fns
                        or new_contracts is not tld.decl.contracts):
                    new_decl = _replace(
                        tld.decl, body=new_body,  # type: ignore[arg-type]
                        where_fns=new_where,
                        contracts=new_contracts)
                    tld = _replace(tld, decl=new_decl)
                    prog_changed = True
            new_tlds.append(tld)
        if prog_changed:
            program = _replace(program, declarations=tuple(new_tlds))

        # Rewrite monomorphized declarations
        new_monos: list[ast.FnDecl] = [
            self._rewrite_fn_ability_ops(mdecl, ability_ops)
            for mdecl in mono_decls
        ]

        # #992: the imported populations compile directly in Pass 2.5/2.6
        # and never pass through the loops above — an `eq`/`compare` in any
        # imported body stayed a raw FnCall codegen cannot lower, dropping
        # the body and dangling the importer's call.  Rewrite each entry
        # too.  Entries are the FLATTENED where-tree (every helper is its
        # own entry), and the rewrite is idempotent, so also rewriting a
        # parent's carried ``where_fns`` cannot double-transform anything.
        self._imported_fn_decls = [
            (path, self._rewrite_fn_ability_ops(idecl, ability_ops))
            for path, idecl in self._imported_fn_decls
        ]
        self._shadowed_module_fns = [
            (path, mangled, self._rewrite_fn_ability_ops(idecl, ability_ops))
            for path, mangled, idecl in self._shadowed_module_fns
        ]

        return program, new_monos

    def _rewrite_fn_ability_ops(
        self,
        decl: ast.FnDecl,
        ability_ops: dict[str, str],
    ) -> ast.FnDecl:
        """Rewrite one declaration's body, where-tree, and contracts."""
        from dataclasses import replace as _replace

        new_body = self._rewrite_ops_in_expr(decl.body, ability_ops)
        new_where = self._rewrite_where_fns(decl.where_fns, ability_ops)
        new_contracts = self._rewrite_ops_in_contracts(
            decl.contracts, ability_ops)
        if (new_body is not decl.body
                or new_where is not decl.where_fns
                or new_contracts is not decl.contracts):
            decl = _replace(
                decl, body=new_body,  # type: ignore[arg-type]
                where_fns=new_where,
                contracts=new_contracts)
        return decl

    def _rewrite_ops_in_contracts(
        self,
        contracts: tuple[ast.Contract, ...],
        ability_ops: dict[str, str],
    ) -> tuple[ast.Contract, ...]:
        """Rewrite ability op calls inside a function's contract clauses.

        The same Pass 1.6 canonicalisation that lowers ``eq(a, b)`` →
        ``BinaryExpr(a, EQ, b)`` in bodies must also run over ``requires`` /
        ``ensures`` / ``decreases`` predicates (#874).  A contract predicate
        written with the ability op reached the WASM contract-lowering path as
        a bare ``FnCall`` whose target is unregistered, tripping the
        ``_translate_call`` guard-rail with an *uncaught* ``CodegenSkip`` — the
        contract path runs outside ``_compile_fn``'s skip-to-E602 try/except.
        Rewriting here keeps codegen on the one canonical operator form
        (#815) so ``vera check``-green contracts compile and enforce.
        """
        from dataclasses import replace as _replace

        new_contracts: list[ast.Contract] = []
        changed = False
        for contract in contracts:
            if isinstance(contract, (ast.Requires, ast.Ensures)):
                new_expr = self._rewrite_ops_in_expr(
                    contract.expr, ability_ops)
                if new_expr is not contract.expr:
                    new_contracts.append(_replace(contract, expr=new_expr))
                    changed = True
                    continue
            elif isinstance(contract, ast.Decreases):
                new_exprs = tuple(
                    self._rewrite_ops_in_expr(e, ability_ops)
                    for e in contract.exprs
                )
                if any(n is not o
                       for n, o in zip(new_exprs, contract.exprs)):
                    new_contracts.append(
                        _replace(contract, exprs=new_exprs))
                    changed = True
                    continue
            new_contracts.append(contract)
        return tuple(new_contracts) if changed else contracts

    def _rewrite_where_fns(
        self,
        where_fns: tuple[ast.FnDecl, ...] | None,
        ability_ops: dict[str, str],
    ) -> tuple[ast.FnDecl, ...] | None:
        """Rewrite ability ops in where-block function bodies AND contracts,
        recursing into nested (grandchild) helpers.

        A `where`-helper carries its own full contract block, so its
        `requires` / `ensures` / `decreases` predicates hit the same
        contract-lowering CodegenSkip as a top-level fn when they use `eq` /
        `compare` (#874).  Rewrite both the body and the contracts through the
        same Pass 1.6 canonicalisation (PR #887 review found the first pass
        covered only `wfn.body`).

        A helper's OWN `where_fns` must be rewritten too (#989): the #978
        emission fix flattens `decl.where_fns` at any depth so a grandchild's
        body reaches `_compile_fn`, but if its `eq` / `compare` was never
        lowered here it stays a raw FnCall — `_compile_fn` trips CodegenSkip,
        drops the body, and the parent's `return_call $grandchild` dangles
        (`unknown func`).  Recurse to mirror `_flatten_where_fns`.
        """
        if not where_fns:
            return where_fns
        from dataclasses import replace as _replace

        new_fns: list[ast.FnDecl] = []
        changed = False
        for wfn in where_fns:
            new_body = self._rewrite_ops_in_expr(wfn.body, ability_ops)
            new_contracts = self._rewrite_ops_in_contracts(
                wfn.contracts, ability_ops)
            new_nested = self._rewrite_where_fns(
                wfn.where_fns, ability_ops)
            if (new_body is not wfn.body
                    or new_contracts is not wfn.contracts
                    or new_nested is not wfn.where_fns):
                new_fns.append(_replace(
                    wfn,
                    body=new_body,  # type: ignore[arg-type]
                    contracts=new_contracts,
                    where_fns=new_nested))
                changed = True
            else:
                new_fns.append(wfn)
        return tuple(new_fns) if changed else where_fns

    def _rewrite_ops_in_expr(
        self,
        expr: ast.Expr,
        ability_ops: dict[str, str],
    ) -> ast.Expr:
        """Recursively rewrite ability op calls in an expression tree."""
        from dataclasses import replace as _replace

        # FnCall: check if it's an ability op to rewrite
        if isinstance(expr, ast.FnCall):
            if (expr.name in ability_ops
                    and expr.name not in self._fn_sigs):
                # eq(a, b) → BinaryExpr(a, EQ, b)
                if expr.name == "eq" and len(expr.args) == 2:
                    left = self._rewrite_ops_in_expr(
                        expr.args[0], ability_ops)
                    right = self._rewrite_ops_in_expr(
                        expr.args[1], ability_ops)
                    return ast.BinaryExpr(
                        left=left, op=ast.BinOp.EQ, right=right,
                        span=expr.span,
                    )
                # compare(a, b) →
                #   if a < b then Less
                #   else if a == b then Equal
                #   else Greater
                if expr.name == "compare" and len(expr.args) == 2:
                    left = self._rewrite_ops_in_expr(
                        expr.args[0], ability_ops)
                    right = self._rewrite_ops_in_expr(
                        expr.args[1], ability_ops)
                    return ast.IfExpr(
                        condition=ast.BinaryExpr(
                            left=left, op=ast.BinOp.LT, right=right,
                            span=expr.span,
                        ),
                        then_branch=ast.Block(
                            statements=(), span=expr.span,
                            expr=ast.NullaryConstructor(
                                name="Less", span=expr.span),
                        ),
                        else_branch=ast.Block(
                            statements=(), span=expr.span,
                            expr=ast.IfExpr(
                                condition=ast.BinaryExpr(
                                    left=left, op=ast.BinOp.EQ,
                                    right=right, span=expr.span,
                                ),
                                then_branch=ast.Block(
                                    statements=(), span=expr.span,
                                    expr=ast.NullaryConstructor(
                                        name="Equal", span=expr.span),
                                ),
                                else_branch=ast.Block(
                                    statements=(), span=expr.span,
                                    expr=ast.NullaryConstructor(
                                        name="Greater", span=expr.span),
                                ),
                                span=expr.span,
                            ),
                        ),
                        span=expr.span,
                    )
            # Recurse into args of non-ability calls
            new_args = tuple(
                self._rewrite_ops_in_expr(a, ability_ops)
                for a in expr.args
            )
            if any(n is not o for n, o in zip(new_args, expr.args)):
                return _replace(expr, args=new_args)
            return expr

        # Block: rewrite statements + final expr
        if isinstance(expr, ast.Block):
            new_stmts = tuple(
                self._rewrite_ops_in_stmt(s, ability_ops)
                for s in expr.statements
            )
            new_final = self._rewrite_ops_in_expr(expr.expr, ability_ops)
            if (any(n is not o for n, o in zip(new_stmts, expr.statements))
                    or new_final is not expr.expr):
                return _replace(
                    expr, statements=new_stmts, expr=new_final)
            return expr

        if isinstance(expr, ast.BinaryExpr):
            left = self._rewrite_ops_in_expr(expr.left, ability_ops)
            right = self._rewrite_ops_in_expr(expr.right, ability_ops)
            if left is not expr.left or right is not expr.right:
                return _replace(expr, left=left, right=right)
            return expr

        if isinstance(expr, ast.UnaryExpr):
            operand = self._rewrite_ops_in_expr(expr.operand, ability_ops)
            if operand is not expr.operand:
                return _replace(expr, operand=operand)
            return expr

        if isinstance(expr, ast.IfExpr):
            cond = self._rewrite_ops_in_expr(expr.condition, ability_ops)
            then = self._rewrite_ops_in_expr(expr.then_branch, ability_ops)
            els = self._rewrite_ops_in_expr(expr.else_branch, ability_ops)
            if (cond is not expr.condition or then is not expr.then_branch
                    or els is not expr.else_branch):
                return _replace(
                    expr, condition=cond,
                    then_branch=then,  # type: ignore[arg-type]
                    else_branch=els)  # type: ignore[arg-type]
            return expr

        if isinstance(expr, ast.MatchExpr):
            scr = self._rewrite_ops_in_expr(expr.scrutinee, ability_ops)
            rewritten_arms: list[ast.MatchArm] = []
            for arm in expr.arms:
                new_body = self._rewrite_ops_in_expr(arm.body, ability_ops)
                if new_body is not arm.body:
                    rewritten_arms.append(_replace(arm, body=new_body))
                else:
                    rewritten_arms.append(arm)
            new_arms = tuple(rewritten_arms)
            if (scr is not expr.scrutinee
                    or any(n is not o
                           for n, o in zip(new_arms, expr.arms))):
                return _replace(expr, scrutinee=scr, arms=new_arms)
            return expr

        if isinstance(expr, ast.ConstructorCall):
            new_args = tuple(
                self._rewrite_ops_in_expr(a, ability_ops)
                for a in expr.args
            )
            if any(n is not o for n, o in zip(new_args, expr.args)):
                return _replace(expr, args=new_args)
            return expr

        if isinstance(expr, ast.AnonFn):
            new_body = self._rewrite_ops_in_expr(expr.body, ability_ops)
            if new_body is not expr.body:
                return _replace(expr, body=new_body)  # type: ignore[arg-type]
            return expr

        if isinstance(expr, ast.ModuleCall):
            new_args = tuple(
                self._rewrite_ops_in_expr(a, ability_ops)
                for a in expr.args
            )
            if any(n is not o for n, o in zip(new_args, expr.args)):
                return _replace(expr, args=new_args)
            return expr

        # Quantifiers: rewrite the domain and the predicate body.  A `forall` /
        # `exists` in a contract (`ensures(forall(..., |i| eq(xs[i], 0)))`) is
        # runtime-lowered by `_translate_quantifier`, which compiles the
        # predicate `AnonFn` body — so an `eq` / `compare` inside it hits the
        # same unregistered-call CodegenSkip as a top-level contract op unless
        # canonicalised here first (PR #887 review: the walker fell through
        # quantifier nodes to the leaf return).
        if isinstance(expr, (ast.ForallExpr, ast.ExistsExpr)):
            new_domain = self._rewrite_ops_in_expr(expr.domain, ability_ops)
            new_pred = self._rewrite_ops_in_expr(expr.predicate, ability_ops)
            if new_domain is not expr.domain or new_pred is not expr.predicate:
                return _replace(
                    expr, domain=new_domain,
                    predicate=new_pred)  # type: ignore[arg-type]
            return expr

        # Leaf nodes (literals, slot refs, etc.) — no rewriting needed
        return expr

    def _rewrite_ops_in_stmt(
        self,
        stmt: ast.Stmt,
        ability_ops: dict[str, str],
    ) -> ast.Stmt:
        """Rewrite ability ops inside a statement."""
        from dataclasses import replace as _replace

        if isinstance(stmt, ast.LetStmt):
            new_val = self._rewrite_ops_in_expr(stmt.value, ability_ops)
            if new_val is not stmt.value:
                return _replace(stmt, value=new_val)
        elif isinstance(stmt, ast.ExprStmt):
            new_expr = self._rewrite_ops_in_expr(stmt.expr, ability_ops)
            if new_expr is not stmt.expr:
                return _replace(stmt, expr=new_expr)
        return stmt
