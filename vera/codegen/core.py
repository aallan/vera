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

import dataclasses
from typing import TYPE_CHECKING

import wasmtime

from vera import ast
from vera.codegen.api import CompileResult
from vera.codegen.memory import ConstructorLayout
from vera.errors import Diagnostic, SourceLocation
from vera.monomorphize import qualify_nested_generic_decls
from vera.prelude import PRELUDE_FILE, mentioned_fn_names
from vera.slots import type_expr_slot_name
from vera.wasm import StringPool
from vera.wasm.async_fusion import (
    compute_future_ret_fns,
    compute_future_ret_module_fns,
)
from vera.wasm.inference import substitute_type_vars

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
        # Function bodies that were registered but did not emit WAT. Later
        # callers use this to produce a source-located E602 instead of a
        # dangling call that fails during WAT assembly.
        self._skipped_fns: set[str] = set()
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
        self._state_types: list[tuple[str, str]] = []  # (type_name, wasm_type)
        self._exn_types: list[tuple[str, str]] = []  # (type_name, wasm_type)
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
        self._random_ops_used: set[str] = set()  # Random host-import builtins (#465)
        self._math_ops_used: set[str] = set()  # Math host-import builtins (#467)

        # ADT layout metadata (populated during registration)
        self._adt_layouts: dict[str, dict[str, ConstructorLayout]] = {}
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

        # Closure compilation state
        self._closure_table: list[str] = []  # lifted fn names for table
        self._closure_sigs: dict[str, str] = {}  # sig_key -> WAT type decl
        self._closure_fns_wat: list[str] = []  # WAT for lifted closures
        self._needs_table: bool = False
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
        # user functions and by the closure-lifting pass for `$anon_N`
        # helpers; entries for prelude-injected FnDecls are removed
        # immediately after registration in `compile_program` (see the
        # post-`inject_prelude` loop) and migrated to
        # `_prelude_fn_names`.  Monomorphized names like `identity$Int`
        # are NOT registered explicitly — the trap-time resolver
        # (`_resolve_trap_frames` in `vera/codegen/api.py`) strips the
        # rightmost `$` suffix and looks up the base name, since `$`
        # cannot appear in user-written Vera identifiers and so any
        # `$` in a WAT name was inserted by the monomorphization
        # mangler.  Built-in WASM helpers (`$alloc`, `$gc_collect`,
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
        error_code: str = "",
    ) -> None:
        """Record a compilation warning (function skipped)."""
        loc, source_line = self._diag_location(node)
        self.diagnostics.append(Diagnostic(
            description=description,
            location=loc,
            source_line=source_line,
            rationale=rationale,
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
    # Compilation entry point
    # -----------------------------------------------------------------

    def compile_program(self, program: ast.Program) -> CompileResult:
        """Compile a complete Vera program to WebAssembly."""
        self._skipped_fns.clear()

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

        # Pass 0.5: register imported module declarations (C7e)
        self._register_modules(program)

        # Pass 1: register local function signatures (shadows imports)
        self._register_all(program)

        # #841: Future<Result<String, String>>-returning fn names — one
        # derivation feeds both import-emission passes (pre-scan +
        # WasmContext) so they agree on which awaits need the
        # fused-handle check.  Derived from the return-type registry
        # (local Pass-1 registrations + the Pass-0 cross-module #628
        # harvest), not the local declarations, so imported and
        # module-qualified calls classify too.
        self._future_ret_fns = compute_future_ret_fns(
            self._fn_ret_type_exprs,
        )
        self._future_ret_module_fns = compute_future_ret_module_fns(
            self._module_fn_ret_type_exprs,
        )

        # Pass 1.2: inject prelude ADTs and combinator implementations
        # Prelude functions are registered as builtins in the type checker
        # (environment.py) but need compilable AST bodies for codegen.
        # inject_prelude prepends DataDecl, FnDecl, and TypeAliasDecl
        # nodes to program.declarations; we register them here.
        existing_fns = set(self._fn_sigs.keys())
        existing_adts = set(self._adt_layouts.keys())
        from vera.prelude import inject_prelude
        # #851 — keep the synthetic prelude buffer: injected decls'
        # spans index into it, and `_diag_location` quotes it (under
        # the `<prelude>` origin) for prelude-origin diagnostics.
        self._prelude_source = inject_prelude(program)
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and decl.name not in existing_fns:
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
            elif isinstance(decl, ast.DataDecl):
                if decl.name not in existing_adts:  # pragma: no cover
                    self._register_data(decl)
            elif isinstance(decl, ast.TypeAliasDecl):
                if decl.name not in self._type_aliases:
                    self._type_aliases[decl.name] = decl.type_expr
                    if decl.type_params:
                        self._type_alias_params[decl.name] = decl.type_params

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
            self._register_fn(mdecl)
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
                fn_wat = self._compile_fn(decl, export=is_public)
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
                    for wfn in self._flatten_where_fns(decl):
                        wfn_wat = self._compile_fn(wfn, export=False)
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
                        else:
                            self._skipped_fns.add(wfn.name)
                else:
                    self._skipped_fns.add(decl.name)

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
            fn_wat = self._compile_fn(
                mdecl, export=is_public,
                imported=origin is not None,
                module_tables=(
                    self._module_artifacts.get(origin)
                    if origin is not None else None
                ),
            )
            if fn_wat is not None:
                functions_wat.append(fn_wat)
                compiled_mono_bases.add(orig_name)
                if is_public:
                    exports.append(mdecl.name)
            else:
                self._skipped_fns.add(mdecl.name)

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
            fn_wat = self._compile_fn(
                idecl, export=False,
                module_renames=self._module_intra_renames.get(path, {}),
                imported=True,  # #986: don't consult the main-file span tables
                # #987: thread THIS module's own span-keyed tables so the
                # imported body's @Nat -> @Int widening guard fires.
                module_tables=self._module_artifacts.get(path),
            )
            if fn_wat is not None:
                functions_wat.append(fn_wat)
            else:
                self._skipped_fns.add(idecl.name)

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
            fn_wat = self._compile_fn(
                dataclasses.replace(idecl, name=mangled),
                export=False,
                module_renames=self._module_intra_renames.get(path, {}),
                imported=True,  # #986: don't consult the main-file span tables
                # #987: the ``mod$…`` rename only changes the WASM function name;
                # the body's node spans are unchanged, so THIS module's table
                # still keys them correctly and its widen guard fires.
                module_tables=self._module_artifacts.get(path),
            )
            if fn_wat is not None:
                functions_wat.append(fn_wat)
            else:
                self._skipped_fns.add(mangled)

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
        except Exception as exc:
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
        )

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
        """
        if isinstance(te, ast.NamedType):
            if te.name == "String":
                return True
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
            # Type aliases — substitute a parameterised alias's own type
            # params with the concrete `te.type_args` BEFORE recursing
            # (mirrors `_type_expr_to_wasm_type`'s #635 block below), so
            # `type Deferred<T> = Future<T>` used as `Deferred<String>`
            # resolves to String instead of recursing on the bare `T` and
            # displaying the raw pointer (PR #1041 review).
            if te.name in self._type_aliases:
                alias = self._type_aliases[te.name]
                alias_params = self._type_alias_params.get(te.name)
                if (alias_params and te.type_args
                        and len(alias_params) == len(te.type_args)):
                    local_subst = dict(zip(alias_params, te.type_args))
                    alias = substitute_type_vars(alias, local_subst)
                return self._return_type_is_string(alias)
        if isinstance(te, ast.RefinementType):
            return self._return_type_is_string(te.base_type)
        return False

    def _type_expr_to_wasm_type(self, te: ast.TypeExpr) -> str | None:
        """Map a Vera TypeExpr to a WAT type string.

        Returns None for Unit, "unsupported" for non-compilable types,
        "i32_pair" for types represented as (i32, i32) pairs (String, Array).
        """
        if isinstance(te, ast.NamedType):
            name = te.name
            if name in ("Int", "Nat"):
                return "i64"
            if name == "Float64":
                return "f64"
            if name in ("Bool", "Byte"):
                return "i32"
            if name == "Unit":
                return None
            if name in ("String", "Array"):
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
            # ADT types compile to i32 (heap pointer)
            if name in self._adt_layouts:
                return "i32"
            # Type aliases — recurse to resolve the underlying type.
            # When the alias is parameterised (`type Box<T> =
            # Array<T>`), substitute the alias's own type params with
            # the concrete `te.type_args` *before* recursing, so type
            # variables in the alias body don't leak through and get
            # mis-classified as `"unsupported"`.  Closes #635 — the
            # parallel of the walker fix landed in PR #631 for
            # `_canonical_named_type`, applied to this compilability
            # check.
            if name in self._type_aliases:
                alias = self._type_aliases[name]
                alias_params = self._type_alias_params.get(name)
                if (alias_params and te.type_args
                        and len(alias_params) == len(te.type_args)):
                    local_subst = dict(zip(alias_params, te.type_args))
                    alias = substitute_type_vars(alias, local_subst)
                return self._type_expr_to_wasm_type(alias)
            return "unsupported"
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_wasm_type(te.base_type)
        # Function types compile to i32 (closure pointer)
        if isinstance(te, ast.FnType):
            return "i32"
        return "unsupported"

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str | None:
        """Extract the slot name from a type expression.

        Delegates to the shared recursive :func:`vera.slots.type_expr_slot_name`
        so nested composite type args (`Option<Tuple<Int, Int>>`) are
        FULLY qualified and distinguishable (#914 finding 2), and every
        slot-name builder agrees by construction (dedup).
        """
        return type_expr_slot_name(te)

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
