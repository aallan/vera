"""Vera type checker — Tier 1 decidable type checking.

Validates expression types, slot reference resolution, effect annotations,
and contract well-formedness.  Consumes Program AST nodes from parse_to_ast()
and produces a list of Diagnostic errors (empty = success).

Refinement predicate verification and contract satisfiability are handled
by the contract verifier (vera/verifier.py) via Z3.

The ``TypeChecker`` class is composed from several mixin modules that
each handle a specific concern:

* :mod:`~vera.checker.resolution` — AST TypeExpr → semantic Type
* :mod:`~vera.checker.modules` — cross-module registration (C7b/C7c)
* :mod:`~vera.checker.registration` — Pass 1 forward declarations
* :mod:`~vera.checker.expressions` — expression type synthesis
* :mod:`~vera.checker.calls` — function / constructor / module calls
* :mod:`~vera.checker.control` — if/match, patterns, effect handlers
"""

from __future__ import annotations

from collections.abc import Callable, Container
from dataclasses import dataclass, replace
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from vera.resolver import ResolvedModule

from vera import ast, naming
from vera.errors import Diagnostic, SourceLocation
from vera.naming import AliasEnv
from vera.registration import where_helper_parents
from vera.environment import (
    AdtInfo,
    FunctionInfo,
    TypeEnv,
)
from vera.types import (
    EffectInstance,
    BOOL,
    INT,
    NAT,
    AdtType,
    ModuleArtifacts,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    is_subtype,
    pretty_type,
    pretty_inferred_type,
)

from vera.checker.resolution import ResolutionMixin
from vera.checker.modules import ModulesMixin
from vera.checker.registration import RegistrationMixin
from vera.checker.expressions import ExpressionsMixin
from vera.checker.calls import CallsMixin
from vera.checker.control import ControlFlowMixin


class _ScopedFnNames:
    """Membership over the checker's LEXICAL function scope (#1284).

    A view rather than a set because the scope is a stack that changes as
    checking descends: materialising it would freeze an answer the checker
    itself would give differently one frame later.
    """

    __slots__ = ("_lookup",)

    def __init__(self, lookup: Callable[[str], object | None]) -> None:
        self._lookup = lookup

    def __contains__(self, name: object) -> bool:
        return isinstance(name, str) and self._lookup(name) is not None


# =====================================================================
# Public API
# =====================================================================

def typecheck(
    program: ast.Program,
    source: str = "",
    file: str | None = None,
    resolved_modules: list[ResolvedModule] | None = None,
) -> list[Diagnostic]:
    """Type-check a Vera Program AST.

    Returns a list of Diagnostics (empty = no errors).

    *resolved_modules* — modules resolved from ``import`` declarations
    (see :class:`~vera.resolver.ModuleResolver`).  Cross-module type
    merging (C7b): imported function signatures are registered and
    used for arity, argument-type, and effect checking.
    """
    checker = TypeChecker(
        source=source, file=file, resolved_modules=resolved_modules,
    )
    checker.check_program(program)
    return checker.errors


@dataclass
class HoleSite:
    """One typed hole's location and context (#222 Phase D).

    Mirrors what the W001 diagnostic narrates, as structured data the
    LSP completion feature can serve directly: the expected type and
    every in-scope binding (slot-reference string, pretty type),
    innermost first.
    """

    line: int
    column: int
    end_line: int
    end_column: int
    expected: str
    bindings: list[tuple[str, str]]


@dataclass
class CheckArtifacts:
    """Side-tables collected during one opt-in type-check pass.

    ``expr_types`` maps each typed expression's span — keyed
    ``(line, column, end_line, end_column)``, all 1-based per
    ``ast.Span`` — to its pretty-printed type.  Populated by the
    ``_synth_expr`` recording wrapper, so every expression the checker
    synthesises a type for is present (the LSP hover substrate).
    """

    expr_types: dict[tuple[int, int, int, int], str]
    holes: list[HoleSite]
    # #747: semantic-type side-tables for the verifier (see TypeChecker).
    expr_semantic_types: dict[tuple[int, int, int, int], Type]
    expr_target_types: dict[tuple[int, int, int, int], Type]
    # #987: per-resolved-module span-keyed side-tables, keyed by module path.
    # Each entry is that module's OWN ``(expr_semantic_types,
    # expr_target_types)`` — the top-level tables above are keyed by bare span
    # with no file identity, so an imported body compiled into the flat WASM
    # module (Pass 2.5 / 2.6) cannot recover its component targets from them.
    # Codegen threads the matching entry when compiling each module's body, so
    # the #820 @Nat -> @Int widening guard fires at the array-element /
    # tuple-construction sites through the import door, not just same-file.
    module_artifacts: ModuleArtifacts
    # #1208: the ENTRY module's naming environment — the alias bodies, alias
    # parameters, and declared-ADT names :mod:`vera.naming` renders slot names,
    # slot-reference keys, and State/Exn cell families against.  Captured from
    # the checker's own ``TypeEnv`` once the program has been checked, so a
    # consumer downstream of the check renders against exactly the table the
    # checker keyed its bindings by rather than rebuilding an approximation.
    alias_env: AliasEnv


def typecheck_with_artifacts(
    program: ast.Program,
    source: str = "",
    file: str | None = None,
    resolved_modules: list[ResolvedModule] | None = None,
    collect_module_artifacts: bool = False,
) -> tuple[list[Diagnostic], CheckArtifacts]:
    """Type-check and additionally collect LSP artifacts (#222 Phase D).

    Identical diagnostics to :func:`typecheck` — collection is purely
    observational (a dict write per synthesised expression; decision R4
    of the #222 plan chose this eager side-table over re-synthesis at
    query time).  Existing callers keep using :func:`typecheck`; only
    the LSP layer pays the collection cost.

    ``collect_module_artifacts`` (#987, opt-in per PR #997 review) gates the
    per-resolved-module side-table pass.  Only the codegen-bound callers
    (``vera compile`` / ``run`` / ``serve`` / ``test``) consume
    ``CheckArtifacts.module_artifacts`` — they pass ``True``.  ``vera verify``
    and the warm ``VerificationSession`` read only the top-level
    ``expr_semantic_types`` / ``expr_target_types`` tables and would pay a full
    extra ``check_program`` per resolved module for nothing, so they leave it
    ``False`` (``module_artifacts`` is then an empty dict, which ``_compile_fn``
    already tolerates — the #986 imported-body suppression fallback).
    ``alias_env`` (#1208), by contrast, is the entry module's own and always
    present — it costs one walk of an already-built table.  There is no
    per-module counterpart in the artifacts: the two consumers that need one
    build it themselves from a namespace they already hold — codegen from its
    own flat alias maps (``_sync_alias_env``), the verifier from its own
    per-module registration (``ContractVerifier._module_alias_envs``) — and a
    third, unread copy here would only be one more table to drift.
    """
    checker = TypeChecker(
        source=source, file=file, resolved_modules=resolved_modules,
    )
    checker.expr_types = {}
    checker.expr_semantic_types = {}
    checker.expr_target_types = {}
    checker.hole_sites = []
    checker.check_program(program)

    module_arts: ModuleArtifacts = {}
    diagnostics = list(checker.errors)
    if collect_module_artifacts:
        # #1244: the imported-body DIAGNOSTICS are already in `diagnostics` —
        # `_register_modules` checks every module's bodies under its own import
        # filter on EVERY path, not just this one, so this pass collects
        # artifacts only.  The memo goes over so the sub-checks here do not
        # re-run a body check the top-level pass has already done.
        module_arts = _collect_module_artifacts(
            resolved_modules, checker._module_body_check_memo,
        )

    return diagnostics, CheckArtifacts(
        expr_types=checker.expr_types,
        holes=checker.hole_sites,
        expr_semantic_types=checker.expr_semantic_types,
        expr_target_types=checker.expr_target_types,
        module_artifacts=module_arts,
        alias_env=naming.alias_env_from_environment(checker.env),
    )


def _collect_module_artifacts(
    resolved_modules: list[ResolvedModule] | None,
    body_check_memo: set[tuple[str, ...]] | None = None,
) -> ModuleArtifacts:
    """Collect each resolved module's OWN span-keyed side-tables (#987).

    The top-level program's ``expr_target_types`` / ``expr_semantic_types`` are
    keyed by bare span ``(line, col, end_line, end_col)`` with no file identity,
    so an imported body compiled into the flat WASM module (Pass 2.5 / 2.6) has
    no entries there — codegen dropped the #820 @Nat -> @Int widening guard at
    the array-element / tuple-construction sites through the import door, while
    the library's own ``vera verify`` reported them Tier-3-guarded (the broken
    promise).  Run the full check over each module in isolation to collect ITS
    table, keyed by module path, so codegen can thread the right one when it
    compiles that module's body.

    Each module's ``direct`` flags are re-derived from its OWN ``import``
    declarations — the closure ``resolved_modules`` was tagged relative to the
    top-level program (a module the program reaches only transitively is
    ``direct=False`` there, but is a DIRECT import of whichever module imports
    it) — so name injection (gated on ``mod.direct``) and qualified-call
    resolution match a standalone check of that module.  Over-inclusion of
    modules the checked one never imports is inert: they are registered but,
    tagged ``direct=False`` and absent from its ``program.imports``, never
    injected or qualified-callable.

    Honesty note (PR #997 review): no BEHAVIOURAL fixture has been found where
    the re-derivation vs reusing the top-level flags changes an emitted guard —
    the necessity at the guard level is therefore unproven.  What IS proven is
    that the re-derivation changes the collected ARTIFACT: in a transitive
    fixture (main -> alib -> blib) ``alib``'s own target table gains its second
    entry only because ``blib`` is re-tagged a DIRECT import of ``alib`` for its
    sub-check.  That artifact-level difference is pinned by
    ``tests/test_xmod_artifact_collection.py::TestTransitiveArtifactContent``.

    Diagnostics are NOT collected here (#1244).  The imported-body errors this
    pass used to surface (Cortex #1147 Finding 2 — a library whose SQL is
    non-literal must fail the importer's compile too, E207) now reach every
    caller from ``ModulesMixin._register_modules``, which checks each module's
    bodies under that module's own import filter on every path rather than only
    on the codegen ones.  Two passes deriving the same diagnostics is the #1213
    disease; this one keeps the artifact it alone produces.

    Cost note (PR #997 review, corrected for #1244): THIS pass is quadratic
    and still codegen-only — N resolved modules each get a full
    ``check_program`` that re-registers the other N-1, so it is O(N^2)
    sub-checks (measured ~85ms at 20 modules vs ~4ms for the main-file-only
    check), and it runs only when a caller asks for artifacts, i.e. for
    ``vera compile``/``run``/``serve``/``test``.

    What is no longer true is that a module's body is checked only on those
    paths.  ``ModulesMixin._register_modules`` checks each module's bodies
    under its own import filter (#1244), and that runs from
    ``check_program`` — so ``vera check``, ``vera verify`` and the warm
    ``VerificationSession`` all pay one full sub-check per resolved module,
    and the session pays it again on every re-check (it calls
    ``typecheck_with_artifacts`` per verify).  ``body_check_memo`` is that
    pass's memo, threaded into each sub-checker here so a body check the
    top-level pass has already run is not repeated per sub-check — without
    it, this O(N^2) pass would multiply the #1244 pass by N.

    Memoising each module's per-check REGISTRATION (its declarations are
    re-derived identically every pass) is the optimisation candidate that
    would collapse both toward O(N); it is tracked as
    [#1275](https://github.com/aallan/vera/issues/1275).
    """
    mods = resolved_modules or []
    result: ModuleArtifacts = {}
    for mod in mods:
        mod_direct = {imp.path for imp in mod.program.imports}
        sub_resolved = [
            replace(other, direct=(other.path in mod_direct))
            for other in mods
            if other.path != mod.path
        ]
        sub_semantic: dict[tuple[int, int, int, int], Type] = {}
        sub_target: dict[tuple[int, int, int, int], Type] = {}
        sub = TypeChecker(
            source=mod.source,
            file=str(mod.file_path),
            resolved_modules=sub_resolved,
        )
        sub._module_body_check_memo = body_check_memo
        sub.expr_types = {}
        sub.expr_semantic_types = sub_semantic
        sub.expr_target_types = sub_target
        sub.hole_sites = []
        sub.check_program(mod.program)
        result[mod.path] = (sub_semantic, sub_target)
    return result


# =====================================================================
# Type checker
# =====================================================================

class TypeChecker(
    ResolutionMixin,
    ModulesMixin,
    RegistrationMixin,
    ExpressionsMixin,
    CallsMixin,
    ControlFlowMixin,
):
    """Top-down type checker with error accumulation.

    Composed from six mixin classes, each in its own module.
    This class provides __init__, diagnostics, and the top-level
    checking orchestration (check_program, _check_decl, _check_fn,
    _check_contract).
    """

    def __init__(
        self,
        source: str = "",
        file: str | None = None,
        resolved_modules: list[ResolvedModule] | None = None,
    ) -> None:
        self.env = TypeEnv()
        self.errors: list[Diagnostic] = []
        # A single root cause can reach `_error` more than once — most
        # visibly, a function's signature types are `_resolve_type`'d in
        # BOTH the registration and the check pass, so a resolution
        # diagnostic on a param/return (e.g. `E135` on an `Array<Unit>`
        # param) would otherwise be emitted twice at one location.  Collapse
        # exact-duplicate diagnostics — identical code, location, severity,
        # and message are indistinguishable to the reader — to a single
        # entry, preserving first-occurrence order (PR #938 review).
        self._seen_diag_keys: set[tuple[str, ...]] = set()
        self.source = source
        self.file = file
        self._effect_ops_used: set[str] = set()
        # #973: canonical type names of the handler state(s) whose HANDLED
        # BODY is currently being checked.  State is in scope as a slot only in
        # handler clauses, never the handled body — the body reaches state
        # through the typed get(())/put(...) operations (spec §7.5; DESIGN
        # principles 2/3/6).  This stack lets a failed slot resolution of a
        # state type inside the body carry a get(()) hint instead of a bare
        # unbound-slot error.  Push/pop straddles the body check in
        # _check_handle; empty everywhere else.
        self._handler_body_state_tnames: list[str] = []
        # #1148: base names of effects handled by enclosing `handle` blocks
        # currently in scope.  Push/pop straddles the body check in
        # _check_handle.  A BARE op call to a non-State/Exn effect is codegen-
        # routable only when its effect is in this stack (rewritten to the
        # handler clause); otherwise it is E217.
        self._handled_effects: list[str] = []
        # #1203 determinism: the handled-effect INSTANCES, innermost last —
        # `_effect_type_mapping` consults this stack innermost-first so an
        # op inside nested same-name handlers (State<Int> under State<Nat>)
        # resolves against the governing handler's type args instead of a
        # frozenset iteration whose order is PYTHONHASHSEED roulette.
        self._handled_effect_insts: list[EffectInstance] = []
        # #969: canonical slot-type names bound by the PARENT function whose
        # where-block is currently being checked.  A where-helper is a closed,
        # param-rooted scope (spec §5): its body cannot read the outer
        # function's parameter slots — the parent's value scope is popped
        # before helper bodies are checked, so an outer slot becomes an
        # ordinary E130.  This stack lets that failed resolution carry a
        # "pass it as an explicit argument" hint when the failing type is one
        # the parent bound.  Push/pop straddles the where-fn loop in
        # _check_fn; empty everywhere else (so no non-helper diagnostic sees
        # the hint).  Parent TYPE params stay in scope through the loop.
        self._where_helper_outer_tnames: list[frozenset[str]] = []
        # #815: ids of FnDecls rejected for redefining a built-in (E151).
        # They are not registered (the built-in stays canonical), so the
        # check phase skips them — re-checking would resolve their own body
        # against the built-in and emit bogus secondary diagnostics.
        self._rejected_builtin_redefs: set[int] = set()
        # #991 checker leg (PR #1013 review): lexically-scoped where-helper
        # resolution, mirroring the verifier and codegen.  ``env.functions``
        # is flat and last-wins, so a bare call to a same-named helper in a
        # DIFFERENT parent tree resolved against whichever helper registered
        # last — a diamond whose two `leaf`s differ in signature was falsely
        # REJECTED (E121 against the wrong leaf's return type) on a valid
        # program.  `_fn_scope_stack` holds the chain of functions whose
        # `where` blocks are lexically in scope (outermost first; maintained
        # by `_check_fn`); `_top_level_fn_infos` pins each top-level
        # function's own info (a nested same-named helper would otherwise
        # clobber it in the flat registry); `_scoped_fn_info_cache` memoizes
        # per-decl infos for the scoped lookup.
        self._fn_scope_stack: list[ast.FnDecl] = []
        self._top_level_fn_infos: dict[str, FunctionInfo] = {}
        # #1307: helper name -> the declarations that own one, for the E178
        # instruction.  Registration no longer publishes helpers into the
        # flat registry, so a bare call from outside the parent resolves to
        # nothing; this is what lets the diagnostic say WHERE the name it
        # cannot reach is declared, instead of E200's "define it in this
        # file" for a name the file already declares.
        self._where_helper_parents: dict[str, set[str]] = {}
        self._scoped_fn_info_cache: dict[
            tuple[int, str | None], FunctionInfo
        ] = {}
        # #222 Phase D: opt-in artifact collection for LSP features.
        # None = off (the default for every existing caller; zero
        # cost).  When dicts are installed by typecheck_with_artifacts,
        # the _synth_expr wrapper records every typed expression span
        # and _check_hole records each hole's expected type + in-scope
        # bindings.
        self.expr_types: dict[tuple[int, int, int, int], str] | None = None
        # #747: parallel side-tables of *semantic* types (not pretty
        # strings) for the verifier — the result type and the ``expected``
        # (instantiated target) type each expression was checked against,
        # so the narrowing walker can resolve the @Nat target at
        # projection / generic-instantiation binding sites.  Co-enabled
        # with ``expr_types`` (both installed by typecheck_with_artifacts).
        self.expr_semantic_types: (
            dict[tuple[int, int, int, int], Type] | None
        ) = None
        self.expr_target_types: (
            dict[tuple[int, int, int, int], Type] | None
        ) = None
        self.hole_sites: list[HoleSite] | None = None
        # Resolved modules (C7a: paths for diagnostics, C7b: full list
        # for cross-module type merging).
        self._resolved_modules: list[ResolvedModule] = (
            resolved_modules or []
        )
        # #890: only DIRECT imports are qualified-callable (`mid::via_mid`)
        # from this program.  A transitively-reached module (`base`, imported
        # only by `mid`) is in ``_resolved_modules`` so codegen can compile
        # the bodies that call into it, but per spec §8.6.4 its declarations
        # are not visible here — a `base::wrap40` from the top-level importer
        # must fail resolution (E230), so it stays out of this set.
        self._resolved_module_paths: set[tuple[str, ...]] = {
            m.path for m in self._resolved_modules if m.direct
        }
        # #1304: bare names two of THIS program's imports both supply, one
        # set per declaration namespace.  Set by
        # ``_reject_ambiguous_imports``, which also reports each one (E155
        # functions / E156 data types / E157 constructors); the injection
        # loops skip them, so an ambiguous name denotes nothing here rather
        # than whichever supplier registered first.  Initialised empty for
        # the paths that register declarations without running
        # ``check_program`` (the per-module harvest builds a checker and
        # calls ``_register_all`` on it directly).
        self._ambiguous_import_fn_names: frozenset[str] = frozenset()
        self._ambiguous_import_type_names: frozenset[str] = frozenset()
        self._ambiguous_import_ctor_names: frozenset[str] = frozenset()
        # C7b: per-module declaration registries (for ModuleCall path).
        self._module_functions: dict[
            tuple[str, ...], dict[str, object]
        ] = {}
        self._module_data_types: dict[
            tuple[str, ...], dict[str, AdtInfo]
        ] = {}
        self._module_constructors: dict[
            tuple[str, ...], dict[str, object]
        ] = {}
        # C7b: import-name filter from ImportDecl nodes.
        self._import_names: dict[
            tuple[str, ...], set[str] | None
        ] = {}
        # #1244: paths whose BODIES this run has already checked under their
        # own import filter, shared down the nested checkers so a module
        # reached from several importers is checked once and an import cycle
        # terminates.  ``None`` until the first module is reached.
        self._module_body_check_memo: set[tuple[str, ...]] | None = None
        # C7c: unfiltered module declarations (for "is private" errors).
        self._module_all_functions: dict[
            tuple[str, ...], dict[str, object]
        ] = {}
        self._module_all_data_types: dict[
            tuple[str, ...], dict[str, AdtInfo]
        ] = {}
        # De-dup removed-alias errors (emitted once per alias name).
        self._reported_alias_errors: set[str] = set()
        # De-dup reserved-namespace type REFERENCES (E154, #1221) — one
        # error per name, at its first mention.
        self._reported_reserved_type_refs: set[str] = set()
        # One range verdict per integer LITERAL (E149, #1252 / PR #1282
        # review).  Keyed by `id(node)` — per OCCURRENCE, not per value or
        # per message, so two distinct out-of-range literals still get two
        # errors.  Ids are stable for the run: the program holds every node
        # alive from parse until the check finishes.  The bool records
        # whether the verdict was contextual (it knew the target type); see
        # `ExpressionsMixin`'s IntLit branch for why an unconstrained
        # verdict is provisional.
        self._literal_range_verdict: dict[int, tuple[Diagnostic, bool]] = {}
        # Monotonic counter for fresh TypeVar names (prevents
        # self-referential mappings when different ADTs share a type
        # parameter name — see #243).
        self._fresh_id: int = 0

    @staticmethod
    def _is_public(visibility: str | None) -> bool:
        """True if the declaration is explicitly ``public``."""
        return visibility == "public"

    # -----------------------------------------------------------------
    # Diagnostics
    # -----------------------------------------------------------------

    def _error(self, node: ast.Node, description: str, *,
               rationale: str = "", fix: str = "",
               spec_ref: str = "", severity: str = "error",
               error_code: str = "") -> None:
        """Record a type error diagnostic."""
        loc = SourceLocation(file=self.file)
        if node.span:
            loc.line = node.span.line
            loc.column = node.span.column
        # Collapse an exact-duplicate (same code, file, position, severity,
        # and message) to a single entry — see `_seen_diag_keys`.
        key = (
            error_code, str(loc.file), str(loc.line),
            str(loc.column), severity, description,
        )
        if key in self._seen_diag_keys:
            return
        self._seen_diag_keys.add(key)
        self.errors.append(Diagnostic(
            description=description,
            location=loc,
            source_line=self._source_line(node),
            rationale=rationale,
            fix=fix,
            spec_ref=spec_ref,
            severity=severity,
            error_code=error_code,
        ))

    def _literal_range_error(
        self, node: ast.Node, description: str, *,
        rationale: str, fix: str, contextual: bool,
    ) -> None:
        """Emit E149 for *node*, keeping ONE verdict per literal.

        An integer literal can be synthesised more than once — a
        refinement predicate's operands are typed with no expected type
        first and against the refined base afterwards — and the two
        passes answer with different bounds, so a single mistake drew
        two E149s naming ``@Nat (u64)`` and ``@Byte`` (PR #1282 review).
        ``_error``'s duplicate collapse cannot see it: the messages
        differ, which is precisely the problem.

        The unconstrained pass is provisional.  It reports the u64 bound
        because nothing has told it the target type, not because u64 is
        the target — so a later CONTEXTUAL verdict supersedes it rather
        than joining it, and the earlier diagnostic is withdrawn.  The
        reverse never happens: a guess does not overrule knowledge, and
        an unconstrained verdict arriving second is dropped.  When the
        unconstrained verdict is the only one, it stands — that is the
        #812 gate, and silencing it would reopen the soundness hole.
        """
        prior = self._literal_range_verdict.get(id(node))
        withdrawn: Diagnostic | None = None
        if prior is not None:
            earlier, was_contextual = prior
            if was_contextual or not contextual:
                return
            # Contextual supersedes provisional: withdraw the guess.  Its
            # `_seen_diag_keys` entry stays, so the withdrawn message
            # cannot reappear from a third synthesis of the same literal.
            if earlier in self.errors:
                self.errors.remove(earlier)
                withdrawn = earlier
        before = len(self.errors)
        self._error(
            node, description, rationale=rationale, fix=fix,
            spec_ref='Chapter 4, Section 4.2 "Literals"',
            error_code="E149",
        )
        if len(self.errors) > before:
            self._literal_range_verdict[id(node)] = (
                self.errors[-1], contextual,
            )
        elif withdrawn is not None:
            # The contextual message was byte-identical to the withdrawn
            # provisional one, so the `_seen_diag_keys` entry kept above
            # suppressed it — and the withdrawal has just removed the only
            # verdict this literal had (PR #1283 review).  Put it back: the
            # rule is ONE verdict per literal, never zero, because zero
            # re-opens the #812 gate silently.  The restored diagnostic is
            # recorded as CONTEXTUAL, since that is the verdict now
            # standing; a later unconstrained synthesis is still dropped.
            self.errors.append(withdrawn)
            self._literal_range_verdict[id(node)] = (withdrawn, contextual)

    def _source_line(self, node: ast.Node) -> str:
        """Extract source line for a node."""
        if not node.span or not self.source:
            return ""
        lines = self.source.splitlines()
        idx = node.span.line - 1
        if 0 <= idx < len(lines):
            return lines[idx]
        return ""

    # -----------------------------------------------------------------
    # Pass 2: Checking
    # -----------------------------------------------------------------

    def check_program(self, program: ast.Program) -> None:
        """Entry point: register modules, then local declarations, then check."""
        self._register_modules(program)  # C7b: cross-module imports
        self._register_all(program)  # local declarations shadow imports
        # #991 checker leg: pin each LOCAL top-level function's own info so
        # the scoped lookup prefers it over a nested helper of the same name
        # that clobbered the flat registry (helpers register last) — the
        # checker then resolves helper calls exactly as the verifier and
        # codegen do.  Rejected built-in redefinitions stay out (the built-in
        # is canonical, #815).
        for tld in program.declarations:
            decl = tld.decl
            if (isinstance(decl, ast.FnDecl)
                    and id(decl) not in self._rejected_builtin_redefs):
                self._top_level_fn_infos[decl.name] = self._fn_info_for_decl(
                    decl, visibility=tld.visibility,
                )
        # #1307/#1383: which declaration owns each `where`-helper name, over
        # THIS program and every module it resolves.  A helper is local to
        # its parent whichever file it is written in — it carries no
        # visibility, so the import injection never offers it — and the
        # importer's bare call therefore resolves to nothing on both tables.
        # Indexing the module graph is what lets the diagnostic say so:
        # across a file boundary E200's "define it in this file" is worse
        # advice than within one, because the name IS declared, IS visible
        # in the imported source, and cannot be imported (E150).
        self._where_helper_parents = {}
        for label, decls in self._helper_index_sources(program):
            for name, parents in where_helper_parents(decls).items():
                owners = self._where_helper_parents.setdefault(name, set())
                owners.update(
                    f"'{parent}'" if label is None
                    else f"'{parent}' in module '{label}'"
                    for parent in parents
                )
        for tld in program.declarations:
            # #815: a built-in redefinition (E151) is already reported and not
            # registered; skip checking its body so it isn't re-checked against
            # the canonical built-in (which would emit bogus diagnostics).
            if id(tld.decl) in self._rejected_builtin_redefs:
                continue
            self._check_decl(tld.decl)

    def _check_decl(self, decl: ast.Decl) -> None:
        """Check a single declaration."""
        if isinstance(decl, ast.FnDecl):
            self._check_fn(decl)
        elif isinstance(decl, ast.DataDecl):
            self._check_data(decl)
        elif isinstance(decl, ast.TypeAliasDecl):
            self._check_alias(decl)
        elif isinstance(decl, (ast.EffectDecl, ast.AbilityDecl)):
            # #861 (PR #876 review): op signatures CAN carry refinement
            # predicates (`op log({ @Int | P } -> ...)`), and registration
            # does not check them — `_register_effect` / `_register_ability`
            # only `_resolve_type` the signature, which wraps the base in
            # `RefinedType(base, predicate)` without ever typing the
            # predicate.
            self._check_op_signatures(decl)

    def _check_op_signatures(
        self, decl: ast.EffectDecl | ast.AbilityDecl,
    ) -> None:
        """Check refinement predicates in effect / ability op signatures
        (#861), with the declaration's type params in scope."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)
        for op in decl.operations:
            for param_te in op.param_types:
                self._check_refinement_predicates(param_te)
            self._check_refinement_predicates(op.return_type)
        self.env.type_params = saved_params

    def _check_alias(self, decl: ast.TypeAliasDecl) -> None:
        """Check a type alias's refinement predicates (#861).

        Registration (`_register_alias`) resolves the alias's *base* but does
        not check any refinement predicate it carries.  Do that here, in the
        check phase, so predicates can reference other registered types and
        functions (e.g. `type SmallVia = { @Byte | ident(@Byte.0) < 10 }`).
        """
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)
        self._check_refinement_predicates(decl.type_expr)
        self.env.type_params = saved_params

    def _check_data(self, decl: ast.DataDecl) -> None:
        """Check an ADT declaration (invariant well-formedness)."""
        # #861: a constructor field type may carry a refinement
        # (`data Wrap = Wrap({ @Int | @Int.0 > 0 })`); check its predicate
        # with the ADT's type params in scope.
        saved_field_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)
        for ctor in decl.constructors:
            if ctor.fields is not None:
                for field_te in ctor.fields:
                    self._check_refinement_predicates(field_te)
        self.env.type_params = saved_field_params

        if decl.invariant is not None:
            # Push scope with constructor bindings for invariant checking
            self.env.push_scope()
            saved_params = dict(self.env.type_params)
            if decl.type_params:
                for tv in decl.type_params:
                    self.env.type_params[tv] = TypeVar(tv)

            inv_type = self._synth_expr(decl.invariant)
            if inv_type and not is_subtype(inv_type, BOOL):
                self._error(
                    decl.invariant,
                    f"Invariant must be Bool, found {pretty_type(inv_type)}.",
                    rationale="Data type invariants are predicates that must "
                              "evaluate to Bool.",
                    fix="The invariant must be a Bool-valued predicate.  Note "
                        "that `data` invariants are not yet implemented (#686); "
                        "until then, express the constraint as a refinement "
                        "type over a real base type, e.g. "
                        "`type Positive = { @Int | @Int.0 > 0 };`.",
                    spec_ref='Chapter 2, Section 2.4.1 "ADT Invariants"',
                    error_code="E120",
                )

            self.env.type_params = saved_params
            self.env.pop_scope()

    def _check_fn(self, decl: ast.FnDecl) -> None:
        """Check a function declaration."""
        saved_params = dict(self.env.type_params)
        saved_return = self.env.current_return_type
        saved_effect = self.env.current_effect_row
        saved_effect_order = self.env.current_effect_order
        # #991 checker leg: this function's frame joins the lexical scope
        # stack for the duration of its body, contracts, AND its where-helper
        # recursion (step 8) — a helper's body must see this function's
        # helpers as ancestors.  Popped alongside the step-9 restores below
        # (the same non-finally discipline as the type-param save/restore:
        # an exception here aborts check_program entirely, so a leaked frame
        # is unobservable).
        self._fn_scope_stack.append(decl)

        # 1. Bind forall type parameters
        if decl.forall_vars:
            for tv in decl.forall_vars:
                self.env.type_params[tv] = TypeVar(tv)

        # 1b. Validate ability constraints
        if decl.forall_constraints:
            for constraint in decl.forall_constraints:
                # E180: ability must exist
                if not self.env.abilities.get(constraint.ability_name):
                    self._error(
                        constraint,
                        f"Unknown ability '{constraint.ability_name}' "
                        f"in constraint.",
                        rationale="Ability constraints must reference a "
                                  "declared ability.",
                        fix=f"Declare 'ability "
                            f"{constraint.ability_name}<T> {{ ... }}' "
                            f"or use a built-in ability like Eq.",
                        spec_ref='Chapter 9, Section 9.8 "Abilities"',
                        error_code="E180",
                    )
                # E181: type var must be declared in forall
                if (decl.forall_vars is None
                        or constraint.type_var not in decl.forall_vars):
                    self._error(
                        constraint,
                        f"Constraint references undeclared type variable "
                        f"'{constraint.type_var}'.",
                        rationale="Type variables in constraints must be "
                                  "declared in the forall clause.",
                        fix=f"Add '{constraint.type_var}' to the forall "
                            f"clause: forall<{constraint.type_var} where "
                            f"{constraint.ability_name}"
                            f"<{constraint.type_var}>>",
                        spec_ref='Chapter 9, Section 9.8 "Abilities"',
                        error_code="E181",
                    )

        # 2. Resolve parameter and return types
        param_types = tuple(self._resolve_type(p) for p in decl.params)
        return_type = self._resolve_type(decl.return_type)
        # #1215: the row AND its source order, from one resolution — a bare op
        # name declared by two effects in this row binds the first in SOURCE
        # order, which the frozenset alone cannot say.
        effect_row, effect_order = self._resolve_effect_row_ordered(decl.effect)

        # 2b. Check refinement predicates written directly in the signature —
        # a refinement can reach a param / return via a type argument, e.g.
        # `@Array<{ @Int | @Int.0 > 0 }>` (#861).  Type params are already in
        # scope from step 1.
        for param_te in decl.params:
            self._check_refinement_predicates(param_te)
        self._check_refinement_predicates(decl.return_type)

        # 3. Set context
        self.env.current_return_type = return_type
        self.env.current_effect_row = effect_row
        self.env.current_effect_order = effect_order
        self._effect_ops_used = set()

        # 4. Push scope and bind parameters
        self.env.push_scope()
        param_slot_names: set[str] = set()
        for i, (param_te, param_ty) in enumerate(
                zip(decl.params, param_types)):
            tname = self._type_expr_to_slot_name(param_te)
            param_slot_names.add(tname)
            self.env.bind(tname, param_ty, "param")

        # 5. Check contracts
        for contract in decl.contracts:
            self._check_contract(contract, decl)

        # 6. Check body (pass return type as expected for bidirectional)
        body_type = self._synth_expr(decl.body, expected=return_type)
        if body_type and not isinstance(body_type, UnknownType):
            if not is_subtype(body_type, return_type):
                self._error(
                    decl.body,
                    f"Function '{decl.name}' body has type "
                    f"{pretty_inferred_type(body_type)}, expected "
                    f"{pretty_type(return_type)}.",
                    rationale="The function body's type must match the "
                              "declared return type.",
                    fix="Change the return type or adjust the body "
                        "expression.",
                    spec_ref='Chapter 5, Section 5.2 "Function Declaration Syntax"',
                    error_code="E121",
                )

        # 7. Check effect compliance (basic)
        if isinstance(effect_row, PureEffectRow) and self._effect_ops_used:
            ops_str = ", ".join(sorted(self._effect_ops_used))
            self._error(
                decl,
                f"Pure function '{decl.name}' performs effect operations: "
                f"{ops_str}.",
                rationale="Functions declared with effects(pure) cannot "
                          "call effect operations.",
                fix=f"Declare the appropriate effects, e.g. "
                    f"effects(<{next(iter(self._effect_ops_used), '...')}>).",
                spec_ref='Chapter 5, Section 5.5 "Effect Declaration"',
                error_code="E122",
            )

        # 8. Check where-block functions.
        #    Pop the parent's VALUE-slot scope FIRST so a helper body cannot
        #    resolve the outer function's parameter slots (#969).  spec §5:
        #    where-helpers are always local to the parent and carry their own
        #    mandatory contracts over their own params; an implicit outer-frame
        #    capture would move a value across a contract boundary uncontracted
        #    (DESIGN principles 2 and 5).  The backends already compile each
        #    helper param-rooted, so a body @T.n reaching an outer slot passed
        #    check + verify then crashed compile with a dangling-slot E699.
        #    Now it is an ordinary E130.  Parent TYPE params stay in scope
        #    (restored below, after the loop), matching spec §5's intent that
        #    a generic parent's helpers may be written over @T.  Note the
        #    retention is not load-bearing for resolution today — an absent
        #    type name falls through to the opaque AdtType branch in
        #    _resolve_named_type and monomorphization is call-site-driven —
        #    so no test fails if it is removed; it is kept as the semantics
        #    the spec states.
        self.env.pop_scope()
        if decl.where_fns:
            # Record the parent's param slot types so a failed slot resolution
            # of one of them inside a helper body carries the pass-as-argument
            # hint instead of the generic lower-index hint.
            self._where_helper_outer_tnames.append(frozenset(param_slot_names))
            try:
                for wfn in decl.where_fns:
                    # #815: skip a where-helper rejected for redefining a
                    # built-in (E151 already emitted; it is not registered, so
                    # re-checking would resolve its body against the built-in).
                    if id(wfn) in self._rejected_builtin_redefs:
                        continue
                    self._check_fn(wfn)
            finally:
                self._where_helper_outer_tnames.pop()

        # 9. Restore context
        self._fn_scope_stack.pop()
        self.env.type_params = saved_params
        self.env.current_return_type = saved_return
        self.env.current_effect_row = saved_effect
        self.env.current_effect_order = saved_effect_order

    def _helper_index_sources(
        self, program: ast.Program,
    ) -> list[tuple[str | None, list[ast.FnDecl]]]:
        """(module label, function declarations) for the helper index.

        ``None`` labels this program's own declarations; a resolved
        module is labelled by its dotted path, so E178 can name the file
        the helper lives in.  Transitive modules are included: their
        helpers are no more callable here than a direct import's, and a
        bare call to one fails codegen the same way.
        """
        sources: list[tuple[str | None, list[ast.FnDecl]]] = [(
            None,
            [tld.decl for tld in program.declarations
             if isinstance(tld.decl, ast.FnDecl)],
        )]
        for mod in self._resolved_modules or ():
            sources.append((
                ".".join(mod.path),
                [tld.decl for tld in mod.program.declarations
                 if isinstance(tld.decl, ast.FnDecl)],
            ))
        return sources

    def _fn_info_for_decl(
        self, decl: ast.FnDecl, visibility: str | None = None,
    ) -> FunctionInfo:
        """Build (memoized) the :class:`FunctionInfo` for a specific FnDecl,
        bypassing the flat, last-wins ``env.functions`` registry (#991).

        The checker twin of the verifier's method of the same name: the
        scoped lookup resolves a same-named ``where``-helper to the exact
        decl in scope, not whichever one registered last.  Reuses the shared
        ``build_fn_info`` so the resolved signature is byte-for-byte what
        ``register_fn`` would have stored.  Keyed on ``(id, visibility)`` so
        a cache hit can never return an info built for another visibility.
        """
        key = (id(decl), visibility)
        info = self._scoped_fn_info_cache.get(key)
        if info is None:
            from vera.registration import build_fn_info
            info = build_fn_info(
                self.env, decl,
                self._resolve_type, self._resolve_effect_row,
                visibility=visibility,
            )
            self._scoped_fn_info_cache[key] = info
        return info

    def _lookup_function_scoped(self, name: str) -> FunctionInfo | None:
        """Resolve a bare call name lexically (#991 checker leg).

        The nearest same-named ``where``-helper visible from the function
        currently being checked wins: the innermost stack frame's helpers
        first, then each ancestor's, then the top-level function of that
        name, and finally the flat registry (built-ins / prelude / imports).
        Matches the verifier's ``_scoped_fn_lookup`` and codegen's
        parent-qualified hoist, so all three subsystems agree on
        helper-name scoping.  A helper rejected for redefining a built-in
        (E151, #815) is skipped — the built-in stays canonical.  With an
        empty stack (data invariants, op signatures) this is exactly the
        flat lookup.

        The frame walk is the ONLY route to a helper: since #1307 the flat
        registry holds none, so this returns ``None`` for a helper named
        from outside its parent (reported as E178 at the call site) rather
        than another declaration's helper.

        A handler-clause operator name skips both scoped tiers and resolves
        against the flat registry alone, because that is the only place its
        binding can live: ``check_handle_expr`` installs one there for the
        duration of each clause body.  In a valid program this changes
        nothing — the name is reserved (E153), so no declaration of it
        exists to be found in either tier.  In a program that declares one
        anyway, it stops the rejected declaration from shadowing the clause
        binding and turning correct clause bodies into argument-type errors
        against the user's signature, a second error chasing the first.  The
        other reserved names need no such carve-out: nothing resolves to
        ``old`` or ``match`` at all.
        """
        from vera.checker.registration import _HANDLER_OPERATOR_FN_NAMES
        if name in _HANDLER_OPERATOR_FN_NAMES:
            return self.env.lookup_function(name)
        for frame in reversed(self._fn_scope_stack):
            for wfn in frame.where_fns or ():
                if (wfn.name == name
                        and id(wfn) not in self._rejected_builtin_redefs):
                    return self._fn_info_for_decl(wfn)
        top = self._top_level_fn_infos.get(name)
        if top is not None:
            return top
        return self.env.lookup_function(name)

    @property
    def _user_fn_names(self) -> Container[str]:
        """The checker's function table, as a membership view (#1284).

        What :func:`~vera.slots.bare_call_denotes_user_fn` consults on this
        side: a name is the user's declaration here exactly when
        :meth:`_lookup_function_scoped` resolves it, so the ownership
        predicate reads whatever this checker actually resolves against
        rather than a separate copy that could answer differently.  Codegen
        passes ``_scoped_fns`` — its registry narrowed to the compiling
        declaration's lexical scope (#1299).

        The two are the same scope since #1307: ``register_fn`` no longer
        recurses ``where`` helpers into the flat ``TypeEnv``, so the
        fallback below reaches built-ins, the prelude and imports but no
        helper, and a helper is reachable only through the frame walk —
        exactly the declarations codegen's ``_scoped_fns`` narrows to.  A
        bare call naming a helper from outside its parent therefore
        resolves to nothing on both tables: the checker reports E178 where
        codegen would have had no target, and where the name is an
        operation's, both lower the operation spec §7.4 prescribes.
        """
        return _ScopedFnNames(self._lookup_function_scoped)

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str:
        """Extract the canonical slot name from a type expression used as a
        parameter binding.  The head is the syntactic name — aliases are
        opaque — while type arguments resolve.

        Delegates to :func:`vera.naming.slot_name` (#1208), which is the ONE
        renderer of that rule; the six subsystems that used to answer this
        question independently disagreed about aliases, and a name minted one
        way and looked up another misses silently.  The argument diagnostics
        the old in-place composition emitted as a side effect are preserved
        by ``_check_slot_name_args`` — see its docstring.
        """
        self._check_slot_name_args(te)
        return naming.slot_name(te, self._naming_env())

    # -----------------------------------------------------------------
    # Contracts
    # -----------------------------------------------------------------

    def _check_contract(self, contract: ast.Contract,
                        fn: ast.FnDecl) -> None:
        """Check a contract clause for well-formedness."""
        if isinstance(contract, ast.Requires):
            self.env.in_contract = True
            ty = self._synth_expr(contract.expr)
            self.env.in_contract = False
            if ty and not is_subtype(ty, BOOL):
                self._error(
                    contract.expr,
                    f"requires() predicate must be Bool, found "
                    f"{pretty_inferred_type(ty)}.",
                    rationale="Contract predicates must evaluate to Bool.",
                    fix="Turn the requires() argument into a Bool-valued "
                        "predicate, e.g. requires(@Int.0 > 0) instead of "
                        "requires(@Int.0).",
                    spec_ref='Chapter 6, Section 6.2.1 "Preconditions (`requires`)"',
                    error_code="E123",
                )

        elif isinstance(contract, ast.Ensures):
            self.env.in_ensures = True
            self.env.in_contract = True
            ty = self._synth_expr(contract.expr)
            self.env.in_ensures = False
            self.env.in_contract = False
            if ty and not is_subtype(ty, BOOL):
                self._error(
                    contract.expr,
                    f"ensures() predicate must be Bool, found "
                    f"{pretty_inferred_type(ty)}.",
                    rationale="Contract predicates must evaluate to Bool.",
                    fix="Turn the ensures() argument into a Bool-valued "
                        "predicate over the result, e.g. "
                        "ensures(@Int.result > 0) instead of "
                        "ensures(@Int.result).",
                    spec_ref='Chapter 6, Section 6.2.2 "Postconditions (`ensures`)"',
                    error_code="E124",
                )

        elif isinstance(contract, ast.Decreases):
            self.env.in_contract = True
            for expr in contract.exprs:
                ty = self._synth_expr(expr)
                # #1172: every measure component must carry a well-founded
                # ordering (spec §5.6.1(3)): Nat, Int (floored at zero by
                # the runtime guard), or a constructor-backed algebraic
                # data type (ordered by structural size).  Anything else —
                # Float64 (decreases forever without crossing a floor),
                # String/Bool/Byte (no decrease order), collections,
                # function types, bare type variables — has no ordering
                # the prover or the runtime guard could enforce, and
                # accepting it silently made the decreases clause
                # decorative.  A refinement measures as its base type; an
                # upstream type error (UnknownType) stays silent to avoid
                # cascading.
                if ty is None:
                    continue
                # Unwrap refinement layers in a loop, not once: a
                # refinement-over-refinement (`{ { @Int | P } | Q }`,
                # the shape `_check_one_refinement_predicate` names) is
                # still ordered by its underlying base.
                base: Type = ty
                while isinstance(base, RefinedType):
                    base = base.base
                if isinstance(base, UnknownType):
                    continue
                well_founded = (
                    base in (INT, NAT)
                    or (
                        isinstance(base, AdtType)
                        and base.name in self.env.data_types
                    )
                )
                if not well_founded:
                    self._error(
                        expr,
                        f"decreases() measure must have a well-founded "
                        f"ordering (Nat, Int, or a data type), found "
                        f"{pretty_inferred_type(ty)}.",
                        rationale="Termination is proved (or checked at "
                                  "runtime) by showing the measure "
                                  "strictly decreases and stays "
                                  "non-negative; a type without that "
                                  "order cannot bound recursion.",
                        fix="Measure something that shrinks toward a "
                            "floor: a Nat/Int counter (e.g. "
                            "decreases(@Nat.0)), a shrinking structure "
                            "(decreases(@List.0)), or a derived size "
                            "(decreases(array_length(@Array<Int>.0))).",
                        spec_ref='Chapter 5, Section 5.6.1 '
                                 '"Decreases Clauses"',
                        error_code="E127",
                    )
            self.env.in_contract = False

    # -----------------------------------------------------------------
    # Refinement predicates (#861)
    # -----------------------------------------------------------------

    def _check_refinement_predicates(self, te: ast.TypeExpr) -> None:
        """Type-check every refinement predicate reachable from *te*.

        A refinement predicate is a *logical* predicate over the refined
        binder (§2.6): `{ @Int | @Int.0 > 0 }`.  Before #861 the predicate
        skipped well-formedness checking entirely — the alias only had its
        *base* resolved (`_register_alias`) — so a non-Bool predicate
        (`{ @Int | @Int.0 }`) or an ill-typed one (`{ @String | @String.0 < 3 }`)
        passed `vera check`.  This is the refinement counterpart of
        `_check_contract`: the predicate must type as Bool — rejected with
        the dedicated code E126, following the registry's one-code-per-
        predicate-position convention (E120 data invariant, E123
        precondition, E124 postcondition) — and its operands are typed by
        the ordinary checker rules.

        Refinements reach the checker not only as a top-level alias body but
        nested inside type arguments (`Array<{ @Int | P }>`) and function-type
        components, so this walks the whole `TypeExpr` tree.  Every
        `type_expr` grammar position routes through this walker: alias
        bodies, fn / anonymous-fn signatures, constructor fields, effect and
        ability op signatures, let / destructure annotations, match binding
        patterns, forall / exists binders, and handler state / clause-param /
        with-clause annotations (PR #876 review — the first pass wired only
        the first three, and a let-annotation escape crashed `vera verify`
        with a raw Z3Exception on the untyped predicate).
        """
        if isinstance(te, ast.RefinementType):
            # Base first: a refinement can nest in its own base
            # (`{ { @Int | P } | Q }`) or reach one via the base's args.
            self._check_refinement_predicates(te.base_type)
            self._check_one_refinement_predicate(te)
            return
        if isinstance(te, ast.NamedType):
            if te.type_args:
                for arg in te.type_args:
                    self._check_refinement_predicates(arg)
            return
        if isinstance(te, ast.FnType):
            for p in te.params:
                self._check_refinement_predicates(p)
            self._check_refinement_predicates(te.return_type)

    def _check_one_refinement_predicate(
        self, te: ast.RefinementType,
    ) -> None:
        """Check a single refinement predicate for well-formedness (Bool)."""
        # Bind the predicate's binder `@<base>.0` to the resolved base type,
        # exactly as the verifier / codegen close the predicate over it.
        binder_name = self._type_expr_to_slot_name(te.base_type)
        resolved_base = self._resolve_type(te.base_type)

        # The binder is the SOLE slot in scope (spec §2.6) — isolate the
        # scope stack rather than pushing on top of it, or a predicate
        # checked at a site with live bindings (a fn body, where-helper,
        # handler clause) could resolve slots beyond its binder, e.g.
        # `let @{ @Int | @Int.0 > @Int.1 } = 5;` reaching the enclosing
        # fn's parameter (PR #876 review).
        saved_scopes = self.env.isolate_scopes()
        self.env.bind(binder_name, resolved_base, "refinement")
        saved_in_contract = self.env.in_contract
        self.env.in_contract = True
        # Push this predicate's RESOLVED base for the Byte-literal
        # allowance — a stack keyed per-predicate, so a predicate nested
        # through a forall/exists binder uses its OWN base, not the
        # enclosing predicate's (PR #876 review).
        self.env.refinement_bases.append(resolved_base)
        try:
            ty = self._synth_expr(te.predicate)
        finally:
            self.env.refinement_bases.pop()
            self.env.in_contract = saved_in_contract
            self.env.restore_scopes(saved_scopes)

        if ty and not is_subtype(ty, BOOL):
            self._error(
                te.predicate,
                f"Refinement predicate must be Bool, found "
                f"{pretty_inferred_type(ty)}.",
                rationale="A refinement type `{ @T | P }` constrains its base "
                          "with a logical predicate `P`, which must evaluate to "
                          "Bool — the same rule contract predicates follow.",
                fix="Turn the predicate into a Bool-valued expression over the "
                    "binder, e.g. `{ @Int | @Int.0 > 0 }` instead of "
                    "`{ @Int | @Int.0 }`.",
                spec_ref='Chapter 2, Section 2.6 "Refinement Types"',
                error_code="E126",
            )
