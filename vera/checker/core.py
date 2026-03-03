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

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from vera.resolver import ResolvedModule

from vera import ast
from vera.errors import Diagnostic, SourceLocation
from vera.environment import (
    AdtInfo,
    TypeEnv,
)
from vera.types import (
    BOOL,
    PureEffectRow,
    TypeVar,
    UnknownType,
    canonical_type_name,
    is_subtype,
    pretty_type,
)

from vera.checker.resolution import ResolutionMixin
from vera.checker.modules import ModulesMixin
from vera.checker.registration import RegistrationMixin
from vera.checker.expressions import ExpressionsMixin
from vera.checker.calls import CallsMixin
from vera.checker.control import ControlFlowMixin


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
        self.source = source
        self.file = file
        self._effect_ops_used: set[str] = set()
        # Resolved modules (C7a: paths for diagnostics, C7b: full list
        # for cross-module type merging).
        self._resolved_modules: list[ResolvedModule] = (
            resolved_modules or []
        )
        self._resolved_module_paths: set[tuple[str, ...]] = {
            m.path for m in self._resolved_modules
        }
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
        # C7c: unfiltered module declarations (for "is private" errors).
        self._module_all_functions: dict[
            tuple[str, ...], dict[str, object]
        ] = {}
        self._module_all_data_types: dict[
            tuple[str, ...], dict[str, AdtInfo]
        ] = {}
        # De-dup removed-alias errors (emitted once per alias name).
        self._reported_alias_errors: set[str] = set()

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
        for tld in program.declarations:
            self._check_decl(tld.decl)

    def _check_decl(self, decl: ast.Decl) -> None:
        """Check a single declaration."""
        if isinstance(decl, ast.FnDecl):
            self._check_fn(decl)
        elif isinstance(decl, ast.DataDecl):
            self._check_data(decl)
        # TypeAliasDecl and EffectDecl are validated during registration

    def _check_data(self, decl: ast.DataDecl) -> None:
        """Check an ADT declaration (invariant well-formedness)."""
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
                    spec_ref='Chapter 2, Section 2.5 "Algebraic Data Types"',
                    error_code="E120",
                )

            self.env.type_params = saved_params
            self.env.pop_scope()

    def _check_fn(self, decl: ast.FnDecl) -> None:
        """Check a function declaration."""
        saved_params = dict(self.env.type_params)
        saved_return = self.env.current_return_type
        saved_effect = self.env.current_effect_row

        # 1. Bind forall type parameters
        if decl.forall_vars:
            for tv in decl.forall_vars:
                self.env.type_params[tv] = TypeVar(tv)

        # 2. Resolve parameter and return types
        param_types = tuple(self._resolve_type(p) for p in decl.params)
        return_type = self._resolve_type(decl.return_type)
        effect_row = self._resolve_effect_row(decl.effect)

        # 3. Set context
        self.env.current_return_type = return_type
        self.env.current_effect_row = effect_row
        self._effect_ops_used = set()

        # 4. Push scope and bind parameters
        self.env.push_scope()
        for i, (param_te, param_ty) in enumerate(
                zip(decl.params, param_types)):
            tname = self._type_expr_to_slot_name(param_te)
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
                    f"{pretty_type(body_type)}, expected "
                    f"{pretty_type(return_type)}.",
                    rationale="The function body's type must match the "
                              "declared return type.",
                    fix=f"Change the return type or adjust the body "
                        f"expression.",
                    spec_ref='Chapter 5, Section 5.1 "Function Declarations"',
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
                spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
                error_code="E122",
            )

        # 8. Check where-block functions
        if decl.where_fns:
            for wfn in decl.where_fns:
                self._check_fn(wfn)

        # 9. Restore context
        self.env.pop_scope()
        self.env.type_params = saved_params
        self.env.current_return_type = saved_return
        self.env.current_effect_row = saved_effect

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str:
        """Extract the canonical slot name from a type expression used as a
        parameter binding.  This is the syntactic name — aliases are opaque."""
        if isinstance(te, ast.NamedType):
            if te.type_args:
                resolved_args = tuple(
                    self._resolve_type(a) for a in te.type_args)
                return canonical_type_name(te.name, resolved_args)
            return te.name
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_slot_name(te.base_type)
        if isinstance(te, ast.FnType):
            # Function-typed parameters: use a synthetic name
            return "Fn"
        return "?"

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
                    f"{pretty_type(ty)}.",
                    rationale="Contract predicates must evaluate to Bool.",
                    spec_ref='Chapter 6, Section 6.2.1 "Preconditions"',
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
                    f"{pretty_type(ty)}.",
                    rationale="Contract predicates must evaluate to Bool.",
                    spec_ref='Chapter 6, Section 6.2.2 "Postconditions"',
                    error_code="E124",
                )

        elif isinstance(contract, ast.Decreases):
            self.env.in_contract = True
            for expr in contract.exprs:
                ty = self._synth_expr(expr)
                # Type is checked; termination verification is Tier 3
            self.env.in_contract = False
