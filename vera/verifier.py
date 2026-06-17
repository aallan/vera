"""Vera contract verifier — Z3-backed contract checking.

Verifies that function contracts (requires/ensures/decreases) are
semantically valid using the Z3 SMT solver.  Consumes a type-checked
Program AST and produces diagnostics with counterexamples.

Tier 1: decidable fragment (QF_LIA + length + Boolean).
Tier 3: graceful fallback for unsupported constructs.

See spec/06-contracts.md for the full verification specification.
"""

from __future__ import annotations

import z3

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from vera import ast
from vera.environment import ConstructorInfo, FunctionInfo, TypeEnv

if TYPE_CHECKING:
    from vera.resolver import ResolvedModule
from vera.errors import Diagnostic, SourceLocation
from vera.obligations.core import (
    ObligationKind,
    ObligationStatus,
    ProofObligation,
    expr_text_for,
)
from vera.slots import slot_table
from vera.smt import SlotEnv, SmtContext
from vera.types import (
    BOOL,
    FLOAT64,
    INT,
    NAT,
    STRING,
    UNIT,
    AdtType,
    EffectRowType,
    FunctionType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    contains_typevar,
    substitute,
)


# =====================================================================
# Public API
# =====================================================================

@dataclass
class VerifySummary:
    """Counts of contracts by verification outcome."""

    tier1_verified: int = 0
    tier3_runtime: int = 0
    assumptions: int = 0
    total: int = 0


@dataclass
class VerifyResult:
    """Result of contract verification."""

    diagnostics: list[Diagnostic]
    summary: VerifySummary
    # #222 Phase A: reified obligations, one per discharge site, in
    # discharge order.  Empty-list default keeps existing constructors
    # (tests, tooling) source-compatible.
    obligations: list[ProofObligation] = field(default_factory=list)


def verify(
    program: ast.Program,
    source: str = "",
    file: str | None = None,
    timeout_ms: int = 10_000,
    resolved_modules: list[ResolvedModule] | None = None,
    expr_types: dict[tuple[int, int, int, int], Type] | None = None,
    expr_target_types: dict[tuple[int, int, int, int], Type] | None = None,
) -> VerifyResult:
    """Verify contracts in a type-checked Vera Program AST.

    Returns a VerifyResult with diagnostics and a verification summary.
    The program must already have passed type checking (C3).

    *resolved_modules* provides imported module ASTs for cross-module
    contract verification (C7d).  Imported function preconditions are
    checked at call sites; postconditions are assumed.
    """
    if expr_types is None and expr_target_types is None:
        # #747: when the caller didn't supply the checker's semantic-type
        # side-tables, collect them here so a bare verify() matches the CLI
        # (cmd_verify) and LSP (VerificationSession) paths — both of which
        # thread them — keeping the warm/cold differential oracle and any
        # external caller consistent.  Lazy import avoids a module cycle.
        from vera.checker import typecheck_with_artifacts
        _diags, _arts = typecheck_with_artifacts(
            program, source, file=file, resolved_modules=resolved_modules,
        )
        expr_types = _arts.expr_semantic_types
        expr_target_types = _arts.expr_target_types
    verifier = ContractVerifier(
        source=source, file=file, timeout_ms=timeout_ms,
        resolved_modules=resolved_modules,
        expr_types=expr_types, expr_target_types=expr_target_types,
    )
    verifier.verify_program(program)
    return VerifyResult(
        diagnostics=verifier.errors,
        summary=verifier.summary,
        obligations=verifier.obligations,
    )


# =====================================================================
# Contract verifier
# =====================================================================

class ContractVerifier:
    """Walks the AST, generates VCs, and submits them to Z3."""

    def __init__(
        self,
        source: str = "",
        file: str | None = None,
        timeout_ms: int = 10_000,
        resolved_modules: list[ResolvedModule] | None = None,
        shared_smt: SmtContext | None = None,
        expr_types: dict[tuple[int, int, int, int], Type] | None = None,
        expr_target_types: dict[tuple[int, int, int, int], Type] | None = None,
    ) -> None:
        self.env = TypeEnv()
        self.errors: list[Diagnostic] = []
        self.summary = VerifySummary()
        # #222 Phase A: reified obligations in discharge order.
        self.obligations: list[ProofObligation] = []
        # Warm-session hook: when provided (by
        # obligations.session.VerificationSession), _verify_fn calls
        # shared_smt.reset() per function instead of constructing a
        # fresh SmtContext — reusing one z3.Solver across the whole
        # program.  None (the default) preserves the historical
        # fresh-context-per-function cold path exactly.
        self._shared_smt = shared_smt
        self.source = source
        self.file = file
        self.timeout_ms = timeout_ms
        self._resolved_modules: list[ResolvedModule] = (
            resolved_modules or []
        )
        # Per-module function registries for ModuleCall lookup (C7d)
        self._module_functions: dict[
            tuple[str, ...], dict[str, FunctionInfo]
        ] = {}
        # Import name filter from ImportDecl nodes
        self._import_names: dict[
            tuple[str, ...], set[str] | None
        ] = {}
        # #747: checker-provided span-keyed semantic-type side-tables
        # (from typecheck_with_artifacts).  Empty when a caller verifies
        # without collecting them (the imported-module sub-verifier, or a
        # bare verify() with no tables) — the projection /
        # generic-instantiation narrowing sites then stay deferred
        # exactly as pre-#747.
        self._expr_types: dict[tuple[int, int, int, int], Type] = (
            expr_types or {}
        )
        self._expr_target_types: dict[tuple[int, int, int, int], Type] = (
            expr_target_types or {}
        )

    # -----------------------------------------------------------------
    # #747: checker-provided expression types (span-keyed)
    # -----------------------------------------------------------------

    @staticmethod
    def _span_key(expr: ast.Expr) -> tuple[int, int, int, int] | None:
        sp = getattr(expr, "span", None)
        if sp is None:
            return None
        return (sp.line, sp.column, sp.end_line, sp.end_column)

    def _resolved_type_of(self, expr: ast.Expr) -> Type | None:
        """The checker's synthesised *result* type for *expr* (#747).

        ``None`` when the side-table wasn't collected or the node has no
        span — callers treat that as "unknown" and fall back to the
        pre-#747 static checks, never as a positive @Nat answer.
        """
        key = self._span_key(expr)
        return self._expr_types.get(key) if key is not None else None

    def _target_type_of(self, expr: ast.Expr) -> Type | None:
        """The instantiated *expected* type *expr* was checked against
        (#747) — the @Nat target at a generic call / construction site;
        ``None`` semantics as :py:meth:`_resolved_type_of`.
        """
        key = self._span_key(expr)
        return self._expr_target_types.get(key) if key is not None else None

    def _nat_binding_target(
        self, arg: ast.Expr, formal: Type | None
    ) -> bool:
        """True if *arg* narrows into a binding slot whose declared or
        *instantiated* type is @Nat.

        A concretely-@Nat *formal* / field obligates without the
        side-table, exactly as #552.  When *formal* is generic (a
        ``TypeVar`` constructor field, effect-op formal, or function
        formal fixed to @Nat at this call site) it is not statically
        @Nat, so we consult the checker's recorded *instantiated target*
        for *arg* (#747).  A concretely-typed non-@Nat formal is never
        second-guessed via the table, so the #552 concrete sites keep
        their table-independent behaviour exactly.
        """
        if formal is not None and self._is_nat_type(formal):
            return True
        if formal is not None and not contains_typevar(formal):
            return False
        target = self._target_type_of(arg)
        return target is not None and self._is_nat_type(target)

    # -----------------------------------------------------------------
    # Diagnostics
    # -----------------------------------------------------------------

    def _error(
        self,
        node: ast.Node,
        description: str,
        *,
        rationale: str = "",
        fix: str = "",
        spec_ref: str = "",
        error_code: str = "",
    ) -> None:
        """Record a verification error."""
        loc = SourceLocation(file=self.file)
        if node.span:
            loc.line = node.span.line
            loc.column = node.span.column
        self.errors.append(Diagnostic(
            description=description,
            location=loc,
            source_line=self._get_source_line(loc.line),
            rationale=rationale,
            fix=fix,
            spec_ref=spec_ref,
            severity="error",
            error_code=error_code,
        ))

    def _warning(
        self,
        node: ast.Node,
        description: str,
        *,
        rationale: str = "",
        spec_ref: str = "",
        error_code: str = "",
        tier: int | None = None,
    ) -> None:
        """Record a verification warning (Tier 3 fallback)."""
        loc = SourceLocation(file=self.file)
        if node.span:
            loc.line = node.span.line
            loc.column = node.span.column
        self.errors.append(Diagnostic(
            description=description,
            location=loc,
            source_line=self._get_source_line(loc.line),
            rationale=rationale,
            spec_ref=spec_ref,
            severity="warning",
            error_code=error_code,
            tier=tier,
        ))

    def _get_source_line(self, line: int) -> str:
        """Extract a line from the source text."""
        lines = self.source.splitlines()
        if 1 <= line <= len(lines):
            return lines[line - 1]
        return ""

    # -----------------------------------------------------------------
    # Obligation recording (#222 Phase A)
    # -----------------------------------------------------------------

    def _record_obligation(
        self,
        fn_name: str,
        kind: ObligationKind,
        node: ast.Expr | ast.Contract,
        status: ObligationStatus,
        *,
        error_code: str = "",
        counterexample: dict[str, str] | None = None,
        span_node: ast.Node | None = None,
    ) -> None:
        """Reify one obligation at its discharge site.

        Purely observational: called at the moment an obligation's
        outcome is known, never altering discharge order or solver
        state.  The summary counters and diagnostics remain the source
        of truth for behaviour; obligations mirror them one-to-one
        (asserted by the differential tests in test_obligations.py).

        *span_node* overrides where the obligation is located when that
        differs from where its expression text comes from — call-site
        preconditions render the callee's contract expression but are
        located at the call site, so two calls violating the same
        precondition stay distinct obligations.
        """
        loc = span_node if span_node is not None else node
        line = loc.span.line if loc.span else 0
        column = loc.span.column if loc.span else 0
        self.obligations.append(ProofObligation(
            fn_name=fn_name,
            kind=kind,
            expr_text=expr_text_for(node),
            status=status,
            line=line,
            column=column,
            error_code=error_code,
            counterexample=counterexample,
        ))

    @staticmethod
    def _contract_kind(contract: ast.Contract) -> ObligationKind:
        """Map a contract AST node to its obligation kind.

        ``Invariant`` (the fourth Contract subclass) is a data-decl
        contract (#686, unimplemented) and never appears in
        ``FnDecl.contracts``; the Decreases fallback is the only other
        function-level contract.
        """
        if isinstance(contract, ast.Requires):
            return "requires"
        if isinstance(contract, ast.Ensures):
            return "ensures"
        return "decreases"

    # -----------------------------------------------------------------
    # Registration pass
    # -----------------------------------------------------------------

    def _register_all(self, program: ast.Program) -> None:
        """Register all declarations (lightweight pass for forward refs)."""
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                self._register_fn(decl, visibility=tld.visibility)
            elif isinstance(decl, ast.DataDecl):
                self._register_data(decl)
            elif isinstance(decl, ast.EffectDecl):
                self._register_effect(decl)
            elif isinstance(decl, ast.TypeAliasDecl):
                self._register_alias(decl)
            elif isinstance(decl, ast.AbilityDecl):
                self._register_ability(decl)

    def _register_fn(
        self, decl: ast.FnDecl, visibility: str | None = None,
    ) -> None:
        """Register a function signature and its contracts."""
        from vera.registration import register_fn
        register_fn(
            self.env, decl,
            self._resolve_type, self._resolve_effect_row,
            visibility=visibility,
        )

    def _register_data(self, decl: ast.DataDecl) -> None:
        """Register an ADT with constructor info for SMT translation."""
        from vera.environment import AdtInfo, ConstructorInfo
        # Set up type params for resolving constructor field types
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)
        ctors: dict[str, ConstructorInfo] = {}
        for ctor in decl.constructors:
            field_types = None
            if ctor.fields is not None:
                field_types = tuple(
                    self._resolve_type(f) for f in ctor.fields)
            ctors[ctor.name] = ConstructorInfo(
                name=ctor.name,
                parent_type=decl.name,
                parent_type_params=decl.type_params,
                field_types=field_types,
            )
        self.env.data_types[decl.name] = AdtInfo(
            name=decl.name,
            type_params=decl.type_params,
            constructors=ctors,
        )
        self.env.type_params = saved_params

    def _register_effect(self, decl: ast.EffectDecl) -> None:
        """Register an effect declaration.

        Populates an ``OpInfo`` per declared operation (mirroring
        :py:meth:`_register_ability`) so the binding-site walker's
        ``lookup_effect_op`` sees user-effect signatures — a user effect's
        @Nat-parameter narrowing is obligated just like built-in
        ``IO.sleep`` (#552 / PR #748 review).
        """
        from vera.environment import EffectInfo, OpInfo
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)
        ops: dict[str, OpInfo] = {}
        for op in decl.operations:
            param_types = tuple(
                self._resolve_type(p) for p in op.param_types)
            ret_type = self._resolve_type(op.return_type)
            ops[op.name] = OpInfo(op.name, param_types, ret_type,
                                  decl.name)
        self.env.effects[decl.name] = EffectInfo(
            name=decl.name,
            type_params=decl.type_params,
            operations=ops,
        )
        self.env.type_params = saved_params

    def _register_alias(self, decl: ast.TypeAliasDecl) -> None:
        """Register a type alias."""
        from vera.environment import TypeAliasInfo
        resolved = self._resolve_type(decl.type_expr)
        self.env.type_aliases[decl.name] = TypeAliasInfo(
            name=decl.name,
            type_params=decl.type_params,
            resolved_type=resolved,
        )

    def _register_ability(self, decl: ast.AbilityDecl) -> None:
        """Register an ability declaration."""
        from vera.environment import AbilityInfo, OpInfo
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)
        ops: dict[str, OpInfo] = {}
        for op in decl.operations:
            param_types = tuple(
                self._resolve_type(p) for p in op.param_types)
            ret_type = self._resolve_type(op.return_type)
            ops[op.name] = OpInfo(op.name, param_types, ret_type,
                                  decl.name)
        self.env.abilities[decl.name] = AbilityInfo(
            name=decl.name,
            type_params=decl.type_params,
            operations=ops,
        )
        self.env.type_params = saved_params

    # -----------------------------------------------------------------
    # Cross-module registration (C7d)
    # -----------------------------------------------------------------

    def _register_modules(self, program: ast.Program) -> None:
        """Register imported function contracts for cross-module verification.

        Mirrors the checker's ``_register_modules`` pattern (C7b):
        1. Build import-name filter from ImportDecl nodes.
        2. For each resolved module, register in isolation and harvest
           public function signatures (including contracts).
        3. Inject into ``self.env.functions`` for bare-call lookup.
        4. Store per-module dicts for ModuleCall qualified lookup.
        """
        if not self._resolved_modules:
            return

        # 1. Build import filter
        for imp in program.imports:
            self._import_names[imp.path] = (
                set(imp.names) if imp.names is not None else None
            )

        # Snapshot builtin function names
        _builtins = TypeEnv()
        builtin_fn_names = set(_builtins.functions)

        # 2. Register each module in isolation
        for mod in self._resolved_modules:
            temp = ContractVerifier(source=mod.source)
            temp._register_all(mod.program)

            # All module-declared functions (exclude builtins)
            all_fns = {
                k: v for k, v in temp.env.functions.items()
                if k not in builtin_fn_names or v.span is not None
            }

            # 3. Filter to public only
            mod_fns = {
                k: v for k, v in all_fns.items()
                if v.visibility == "public"
            }

            self._module_functions[mod.path] = mod_fns

            # 4. Inject into self.env for bare calls
            name_filter = self._import_names.get(mod.path)
            for fn_name, fn_info in mod_fns.items():
                if name_filter is None or fn_name in name_filter:
                    self.env.functions.setdefault(fn_name, fn_info)

    def _lookup_module_function(
        self, path: tuple[str, ...], name: str,
    ) -> FunctionInfo | None:
        """Look up a function in a specific module's public registry."""
        mod_fns = self._module_functions.get(path)
        if mod_fns is None:
            return None
        return mod_fns.get(name)

    # -----------------------------------------------------------------
    # Type resolution (simplified — reuses TypeEnv patterns)
    # -----------------------------------------------------------------

    def _resolve_type(self, te: ast.TypeExpr) -> Type:
        """Resolve a type expression to a semantic Type."""
        if isinstance(te, ast.NamedType):
            # Check type params first
            if te.name in self.env.type_params:
                return self.env.type_params[te.name]
            # Check type aliases
            if te.name in self.env.type_aliases:
                alias = self.env.type_aliases[te.name]
                return alias.resolved_type
            # Check ADTs
            if te.name in self.env.data_types:
                args: tuple[Type, ...] = ()
                if te.type_args:
                    args = tuple(self._resolve_type(a) for a in te.type_args)
                return AdtType(te.name, args)
            # Check primitives
            from vera.types import PRIMITIVES
            if te.name in PRIMITIVES:
                return PRIMITIVES[te.name]
            # Unknown — treat as opaque but preserve type args
            return AdtType(te.name, tuple(
                self._resolve_type(a) for a in te.type_args
            ) if te.type_args else ())

        if isinstance(te, ast.RefinementType):
            base = self._resolve_type(te.base_type)
            return RefinedType(base, te.predicate)

        if isinstance(te, ast.FnType):
            params = tuple(self._resolve_type(p) for p in te.params)
            ret = self._resolve_type(te.return_type)
            return FunctionType(params, ret, PureEffectRow())

        return UNIT  # pragma: no cover

    def _resolve_effect_row(self, eff: ast.EffectRow) -> EffectRowType:
        """Resolve an effect row."""
        from vera.types import ConcreteEffectRow, EffectInstance
        if isinstance(eff, ast.PureEffect):
            return PureEffectRow()
        if isinstance(eff, ast.EffectSet):
            effects = []
            for e in eff.effects:
                if not isinstance(e, ast.EffectRef):  # pragma: no cover
                    continue
                eff_args: tuple[Type, ...] = ()
                if e.type_args:
                    eff_args = tuple(self._resolve_type(a) for a in e.type_args)
                effects.append(EffectInstance(e.name, eff_args))
            return ConcreteEffectRow(frozenset(effects))
        return PureEffectRow()  # pragma: no cover

    # -----------------------------------------------------------------
    # Verification
    # -----------------------------------------------------------------

    def register_program(self, program: ast.Program) -> None:
        """Run the registration passes without verifying anything.

        Public seam for the incremental session (#222 Phase B): the
        session registers the whole program once, then drives
        per-function verification selectively, replaying cached
        results for functions whose inputs are unchanged.
        """
        self._register_modules(program)  # C7d: cross-module imports
        self._register_all(program)      # local declarations shadow imports

    def verify_program(self, program: ast.Program) -> None:
        """Entry point: register modules, then local declarations, then verify."""
        self.register_program(program)
        for tld in program.declarations:
            if isinstance(tld.decl, ast.FnDecl):
                self._verify_fn(tld.decl)

    def _verify_fn(
        self,
        decl: ast.FnDecl,
        parent_where_group: ast.FnDecl | None = None,
    ) -> None:
        """Verify all contracts on a single function."""
        # Skip generic functions (type variables can't be translated to Z3)
        if decl.forall_vars:
            for contract in decl.contracts:
                if not self._is_trivial(contract):
                    self.summary.tier3_runtime += 1
                    self.summary.total += 1
                    self._record_obligation(
                        decl.name, self._contract_kind(contract),
                        contract, "tier3", error_code="E520",
                    )
                    self._warning(
                        contract,
                        f"Cannot statically verify contract in generic function "
                        f"'{decl.name}'. Contract will be checked at runtime.",
                        rationale="Generic functions have type variables that "
                                  "cannot be represented in the SMT solver.",
                        spec_ref='Chapter 6, Section 6.8 "Summary of Verification Tiers"',
                        error_code="E520",
                        tier=3,
                    )
                else:
                    self.summary.tier1_verified += 1
                    self.summary.total += 1
                    self._record_obligation(
                        decl.name, self._contract_kind(contract),
                        contract, "verified",
                    )
            return

        if self._shared_smt is not None:
            # Warm session (#222 Phase A): reuse one z3.Solver across
            # functions.  reset() clears all per-function state (vars,
            # assertions, sorts, path conditions, uninterpreted-fn
            # caches) while the ADT registry persists; the lookups are
            # rebound because they close over this verifier's env.
            smt = self._shared_smt
            smt.reset()
            smt._fn_lookup = self.env.lookup_function
            smt._module_fn_lookup = self._lookup_module_function
        else:
            smt = SmtContext(
                timeout_ms=self.timeout_ms,
                fn_lookup=self.env.lookup_function,
                module_fn_lookup=self._lookup_module_function,
            )
        # Register all known ADTs with the SMT context.  Idempotent on
        # the warm path (same AdtInfo re-registered into the persistent
        # registry); kept per-function so cold and warm stay identical.
        for adt_info in self.env.data_types.values():
            smt.register_adt(adt_info)
        slot_env = SlotEnv()

        # 1. Declare Z3 constants for parameters
        param_types = [self._resolve_type(p) for p in decl.params]
        for i, (param_te, param_ty) in enumerate(zip(decl.params, param_types)):
            type_name = self._type_expr_to_slot_name(param_te)
            z3_name = f"@{type_name}.{self._count_slots(slot_env, type_name)}"

            if self._is_nat_type(param_ty):
                var = smt.declare_nat(z3_name)
            elif self._is_bool_type(param_ty):
                var = smt.declare_bool(z3_name)
            elif self._is_string_type(param_ty):
                var = smt.declare_string(z3_name)
            elif self._is_float64_type(param_ty):
                var = smt.declare_float64(z3_name)
            elif self._is_array_type(param_ty):
                # #667 — Array<T> gets a proper uninterpreted sort
                # so `arr[i]` and `[a, b, c]` translate to typed
                # `index_<T>` / array constants rather than falling
                # back to `declare_int` (which made IndexExpr and
                # ArrayLit in contracts return None and drop the
                # predicate to Tier 3).
                array_var = self._declare_array_var(smt, z3_name, param_ty)
                var = array_var if array_var is not None else smt.declare_int(z3_name)
            elif self._is_adt_type(param_ty):
                adt_var = smt.declare_adt(z3_name, param_ty)
                var = adt_var if adt_var is not None else smt.declare_int(z3_name)
            else:
                var = smt.declare_int(z3_name)

            slot_env = slot_env.push(type_name, var)

        # 2. Declare result variable
        ret_type = self._resolve_type(decl.return_type)
        if self._is_nat_type(ret_type):
            result_var = smt.declare_nat("@result")
        elif self._is_bool_type(ret_type):
            result_var = smt.declare_bool("@result")
        elif self._is_string_type(ret_type):
            result_var = smt.declare_string("@result")
        elif self._is_float64_type(ret_type):
            result_var = smt.declare_float64("@result")
        elif self._is_array_type(ret_type):
            array_var = self._declare_array_var(smt, "@result", ret_type)
            result_var = (array_var if array_var is not None
                          else smt.declare_int("@result"))
        elif self._is_adt_type(ret_type):
            adt_var = smt.declare_adt("@result", ret_type)
            result_var = adt_var if adt_var is not None else smt.declare_int("@result")
        else:
            result_var = smt.declare_int("@result")
        smt.set_result_var(result_var)

        # 3. Collect precondition assumptions
        assumptions: list[object] = []  # Z3 BoolRef expressions
        for contract in decl.contracts:
            if isinstance(contract, ast.Requires):
                self.summary.total += 1
                if self._is_trivial(contract):
                    self.summary.tier1_verified += 1
                    self._record_obligation(
                        decl.name, "requires", contract, "verified",
                    )
                    continue
                z3_pre = smt.translate_expr(contract.expr, slot_env)
                if z3_pre is None:
                    self.summary.tier3_runtime += 1
                    self._record_obligation(
                        decl.name, "requires", contract, "tier3",
                        error_code="E521",
                    )
                    self._warning(
                        contract,
                        f"Precondition in '{decl.name}' uses constructs "
                        f"outside the decidable fragment. "
                        f"Contract will be checked at runtime.",
                        rationale="The contract expression contains constructs "
                                  "that cannot be translated to SMT (e.g., "
                                  "pattern matching, effect operations, "
                                  "quantifiers).",
                        spec_ref='Chapter 6, Section 6.8 "Summary of Verification Tiers"',
                        error_code="E521",
                        tier=3,
                    )
                    continue
                assumptions.append(z3_pre)
                self.summary.tier1_verified += 1
                self._record_obligation(
                    decl.name, "requires", contract, "verified",
                )

        # 4. Assert caller assumptions into solver so _translate_call
        #    can see them during body translation.
        for a in assumptions:
            smt.solver.add(a)

        # 5. Translate function body
        body_expr = smt.translate_expr(decl.body, slot_env)

        # 5.5. Check @Nat subtraction underflow obligations (#520).
        #      Walks the body looking for `@Nat - @Nat` sites and emits
        #      an obligation `lhs >= rhs` at each, dischargeable from
        #      preconditions and path conditions.
        #      The walker re-translates let RHSes, conditions, and
        #      subtraction operands; the SMT layer's identity dedup
        #      keeps one call violation per site across those repeat
        #      visits — and lets the walker be the sole recorder for
        #      sites the body pass never translates (#727).
        if decl.body is not None:
            self._walk_for_subtraction_obligations(
                decl, decl.body, smt, slot_env, assumptions,
            )

        # 5.7. Check @Nat binding-site narrowing obligations (#552).
        #      Generalises #520 from @Nat-@Nat subtraction to every
        #      site where an @Int value narrows into a @Nat slot: let
        #      bindings, call arguments, effect-operation arguments,
        #      constructor fields, top-level match binds, and literal-
        #      tuple destructures.  Emits
        #      `value >= 0` at each, discharged from preconditions and
        #      path conditions exactly like #520.  Projection sites
        #      whose source type is not statically resolvable here
        #      (ADT sub-pattern binds, non-literal destructures) are
        #      left unchecked — neither obligated here nor guarded by
        #      codegen — tracked as #747 (needs scrutinee-type inference).
        if decl.body is not None:
            self._walk_for_nat_binding_obligations(
                decl, decl.body, smt, slot_env, assumptions,
            )

        # 6. Report any call-site precondition violations
        for v in smt.drain_call_violations():
            # Phase A records call-site obligations only on violation:
            # successful call-pre checks discharge silently inside the
            # SMT layer's _translate_call and are not yet enumerated
            # (Phase B extends the SMT layer to record successes for
            # the discharge cache).  Summary counters are untouched
            # here, mirroring the existing bookkeeping.  The span comes
            # from the CALL SITE (not the callee's contract node) so
            # two calls violating the same precondition remain distinct
            # obligations; E501 matches _report_call_violation.
            self._record_obligation(
                decl.name, "call_pre", v.precondition, "violated",
                error_code="E501",
                counterexample=v.counterexample,
                span_node=v.call_node,
            )
            self._report_call_violation(
                decl, v.callee_name, v.call_node,
                v.precondition, v.counterexample,
            )

        # 7. Verify ensures clauses
        for contract in decl.contracts:
            if isinstance(contract, ast.Ensures):
                self.summary.total += 1
                if self._is_trivial(contract):
                    self.summary.tier1_verified += 1
                    self._record_obligation(
                        decl.name, "ensures", contract, "verified",
                    )
                    continue

                if body_expr is None:
                    self.summary.tier3_runtime += 1
                    self._record_obligation(
                        decl.name, "ensures", contract, "tier3",
                        error_code="E522",
                    )
                    self._warning(
                        contract,
                        f"Cannot statically verify postcondition in "
                        f"'{decl.name}'. Function body uses constructs "
                        f"outside the decidable fragment. "
                        f"Contract will be checked at runtime.",
                        rationale="The function body contains constructs that "
                                  "cannot be translated to SMT (e.g., "
                                  "effect operations, lambdas, "
                                  "generic calls).",
                        spec_ref='Chapter 6, Section 6.8 "Summary of Verification Tiers"',
                        error_code="E522",
                        tier=3,
                    )
                    continue

                # Translate the postcondition with @T.result → body result
                smt.set_result_var(body_expr)
                z3_post = smt.translate_expr(contract.expr, slot_env)

                if z3_post is None:
                    self.summary.tier3_runtime += 1
                    self._record_obligation(
                        decl.name, "ensures", contract, "tier3",
                        error_code="E523",
                    )
                    self._warning(
                        contract,
                        f"Postcondition in '{decl.name}' uses constructs "
                        f"outside the decidable fragment. "
                        f"Contract will be checked at runtime.",
                        rationale="The postcondition expression contains "
                                  "constructs that cannot be translated to SMT.",
                        spec_ref='Chapter 6, Section 6.8 "Summary of Verification Tiers"',
                        error_code="E523",
                        tier=3,
                    )
                    continue

                # Check: assumptions ==> postcondition
                smt_result = smt.check_valid(z3_post, assumptions)

                if smt_result.status == "verified":
                    self.summary.tier1_verified += 1
                    self._record_obligation(
                        decl.name, "ensures", contract, "verified",
                    )
                elif smt_result.status == "violated":
                    self.summary.total -= 1  # don't count — it's an error
                    self._record_obligation(
                        decl.name, "ensures", contract, "violated",
                        counterexample=smt_result.counterexample,
                    )
                    self._report_violation(
                        decl, contract, smt_result.counterexample
                    )
                else:  # pragma: no cover
                    # unknown / timeout
                    self.summary.tier3_runtime += 1
                    self._record_obligation(
                        decl.name, "ensures", contract, "timeout",
                        error_code="E524",
                    )
                    self._warning(
                        contract,
                        f"Could not verify postcondition in '{decl.name}' "
                        f"within timeout. Contract will be checked at runtime.",
                        rationale="The SMT solver returned 'unknown', which "
                                  "may indicate the formula is too complex or "
                                  "the timeout was reached.",
                        spec_ref='Chapter 6, Section 6.8 "Summary of Verification Tiers"',
                        error_code="E524",
                        tier=3,
                    )

        # 8. Handle decreases clauses — attempt verification
        # Build mutual recursion group for decreases checking
        group_decls: dict[str, ast.FnDecl] = {decl.name: decl}
        if decl.where_fns:
            for wfn in decl.where_fns:
                group_decls[wfn.name] = wfn
        elif parent_where_group is not None:
            group_decls[parent_where_group.name] = parent_where_group
            if parent_where_group.where_fns:
                for wfn in parent_where_group.where_fns:
                    group_decls[wfn.name] = wfn

        for contract in decl.contracts:
            if isinstance(contract, ast.Decreases):
                self.summary.total += 1
                if self._verify_decreases(
                    decl, contract, smt, slot_env, group_decls,
                ):
                    self.summary.tier1_verified += 1
                    self._record_obligation(
                        decl.name, "decreases", contract, "verified",
                    )
                else:
                    self.summary.tier3_runtime += 1
                    self._record_obligation(
                        decl.name, "decreases", contract, "tier3",
                        error_code="E525",
                    )
                    self._warning(
                        contract,
                        f"Termination metric in '{decl.name}' cannot be "
                        f"statically verified yet. "
                        f"Contract will be checked at runtime.",
                        rationale="Self-recursive functions with Nat or "
                                  "structural ADT measures are verified "
                                  "automatically. This function may use "
                                  "a measure that cannot be translated "
                                  "to Z3.",
                        spec_ref='Chapter 5, Section 5.6.1 "Decreases Clauses"',
                        error_code="E525",
                        tier=3,
                    )

        # 9. Verify where-block functions
        if decl.where_fns:
            for wfn in decl.where_fns:
                self._verify_fn(wfn, parent_where_group=decl)

    # -----------------------------------------------------------------
    # Decreases verification (termination)
    # -----------------------------------------------------------------

    def _verify_decreases(
        self,
        decl: ast.FnDecl,
        contract: ast.Decreases,
        smt: SmtContext,
        slot_env: SlotEnv,
        group_decls: dict[str, ast.FnDecl],
    ) -> bool:
        """Attempt to verify a decreases clause.

        Returns True if the measure strictly decreases at every recursive
        call site (including mutual recursion via where-block siblings)
        while remaining non-negative.  Returns False if verification fails
        or the measure cannot be translated.
        """
        if not contract.exprs:  # pragma: no cover
            return False

        # Only support single-expression decreases for now
        measure_expr = contract.exprs[0]
        z3_initial = smt.translate_expr(measure_expr, slot_env)
        if z3_initial is None:  # pragma: no cover
            return False

        # Collect all recursive call sites (self + mutual) with path conds
        group_names = set(group_decls.keys())
        calls = self._collect_recursive_calls(
            decl.name, decl.body, smt, slot_env, group_names,
        )
        if not calls:
            # No recursive calls found → can't verify
            return False

        import z3 as z3mod

        # For each call site, verify the measure decreases
        for callee_name, call_args, z3_path_conds, call_site_env in calls:
            callee_decl = group_decls.get(callee_name, decl)

            # Build callee's slot env from actual arguments
            callee_env = SlotEnv()
            param_type_exprs = list(callee_decl.params)
            if len(call_args) != len(param_type_exprs):  # pragma: no cover
                return False
            for param_te, arg_expr in zip(param_type_exprs, call_args):
                z3_arg = smt.translate_expr(arg_expr, call_site_env)
                if z3_arg is None:  # pragma: no cover
                    return False
                type_name = self._type_expr_to_slot_name(param_te)
                callee_env = callee_env.push(type_name, z3_arg)

            # For cross-calls, use the callee's decreases expression
            callee_measure_expr: ast.Expr
            if callee_name == decl.name:
                callee_measure_expr = measure_expr
            else:
                found = self._find_decreases_expr(callee_decl)
                if found is None:
                    return False  # sibling has no decreases clause
                callee_measure_expr = found

            # Translate the callee's measure in callee's env
            z3_callee_measure = smt.translate_expr(
                callee_measure_expr, callee_env,
            )
            if z3_callee_measure is None:  # pragma: no cover
                return False

            # Verify: path_conds ⟹ measure strictly decreases
            if isinstance(z3_initial.sort(), z3mod.DatatypeSortRef):
                rank_fn = smt.get_rank_fn(z3_initial.sort())
                if rank_fn is None:  # pragma: no cover
                    return False
                decrease_cond = z3mod.And(
                    rank_fn(z3_callee_measure) < rank_fn(z3_initial),
                    rank_fn(z3_callee_measure) >= 0,
                )
            else:
                decrease_cond = z3mod.And(
                    z3_callee_measure < z3_initial,
                    z3_callee_measure >= 0,
                )
            if z3_path_conds:
                premise = (z3mod.And(*z3_path_conds)
                           if len(z3_path_conds) > 1
                           else z3_path_conds[0])
                goal = z3mod.Implies(premise, decrease_cond)
            else:  # pragma: no cover
                goal = decrease_cond

            result = smt.check_valid(goal, [])
            if result.status != "verified":
                return False

        return True

    @staticmethod
    def _find_decreases_expr(decl: ast.FnDecl) -> ast.Expr | None:
        """Extract the first decreases expression from a function's contracts."""
        for c in decl.contracts:
            if isinstance(c, ast.Decreases) and c.exprs:
                return c.exprs[0]
        return None

    def _collect_recursive_calls(
        self,
        fn_name: str,
        expr: ast.Expr,
        smt: SmtContext,
        slot_env: SlotEnv,
        group_names: set[str] | None = None,
    ) -> list[tuple[str, tuple[ast.Expr, ...], list[object], SlotEnv]]:
        """Walk the AST to find recursive call sites.

        Finds calls to *fn_name* and, when *group_names* is supplied, any
        call to a function in the mutual recursion group.  Returns a list
        of ``(callee_name, call_args, z3_path_conditions, slot_env)``
        tuples.
        """
        effective = group_names or {fn_name}
        results: list[tuple[str, tuple[ast.Expr, ...], list[object], SlotEnv]] = []
        self._walk_for_calls(effective, expr, [], results, smt, slot_env)
        return results

    def _walk_for_calls(
        self,
        group_names: set[str],
        expr: ast.Expr,
        z3_path_conds: list[object],
        results: list[tuple[str, tuple[ast.Expr, ...], list[object], SlotEnv]],
        smt: SmtContext,
        slot_env: SlotEnv,
    ) -> None:
        """Recursively walk AST, tracking Z3 path conditions and slot env."""
        if isinstance(expr, ast.FnCall):
            if expr.name in group_names:
                results.append(
                    (expr.name, expr.args, list(z3_path_conds), slot_env),
                )
            # Also walk into arguments (they might contain recursive calls)
            for arg in expr.args:
                self._walk_for_calls(group_names, arg, z3_path_conds, results,
                                     smt, slot_env)
            return

        if isinstance(expr, ast.IfExpr):
            z3_cond = smt.translate_expr(expr.condition, slot_env)
            if z3_cond is not None:
                import z3 as z3mod
                then_conds = z3_path_conds + [z3_cond]
                self._walk_for_calls(group_names, expr.then_branch,
                                     then_conds, results, smt, slot_env)
                else_conds = z3_path_conds + [z3mod.Not(z3_cond)]
                self._walk_for_calls(group_names, expr.else_branch,
                                     else_conds, results, smt, slot_env)
            else:  # pragma: no cover
                self._walk_for_calls(group_names, expr.then_branch,
                                     z3_path_conds, results, smt, slot_env)
                self._walk_for_calls(group_names, expr.else_branch,
                                     z3_path_conds, results, smt, slot_env)
            return

        if isinstance(expr, ast.Block):
            cur_env = slot_env
            for stmt in expr.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._walk_for_calls(group_names, stmt.value,
                                         z3_path_conds, results, smt, cur_env)
                    val = smt.translate_expr(stmt.value, cur_env)
                    if val is not None:
                        type_name = smt._type_expr_to_slot_name(stmt.type_expr)
                        if type_name is not None:
                            cur_env = cur_env.push(type_name, val)
                elif isinstance(stmt, ast.ExprStmt):  # pragma: no cover
                    self._walk_for_calls(group_names, stmt.expr,
                                         z3_path_conds, results, smt, cur_env)
            self._walk_for_calls(group_names, expr.expr, z3_path_conds,
                                 results, smt, cur_env)
            return

        if isinstance(expr, ast.BinaryExpr):
            self._walk_for_calls(group_names, expr.left, z3_path_conds,
                                 results, smt, slot_env)
            self._walk_for_calls(group_names, expr.right, z3_path_conds,
                                 results, smt, slot_env)
            return

        if isinstance(expr, ast.UnaryExpr):
            self._walk_for_calls(group_names, expr.operand, z3_path_conds,
                                 results, smt, slot_env)
            return

        if isinstance(expr, ast.MatchExpr):
            self._walk_for_calls(group_names, expr.scrutinee, z3_path_conds,
                                 results, smt, slot_env)
            scrutinee_z3 = smt.translate_expr(expr.scrutinee, slot_env)
            for arm in expr.arms:
                arm_env = slot_env
                arm_conds = z3_path_conds
                if scrutinee_z3 is not None:
                    bound = smt._bind_pattern(scrutinee_z3, arm.pattern,
                                              slot_env)
                    if bound is not None:
                        arm_env = bound
                    pat_cond = smt._pattern_condition(scrutinee_z3,
                                                      arm.pattern)
                    if pat_cond is not None:
                        arm_conds = z3_path_conds + [pat_cond]
                self._walk_for_calls(group_names, arm.body, arm_conds,
                                     results, smt, arm_env)
            return

        # Other expression types (literals, slot refs, etc.) — no calls
        return

    # -----------------------------------------------------------------
    # @Nat subtraction underflow obligations (#520)
    # -----------------------------------------------------------------

    def _walk_for_subtraction_obligations(
        self,
        decl: ast.FnDecl,
        expr: ast.Expr,
        smt: SmtContext,
        slot_env: SlotEnv,
        assumptions: list[object],
    ) -> None:
        """Walk *expr* checking ``@Nat - @Nat`` sites for underflow.

        Mirrors :py:meth:`_walk_for_calls` structurally, but emits
        proof obligations at subtraction sites rather than collecting
        recursive call sites.  Path conditions are tracked via
        ``smt._path_conditions`` (pushed/popped on if/match branches),
        so :py:meth:`SmtContext.check_valid` picks them up
        automatically when discharging each obligation.

        The walker recurses into BinaryExpr, UnaryExpr, IfExpr, Block,
        FnCall args, and MatchExpr arm bodies.  Other AST node types
        contain no nested expressions that could host an arithmetic
        subtraction, so they terminate the walk.
        """
        if isinstance(expr, ast.FnCall):
            for arg in expr.args:
                self._walk_for_subtraction_obligations(
                    decl, arg, smt, slot_env, assumptions,
                )
            return

        if isinstance(expr, ast.ModuleCall):
            # Module-qualified calls (e.g. `Math.abs(@Int.0)`) can host
            # `@Nat - @Nat` in their args just like FnCall does — recurse.
            for arg in expr.args:
                self._walk_for_subtraction_obligations(
                    decl, arg, smt, slot_env, assumptions,
                )
            return

        if isinstance(expr, ast.ConstructorCall):
            # ADT constructors (e.g. `Some(@Nat.0 - @Nat.1)`) carry
            # arguments that can host the same subtraction shape.  The
            # constructor's *result* type is the ADT, not @Nat — so
            # `_is_nat_typed`/`_has_nat_origin` don't need a branch
            # here — but the args themselves still need walking.
            for arg in expr.args:
                self._walk_for_subtraction_obligations(
                    decl, arg, smt, slot_env, assumptions,
                )
            return

        if isinstance(expr, ast.QualifiedCall):
            # Qualified calls (e.g. `Map.get(...)`) — like FnCall and
            # ModuleCall, args can hold subtraction sites we must
            # check.  The SMT layer doesn't translate QualifiedCall
            # itself, so any obligation rooted ON a QualifiedCall
            # would already drop to Tier 3 via the existing
            # untranslatable-expression path; recursing here only
            # catches obligations rooted INSIDE its args.
            for arg in expr.args:
                self._walk_for_subtraction_obligations(
                    decl, arg, smt, slot_env, assumptions,
                )
            return

        if isinstance(expr, ast.IfExpr):
            # Walk the condition first (before pushing path-cond) — any
            # @Nat-@Nat in the condition is unconditional from the
            # caller's perspective.
            self._walk_for_subtraction_obligations(
                decl, expr.condition, smt, slot_env, assumptions,
            )
            z3_cond = smt.translate_expr(expr.condition, slot_env)
            if z3_cond is not None:
                import z3 as z3mod
                smt._path_conditions.append(z3_cond)
                try:
                    self._walk_for_subtraction_obligations(
                        decl, expr.then_branch, smt, slot_env, assumptions,
                    )
                finally:
                    smt._path_conditions.pop()
                if expr.else_branch is not None:
                    smt._path_conditions.append(z3mod.Not(z3_cond))
                    try:
                        self._walk_for_subtraction_obligations(
                            decl, expr.else_branch, smt, slot_env,
                            assumptions,
                        )
                    finally:
                        smt._path_conditions.pop()
            else:  # pragma: no cover — condition untranslatable
                self._walk_for_subtraction_obligations(
                    decl, expr.then_branch, smt, slot_env, assumptions,
                )
                if expr.else_branch is not None:
                    self._walk_for_subtraction_obligations(
                        decl, expr.else_branch, smt, slot_env, assumptions,
                    )
            return

        if isinstance(expr, ast.Block):
            cur_env = slot_env
            for stmt in expr.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._walk_for_subtraction_obligations(
                        decl, stmt.value, smt, cur_env, assumptions,
                    )
                    val = smt.translate_expr(stmt.value, cur_env)
                    if val is not None:
                        type_name = smt._type_expr_to_slot_name(stmt.type_expr)
                        if type_name is not None:
                            cur_env = cur_env.push(type_name, val)
                elif isinstance(stmt, ast.ExprStmt):  # pragma: no cover
                    self._walk_for_subtraction_obligations(
                        decl, stmt.expr, smt, cur_env, assumptions,
                    )
            self._walk_for_subtraction_obligations(
                decl, expr.expr, smt, cur_env, assumptions,
            )
            return

        if isinstance(expr, ast.BinaryExpr):
            # Recurse first so nested subtractions are checked even
            # when the outer expression isn't @Nat-typed.
            self._walk_for_subtraction_obligations(
                decl, expr.left, smt, slot_env, assumptions,
            )
            self._walk_for_subtraction_obligations(
                decl, expr.right, smt, slot_env, assumptions,
            )
            if (expr.op == ast.BinOp.SUB
                    and self._is_nat_typed(expr.left)
                    and self._is_nat_typed(expr.right)
                    and (self._has_nat_origin(expr.left)
                         or self._has_nat_origin(expr.right))):
                # Both operands are @Nat-typed AND at least one
                # has Nat-flowed origin (a slot ref, function
                # return, or a recursive expression containing
                # one).  Pure-literal subtractions like `0 - 1`
                # — the common "I want -1" idiom — are
                # intentionally skipped at Path A scope (#520);
                # binding-site narrowing into a @Nat slot is
                # Path B (#552).
                self._check_subtraction_obligation(
                    decl, expr, smt, slot_env, assumptions,
                )
            return

        if isinstance(expr, ast.UnaryExpr):
            self._walk_for_subtraction_obligations(
                decl, expr.operand, smt, slot_env, assumptions,
            )
            return

        if isinstance(expr, ast.MatchExpr):
            self._walk_for_subtraction_obligations(
                decl, expr.scrutinee, smt, slot_env, assumptions,
            )
            scrutinee_z3 = smt.translate_expr(expr.scrutinee, slot_env)
            for arm in expr.arms:
                arm_env = slot_env
                pat_cond = None
                if scrutinee_z3 is not None:
                    bound = smt._bind_pattern(
                        scrutinee_z3, arm.pattern, slot_env,
                    )
                    if bound is not None:
                        arm_env = bound
                    pat_cond = smt._pattern_condition(
                        scrutinee_z3, arm.pattern,
                    )
                if pat_cond is not None:
                    smt._path_conditions.append(pat_cond)
                    try:
                        self._walk_for_subtraction_obligations(
                            decl, arm.body, smt, arm_env, assumptions,
                        )
                    finally:
                        smt._path_conditions.pop()
                else:
                    self._walk_for_subtraction_obligations(
                        decl, arm.body, smt, arm_env, assumptions,
                    )
            return

        # Other expression types (literals, slot refs, quantifiers,
        # closures, indexing, etc.) — no nested arithmetic to walk.
        return

    def _lookup_constructor_info(self, name: str) -> ConstructorInfo | None:
        """Find a constructor's info from either registry.

        ``lookup_constructor`` searches only the flat ``constructors``
        dict that built-ins (``Some`` / ``Ok`` / …) register into;
        :py:meth:`_register_data` files user ``data`` constructors under
        ``data_types[...].constructors`` instead, so look there too.
        """
        ci = self.env.lookup_constructor(name)
        if ci is not None:
            return ci
        for adt in self.env.data_types.values():
            if name in adt.constructors:
                return adt.constructors[name]
        return None

    def _walk_for_nat_binding_obligations(
        self,
        decl: ast.FnDecl,
        expr: ast.Expr,
        smt: SmtContext,
        slot_env: SlotEnv,
        assumptions: list[object],
    ) -> None:
        """Walk *expr* emitting ``value >= 0`` at @Int→@Nat narrowing sites.

        The binding-site generalisation of #520
        (:py:meth:`_walk_for_subtraction_obligations`).  Fires wherever
        an @Int-typed value flows into a freshly-declared @Nat slot:

        * ``let @Nat = <Int>``                  — let bindings;
        * ``f(<Int>)`` with an @Nat formal      — call arguments;
        * ``E.op(<Int>)`` with an @Nat formal   — effect-operation args;
        * ``Ctor(<Int>)`` with an @Nat field    — constructor fields;
        * ``match <Int> { @Nat -> ... }``       — top-level match binds;
        * ``let Tuple<@Nat, ...> = Tuple(<Int>, ...)`` — destructuring a
          literal tuple.

        The obligation fires when ``_narrows_into_nat(value)`` — either a
        genuine @Int narrowing, or a statically-@Nat value whose tree
        contains a pure-literal subtraction (``0 - 1``) that #520 defers.
        This keeps #552 disjoint from #520's @Nat-@Nat (with @Nat origin)
        obligation so the two never co-fire on one site.  Path conditions
        are tracked via ``smt._path_conditions`` so
        :py:meth:`SmtContext.check_valid` discharges each obligation under
        the in-scope branch guards.

        Projection sites whose *source* type the verifier cannot resolve
        statically — ADT sub-pattern binds (``Some(@Nat.0)``) and
        non-literal tuple destructures — are deliberately left unchecked
        (tracked as #747) rather than risk a false E503: the bound
        value's Z3 term is an uninterpreted accessor with no
        non-negativity assertion, so an already-@Nat source would fail
        the proof spuriously.  Codegen does not guard them either (the
        runtime guard covers only the let site), so closing them needs
        scrutinee-type inference.
        """
        if isinstance(expr, (ast.FnCall, ast.ModuleCall)):
            # Site 2: @Nat formal parameters narrowing an @Int argument.
            if isinstance(expr, ast.FnCall):
                callee: object | None = self.env.lookup_function(expr.name)
            else:
                callee = self._lookup_module_function(expr.path, expr.name)
            param_types = getattr(callee, "param_types", None)
            if param_types is not None:
                # A generic function whose `TypeVar` formal is fixed to @Nat
                # by context (e.g. `T = Nat`) is skipped by `_is_nat_type`:
                # only a concretely-@Nat formal obligates, mirroring generic
                # constructor fields and effect-op formals — deferred to #747.
                for arg, formal in zip(expr.args, param_types):
                    if (self._nat_binding_target(arg, formal)
                            and self._narrows_into_nat(arg)):
                        self._check_nat_binding_obligation(
                            decl, arg, smt, slot_env, assumptions,
                            site="call argument",
                        )
            for arg in expr.args:
                self._walk_for_nat_binding_obligations(
                    decl, arg, smt, slot_env, assumptions,
                )
            return

        if isinstance(expr, ast.ConstructorCall):
            # Site 3: @Nat constructor fields narrowing an @Int argument.
            # Only *concretely* @Nat fields fire — a generic field
            # (TypeVar) instantiated to @Nat is not visible here without
            # the call-site type arguments, so it is left unchecked
            # (neither obligated here nor codegen-guarded) — deferred to
            # #747, mirroring the generic effect-op formal case.
            ci = self._lookup_constructor_info(expr.name)
            if ci is not None and ci.field_types is not None:
                for arg, field_ty in zip(expr.args, ci.field_types):
                    if (self._nat_binding_target(arg, field_ty)
                            and self._narrows_into_nat(arg)):
                        self._check_nat_binding_obligation(
                            decl, arg, smt, slot_env, assumptions,
                            site="constructor field",
                        )
            for arg in expr.args:
                self._walk_for_nat_binding_obligations(
                    decl, arg, smt, slot_env, assumptions,
                )
            return

        if isinstance(expr, ast.QualifiedCall):
            # Effect operations (e.g. `IO.sleep : Nat -> Unit`) narrow an
            # @Int argument into a @Nat formal just like a plain call.
            op = self.env.lookup_effect_op(expr.name, qualifier=expr.qualifier)
            param_types = getattr(op, "param_types", None)
            if param_types is not None:
                # A generic (TypeVar) formal — `E<T>.wait` instantiated as
                # `E<Nat>` — is skipped by `_is_nat_type`: only a concretely
                # @Nat formal obligates, mirroring generic constructor fields.
                # Resolving the instantiation is deferred to #747.
                for arg, formal in zip(expr.args, param_types):
                    if (self._nat_binding_target(arg, formal)
                            and self._narrows_into_nat(arg)):
                        self._check_nat_binding_obligation(
                            decl, arg, smt, slot_env, assumptions,
                            site="effect-operation argument",
                        )
            for arg in expr.args:
                self._walk_for_nat_binding_obligations(
                    decl, arg, smt, slot_env, assumptions,
                )
            return

        if isinstance(expr, ast.IfExpr):
            self._walk_for_nat_binding_obligations(
                decl, expr.condition, smt, slot_env, assumptions,
            )
            z3_cond = smt.translate_expr(expr.condition, slot_env)
            if z3_cond is not None:
                import z3 as z3mod
                smt._path_conditions.append(z3_cond)
                try:
                    self._walk_for_nat_binding_obligations(
                        decl, expr.then_branch, smt, slot_env, assumptions,
                    )
                finally:
                    smt._path_conditions.pop()
                if expr.else_branch is not None:
                    smt._path_conditions.append(z3mod.Not(z3_cond))
                    try:
                        self._walk_for_nat_binding_obligations(
                            decl, expr.else_branch, smt, slot_env,
                            assumptions,
                        )
                    finally:
                        smt._path_conditions.pop()
            else:  # pragma: no cover — condition untranslatable
                self._walk_for_nat_binding_obligations(
                    decl, expr.then_branch, smt, slot_env, assumptions,
                )
                if expr.else_branch is not None:
                    self._walk_for_nat_binding_obligations(
                        decl, expr.else_branch, smt, slot_env, assumptions,
                    )
            return

        if isinstance(expr, ast.Block):
            cur_env = slot_env
            for stmt in expr.statements:
                if isinstance(stmt, ast.LetStmt):
                    # Site 1: `let @Nat = <Int>`.
                    self._walk_for_nat_binding_obligations(
                        decl, stmt.value, smt, cur_env, assumptions,
                    )
                    if (self._is_nat_type(self._resolve_type(stmt.type_expr))
                            and self._narrows_into_nat(stmt.value)):
                        self._check_nat_binding_obligation(
                            decl, stmt.value, smt, cur_env, assumptions,
                            site="let binding",
                        )
                    # Rebind the let slot in cur_env so a later obligation
                    # translates against this value, not a stale outer binding
                    # of the same slot name.  An untranslatable RHS (e.g.
                    # `let @Int = E.next(())`) falls back to a fresh slot var
                    # carrying its type invariant only, so the stale outer
                    # binding is never reused for a later obligation — mirrors
                    # the destructure path (CodeRabbit, PR #748).
                    val = smt.translate_expr(stmt.value, cur_env)
                    if val is None:
                        val = self._fresh_slot_var(smt, stmt.type_expr)
                    if val is not None:
                        type_name = smt._type_expr_to_slot_name(stmt.type_expr)
                        if type_name is not None:
                            cur_env = cur_env.push(type_name, val)
                elif isinstance(stmt, ast.LetDestruct):
                    # Site 6: `let Tuple<@Nat, ...> = Tuple(<Int>, ...)`.
                    # A literal-constructor source pairs each binding with a
                    # translatable sub-expression and is obligation-checked;
                    # a non-literal source is left unchecked here — there is
                    # no runtime guard off the `let` site (#747).
                    self._walk_for_nat_binding_obligations(
                        decl, stmt.value, smt, cur_env, assumptions,
                    )
                    lit_args: tuple[ast.Expr, ...] = ()
                    if (isinstance(stmt.value, ast.ConstructorCall)
                            and stmt.value.name == stmt.constructor):
                        lit_args = stmt.value.args
                        for te, sub in zip(stmt.type_bindings, lit_args):
                            if (self._is_nat_type(self._resolve_type(te))
                                    and self._narrows_into_nat(sub)):
                                self._check_nat_binding_obligation(
                                    decl, sub, smt, cur_env, assumptions,
                                    site="tuple destructure",
                                )
                    # Non-literal tuple sources (#747 site 2) stay
                    # unobligated: the SMT layer models a tuple as a scalar
                    # (its sort is `Int`, not a projectable datatype), so a
                    # component `>= 0` obligation cannot be expressed yet.
                    # Tracked for when SMT tuple support lands.
                    # Rebind every destructured slot in cur_env so a later
                    # obligation translates against the destructured value,
                    # not a stale outer binding of the same slot name
                    # (CodeRabbit, PR #748).  A literal component is
                    # translated in the *outer* env first (avoiding same-type
                    # self-shadowing); a non-literal source — or a component
                    # the SMT layer can't translate — falls back to a fresh
                    # slot var carrying only its type invariant, so the stale
                    # outer binding is never reused for a later obligation.
                    pushed: list[tuple[str, object]] = []
                    for i, te in enumerate(stmt.type_bindings):
                        type_name = smt._type_expr_to_slot_name(te)
                        if type_name is None:
                            continue
                        slot_val: object | None = None
                        if i < len(lit_args):
                            slot_val = smt.translate_expr(lit_args[i], cur_env)
                        if slot_val is None:
                            slot_val = self._fresh_slot_var(smt, te)
                        if slot_val is not None:
                            pushed.append((type_name, slot_val))
                    for tn, sv in pushed:
                        cur_env = cur_env.push(tn, sv)
                elif isinstance(stmt, ast.ExprStmt):  # pragma: no cover
                    self._walk_for_nat_binding_obligations(
                        decl, stmt.expr, smt, cur_env, assumptions,
                    )
            self._walk_for_nat_binding_obligations(
                decl, expr.expr, smt, cur_env, assumptions,
            )
            return

        if isinstance(expr, ast.BinaryExpr):
            self._walk_for_nat_binding_obligations(
                decl, expr.left, smt, slot_env, assumptions,
            )
            self._walk_for_nat_binding_obligations(
                decl, expr.right, smt, slot_env, assumptions,
            )
            return

        if isinstance(expr, ast.UnaryExpr):
            self._walk_for_nat_binding_obligations(
                decl, expr.operand, smt, slot_env, assumptions,
            )
            return

        if isinstance(expr, ast.MatchExpr):
            self._walk_for_nat_binding_obligations(
                decl, expr.scrutinee, smt, slot_env, assumptions,
            )
            scrutinee_z3 = smt.translate_expr(expr.scrutinee, slot_env)
            for arm in expr.arms:
                arm_env = slot_env
                pat_cond = None
                if scrutinee_z3 is not None:
                    bound = smt._bind_pattern(
                        scrutinee_z3, arm.pattern, slot_env,
                    )
                    if bound is not None:
                        arm_env = bound
                    pat_cond = smt._pattern_condition(
                        scrutinee_z3, arm.pattern,
                    )
                # Site 4: top-level `match <Int> { @Nat -> ... }`.  A
                # binding pattern is irrefutable, so the scrutinee >= 0
                # obligation holds whenever the arm is taken — check it
                # under the function's preconditions + outer path
                # conditions (no per-arm guard needed).
                if (isinstance(arm.pattern, ast.BindingPattern)
                        and self._is_nat_type(
                            self._resolve_type(arm.pattern.type_expr))
                        and self._narrows_into_nat(expr.scrutinee)):
                    self._check_nat_binding_obligation(
                        decl, expr.scrutinee, smt, slot_env, assumptions,
                        site="match binding",
                    )
                elif isinstance(arm.pattern, ast.ConstructorPattern):
                    # Site 1 (#747): @Nat sub-patterns narrowing a non-@Nat
                    # ADT field — the @Int payload of `Some(@Nat.0)` on an
                    # `Option<Int>` scrutinee.
                    self._obligate_subpattern_narrowings(
                        decl, expr.scrutinee, scrutinee_z3, arm.pattern,
                        smt, slot_env, assumptions,
                    )
                if pat_cond is not None:
                    smt._path_conditions.append(pat_cond)
                    try:
                        self._walk_for_nat_binding_obligations(
                            decl, arm.body, smt, arm_env, assumptions,
                        )
                    finally:
                        smt._path_conditions.pop()
                else:
                    self._walk_for_nat_binding_obligations(
                        decl, arm.body, smt, arm_env, assumptions,
                    )
            return

        # Expression containers that hold arbitrary sub-expressions: a
        # narrowing nested inside one (e.g. `[takes_nat(@Int.0)]`) must
        # still be visited.  (The #520 subtraction walker has the same
        # pre-existing container gap; aligning it is out of #552's scope.)
        if isinstance(expr, ast.ArrayLit):
            for elem in expr.elements:
                self._walk_for_nat_binding_obligations(
                    decl, elem, smt, slot_env, assumptions,
                )
            return

        if isinstance(expr, ast.IndexExpr):
            self._walk_for_nat_binding_obligations(
                decl, expr.collection, smt, slot_env, assumptions,
            )
            self._walk_for_nat_binding_obligations(
                decl, expr.index, smt, slot_env, assumptions,
            )
            return

        if isinstance(expr, ast.InterpolatedString):
            for part in expr.parts:
                if isinstance(part, ast.Expr):
                    self._walk_for_nat_binding_obligations(
                        decl, part, smt, slot_env, assumptions,
                    )
            return

        # Other expression types — no nested binding site to walk.
        return

    def _check_subtraction_obligation(
        self,
        decl: ast.FnDecl,
        expr: ast.BinaryExpr,
        smt: SmtContext,
        slot_env: SlotEnv,
        assumptions: list[object],
    ) -> None:
        """Discharge the ``lhs >= rhs`` obligation at a single site.

        On success, increments ``tier1_verified``.  On failure, emits an
        E502 error with a Z3 counterexample.  Path conditions in
        ``smt._path_conditions`` are picked up automatically by
        :py:meth:`SmtContext.check_valid`.
        """
        self.summary.total += 1
        lhs = smt.translate_expr(expr.left, slot_env)
        rhs = smt.translate_expr(expr.right, slot_env)
        if lhs is None or rhs is None:  # pragma: no cover — both Nat
            self.summary.tier3_runtime += 1
            self._record_obligation(decl.name, "nat_sub", expr, "tier3")
            return

        obligation = lhs >= rhs
        result = smt.check_valid(obligation, list(assumptions))

        if result.status == "verified":
            self.summary.tier1_verified += 1
            self._record_obligation(decl.name, "nat_sub", expr, "verified")
        elif result.status == "violated":
            self.summary.total -= 1  # don't count — it's an error
            self._record_obligation(
                decl.name, "nat_sub", expr, "violated",
                error_code="E502",
                counterexample=result.counterexample,
            )
            self._report_underflow(decl, expr, result.counterexample)
        else:  # pragma: no cover — solver timeout
            self.summary.tier3_runtime += 1
            self._record_obligation(
                decl.name, "nat_sub", expr, "timeout",
            )

    def _fresh_slot_var(
        self, smt: SmtContext, te: ast.TypeExpr,
    ) -> object | None:
        """A fresh Z3 var carrying the binding type's invariant.

        Used to invalidate a stale outer binding when a destructure rebinds
        a slot to a value the SMT layer cannot translate (a non-literal
        source, or a literal component that does not translate), so a later
        obligation never reads the old, more-constrained binding of the same
        slot name (CodeRabbit, PR #748).  Dispatches on the *resolved* type
        so a scalar reached through an alias (e.g. ``type Count = Nat``) is
        still invalidated; returns ``None`` only for a type with no scalar
        SMT sort (the stale binding is then irrelevant to a `value >= 0`
        obligation anyway).
        """
        resolved = self._resolve_type(te)
        fresh = smt._fresh_name("destructure")
        result: object | None = None
        if self._is_nat_type(resolved):
            result = smt.declare_nat(fresh)
        elif resolved == INT or (
            isinstance(resolved, RefinedType) and resolved.base == INT
        ):
            result = smt.declare_int(fresh)
        elif self._is_bool_type(resolved):
            result = smt.declare_bool(fresh)
        elif self._is_float64_type(resolved):
            result = smt.declare_float64(fresh)
        elif self._is_string_type(resolved):
            result = smt.declare_string(fresh)
        return result

    def _check_nat_binding_obligation(
        self,
        decl: ast.FnDecl,
        value_node: ast.Expr,
        smt: SmtContext,
        slot_env: SlotEnv,
        assumptions: list[object],
        *,
        site: str,
    ) -> None:
        """Discharge a ``value >= 0`` obligation at one @Nat binding site.

        Mirrors :py:meth:`_check_subtraction_obligation`: on success
        increments ``tier1_verified``; on a Z3 counterexample emits an
        E503 error.  When the value is untranslatable or the solver times
        out the outcome depends on the site — the `let` site is backed by
        the codegen runtime guard (counted ``tier3_runtime``), while every
        other site has no guard, so the narrowing is surfaced as an E504
        warning and excluded from the totals (#747; see
        :py:meth:`_record_nat_bind_tier3`).  Path conditions in
        ``smt._path_conditions`` are folded in automatically by
        :py:meth:`SmtContext.check_valid`.
        """
        self.summary.total += 1
        val = smt.translate_expr(value_node, slot_env)
        if val is None:
            self._record_nat_bind_tier3(decl, value_node, site, "tier3")
            return

        obligation = val >= 0
        result = smt.check_valid(obligation, list(assumptions))

        if result.status == "verified":
            self.summary.tier1_verified += 1
            self._record_obligation(decl.name, "nat_bind", value_node, "verified")
        elif result.status == "violated":
            self.summary.total -= 1  # don't count — it's an error
            self._record_obligation(
                decl.name, "nat_bind", value_node, "violated",
                error_code="E503",
                counterexample=result.counterexample,
            )
            self._report_nat_binding(decl, value_node, site, result.counterexample)
        else:  # pragma: no cover — solver timeout
            self._record_nat_bind_tier3(decl, value_node, site, "timeout")

    def _check_nat_binding_obligation_term(
        self,
        decl: ast.FnDecl,
        term: object,
        smt: SmtContext,
        assumptions: list[object],
        *,
        site: str,
        node: ast.Expr,
    ) -> None:
        """Discharge ``term >= 0`` for a *projected* value — an ADT
        sub-pattern field or a non-literal destructure component — whose
        Z3 term we already have (#747).

        Unlike :py:meth:`_check_nat_binding_obligation` the value is an
        uninterpreted field accessor, not an AST expression, so there is
        no translation step and no ``let``-style runtime guard: an
        undischarged obligation is a genuine E503 (the accessor is
        unconstrained, so Z3 witnesses the negative payload).  *node*
        gives the diagnostic location.
        """
        self.summary.total += 1
        obligation = term >= 0  # type: ignore[operator]
        result = smt.check_valid(obligation, list(assumptions))
        if result.status == "verified":
            self.summary.tier1_verified += 1
            self._record_obligation(decl.name, "nat_bind", node, "verified")
        elif result.status == "violated":
            self.summary.total -= 1
            self._record_obligation(
                decl.name, "nat_bind", node, "violated",
                error_code="E503", counterexample=result.counterexample,
            )
            self._report_nat_binding(decl, node, site, result.counterexample)
        else:  # pragma: no cover — solver timeout
            self._record_nat_bind_tier3(decl, node, site, "timeout")

    def _instantiated_field_types(
        self, ctor_name: str, scrut_ty: Type | None,
    ) -> tuple[Type, ...] | None:
        """A constructor's field types instantiated against *scrut_ty*'s
        type arguments (#747) — mirrors the checker's ``_check_ctor_pattern``.

        ``None`` when the constructor or the scrutinee's ADT type is
        unknown, so callers leave the sub-pattern unchecked rather than
        guess at a narrowing.
        """
        ci = self._lookup_constructor_info(ctor_name)
        if ci is None or ci.field_types is None:
            return None
        field_types = ci.field_types
        if (isinstance(scrut_ty, AdtType) and ci.parent_type_params
                and scrut_ty.type_args):
            mapping = dict(zip(ci.parent_type_params, scrut_ty.type_args))
            field_types = tuple(substitute(ft, mapping) for ft in field_types)
        return field_types

    def _obligate_subpattern_narrowings(
        self,
        decl: ast.FnDecl,
        scrutinee: ast.Expr,
        scrutinee_z3: object,
        pattern: ast.ConstructorPattern,
        smt: SmtContext,
        slot_env: SlotEnv,
        assumptions: list[object],
    ) -> None:
        """#747: obligate each @Nat sub-pattern binding that narrows a
        non-@Nat ADT field — ``match opt { Some(@Nat.0) -> }`` on
        ``Option<Int>``.

        The field's Z3 term is an uninterpreted accessor, so only a
        *genuine* narrowing (the source field is not already @Nat) is
        obligated; an already-@Nat field would fail the proof spuriously
        (its accessor carries no ``>= 0`` fact).
        """
        field_types = self._instantiated_field_types(
            pattern.name, self._resolved_type_of(scrutinee))
        if field_types is None:
            return
        # A literal-constructor scrutinee (`match Some(@Int.0) { ... }`)
        # binds the constructor's own arguments — translatable AST nodes,
        # obligated directly.  An opaque scrutinee binds uninterpreted
        # field accessors, obligated as Z3 terms.
        lit_args: tuple[ast.Expr, ...] | None = None
        if (isinstance(scrutinee, ast.ConstructorCall)
                and scrutinee.name == pattern.name):
            lit_args = scrutinee.args
        sort = None
        idx = None
        if lit_args is None:
            if scrutinee_z3 is None:
                return
            try:
                sort = scrutinee_z3.sort()  # type: ignore[attr-defined]
                idx = smt._find_ctor_index(sort, pattern.name)
            except Exception:  # pragma: no cover — non-datatype scrutinee
                return
            if idx is None:  # pragma: no cover
                return
        for i, (sub_pat, field_ty) in enumerate(
                zip(pattern.sub_patterns, field_types)):
            if not isinstance(sub_pat, ast.BindingPattern):
                continue
            target = self._resolve_type(sub_pat.type_expr)
            if not (self._is_nat_type(target)
                    and not self._is_nat_type(field_ty)):
                continue
            if lit_args is not None:
                if i < len(lit_args) and self._narrows_into_nat(lit_args[i]):
                    self._check_nat_binding_obligation(
                        decl, lit_args[i], smt, slot_env, assumptions,
                        site="ADT sub-pattern bind",
                    )
            else:
                assert sort is not None  # set above when lit_args is None
                field_term = sort.accessor(idx, i)(scrutinee_z3)
                self._check_nat_binding_obligation_term(
                    decl, field_term, smt, assumptions,
                    site="ADT sub-pattern bind", node=scrutinee,
                )

    def _record_nat_bind_tier3(
        self,
        decl: ast.FnDecl,
        value_node: ast.Expr,
        site: str,
        status: ObligationStatus,
    ) -> None:
        """Record a Tier-3 nat_bind outcome (untranslatable value or solver
        timeout), distinguishing the guarded `let` site from unguarded
        non-let sites.

        The codegen runtime guard backs only the `let` site, so a Tier-3
        narrowing there genuinely falls to a runtime check (``tier3_runtime``).
        At every other site (#747) there is no guard: rather than silently
        counting it as a "runtime check" it never gets, surface an E504
        warning and exclude it from the discharged totals (like a violation).
        """
        if site == "let binding":
            self.summary.tier3_runtime += 1
            self._record_obligation(decl.name, "nat_bind", value_node, status)
        else:
            self.summary.total -= 1
            self._record_obligation(
                decl.name, "nat_bind", value_node, "tier3_unguarded",
                error_code="E504",
            )
            self._report_nat_binding_unguarded(decl, value_node, site)

    def _report_nat_binding_unguarded(
        self,
        decl: ast.FnDecl,
        node: ast.Expr,
        site: str,
    ) -> None:
        """Emit an E504 warning for a non-let @Nat narrowing the SMT layer
        could not discharge and codegen does not guard (#747)."""
        self._warning(
            node,
            (
                f"@Int value narrowing into a @Nat {site} in '{decl.name}' "
                "could not be verified statically and is not runtime-guarded "
                "(#747) — add `requires(... >= 0)`, bind it to a `let @Nat` "
                "first (which is guarded), or guard it with "
                "`if ... >= 0 then ... else ...`."
            ),
            rationale=(
                "The narrowed value is outside Z3's decidable fragment "
                "(untranslatable or the solver timed out), so the `>= 0` "
                "obligation could not be discharged.  The codegen runtime "
                "guard currently backs only the `let` site, so at this site "
                "the narrowing is neither statically proven nor runtime-"
                "checked."
            ),
            spec_ref='Chapter 11, Section 11.2.1 "Nat as i64"',
            error_code="E504",
            tier=3,
        )

    def _report_underflow(
        self,
        decl: ast.FnDecl,
        expr: ast.BinaryExpr,
        counterexample: dict[str, str] | None,
    ) -> None:
        """Emit an E502 diagnostic for an undischarged underflow obligation."""
        ce_lines: list[str] = []
        if counterexample:
            ce_lines.append("Counterexample:")
            for name, value in sorted(counterexample.items()):
                if name != "@result":
                    ce_lines.append(f"    {name} = {value}")
        ce_text = "\n  ".join(ce_lines) if ce_lines else ""

        description = (
            f"@Nat subtraction in '{decl.name}' may underflow."
        )
        if ce_text:
            description += f"\n  {ce_text}"

        self._error(
            expr,
            description,
            rationale=(
                "@Nat - @Nat carries a Tier-1 proof obligation that "
                "the left operand is at least as large as the right.  "
                "The SMT solver found inputs where this does not hold; "
                "a negative i64 would be produced and stored in a @Nat "
                "slot, violating the type's non-negativity invariant."
            ),
            fix=(
                "Add a precondition that rules out the bad inputs, "
                "e.g. `requires(@Nat.0 >= @Nat.1)`.  Alternatively, "
                "guard the subtraction: `if @Nat.0 >= @Nat.1 then "
                "@Nat.0 - @Nat.1 else 0` — the path condition "
                "discharges the obligation in the then-branch."
            ),
            spec_ref=(
                'Chapter 4, Section 4.4 "Arithmetic Expressions" '
                'and Chapter 11, Section 11.2.1 "Nat as i64"'
            ),
            error_code="E502",
        )

    def _report_nat_binding(
        self,
        decl: ast.FnDecl,
        node: ast.Expr,
        site: str,
        counterexample: dict[str, str] | None,
    ) -> None:
        """Emit an E503 diagnostic for an undischarged @Nat narrowing."""
        ce_lines: list[str] = []
        if counterexample:
            ce_lines.append("Counterexample:")
            for name, value in sorted(counterexample.items()):
                if name != "@result":
                    ce_lines.append(f"    {name} = {value}")
        ce_text = "\n  ".join(ce_lines) if ce_lines else ""

        description = (
            f"@Int value narrowing into a @Nat {site} in '{decl.name}' "
            f"may be negative."
        )
        if ce_text:
            description += f"\n  {ce_text}"

        self._error(
            node,
            description,
            rationale=(
                "A @Nat slot carries a non-negativity invariant, but the "
                "type checker permits Int <: Nat narrowing and defers the "
                "`>= 0` proof to verification.  The SMT solver found "
                "inputs where the narrowed value is negative — a negative "
                "i64 would be stored in a @Nat slot, violating the type's "
                "invariant."
            ),
            fix=(
                "Add a precondition ruling out the bad inputs, e.g. "
                "`requires(@Int.0 >= 0)`.  Alternatively, guard the "
                "binding: `if @Int.0 >= 0 then ... else ...` — the path "
                "condition discharges the obligation in the then-branch."
            ),
            spec_ref=(
                'Chapter 4, Section 4.7 "Let Bindings" and Chapter 11, '
                'Section 11.2.1 "Nat as i64"'
            ),
            error_code="E503",
        )

    def _is_nat_typed(self, expr: ast.Expr) -> bool:
        """Return True iff *expr* has static type ``@Nat``.

        Conservative: returns False for expressions whose type cannot
        be determined locally.  False is the safe default — it means
        "skip the obligation," matching the existing (pre-#520)
        behaviour, so this can never reject a program that previously
        verified.  Only programs with definitely-@Nat-typed unguarded
        subtractions become rejected.

        Recurses through arithmetic expressions, ``IfExpr``, ``Block``,
        ``MatchExpr``, and ``FnCall`` (looking up the callee's return
        type).  Returns False for ``UnaryExpr`` because unary negation
        always produces ``@Int``, never ``@Nat``.

        See #552 for the broader generalisation that fires on every
        binding site rather than just at subtraction.
        """
        if isinstance(expr, ast.SlotRef):
            return expr.type_name == "Nat"
        if isinstance(expr, ast.IntLit):
            # Non-negative literals can be coerced to Nat.
            return expr.value >= 0
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in (
                ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
                ast.BinOp.DIV, ast.BinOp.MOD,
            ):
                # Per checker.py:264-267, the result of an arithmetic
                # operator is the more general operand type (Nat <: Int).
                # So the result is @Nat iff BOTH operands are @Nat.
                return (self._is_nat_typed(expr.left)
                        and self._is_nat_typed(expr.right))
            return False
        if isinstance(expr, ast.IfExpr):
            if expr.else_branch is None:
                return False
            return (self._is_nat_typed(expr.then_branch)
                    and self._is_nat_typed(expr.else_branch))
        if isinstance(expr, ast.Block):
            return self._is_nat_typed(expr.expr)
        if isinstance(expr, ast.MatchExpr):
            if not expr.arms:
                return False
            return all(self._is_nat_typed(arm.body) for arm in expr.arms)
        if isinstance(expr, ast.FnCall):
            fn = self.env.lookup_function(expr.name)
            if fn is not None:
                # FunctionInfo.return_type is already a resolved Type
                # (vera/environment.py:43), no need for _resolve_type.
                return self._is_nat_type(fn.return_type)
            return False
        if isinstance(expr, ast.ModuleCall):
            # Module-qualified calls (e.g. `Math.abs(...)`) — resolve via
            # the per-module registry the verifier already maintains.
            mfn = self._lookup_module_function(expr.path, expr.name)
            if mfn is not None:
                return self._is_nat_type(mfn.return_type)
            return False
        # UnaryExpr: negation always produces @Int.
        # Other AST node types: conservative False.
        return False

    def _has_nat_origin(self, expr: ast.Expr) -> bool:
        """Return True iff *expr* derives from a definitely-@Nat source.

        Distinct from :py:meth:`_is_nat_typed`: that classifies the
        *static type* of the expression (and treats non-negative
        IntLits as @Nat per checker.py:62).  This helper instead
        asks whether the value has @Nat *provenance* — a parameter,
        let binding, or function call carrying the @Nat invariant
        forward — as opposed to a pure literal computation like
        ``0 - 1``.

        Used to scope #520's obligation: pure-literal subtractions
        such as ``0 - 1`` (the common "I want -1" idiom) are
        intentionally skipped because they're typically consumed
        at @Int positions where the result is upcast.  Catching
        ``let @Nat = 0 - 1`` requires the broader binding-site
        check tracked as #552.
        """
        if isinstance(expr, ast.SlotRef):
            return expr.type_name == "Nat"
        if isinstance(expr, ast.FnCall):
            fn = self.env.lookup_function(expr.name)
            if fn is None:
                return False
            return self._is_nat_type(fn.return_type)
        if isinstance(expr, ast.ModuleCall):
            mfn = self._lookup_module_function(expr.path, expr.name)
            if mfn is None:
                return False
            return self._is_nat_type(mfn.return_type)
        if isinstance(expr, ast.BinaryExpr):
            return (self._has_nat_origin(expr.left)
                    or self._has_nat_origin(expr.right))
        if isinstance(expr, ast.UnaryExpr):
            return self._has_nat_origin(expr.operand)
        if isinstance(expr, ast.IfExpr):
            if expr.else_branch is None:
                return False
            return (self._has_nat_origin(expr.then_branch)
                    or self._has_nat_origin(expr.else_branch))
        if isinstance(expr, ast.Block):
            return self._has_nat_origin(expr.expr)
        if isinstance(expr, ast.MatchExpr):
            if not expr.arms:
                return False
            return any(self._has_nat_origin(arm.body) for arm in expr.arms)
        return False

    def _narrows_into_nat(self, value: ast.Expr) -> bool:
        """Return True iff binding *value* into a @Nat slot is a
        narrowing that needs a ``value >= 0`` obligation (#552).

        Fires in two shapes:

        * the value is not statically @Nat — a genuine @Int narrowing
          (``@Int.0``, ``@Int.0 - 100``, ``-1``); or
        * the value is statically @Nat but its value-producing tree
          contains a pure-literal subtraction that can underflow
          (``0 - 1``, however wrapped or nested) — ``_is_nat_typed`` calls
          such a value @Nat, yet it can be negative.  #520 deliberately
          exempts these (no @Nat provenance) and defers them here.

        A genuine @Nat value (slot ref, @Nat-returning call, non-negative
        literal, @Nat-origin arithmetic, or a #520-covered ``@Nat - @Nat``
        with @Nat origin) returns False so the two obligations never
        co-fire on one site.  See :py:meth:`_has_underflow_leaf`.
        """
        if not self._is_nat_typed(value):
            return True
        return self._has_underflow_leaf(value)

    def _has_underflow_leaf(self, value: ast.Expr) -> bool:
        """True iff a statically-@Nat *value* can still be negative
        because its value-producing tree contains a pure-literal
        subtraction (a subtraction with no @Nat provenance).

        Descends arithmetic operands, ``Block`` tails, ``IfExpr``
        branches, and ``MatchExpr`` arms, so the #520-exempt ``0 - 1``
        idiom is caught however it is wrapped: ``{ 0 - 1 }``,
        ``if c then 5 else 0 - 1``, ``(0 - 1) + x`` all qualify.  A value
        with no such subtraction (a non-negative literal, an addition of
        @Nat values, or a ``@Nat - @Nat`` with @Nat origin) returns
        False.  Z3 then discharges the genuinely-safe cases (``5 - 1``)
        at Tier 1 and rejects the negative ones (``0 - 1``) with E503.
        """
        if isinstance(value, ast.BinaryExpr):
            if (value.op == ast.BinOp.SUB
                    and not self._has_nat_origin(value)):
                return True
            return (self._has_underflow_leaf(value.left)
                    or self._has_underflow_leaf(value.right))
        if isinstance(value, ast.Block):
            return self._has_underflow_leaf(value.expr)
        if isinstance(value, ast.IfExpr):
            if value.else_branch is None:
                return False
            return (self._has_underflow_leaf(value.then_branch)
                    or self._has_underflow_leaf(value.else_branch))
        if isinstance(value, ast.MatchExpr):
            return any(self._has_underflow_leaf(arm.body)
                       for arm in value.arms)
        return False

    # -----------------------------------------------------------------
    # Counterexample reporting
    # -----------------------------------------------------------------

    def _report_violation(
        self,
        fn: ast.FnDecl,
        contract: ast.Ensures,
        counterexample: dict[str, str] | None,
    ) -> None:
        """Report a contract violation with counterexample."""
        # Build counterexample description
        ce_lines: list[str] = []
        if counterexample:
            ce_lines.append("Counterexample:")
            for name, value in sorted(counterexample.items()):
                if name != "@result":
                    ce_lines.append(f"    {name} = {value}")
            if "@result" in counterexample:
                result_name = f"@{self._type_expr_to_slot_name(fn.return_type)}.result"
                ce_lines.append(f"    {result_name} = {counterexample['@result']}")

        ce_text = "\n  ".join(ce_lines) if ce_lines else ""

        description = (
            f"Postcondition does not hold in function '{fn.name}'."
        )
        if ce_text:
            description += f"\n  {ce_text}"

        self._error(
            contract,
            description,
            rationale=(
                "The SMT solver found concrete input values for which "
                "the postcondition is false. This means the function body "
                "does not satisfy its ensures() contract for all valid inputs."
            ),
            fix=(
                # #675: name all three repair classes without
                # implying any one is the "correct" answer.  The
                # verifier knows the implementation and the
                # contract disagree; it does not know which one
                # the programmer intended.  In practice fixing
                # the implementation is the most common repair
                # (especially when E500 catches a typo in the
                # body) so it comes first.
                "Resolve the mismatch between the function body "
                "and its contract: fix the implementation so it "
                "satisfies this ensures() clause, strengthen "
                "requires(...) if the counterexample is outside "
                "the intended input domain, or weaken/change "
                "ensures(...) if the postcondition overstates "
                "the intended guarantee."
            ),
            spec_ref='Chapter 6, Section 6.4.1 "Verification Conditions"',
            error_code="E500",
        )

    def _pre_at_call_site(
        self,
        callee_params: tuple[ast.TypeExpr, ...],
        call_node: ast.FnCall | ast.ModuleCall,
        precondition: ast.Requires,
    ) -> str | None:
        """The precondition rendered in CALL-SITE terms, or None.

        Callee-parameter slot references are replaced by the actual
        argument expressions of *call_node* (De Bruijn resolution via
        :func:`vera.slots.slot_table`), and the result is rendered
        with ``format_expr`` — turning, e.g.,
        ``requires(string_length(@String.0) > 0)`` at the call
        ``f("")`` into ``string_length("") > 0``.  Returns None when
        any slot cannot be mapped (unknown type in the table, index
        out of range, arity mismatch), in which case the caller keeps
        the generic wording.
        """
        import dataclasses as _dc

        table = slot_table(callee_params)

        class _NoSubstitution(Exception):
            pass

        def rebuild(node: ast.Expr) -> ast.Expr:
            if isinstance(node, ast.SlotRef):
                positions = table.get(node.type_name)
                if not positions or node.index >= len(positions):
                    raise _NoSubstitution
                pos = positions[node.index]
                if pos > len(call_node.args):
                    raise _NoSubstitution
                return call_node.args[pos - 1]
            changes: dict[str, object] = {}
            for f in _dc.fields(node):
                value = getattr(node, f.name)
                if isinstance(value, ast.Expr):
                    new_value = rebuild(value)
                    if new_value is not value:
                        changes[f.name] = new_value
                elif (
                    isinstance(value, tuple)
                    and value
                    and all(isinstance(x, ast.Expr) for x in value)
                ):
                    new_tuple = tuple(rebuild(x) for x in value)
                    if any(
                        a is not b for a, b in zip(new_tuple, value)
                    ):
                        changes[f.name] = new_tuple
            if changes:
                # dataclasses.replace's typeshed overload can't see
                # the per-subclass field types through **dict.
                return _dc.replace(node, **changes)  # type: ignore[arg-type]
            return node

        try:
            rebuilt = rebuild(precondition.expr)
        except _NoSubstitution:
            return None
        return ast.format_expr(rebuilt)

    def _report_call_violation(
        self,
        caller: ast.FnDecl,
        callee_name: str,
        call_node: ast.FnCall | ast.ModuleCall,
        precondition: ast.Requires,
        counterexample: dict[str, str] | None,
    ) -> None:
        """Report a call site where the callee's precondition may not hold."""
        pre_text = self._contract_source_text(precondition)

        # Render the precondition in call-site terms (callee slots
        # replaced by the actual arguments) so the message states
        # exactly what could not be proven — and the fix can show
        # concrete code instead of generic advice.  Falls back to the
        # generic wording when the callee or a slot cannot be
        # resolved (e.g. module-qualified callees).
        site_pre: str | None = None
        # Module-qualified callees are excluded outright: lookup_function
        # resolves the BARE name, so a local function sharing the
        # callee's name would supply the wrong parameter table.
        callee_info = (
            None
            if isinstance(call_node, ast.ModuleCall)
            else self.env.lookup_function(callee_name)
        )
        if callee_info is not None and callee_info.param_type_exprs:
            from typing import cast

            site_pre = self._pre_at_call_site(
                cast(
                    "tuple[ast.TypeExpr, ...]",
                    callee_info.param_type_exprs,
                ),
                call_node,
                precondition,
            )

        # Build counterexample description
        ce_lines: list[str] = []
        if counterexample:
            ce_lines.append("Counterexample:")
            for name, value in sorted(counterexample.items()):
                if not name.startswith("_call_"):
                    ce_lines.append(f"    {name} = {value}")

        ce_text = "\n  ".join(ce_lines) if ce_lines else ""

        description = (
            f"Call to '{callee_name}' in function '{caller.name}' "
            f"may violate the callee's precondition."
        )
        if pre_text:
            description += f"\n  Precondition: {pre_text}"
        if site_pre:
            description += f"\n  At this call site: {site_pre}"
        if ce_text:
            description += f"\n  {ce_text}"

        self._error(
            call_node,
            description,
            rationale=(
                "The SMT solver could not prove that the callee's "
                "precondition holds at this call site given the caller's "
                "assumptions. The callee may receive arguments that violate "
                "its contract."
            ),
            fix=(
                (
                    f"Guard the call so the precondition holds, e.g. "
                    f"if {site_pre} then {{ "
                    f"{ast.format_expr(call_node)} }} else {{ ... }} "
                    f"— or strengthen '{caller.name}' with "
                    f"requires({site_pre})."
                )
                if site_pre
                else (
                    f"Add a precondition to '{caller.name}' or guard "
                    f"the call with an if-expression that ensures the "
                    f"callee's precondition is satisfied."
                )
            ),
            spec_ref='Chapter 6, Section 6.4.2 "Call-Site Verification"',
            error_code="E501",
        )

    def _contract_source_text(self, contract: ast.Contract) -> str:
        """Extract the source text of a contract clause."""
        if contract.span:
            lines = self.source.splitlines()
            if 1 <= contract.span.line <= len(lines):
                return lines[contract.span.line - 1].strip()
        return ""

    # -----------------------------------------------------------------
    # Helpers
    # -----------------------------------------------------------------

    @staticmethod
    def _is_trivial(contract: ast.Contract) -> bool:
        """Check if a contract is trivially true (literal true)."""
        if isinstance(contract, ast.Requires):
            return isinstance(contract.expr, ast.BoolLit) and contract.expr.value
        if isinstance(contract, ast.Ensures):
            return isinstance(contract.expr, ast.BoolLit) and contract.expr.value
        return False  # pragma: no cover

    @staticmethod
    def _is_nat_type(ty: Type) -> bool:
        """Check if a type is Nat (non-negative integer)."""
        return ty == NAT or (isinstance(ty, RefinedType) and ty.base == NAT)

    @staticmethod
    def _is_bool_type(ty: Type) -> bool:
        """Check if a type is Bool (including refinements of Bool)."""
        return ty == BOOL or (isinstance(ty, RefinedType) and ty.base == BOOL)

    @staticmethod
    def _is_adt_type(ty: Type) -> bool:
        """Check if a type is an algebraic data type."""
        from vera.types import AdtType
        return isinstance(ty, AdtType)

    @staticmethod
    def _is_array_type(ty: Type) -> bool:
        """Check if a type is an Array<T> (incl. refinements).

        Internally `Array<T>` is represented as `AdtType("Array",
        (T,))`, but it's a built-in carrier — not user-registered
        in the SMT layer's `_adt_registry`.  Detecting it here
        lets the verifier route Array<T> slots through the
        dedicated Array-sort code path (#667).
        """
        from vera.types import AdtType
        if isinstance(ty, RefinedType):
            ty = ty.base
        return isinstance(ty, AdtType) and ty.name == "Array"

    def _declare_array_var(
        self,
        smt: "SmtContext",
        name: str,
        ty: Type,
    ) -> z3.ExprRef | None:
        """Declare an Array-typed Z3 constant for parameter `name`.

        Resolves the element type to a Z3 sort and delegates to
        `smt.declare_array_var`.  Returns None if the element type
        can't be mapped (e.g. `Array<FnType<...>>`).
        """
        from vera.types import AdtType
        if isinstance(ty, RefinedType):
            ty = ty.base
        if not isinstance(ty, AdtType) or ty.name != "Array":
            return None
        if not ty.type_args:
            return None
        element_sort = smt._vera_type_to_z3_sort(ty.type_args[0])
        if element_sort is None:
            return None
        return smt.declare_array_var(name, element_sort)

    @staticmethod
    def _is_string_type(ty: Type) -> bool:
        """Check if a type is String (including refinements of String)."""
        return ty == STRING or (isinstance(ty, RefinedType) and ty.base == STRING)

    @staticmethod
    def _is_float64_type(ty: Type) -> bool:
        """Check if a type is Float64 (including refinements of Float64)."""
        return ty == FLOAT64 or (isinstance(ty, RefinedType) and ty.base == FLOAT64)

    @staticmethod
    def _count_slots(env: SlotEnv, type_name: str) -> int:
        """Count how many slots exist for a type name."""
        stack = env._stacks.get(type_name, [])
        return len(stack)

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str:
        """Extract the canonical slot name from a type expression."""
        if isinstance(te, ast.NamedType):
            if te.type_args:
                arg_names = []
                for a in te.type_args:
                    if isinstance(a, ast.NamedType):
                        arg_names.append(a.name)
                    else:  # pragma: no cover
                        return "?"
                return f"{te.name}<{', '.join(arg_names)}>"
            return te.name
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_slot_name(te.base_type)
        if isinstance(te, ast.FnType):
            return "Fn"
        return "?"  # pragma: no cover
