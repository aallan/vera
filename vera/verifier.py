"""Vera contract verifier — Z3-backed contract checking.

Verifies that function contracts (requires/ensures/decreases) are
semantically valid using the Z3 SMT solver.  Consumes a type-checked
Program AST and produces diagnostics with counterexamples.

Tier 1: decidable fragment (QF_LIA + length + Boolean).
Tier 3: graceful fallback for unsupported constructs.

See spec/06-contracts.md for the full verification specification.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from vera import ast
from vera.environment import FunctionInfo, TypeEnv

if TYPE_CHECKING:
    from vera.resolver import ResolvedModule
from vera.errors import Diagnostic, SourceLocation
from vera.smt import CallViolation, SlotEnv, SmtContext
from vera.types import (
    BOOL,
    INT,
    NAT,
    UNIT,
    AdtType,
    EffectRowType,
    FunctionType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    canonical_type_name,
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


def verify(
    program: ast.Program,
    source: str = "",
    file: str | None = None,
    timeout_ms: int = 10_000,
    resolved_modules: list[ResolvedModule] | None = None,
) -> VerifyResult:
    """Verify contracts in a type-checked Vera Program AST.

    Returns a VerifyResult with diagnostics and a verification summary.
    The program must already have passed type checking (C3).

    *resolved_modules* provides imported module ASTs for cross-module
    contract verification (C7d).  Imported function preconditions are
    checked at call sites; postconditions are assumed.
    """
    verifier = ContractVerifier(
        source=source, file=file, timeout_ms=timeout_ms,
        resolved_modules=resolved_modules,
    )
    verifier.verify_program(program)
    return VerifyResult(
        diagnostics=verifier.errors,
        summary=verifier.summary,
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
    ) -> None:
        self.env = TypeEnv()
        self.errors: list[Diagnostic] = []
        self.summary = VerifySummary()
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
        ))

    def _get_source_line(self, line: int) -> str:
        """Extract a line from the source text."""
        lines = self.source.splitlines()
        if 1 <= line <= len(lines):
            return lines[line - 1]
        return ""

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
        from vera.types import TypeVar
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
        """Register an effect declaration."""
        from vera.environment import EffectInfo, OpInfo
        self.env.effects[decl.name] = EffectInfo(
            name=decl.name,
            type_params=decl.type_params,
            operations={},
        )

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
        from vera.types import TypeVar
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

    def verify_program(self, program: ast.Program) -> None:
        """Entry point: register modules, then local declarations, then verify."""
        self._register_modules(program)  # C7d: cross-module imports
        self._register_all(program)      # local declarations shadow imports
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
                    self._warning(
                        contract,
                        f"Cannot statically verify contract in generic function "
                        f"'{decl.name}'. Contract will be checked at runtime.",
                        rationale="Generic functions have type variables that "
                                  "cannot be represented in the SMT solver.",
                        spec_ref='Chapter 6, Section 6.8 "Summary of Verification Tiers"',
                        error_code="E520",
                    )
                else:
                    self.summary.tier1_verified += 1
                    self.summary.total += 1
            return

        smt = SmtContext(
            timeout_ms=self.timeout_ms,
            fn_lookup=self.env.lookup_function,
            module_fn_lookup=self._lookup_module_function,
        )
        # Register all known ADTs with the SMT context
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
            elif self._is_adt_type(param_ty):
                adt_var = smt.declare_adt(z3_name, param_ty)
                var = adt_var if adt_var is not None else smt.declare_int(z3_name)
            else:
                var = smt.declare_int(z3_name)

            slot_env = slot_env.push(type_name, var)

        # 2. Declare result variable
        ret_type = self._resolve_type(decl.return_type)
        ret_type_name = self._type_expr_to_slot_name(decl.return_type)
        if self._is_nat_type(ret_type):
            result_var = smt.declare_nat("@result")
        elif self._is_bool_type(ret_type):
            result_var = smt.declare_bool("@result")
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
                    continue
                z3_pre = smt.translate_expr(contract.expr, slot_env)
                if z3_pre is None:
                    self.summary.tier3_runtime += 1
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
                    )
                    continue
                assumptions.append(z3_pre)
                self.summary.tier1_verified += 1

        # 4. Assert caller assumptions into solver so _translate_call
        #    can see them during body translation.
        for a in assumptions:
            smt.solver.add(a)

        # 5. Translate function body
        body_expr = smt.translate_expr(decl.body, slot_env)

        # 6. Report any call-site precondition violations
        for v in smt.drain_call_violations():
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
                    continue

                if body_expr is None:
                    self.summary.tier3_runtime += 1
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
                    )
                    continue

                # Translate the postcondition with @T.result → body result
                smt.set_result_var(body_expr)
                z3_post = smt.translate_expr(contract.expr, slot_env)

                if z3_post is None:
                    self.summary.tier3_runtime += 1
                    self._warning(
                        contract,
                        f"Postcondition in '{decl.name}' uses constructs "
                        f"outside the decidable fragment. "
                        f"Contract will be checked at runtime.",
                        rationale="The postcondition expression contains "
                                  "constructs that cannot be translated to SMT.",
                        spec_ref='Chapter 6, Section 6.8 "Summary of Verification Tiers"',
                        error_code="E523",
                    )
                    continue

                # Check: assumptions ==> postcondition
                smt_result = smt.check_valid(z3_post, assumptions)

                if smt_result.status == "verified":
                    self.summary.tier1_verified += 1
                elif smt_result.status == "violated":
                    self.summary.total -= 1  # don't count — it's an error
                    self._report_violation(
                        decl, contract, smt_result.counterexample
                    )
                else:  # pragma: no cover
                    # unknown / timeout
                    self.summary.tier3_runtime += 1
                    self._warning(
                        contract,
                        f"Could not verify postcondition in '{decl.name}' "
                        f"within timeout. Contract will be checked at runtime.",
                        rationale="The SMT solver returned 'unknown', which "
                                  "may indicate the formula is too complex or "
                                  "the timeout was reached.",
                        spec_ref='Chapter 6, Section 6.8 "Summary of Verification Tiers"',
                        error_code="E524",
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
                else:
                    self.summary.tier3_runtime += 1
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
    # Counterexample reporting
    # -----------------------------------------------------------------

    def _report_violation(
        self,
        fn: ast.FnDecl,
        contract: ast.Ensures,
        counterexample: dict[str, str] | None,
    ) -> None:
        """Report a contract violation with counterexample."""
        # Build the contract text from source
        contract_text = self._contract_source_text(contract)

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
                "Either strengthen the precondition (add a requires() clause "
                "that excludes the counterexample inputs) or weaken the "
                "postcondition to match the actual function behaviour."
            ),
            spec_ref='Chapter 6, Section 6.4.1 "Verification Conditions"',
            error_code="E500",
        )

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
                f"Add a precondition to '{caller.name}' or guard the call "
                f"with an if-expression that ensures the callee's "
                f"precondition is satisfied."
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
        """Check if a type is Bool."""
        return ty == BOOL

    @staticmethod
    def _is_adt_type(ty: Type) -> bool:
        """Check if a type is an algebraic data type."""
        from vera.types import AdtType
        return isinstance(ty, AdtType)

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
