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

from vera import ast
from vera.environment import FunctionInfo, TypeEnv
from vera.errors import Diagnostic, SourceLocation
from vera.smt import SlotEnv, SmtContext
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
) -> VerifyResult:
    """Verify contracts in a type-checked Vera Program AST.

    Returns a VerifyResult with diagnostics and a verification summary.
    The program must already have passed type checking (C3).
    """
    verifier = ContractVerifier(source=source, file=file, timeout_ms=timeout_ms)
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
    ) -> None:
        self.env = TypeEnv()
        self.errors: list[Diagnostic] = []
        self.summary = VerifySummary()
        self.source = source
        self.file = file
        self.timeout_ms = timeout_ms

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
        ))

    def _warning(
        self,
        node: ast.Node,
        description: str,
        *,
        rationale: str = "",
        spec_ref: str = "",
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
                self._register_fn(decl)
            elif isinstance(decl, ast.DataDecl):
                self._register_data(decl)
            elif isinstance(decl, ast.EffectDecl):
                self._register_effect(decl)
            elif isinstance(decl, ast.TypeAliasDecl):
                self._register_alias(decl)

    def _register_fn(self, decl: ast.FnDecl) -> None:
        """Register a function signature and its contracts."""
        from vera.registration import register_fn
        register_fn(
            self.env, decl,
            self._resolve_type, self._resolve_effect_row,
        )

    def _register_data(self, decl: ast.DataDecl) -> None:
        """Register an ADT (minimal — just enough for type resolution)."""
        # The verifier doesn't need full ADT info, but registering
        # the type name allows _resolve_type to recognise it.
        from vera.environment import AdtInfo, ConstructorInfo
        type_params = decl.type_params if decl.type_params else None
        ctors: dict[str, ConstructorInfo] = {}
        self.env.data_types[decl.name] = AdtInfo(
            name=decl.name,
            type_params=type_params,
            constructors=ctors,
        )

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
            # Unknown — treat as opaque
            return AdtType(te.name, ())

        if isinstance(te, ast.RefinementType):
            base = self._resolve_type(te.base_type)
            return RefinedType(base, te.predicate)

        if isinstance(te, ast.FnType):
            params = tuple(self._resolve_type(p) for p in te.params)
            ret = self._resolve_type(te.return_type)
            return FunctionType(params, ret, PureEffectRow())

        return UNIT

    def _resolve_effect_row(self, eff: ast.EffectRow) -> EffectRowType:
        """Resolve an effect row."""
        from vera.types import ConcreteEffectRow, EffectInstance
        if isinstance(eff, ast.PureEffect):
            return PureEffectRow()
        if isinstance(eff, ast.EffectSet):
            effects = []
            for e in eff.effects:
                if not isinstance(e, ast.EffectRef):
                    continue
                eff_args: tuple[Type, ...] = ()
                if e.type_args:
                    eff_args = tuple(self._resolve_type(a) for a in e.type_args)
                effects.append(EffectInstance(e.name, eff_args))
            return ConcreteEffectRow(frozenset(effects))
        return PureEffectRow()

    # -----------------------------------------------------------------
    # Verification
    # -----------------------------------------------------------------

    def verify_program(self, program: ast.Program) -> None:
        """Entry point: register declarations then verify each function."""
        self._register_all(program)
        for tld in program.declarations:
            if isinstance(tld.decl, ast.FnDecl):
                self._verify_fn(tld.decl)

    def _verify_fn(self, decl: ast.FnDecl) -> None:
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
                        spec_ref='Chapter 6, Section 6.5 "Verification Tiers"',
                    )
                else:
                    self.summary.tier1_verified += 1
                    self.summary.total += 1
            return

        smt = SmtContext(timeout_ms=self.timeout_ms)
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
                        spec_ref='Chapter 6, Section 6.5 "Verification Tiers"',
                    )
                    continue
                assumptions.append(z3_pre)
                self.summary.tier1_verified += 1

        # 4. Translate function body
        body_expr = smt.translate_expr(decl.body, slot_env)

        # 5. Verify ensures clauses
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
                                  "pattern matching, recursive calls, "
                                  "effect operations).",
                        spec_ref='Chapter 6, Section 6.5 "Verification Tiers"',
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
                        spec_ref='Chapter 6, Section 6.5 "Verification Tiers"',
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
                else:
                    # unknown / timeout
                    self.summary.tier3_runtime += 1
                    self._warning(
                        contract,
                        f"Could not verify postcondition in '{decl.name}' "
                        f"within timeout. Contract will be checked at runtime.",
                        rationale="The SMT solver returned 'unknown', which "
                                  "may indicate the formula is too complex or "
                                  "the timeout was reached.",
                        spec_ref='Chapter 6, Section 6.5 "Verification Tiers"',
                    )

        # 6. Handle decreases clauses (Tier 3 for now)
        for contract in decl.contracts:
            if isinstance(contract, ast.Decreases):
                self.summary.total += 1
                self.summary.tier3_runtime += 1
                self._warning(
                    contract,
                    f"Termination metric in '{decl.name}' cannot be "
                    f"statically verified yet. "
                    f"Contract will be checked at runtime.",
                    rationale="Termination verification for recursive "
                              "functions requires reasoning about recursive "
                              "call sites, which is not yet implemented.",
                    spec_ref='Chapter 6, Section 6.6 "Termination"',
                )

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
            spec_ref='Chapter 6, Section 6.4 "Verification Conditions"',
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
        return False

    @staticmethod
    def _is_nat_type(ty: Type) -> bool:
        """Check if a type is Nat (non-negative integer)."""
        return ty == NAT or (isinstance(ty, RefinedType) and ty.base == NAT)

    @staticmethod
    def _is_bool_type(ty: Type) -> bool:
        """Check if a type is Bool."""
        return ty == BOOL

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
                    else:
                        return "?"
                return f"{te.name}<{', '.join(arg_names)}>"
            return te.name
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_slot_name(te.base_type)
        if isinstance(te, ast.FnType):
            return "Fn"
        return "?"
