"""Vera contract-driven test engine — Z3-guided input generation.

Generates test inputs from requires() clauses via Z3, executes compiled
WASM, and validates ensures() contracts at runtime.  Functions already
proved by the verifier (Tier 1) are reported as "verified"; functions
with Tier 3 contracts are exercised with generated inputs.

See spec/06-contracts.md, Section 6.8 "Summary of Verification Tiers".
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

import z3

from vera import ast
from vera.errors import Diagnostic, SourceLocation
from vera.smt import SlotEnv, SmtContext
from vera.types import BOOL, BYTE, FLOAT64, INT, NAT, STRING, UNIT, PrimitiveType, RefinedType, Type, base_type

if TYPE_CHECKING:
    from vera.resolver import ResolvedModule


# =====================================================================
# Result types
# =====================================================================

@dataclass
class TrialResult:
    """Outcome of a single test trial."""

    fn_name: str
    args: dict[str, int | float]  # {"@Int.0": 5, "@Nat.0": 3}
    status: str  # "pass" | "fail" | "error"
    message: str  # violation message or empty


@dataclass
class FunctionTestResult:
    """Test result for a single function."""

    fn_name: str
    category: str  # "verified" | "tested" | "skipped"
    reason: str
    trials_run: int
    trials_passed: int
    trials_failed: int
    failures: list[TrialResult]


@dataclass
class TestSummary:
    """Aggregate counts across all functions."""

    verified: int = 0  # Tier 1 (proved)
    tested: int = 0  # Tier 3 exercised
    passed: int = 0  # tested + all trials OK
    failed: int = 0  # tested + at least one trial failed
    skipped: int = 0  # can't generate inputs
    total_trials: int = 0
    total_passes: int = 0
    total_failures: int = 0


@dataclass
class TestResult:
    """Complete result of testing a program."""

    __test__ = False  # prevent pytest collection

    functions: list[FunctionTestResult]
    summary: TestSummary
    diagnostics: list[Diagnostic]


# =====================================================================
# Z3-supported parameter types
# =====================================================================

# Types we can encode in Z3 for input generation
_Z3_SUPPORTED = {INT, NAT, BOOL, BYTE}

# Boundary values seeded before the diversity loop
_BOUNDARY_INT = [0, 1, -1, 2, -2, 10, -10, 100, -100]
_BOUNDARY_NAT = [0, 1, 2, 10, 100]
_BOUNDARY_BYTE = [0, 1, 127, 128, 255]
_BOUNDARY_BOOL = [True, False]

# i64 safe range (stays within WASM i64 and JS number precision)
_I64_BOUND = 2**53


# =====================================================================
# Public API
# =====================================================================

def test(
    program: ast.Program,
    source: str = "",
    file: str | None = None,
    trials: int = 100,
    fn_name: str | None = None,
    resolved_modules: list[ResolvedModule] | None = None,
) -> TestResult:
    """Test a type-checked Vera program by generating inputs from contracts.

    1. Run the verifier to classify functions as Tier 1 or Tier 3.
    2. For Tier 3 functions, generate inputs via Z3 from requires() clauses.
    3. Compile to WASM and execute each trial.
    4. Report results.
    """
    engine = _TestEngine(
        program=program,
        source=source,
        file=file,
        trials=trials,
        fn_name=fn_name,
        resolved_modules=resolved_modules,
    )
    return engine.run()


# =====================================================================
# Test engine
# =====================================================================

class _TestEngine:
    """Orchestrates classification, input generation, and execution."""

    def __init__(
        self,
        program: ast.Program,
        source: str,
        file: str | None,
        trials: int,
        fn_name: str | None,
        resolved_modules: list[ResolvedModule] | None,
    ) -> None:
        self.program = program
        self.source = source
        self.file = file
        self.trials = trials
        self.fn_name = fn_name
        self.resolved_modules = resolved_modules or []

    def run(self) -> TestResult:
        """Execute the full test pipeline."""
        from vera.checker import typecheck
        from vera.codegen import compile as codegen_compile
        from vera.verifier import verify

        # 1. Classify functions via the verifier
        verify_result = verify(
            self.program,
            source=self.source,
            file=self.file,
            resolved_modules=self.resolved_modules,
        )
        classification = _classify_functions(
            self.program, verify_result.diagnostics,
        )

        # 2. Filter to target functions
        targets = self._get_targets(classification)

        # 3. Compile (needed for execution)
        compile_result = codegen_compile(
            self.program,
            source=self.source,
            file=self.file,
            resolved_modules=self.resolved_modules,
        )
        compile_errors = [
            d for d in compile_result.diagnostics
            if d.severity == "error"
        ]

        summary = TestSummary()
        results: list[FunctionTestResult] = []
        diagnostics: list[Diagnostic] = []

        for fn_name, category, reason, decl in targets:
            if category == "verified":
                summary.verified += 1
                results.append(FunctionTestResult(
                    fn_name=fn_name,
                    category="verified",
                    reason=reason,
                    trials_run=0,
                    trials_passed=0,
                    trials_failed=0,
                    failures=[],
                ))
                continue

            if category == "skipped":
                summary.skipped += 1
                results.append(FunctionTestResult(
                    fn_name=fn_name,
                    category="skipped",
                    reason=reason,
                    trials_run=0,
                    trials_passed=0,
                    trials_failed=0,
                    failures=[],
                ))
                continue

            # category == "tier3" — generate inputs and execute
            if compile_errors:  # pragma: no cover — compile errors already caught before tier3
                summary.skipped += 1
                results.append(FunctionTestResult(
                    fn_name=fn_name,
                    category="skipped",
                    reason="compilation errors",
                    trials_run=0,
                    trials_passed=0,
                    trials_failed=0,
                    failures=[],
                ))
                continue

            # Check if function is exported
            if fn_name not in compile_result.exports:  # pragma: no cover — _get_targets filters private fns
                summary.skipped += 1
                results.append(FunctionTestResult(
                    fn_name=fn_name,
                    category="skipped",
                    reason="not exported (private)",
                    trials_run=0,
                    trials_passed=0,
                    trials_failed=0,
                    failures=[],
                ))
                continue

            # Generate inputs
            param_types = _get_param_types(decl)
            inputs = _generate_inputs(decl, param_types, self.trials)

            if inputs is None:  # pragma: no cover — _classify_functions filters unsupported types
                unsupported_names = sorted({
                    t.name if isinstance(t, PrimitiveType) else type(t).__name__
                    for pt in param_types
                    for t in (base_type(pt),)
                    if t not in _Z3_SUPPORTED
                })
                skip_reason = f"cannot generate {', '.join(unsupported_names)} inputs (see #169)"
                summary.skipped += 1
                results.append(FunctionTestResult(
                    fn_name=fn_name,
                    category="skipped",
                    reason=skip_reason,
                    trials_run=0,
                    trials_passed=0,
                    trials_failed=0,
                    failures=[],
                ))
                diagnostics.append(Diagnostic(
                    description=(
                        f"Cannot generate test inputs for '{fn_name}': "
                        f"parameter types are not Z3-encodable."
                    ),
                    location=_fn_location(decl, self.file),
                    source_line=_get_source_line(self.source, decl),
                    severity="warning",
                    error_code="E701",
                ))
                continue

            if not inputs:
                # Precondition is unsatisfiable
                summary.skipped += 1
                results.append(FunctionTestResult(
                    fn_name=fn_name,
                    category="skipped",
                    reason="precondition is unsatisfiable (no valid inputs)",
                    trials_run=0,
                    trials_passed=0,
                    trials_failed=0,
                    failures=[],
                ))
                continue

            # Run trials
            trial_results = _run_trials(
                compile_result, fn_name, inputs, param_types, decl,
            )

            n_passed = sum(1 for t in trial_results if t.status == "pass")
            n_failed = sum(
                1 for t in trial_results if t.status in ("fail", "error")
            )
            failures = [
                t for t in trial_results if t.status in ("fail", "error")
            ]

            summary.tested += 1
            summary.total_trials += len(trial_results)
            summary.total_passes += n_passed
            summary.total_failures += n_failed

            if n_failed > 0:
                summary.failed += 1
                # Record diagnostic for each unique failure
                for trial in failures[:3]:  # limit to first 3
                    diagnostics.append(Diagnostic(
                        description=(
                            f"Contract violation in '{fn_name}': "
                            f"{trial.message}"
                        ),
                        location=_fn_location(decl, self.file),
                        source_line=_get_source_line(self.source, decl),
                        severity="error",
                        error_code="E700",
                    ))
            else:
                summary.passed += 1

            results.append(FunctionTestResult(
                fn_name=fn_name,
                category="tested",
                reason="Tier 3 contract (runtime check)",
                trials_run=len(trial_results),
                trials_passed=n_passed,
                trials_failed=n_failed,
                failures=failures,
            ))

        return TestResult(
            functions=results,
            summary=summary,
            diagnostics=diagnostics,
        )

    def _get_targets(
        self,
        classification: dict[str, tuple[str, str, ast.FnDecl]],
    ) -> list[tuple[str, str, str, ast.FnDecl]]:
        """Return (name, category, reason, decl) for each target function."""
        targets: list[tuple[str, str, str, ast.FnDecl]] = []

        for tld in self.program.declarations:
            if not isinstance(tld.decl, ast.FnDecl):
                continue
            decl = tld.decl

            # Skip private functions
            if tld.visibility != "public":
                continue

            # Filter by --fn if specified
            if self.fn_name and decl.name != self.fn_name:
                continue

            if decl.name in classification:
                cat, reason, _ = classification[decl.name]
                targets.append((decl.name, cat, reason, decl))
            else:  # pragma: no cover — all public fns are classified
                targets.append((
                    decl.name, "skipped", "not classifiable", decl,
                ))

        return targets


# =====================================================================
# Function classification
# =====================================================================

def _classify_functions(
    program: ast.Program,
    verify_diagnostics: list[Diagnostic],
) -> dict[str, tuple[str, str, ast.FnDecl]]:
    """Classify each function as verified/tier3/skipped.

    Returns {name: (category, reason, decl)}.
    """
    # Collect function names mentioned in Tier 3 warnings
    tier3_fns: set[str] = set()
    tier3_codes = {"E520", "E521", "E522", "E523", "E524", "E525"}
    for diag in verify_diagnostics:
        if diag.severity == "warning" and diag.error_code in tier3_codes:
            # Extract fn name from description: '...'
            m = re.search(r"'(\w+)'", diag.description)
            if m:
                tier3_fns.add(m.group(1))

    result: dict[str, tuple[str, str, ast.FnDecl]] = {}

    for tld in program.declarations:
        if not isinstance(tld.decl, ast.FnDecl):
            continue
        decl = tld.decl

        # Skip private functions
        if tld.visibility != "public":
            continue

        # Generic → skip
        if decl.forall_vars:
            result[decl.name] = ("skipped", "generic function", decl)
            continue

        # Check parameter types
        param_types = _get_param_types(decl)
        has_unsupported = any(
            base_type(pt) not in _Z3_SUPPORTED for pt in param_types
        )

        # Unit-only params (no real params to test)
        if all(base_type(pt) == UNIT for pt in param_types):
            # If it has non-trivial contracts, still classify
            has_nontrivial = _has_nontrivial_contracts(decl)
            if not has_nontrivial:
                result[decl.name] = ("skipped", "trivial contracts only", decl)
                continue
            # Unit param + non-trivial contracts → Tier 1 or skip
            if decl.name in tier3_fns:
                result[decl.name] = (
                    "skipped",
                    "Tier 3 but no testable parameters",
                    decl,
                )
            else:
                result[decl.name] = ("verified", "Tier 1 (proved)", decl)
            continue

        # Unsupported param types → skip
        if has_unsupported:
            unsupported_names = sorted({
                t.name if isinstance(t, PrimitiveType) else type(t).__name__
                for pt in param_types
                for t in (base_type(pt),)
                if t not in _Z3_SUPPORTED
            })
            result[decl.name] = (
                "skipped",
                f"cannot generate {', '.join(unsupported_names)} inputs (see #169)",
                decl,
            )
            continue

        # Trivial contracts only → skip
        if not _has_nontrivial_contracts(decl):
            result[decl.name] = ("skipped", "trivial contracts only", decl)
            continue

        # Tier 3 → test
        if decl.name in tier3_fns:
            result[decl.name] = (
                "tier3", "Tier 3 contract (runtime check)", decl,
            )
            continue

        # Has non-trivial contracts and all proved → verified
        result[decl.name] = ("verified", "Tier 1 (proved)", decl)

    return result


def _has_nontrivial_contracts(decl: ast.FnDecl) -> bool:
    """Check if a function has any non-trivial requires/ensures."""
    for contract in decl.contracts:
        if isinstance(contract, (ast.Requires, ast.Ensures)):
            if not (
                isinstance(contract.expr, ast.BoolLit) and contract.expr.value
            ):
                return True
        if isinstance(contract, ast.Decreases):
            return True
    return False


def _get_param_types(decl: ast.FnDecl) -> list[Type]:
    """Resolve parameter types for a function declaration."""
    from vera.types import PRIMITIVES
    types: list[Type] = []
    for param_te in decl.params:
        if isinstance(param_te, ast.NamedType):
            ty = PRIMITIVES.get(param_te.name)
            if ty is not None:
                types.append(ty)
            else:
                # Non-primitive (ADT, etc.)
                types.append(Type())
        elif isinstance(param_te, ast.RefinementType):
            if isinstance(param_te.base_type, ast.NamedType):
                ty = PRIMITIVES.get(param_te.base_type.name)
                if ty is not None:
                    types.append(RefinedType(ty, param_te.predicate))
                else:
                    types.append(Type())
            else:
                types.append(Type())
        else:
            types.append(Type())
    return types


# =====================================================================
# Z3 input generation
# =====================================================================

def _generate_inputs(
    decl: ast.FnDecl,
    param_types: list[Type],
    count: int,
) -> list[list[int]] | None:
    """Generate test inputs from requires() clauses via Z3.

    Returns None if any parameter type is unsupported.
    Returns empty list if precondition is unsatisfiable.
    """
    # 1. Check all param types are Z3-supported
    for pt in param_types:
        bt = base_type(pt)
        if bt not in _Z3_SUPPORTED:
            return None

    # 2. Declare Z3 variables
    smt = SmtContext(timeout_ms=5000)
    slot_env = SlotEnv()
    z3_vars: list[z3.ExprRef] = []
    var_types: list[Type] = []  # base types for each var

    for i, (param_te, param_ty) in enumerate(zip(decl.params, param_types)):
        bt = base_type(param_ty)
        type_name = _type_expr_to_slot_name(param_te)
        slot_idx = _count_slots(slot_env, type_name)
        z3_name = f"@{type_name}.{slot_idx}"

        if bt == NAT:
            var = smt.declare_nat(z3_name)
        elif bt == BOOL:
            var = smt.declare_bool(z3_name)
        elif bt == BYTE:
            var = smt.declare_int(z3_name)
            smt.solver.add(var >= 0)
            smt.solver.add(var <= 255)
        else:
            # Int
            var = smt.declare_int(z3_name)

        slot_env = slot_env.push(type_name, var)
        z3_vars.append(var)
        var_types.append(bt)

    # 3. Bound Int/Nat to i64-safe range
    for var, bt in zip(z3_vars, var_types):
        if bt == INT:
            smt.solver.add(var >= -_I64_BOUND)
            smt.solver.add(var <= _I64_BOUND)
        elif bt == NAT:
            smt.solver.add(var <= _I64_BOUND)

    # 4. Translate requires() clauses to Z3 constraints
    for contract in decl.contracts:
        if not isinstance(contract, ast.Requires):
            continue
        if isinstance(contract.expr, ast.BoolLit) and contract.expr.value:
            continue  # skip trivial requires(true)
        z3_expr = smt.translate_expr(contract.expr, slot_env)
        if z3_expr is not None:
            smt.solver.add(z3_expr)
        # If untranslatable, we skip the constraint (best-effort)

    # 5. Collect inputs: boundary seeding + diversity loop
    inputs: list[list[int]] = []
    seen: set[tuple[int, ...]] = set()

    # Boundary seeding
    _seed_boundaries(smt, z3_vars, var_types, inputs, seen)

    # Diversity loop
    while len(inputs) < count:
        result = smt.solver.check()
        if result != z3.sat:
            break  # unsat or unknown → stop

        model = smt.solver.model()
        values = _extract_values(model, z3_vars, var_types)
        key = tuple(values)
        if key not in seen:
            seen.add(key)
            inputs.append(values)

        # Add blocking clause to get diverse inputs
        block = z3.Or([
            var != model.evaluate(var, model_completion=True)
            for var in z3_vars
        ])
        smt.solver.add(block)

    return inputs


def _seed_boundaries(
    smt: SmtContext,
    z3_vars: list[z3.ExprRef],
    var_types: list[Type],
    inputs: list[list[int]],
    seen: set[tuple[int, ...]],
) -> None:
    """Try boundary values for each parameter."""
    for i, (var, bt) in enumerate(zip(z3_vars, var_types)):
        boundaries: list[int | bool]
        if bt == BOOL:
            boundaries = list(_BOUNDARY_BOOL)
        elif bt == BYTE:
            boundaries = list(_BOUNDARY_BYTE)
        elif bt == NAT:
            boundaries = list(_BOUNDARY_NAT)
        else:
            boundaries = list(_BOUNDARY_INT)

        for bval in boundaries:
            smt.solver.push()
            if bt == BOOL:
                smt.solver.add(var == z3.BoolVal(bval))
            else:
                smt.solver.add(var == bval)

            if smt.solver.check() == z3.sat:
                model = smt.solver.model()
                values = _extract_values(model, z3_vars, var_types)
                key = tuple(values)
                if key not in seen:
                    seen.add(key)
                    inputs.append(values)
            smt.solver.pop()


def _extract_values(
    model: z3.ModelRef,
    z3_vars: list[z3.ExprRef],
    var_types: list[Type],
) -> list[int]:
    """Extract Python int values from a Z3 model."""
    values: list[int] = []
    for var, bt in zip(z3_vars, var_types):
        val = model.evaluate(var, model_completion=True)
        if bt == BOOL:
            # Convert to 0/1 for WASM
            values.append(1 if z3.is_true(val) else 0)
        else:
            values.append(int(str(val)))
    return values


# =====================================================================
# Test execution
# =====================================================================

def _run_trials(
    compile_result: object,
    fn_name: str,
    inputs: list[list[int]],
    param_types: list[Type],
    decl: ast.FnDecl,
) -> list[TrialResult]:
    """Execute test trials against the compiled WASM module."""
    from vera.codegen import execute

    results: list[TrialResult] = []
    for args in inputs:
        # Build descriptive arg dict
        arg_dict: dict[str, int | float] = {}
        slot_counts: dict[str, int] = {}
        for param_te, val in zip(decl.params, args):
            tname = _type_expr_to_slot_name(param_te)
            idx = slot_counts.get(tname, 0)
            arg_dict[f"@{tname}.{idx}"] = val
            slot_counts[tname] = idx + 1

        try:
            execute(compile_result, fn_name=fn_name, args=args)  # type: ignore[arg-type]
            results.append(TrialResult(
                fn_name=fn_name, args=arg_dict,
                status="pass", message="",
            ))
        except RuntimeError as e:
            msg = str(e)
            if "contract" in msg.lower() or "ensures" in msg.lower():
                results.append(TrialResult(
                    fn_name=fn_name, args=arg_dict,
                    status="fail", message=msg,
                ))
            else:  # pragma: no cover — non-contract RuntimeError during WASM execution
                results.append(TrialResult(
                    fn_name=fn_name, args=arg_dict,
                    status="error", message=msg,
                ))
        except Exception as e:  # pragma: no cover — WASM traps, stack overflow, etc.
            exc_name = type(e).__name__
            if exc_name in ("Trap", "WasmtimeError"):
                msg = str(e)
                if "contract" in msg.lower():
                    results.append(TrialResult(
                        fn_name=fn_name, args=arg_dict,
                        status="fail", message=msg,
                    ))
                else:
                    results.append(TrialResult(
                        fn_name=fn_name, args=arg_dict,
                        status="error", message=msg,
                    ))
            else:
                results.append(TrialResult(
                    fn_name=fn_name, args=arg_dict,
                    status="error", message=str(e),
                ))

    return results


# =====================================================================
# Helpers
# =====================================================================

def _type_expr_to_slot_name(te: ast.TypeExpr) -> str:
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
        return _type_expr_to_slot_name(te.base_type)
    return "?"


def _count_slots(env: SlotEnv, type_name: str) -> int:
    """Count how many slots exist for a type name."""
    stack = env._stacks.get(type_name, [])
    return len(stack)


def _fn_location(decl: ast.FnDecl, file: str | None) -> SourceLocation:
    """Build a SourceLocation from a FnDecl."""
    loc = SourceLocation(file=file)
    if decl.span:
        loc.line = decl.span.line
        loc.column = decl.span.column
    return loc


def _get_source_line(source: str, decl: ast.FnDecl) -> str:
    """Extract the source line for a function declaration."""
    if decl.span:
        lines = source.splitlines()
        if 1 <= decl.span.line <= len(lines):
            return lines[decl.span.line - 1]
    return ""
