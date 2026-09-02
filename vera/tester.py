"""Vera contract-driven test engine — Z3-guided input generation.

Generates test inputs from requires() clauses via Z3, executes compiled
WASM, and validates ensures() contracts at runtime.  Functions already
proved by the verifier (Tier 1) are reported as "verified"; functions
with Tier 3 contracts are exercised with generated inputs.

See spec/06-contracts.md, Section 6.8 "Summary of Verification Tiers".
"""

from __future__ import annotations

import math
import re
from dataclasses import dataclass
from typing import TYPE_CHECKING

import z3

from vera import ast, naming
from vera.errors import Diagnostic, SourceLocation
from vera.obligations.core import ProofObligation
from vera.naming import EMPTY_ALIAS_ENV, AliasEnv
from vera.slots import fn_slot_scope
from vera.smt import SlotEnv, SmtContext
from vera.types import BOOL, BYTE, FLOAT64, INT, NAT, STRING, UNIT, ModuleArtifacts, PrimitiveType, Type, base_type, pretty_type

if TYPE_CHECKING:
    from vera.codegen import CompileResult
    from vera.resolver import ResolvedModule


# =====================================================================
# Result types
# =====================================================================

@dataclass
class TrialResult:
    """Outcome of a single test trial."""

    fn_name: str
    args: dict[str, int | float | str]  # {"@Int.0": 5, "@String.0": "hello"}
    status: str  # "pass" | "fail" | "error"
    message: str  # violation message or empty


@dataclass
class FunctionTestResult:
    """Test result for a single function."""

    fn_name: str
    category: str  # "verified" | "tested" | "failed" | "skipped"
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
    failed: int = 0  # verifier-refuted or tested + at least one trial failed
    skipped: int = 0  # can't generate inputs
    total_trials: int = 0
    total_passes: int = 0
    total_failures: int = 0
    # Verifier errors whose target function isn't in ``functions``
    # (e.g. when ``--fn`` filters to a subset, or for private
    # functions excluded from the displayed list).  Without this
    # field a CLI consumer would have to re-run the regex
    # attribution itself to spot fail-closed cases; exposing it as
    # structured data on the summary keeps ``vera.tester``'s public
    # API surface small and ``vera/cli.py`` purely presentational.
    unlisted_errors: int = 0


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
_Z3_SUPPORTED = {INT, NAT, BOOL, BYTE, STRING, FLOAT64}

# Types that require the raw_args calling convention (String uses i32_pair ABI)
_NEEDS_RAW = {STRING, FLOAT64}

# Verifier-error codes that cause a function to be classified as
# ``"failed"`` rather than ``"verified"`` / ``"tier3"`` / ``"skipped"``.
# Private — ``vera/cli.py`` no longer needs this set directly; the
# engine attributes errors to functions internally and exposes the
# count of unattributable / filtered-out errors as
# ``TestSummary.unlisted_errors``.
_VERIFICATION_ERROR_CODES = frozenset({"E500", "E501", "E502"})

# The obligation kinds that carry a CONTRACT the programmer wrote, and so the
# kinds whose Tier-3 status means "this clause is checked at runtime, not
# proved" — the question `_classify_functions` is asking (#1375).  Its
# complement is the per-site SAFETY family (nat_sub, nat_bind, refine_bind,
# call_pre, div_zero, index_bounds, int_overflow), where `tier3` means a
# codegen trap rather than a proof is the guard: a property of one operation,
# not a demoted contract, and not something trials can adjudicate.
# `test_every_obligation_kind_is_classified` pins the partition against the
# live ObligationKind vocabulary, so a new kind has to be placed deliberately
# rather than defaulting into whichever side happens to be written first.
_CONTRACT_KINDS = frozenset({"requires", "ensures", "decreases", "assert"})

# The internal classification for a function skipped because the input
# generator cannot model one of its input constraints (#1229).  Distinct from
# plain ``"skipped"`` only so the engine can DISCLOSE the skip as an E701
# warning as well as report it; the reported ``category`` is ``"skipped"``.
_UNTRANSLATABLE_CATEGORY = "skipped_untranslatable"


def _unsupported_type_names(param_types: list[Type]) -> list[str]:
    """Return a sorted list of type names that cannot be Z3-encoded.

    Named by the checker's own :func:`~vera.types.pretty_type`, so the skip
    reason reads in the user's vocabulary: since #1216 the types reaching
    here are the RESOLVED ones, and reporting an ADT parameter as
    ``Option<Int>`` rather than as its Python class name is what makes the
    message actionable.  Primitives keep their bare name (``pretty_type``
    agrees) — only the composite cases change spelling.
    """
    return sorted({
        t.name if isinstance(t, PrimitiveType) else pretty_type(t)
        for pt in param_types
        for t in (base_type(pt),)
        if t not in _Z3_SUPPORTED
    })


# Boundary values seeded before the diversity loop
_BOUNDARY_INT = [0, 1, -1, 2, -2, 10, -10, 100, -100]
_BOUNDARY_NAT = [0, 1, 2, 10, 100]
_BOUNDARY_BYTE = [0, 1, 127, 128, 255]
_BOUNDARY_BOOL = [True, False]
_BOUNDARY_STRING: list[str] = ["", "a", "abc", "hello world", "abc123", "\n", "\t", "   "]
# Float64 boundaries (finite).  NaN / +/-Inf are representable under the FP sort
# (#797) and the verifier reasons about them, but are exercised via contracts
# rather than seeded as test inputs here.
_BOUNDARY_FLOAT64: list[float] = [
    0.0, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, 10.0, -10.0,
    1e10, -1e10, 1e-10, -1e-10,
    # 2^53: the precision boundary where ULP reaches 2, so `x + 1.0 == x` — the
    # exact edge that made the old Real-sort model unsound (#797).
    float(2**53), -float(2**53),
]

# i64 safe range (stays within WASM i64 and JS number precision)
_I64_BOUND = 2**53

# Maximum Z3-generated string length (prevents pathologically long strings)
_MAX_STRING_LEN = 50


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
    expr_semantic_types: dict[tuple[int, int, int, int], Type] | None = None,
    expr_target_types: dict[tuple[int, int, int, int], Type] | None = None,
    module_artifacts: ModuleArtifacts | None = None,
    alias_env: AliasEnv = EMPTY_ALIAS_ENV,
) -> TestResult:
    """Test a type-checked Vera program by generating inputs from contracts.

    1. Run the verifier to classify functions as Tier 1 or Tier 3.
    2. For Tier 3 functions, generate inputs via Z3 from requires() clauses.
    3. Compile to WASM and execute each trial.
    4. Report results.

    ``expr_semantic_types`` / ``expr_target_types`` are the checker's
    resolved- and target-type side-tables (``CheckerArtifacts``).  #986: they
    are threaded into BOTH the verifier (classification) and codegen (the WASM
    the tester executes) so the tester compiles the SAME @Nat->@Int widen guards
    the verifier obligates — without them a tuple/array-component widen guard
    (recovered only from the target table) silently vanished from the
    tester-compiled WASM while the verifier still classified it tier3-guarded.

    ``module_artifacts`` (#987) carries each resolved module's OWN side-tables so
    the tester-compiled WASM also emits the widen guards for IMPORTED bodies —
    the same threading ``vera run`` / ``vera compile`` use.

    ``alias_env`` (#1208) is the checked program's naming environment
    (``CheckArtifacts.alias_env``), carried down to the Z3 input generator so
    the slot names it declares variables under are the checker's.
    """
    engine = _TestEngine(
        program=program,
        source=source,
        file=file,
        trials=trials,
        fn_name=fn_name,
        resolved_modules=resolved_modules,
        expr_semantic_types=expr_semantic_types,
        expr_target_types=expr_target_types,
        module_artifacts=module_artifacts,
        alias_env=alias_env,
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
        expr_semantic_types: (
            dict[tuple[int, int, int, int], Type] | None) = None,
        expr_target_types: (
            dict[tuple[int, int, int, int], Type] | None) = None,
        module_artifacts: ModuleArtifacts | None = None,
        alias_env: AliasEnv = EMPTY_ALIAS_ENV,
    ) -> None:
        self.program = program
        self.source = source
        self.file = file
        self.trials = trials
        self.fn_name = fn_name
        self.resolved_modules = resolved_modules or []
        # #986: the checker's resolved- / target-type side-tables, threaded into
        # both `verify` and `codegen_compile` below so the tester's WASM carries
        # the same widen guards the verifier obligates.
        self.expr_semantic_types = expr_semantic_types
        self.expr_target_types = expr_target_types
        # #987: per-module tables so the tester's WASM emits the widen guards for
        # imported bodies too (threaded into `codegen_compile` below).
        self.module_artifacts = module_artifacts
        # #1208: the checked program's naming environment, threaded into the
        # Z3 input generator so its slot names are the checker's.
        self.alias_env = alias_env

    def run(self) -> TestResult:
        """Execute the full test pipeline."""
        from vera.codegen import compile as codegen_compile
        from vera.verifier import verify

        # 1. Classify functions via the verifier
        verify_result = verify(
            self.program,
            source=self.source,
            file=self.file,
            resolved_modules=self.resolved_modules,
            expr_types=self.expr_semantic_types,
            expr_target_types=self.expr_target_types,
        )
        classification = _classify_functions(
            self.program, verify_result.diagnostics,
            verify_result.obligations, self.alias_env,
        )

        # 2. Filter to target functions
        targets = self._get_targets(classification)
        verifier_errors = [
            d for d in verify_result.diagnostics if d.severity == "error"
        ]

        # 3. Compile (needed for execution)
        compile_result = codegen_compile(
            self.program,
            source=self.source,
            file=self.file,
            resolved_modules=self.resolved_modules,
            expr_semantic_types=self.expr_semantic_types,
            expr_target_types=self.expr_target_types,
            module_artifacts=self.module_artifacts,
        )
        compile_errors = [
            d for d in compile_result.diagnostics
            if d.severity == "error"
        ]

        summary = TestSummary()
        results: list[FunctionTestResult] = []
        diagnostics: list[Diagnostic] = verifier_errors

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

            if category == "failed":
                summary.failed += 1
                results.append(FunctionTestResult(
                    fn_name=fn_name,
                    category="failed",
                    reason=reason,
                    trials_run=0,
                    trials_passed=0,
                    trials_failed=0,
                    failures=[],
                ))
                continue

            if category in ("skipped", _UNTRANSLATABLE_CATEGORY):
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
                if category == _UNTRANSLATABLE_CATEGORY:
                    # #1229: disclose the blocker as a diagnostic too, the way
                    # an un-encodable parameter type does.  A consumer reading
                    # only `diagnostics` would otherwise see a clean run and
                    # never learn that nothing was exercised.
                    diagnostics.append(Diagnostic(
                        description=(
                            f"Skipping test generation for '{fn_name}': "
                            f"{reason}."
                        ),
                        location=_fn_location(decl, self.file),
                        source_line=_get_source_line(self.source, decl),
                        rationale=(
                            "Contract-driven testing generates inputs with Z3 "
                            "from each parameter's type, its refinement "
                            "predicate, and the function's `requires` clauses. "
                            "A constraint the SMT layer cannot translate "
                            "reaches the solver as nothing at all, so the "
                            "inputs it produces may violate it and the "
                            "compiled function traps on its own guard — which "
                            "is a limit of the generator, not a falsified "
                            "contract, so the function is skipped rather than "
                            "reported as failing."
                        ),
                        fix=(
                            "Restate the constraint in terms the SMT layer "
                            "models (for example compare a `string_length` "
                            "against a literal rather than a computed value), "
                            "or exercise this function with a hand-written "
                            "test instead."
                        ),
                        spec_ref=(
                            'Chapter 0, Section 0.5.6 '
                            '"Contract-Driven Testing"'
                        ),
                        severity="warning",
                        error_code="E701",
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

            # Not exported.  `_get_targets` already filtered out private
            # declarations, so the live case here is #1186: a PUBLIC
            # function that codegen DROPPED — its own `[E602]`-class skip,
            # or the `[E620]` it earned by calling something skipped.
            # Reporting that as "private" told the user to fix a
            # visibility modifier that was already correct.
            if fn_name not in compile_result.exports:
                summary.skipped += 1
                results.append(FunctionTestResult(
                    fn_name=fn_name,
                    category="skipped",
                    reason=_not_exported_reason(
                        fn_name, compile_result, self.file,
                    ),
                    trials_run=0,
                    trials_passed=0,
                    trials_failed=0,
                    failures=[],
                ))
                continue

            # Generate inputs
            param_types = _get_param_types(decl, self.alias_env)
            inputs = _generate_inputs(
                decl, param_types, self.trials, self.alias_env)

            if inputs is None:  # pragma: no cover — _classify_functions filters unsupported types
                unsupported_names = _unsupported_type_names(param_types)
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
                    rationale=(
                        "Contract-driven testing synthesises inputs with Z3 "
                        "from each parameter's type; a type Z3 cannot encode "
                        "cannot be exercised, so the function is skipped."
                    ),
                    spec_ref='Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
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
                self.alias_env,
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
                        rationale=(
                            "Contract-driven testing ran the compiled "
                            "function on Z3-generated inputs satisfying its "
                            "`requires`; on a real result it either violated "
                            "an `ensures` clause or trapped at runtime."
                        ),
                        fix=(
                            "Correct the implementation so the postcondition "
                            "holds, or adjust the contract (strengthen "
                            "`requires` / weaken `ensures`) to match the "
                            "intended behaviour."
                        ),
                        spec_ref='Chapter 6, "Contracts"',
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

        # Count verifier errors whose target function isn't in the
        # displayed ``results`` list — happens when ``--fn`` filters
        # to a subset, or when a private helper fails verification
        # (private functions aren't displayed).  Exposing this as
        # structured data on the summary saves CLI consumers from
        # re-running the regex attribution.
        displayed_failed = {
            f.fn_name for f in results if f.category == "failed"
        }
        summary.unlisted_errors = sum(
            1 for d in diagnostics
            if d.severity == "error"
            and d.error_code in _VERIFICATION_ERROR_CODES
            and _failed_function_name(d) not in displayed_failed
        )

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


def _not_exported_reason(
    fn_name: str, compile_result: CompileResult, file: str | None,
) -> str:
    """Why *fn_name* has no WASM export, for the skip line (#1186).

    A codegen drop names the root diagnostic and where to find it — with
    the file too when the root sits in an imported module, matching the
    ``[E620]`` cross-file convention.  Everything else falls back to the
    visibility explanation, the only other way a classified target can be
    missing from the export list.
    """
    if fn_name not in compile_result.dropped_fns:
        return "not exported (private)"
    diag = compile_result.dropped_fns[fn_name]
    if diag is None:  # pragma: no cover — every drop records its diagnostic
        return "not exported (dropped by codegen)"
    where = f"line {diag.location.line}, column {diag.location.column}"
    if diag.location.file and diag.location.file != file:
        where = f"{diag.location.file}, {where}"
    return (
        f"not exported (dropped by codegen — see the "
        f"[{diag.error_code}] warning at {where})"
    )


# =====================================================================
# Function classification
# =====================================================================

def _classify_functions(
    program: ast.Program,
    verify_diagnostics: list[Diagnostic],
    obligations: list[ProofObligation],
    alias_env: AliasEnv = EMPTY_ALIAS_ENV,
) -> dict[str, tuple[str, str, ast.FnDecl]]:
    """Classify each function as verified/tier3/skipped.

    Returns {name: (category, reason, decl)}.

    *alias_env* is the checked program's naming environment, needed because
    the encodability question is asked of each parameter's RESOLVED type
    (#1216); the engine passes its own, and the default keeps every alias
    opaque for a caller that has none.
    """
    # #1375: read the OBLIGATION STREAM, the same source `verify --json`
    # reports and `summarize` counts from.  This was a re-derivation — a
    # hardcoded set of Tier-3 warning codes, with the function name recovered
    # by regex from the diagnostic's prose — and a re-derivation of a fact that
    # already exists goes stale the moment a code is added.  It had: E534
    # (#1363's demotion) was absent, so a contract this run demoted to
    # runtime-only truth read back as "Tier 1 (proved)" and was EXCLUDED from
    # trials — the one contract most in need of them.  Statuses carry
    # `fn_name` directly, so the regex goes with the list.
    #
    # Scoped to the CONTRACT kinds, which is what the diagnostic-keyed set
    # covered: only these emit a function-named Tier-3 warning, so only these
    # ever entered it.  The obligation stream is strictly wider — it also
    # carries the per-site SAFETY kinds (int_overflow, nat_bind, div_zero,
    # index_bounds, ...), which are `tier3` whenever a codegen trap rather
    # than a proof is the guard, and which mostly carry no diagnostic at all.
    # Those are not contract demotions: `abs_val` above has both its clauses
    # proved and one `int_overflow` site, and testing it would run trials
    # against a function whose contracts are already Tier 1 — where a trap the
    # guard fires legitimately scores as a falsified contract, the #1229
    # hazard the call below exists to avoid.  Keying on `kind` also outlasts
    # the code list it replaces: ObligationKind is a closed vocabulary, so a
    # new Tier-3 *code* on an existing kind (E534 was exactly that) is picked
    # up by construction.
    tier3_fns: set[str] = {
        o.fn_name
        for o in obligations
        if o.status in ("tier3", "timeout") and o.kind in _CONTRACT_KINDS
    }
    failed_fns: dict[str, str] = {}
    for diag in verify_diagnostics:
        if (
            diag.severity == "error"
            and diag.error_code in _VERIFICATION_ERROR_CODES
        ):
            name = _failed_function_name(diag)
            # First-hit wins: if a single function attracts multiple
            # verifier errors (e.g. ``ensures(false)`` produces E500
            # AND `@Nat - @Nat` produces E502 on the same body), the
            # displayed ``reason`` would otherwise depend on
            # diagnostic iteration order.  ``setdefault`` pins it to
            # whichever diagnostic the verifier emitted first.
            if name and name not in failed_fns:
                failed_fns[name] = diag.error_code or "verification error"

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
        param_types = _get_param_types(decl, alias_env)
        has_unsupported = any(
            base_type(pt) not in _Z3_SUPPORTED for pt in param_types
        )

        # Verifier-refuted contracts fail before any verified/tier3/skipped result.
        if decl.name in failed_fns:
            result[decl.name] = (
                "failed", f"verification error ({failed_fns[decl.name]})", decl,
            )
            continue

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
            unsupported_names = _unsupported_type_names(param_types)
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

        # Tier 3 → test, unless the generator cannot honour the precondition.
        # #1229: a constraint the SMT layer defers on reaches the solver as
        # nothing at all, so the inputs may violate it, the compiled function
        # traps on its own guard, and the trial loop scores that trap as a
        # falsified contract — a generator limitation reported as a broken
        # program, which spec §0.3 forbids.  Asked only here, where the answer
        # can change an outcome: a Tier-1 function is never exercised, so an
        # untranslatable clause on one costs nothing and demoting it to
        # "skipped" would throw away a proof.
        if decl.name in tier3_fns:
            blockers = _untranslatable_input_constraints(
                decl, param_types, alias_env,
            )
            if blockers:
                result[decl.name] = (
                    _UNTRANSLATABLE_CATEGORY,
                    _untranslatable_skip_reason(blockers),
                    decl,
                )
                continue
            result[decl.name] = (
                "tier3", "Tier 3 contract (runtime check)", decl,
            )
            continue

        # Has non-trivial contracts and all proved → verified
        result[decl.name] = ("verified", "Tier 1 (proved)", decl)

    return result


def _failed_function_name(diag: Diagnostic) -> str | None:
    """Extract the function responsible for a verifier error diagnostic.

    Private — used internally by ``_classify_functions`` and by the
    engine's ``unlisted_errors`` computation.  ``vera/cli.py`` reads
    the resulting structured count via ``TestSummary.unlisted_errors``
    rather than calling this helper directly.  Returns ``None`` when
    the diagnostic's description doesn't include an attributable
    function name (defensive — the verifier always emits these in
    the expected shape, but the regex match is checked).
    """
    if diag.error_code == "E501":
        # E501 text mentions both callee and caller:
        # "Call to 'callee' in function 'caller' may violate...".
        m = re.search(r"in function '(\w+)'", diag.description)
        if m:
            return m.group(1)

    # E500: "Postcondition does not hold in function 'fn'."
    m = re.search(r"in function '(\w+)'", diag.description)
    if m:
        return m.group(1)

    # E502: "@Nat subtraction in 'fn' may underflow."
    m = re.search(r"in '(\w+)'", diag.description)
    if m:
        return m.group(1)

    return None


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


def _get_param_types(decl: ast.FnDecl, alias_env: AliasEnv) -> list[Type]:
    """The semantic type of each parameter, as the CHECKER resolves it (#1216).

    One resolution, :func:`vera.naming.resolve_type_expr`, against the naming
    environment of the module that declared *decl* — narrowed by the
    function's own ``forall`` variables, which shadow same-named module
    aliases exactly as they do for the checker.  The pre-#1216 derivation
    matched a parameter's SYNTACTIC head against ``PRIMITIVES``, so
    ``type Cnt = Int`` never reached ``Int``: every alias-typed signature was
    classified un-encodable and skipped (E701) although its resolved type is
    ordinary Z3-encodable ``Int``.

    Resolving is not the same as being encodable: an ADT, a function type, a
    type variable and an unresolvable expression all resolve to types
    :data:`_Z3_SUPPORTED` does not contain, and the caller still skips them —
    now by the resolved answer rather than by the spelling.
    """
    scope = fn_slot_scope(alias_env, decl.forall_vars)
    return [naming.resolve_type_expr(te, scope) for te in decl.params]


# =====================================================================
# Z3 input generation
# =====================================================================

@dataclass
class _GenEnv:
    """The Z3 declarations a function's parameters make (#1229 helper).

    Shared by :func:`_generate_inputs` and
    :func:`_untranslatable_input_constraints` so the question "can this
    constraint be translated?" is asked against exactly the declarations the
    generator will translate it against.  Answered from a second, separately
    built context, the two could disagree — and a disagreement here is a
    function reported as testable whose precondition the generator then
    ignores, which is #1229.
    """

    smt: SmtContext
    scope: AliasEnv
    slot_env: SlotEnv
    z3_vars: list[z3.ExprRef]
    var_types: list[Type]


def _declare_param_vars(
    decl: ast.FnDecl,
    param_types: list[Type],
    alias_env: AliasEnv,
) -> _GenEnv | None:
    """Declare one Z3 variable per parameter, range-bounded.

    Returns None if any parameter type is outside :data:`_Z3_SUPPORTED`.

    Names every variable in the function's own slot scope — the module
    environment narrowed by its ``forall`` variables (#1216), the same
    narrowing the checker applies before it binds these parameters.  The SMT
    context gets the SAME narrowed scope (#1208): it is what
    ``_translate_slot_ref`` resolves a ``requires`` clause's ``@T.n`` against,
    so handing it the un-narrowed env would look up under a key the bind side
    never pushed — exactly once a ``forall`` variable shadows a same-named
    module alias.
    """
    for pt in param_types:
        if base_type(pt) not in _Z3_SUPPORTED:
            return None

    scope = fn_slot_scope(alias_env, decl.forall_vars)
    smt = SmtContext(timeout_ms=5000, alias_env=scope)
    slot_env = SlotEnv()
    z3_vars: list[z3.ExprRef] = []
    var_types: list[Type] = []  # base types for each var

    for param_te, param_ty in zip(decl.params, param_types):
        bt = base_type(param_ty)
        type_name = _type_expr_to_slot_name(param_te, scope)
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
        elif bt == STRING:
            var = smt.declare_string(z3_name)
            smt.solver.add(z3.Length(var) <= _MAX_STRING_LEN)
        elif bt == FLOAT64:
            var = smt.declare_float64(z3_name)
        else:
            # Int
            var = smt.declare_int(z3_name)

        slot_env = slot_env.push(type_name, var)
        z3_vars.append(var)
        var_types.append(bt)

    # Bound Int/Nat to i64-safe range
    for var, bt in zip(z3_vars, var_types):
        if bt == INT:
            smt.solver.add(var >= -_I64_BOUND)
            smt.solver.add(var <= _I64_BOUND)
        elif bt == NAT:
            smt.solver.add(var <= _I64_BOUND)

    return _GenEnv(
        smt=smt, scope=scope, slot_env=slot_env,
        z3_vars=z3_vars, var_types=var_types,
    )


def _conjuncts(expr: ast.Expr) -> list[ast.Expr]:
    """*expr* split at its top-level ``&&``, left to right.

    Conjunct granularity is what makes the #1229 skip reason actionable: a
    clause is untranslatable as a whole the moment ONE of its conjuncts is, so
    quoting the clause would name the translatable half as a blocker too.
    """
    if isinstance(expr, ast.BinaryExpr) and expr.op == ast.BinOp.AND:
        return _conjuncts(expr.left) + _conjuncts(expr.right)
    return [expr]


def _untranslatable_input_constraints(
    decl: ast.FnDecl,
    param_types: list[Type],
    alias_env: AliasEnv,
) -> list[str]:
    """The input-shaping constraints the SMT layer cannot translate (#1229).

    Each entry is a rendered expression the generated inputs are REQUIRED to
    satisfy and which the solver will never be told about, so any input it
    produces may violate it — and the compiled function's own entry guard then
    traps, which the trial loop scores as a contract failure.  A correct
    program reported ``19/20 passed, 1 failed`` that way.

    Two sources, one rule.  A ``requires`` conjunct is the reported one:
    ``string_length`` over a non-literal is deliberately untranslatable (#802 —
    Vera counts UTF-8 bytes, Z3's ``Length`` counts code points, and Z3's
    string theory has no byte-length operator), so ``requires(string_length(x)
    > 0)`` constrains nothing and ``_seed_boundaries`` offers ``""``.  A
    refined PARAMETER's predicate is the same defect one door over: it is part
    of the parameter's type rather than of its contract, so no clause states
    it, and codegen emits it as an entry guard all the same.

    The detection is the MECHANISM, not a list of built-ins: it asks the SMT
    layer and believes the answer.  The tester's context is deliberately bare —
    no ``_fn_lookup``, no ADT registry — so a great deal more than
    ``string_length`` defers here (every call to a user function, every
    built-in without an explicit translation branch, every quantifier), and a
    hand-maintained list would have been incomplete the day it was written.

    An empty list means every constraint translated — the generator can honour
    the whole precondition, and the trials it runs mean what they say.
    """
    env = _declare_param_vars(decl, param_types, alias_env)
    if env is None:
        # Unsupported parameter types; the `cannot generate <T> inputs` skip
        # already covers this function and names the types.
        return []

    blockers: list[str] = []
    for param_te, var in zip(decl.params, env.z3_vars):
        parts = naming.refinement_binder_parts(param_te, env.scope)
        if parts is None or parts.base_is_refinement:
            continue
        if env.smt.translate_expr(
            parts.predicate, SlotEnv().push(parts.binder_name, var),
        ) is None:
            blockers.append(ast.format_expr(parts.predicate))

    for contract in decl.contracts:
        if not isinstance(contract, ast.Requires):
            continue
        for conjunct in _conjuncts(contract.expr):
            if isinstance(conjunct, ast.BoolLit) and conjunct.value:
                continue  # trivial `true` constrains nothing by design
            if env.smt.translate_expr(conjunct, env.slot_env) is None:
                blockers.append(ast.format_expr(conjunct))
    return blockers


def _untranslatable_skip_reason(blockers: list[str]) -> str:
    """The skip line for a function blocked by *blockers* (#1229).

    Mirrors the ``cannot generate <T> inputs (see #169)`` taxonomy: name the
    blocker, not merely the outcome.  "skipped" on its own would be no more
    actionable than the wrong FAILED it replaces.
    """
    quoted = ", ".join(f"`{b}`" for b in blockers)
    return f"cannot generate inputs satisfying {quoted} (see #1229)"


def _generate_inputs(
    decl: ast.FnDecl,
    param_types: list[Type],
    count: int,
    alias_env: AliasEnv = EMPTY_ALIAS_ENV,
) -> list[list[int | float | str]] | None:
    """Generate test inputs from requires() clauses via Z3.

    Returns None if any parameter type is unsupported.
    Returns empty list if precondition is unsatisfiable.

    Callers reach here only after :func:`_untranslatable_input_constraints`
    has come back empty, so every constraint below translates and the
    ``is not None`` guards are the belt to that braces (#1229).
    """
    env = _declare_param_vars(decl, param_types, alias_env)
    if env is None:
        return None
    smt, scope, slot_env = env.smt, env.scope, env.slot_env
    z3_vars, var_types = env.z3_vars, env.var_types

    # 3b. Refinement membership.  A refined parameter's predicate is part of
    # its TYPE, not of its contract, so no `requires` clause states it — and
    # codegen emits it as an entry guard that traps on a violating argument.
    # Since #1216 a refined alias reaches here (a refinement is unwritable in
    # parameter position, so an alias is the only way to have one), and an
    # unconstrained generator would manufacture arguments the guard rejects
    # and report the trap as a contract failure.  The binder comes from
    # `vera.naming`, so the predicate's own `@Base.n` resolves onto this
    # variable under exactly the name codegen's guard pushes it under.
    #
    # The binder is the SOLE slot in scope (spec §2.6): the checker isolates
    # the scope stack for the predicate rather than pushing onto it
    # (`_check_one_refinement_predicate`), so translating against a FRESH
    # `SlotEnv` rather than the accumulated one keeps this side to the same
    # rule.  Pushing onto the accumulated env instead let a `@Base.1` in the
    # predicate capture a sibling parameter's variable — a constraint the
    # emitted guard never checks.  The checker rejects such a predicate
    # (E130) so no check-clean program reaches it; isolating here means a
    # future scoping change cannot turn that into a silent wrong constraint.
    for param_te, var in zip(decl.params, z3_vars):
        parts = naming.refinement_binder_parts(param_te, scope)
        if parts is None or parts.base_is_refinement:
            continue
        membership = smt.translate_expr(
            parts.predicate, SlotEnv().push(parts.binder_name, var),
        )
        if membership is not None:
            smt.solver.add(membership)

    # 4. Translate requires() clauses to Z3 constraints
    for contract in decl.contracts:
        if not isinstance(contract, ast.Requires):
            continue
        if isinstance(contract.expr, ast.BoolLit) and contract.expr.value:
            continue  # skip trivial requires(true)
        z3_expr = smt.translate_expr(contract.expr, slot_env)
        if z3_expr is not None:
            smt.solver.add(z3_expr)
        # Untranslatable clauses never reach here: `_classify_functions` skips
        # the function first, naming the conjunct (#1229).  Dropping one
        # silently is what let the generator manufacture inputs the
        # precondition forbids and score the resulting trap as a failure.

    # 5. Collect inputs: boundary seeding + diversity loop
    inputs: list[list[int | float | str]] = []
    seen: set[tuple[int | float | str, ...]] = set()

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
    inputs: list[list[int | float | str]],
    seen: set[tuple[int | float | str, ...]],
) -> None:
    """Try boundary values for each parameter."""
    for i, (var, bt) in enumerate(zip(z3_vars, var_types)):
        if bt == STRING:
            for sval in _BOUNDARY_STRING:
                smt.solver.push()
                smt.solver.add(var == z3.StringVal(sval))
                if smt.solver.check() == z3.sat:
                    model = smt.solver.model()
                    values = _extract_values(model, z3_vars, var_types)
                    key = tuple(values)
                    if key not in seen:
                        seen.add(key)
                        inputs.append(values)
                smt.solver.pop()
            continue

        if bt == FLOAT64:
            for fval in _BOUNDARY_FLOAT64:
                smt.solver.push()
                # #797: Float64 is a FloatingPoint sort now, so constrain with an
                # FP literal at the var's sort (a Real literal is a sort
                # mismatch).  Structural `==` pins the exact value.
                smt.solver.add(var == z3.FPVal(fval, var.sort()))
                if smt.solver.check() == z3.sat:
                    model = smt.solver.model()
                    values = _extract_values(model, z3_vars, var_types)
                    key = tuple(values)
                    if key not in seen:
                        seen.add(key)
                        inputs.append(values)
                smt.solver.pop()
            continue

        boundaries: list[int | bool]
        if bt == BOOL:
            boundaries = list(_BOUNDARY_BOOL)
        elif bt == BYTE:
            boundaries = list(_BOUNDARY_BYTE)
        elif bt == NAT:
            boundaries = list(_BOUNDARY_NAT)
        else:
            boundaries = list(_BOUNDARY_INT)

        for ival in boundaries:
            smt.solver.push()
            if bt == BOOL:
                smt.solver.add(var == z3.BoolVal(ival))
            else:
                smt.solver.add(var == ival)

            if smt.solver.check() == z3.sat:
                model = smt.solver.model()
                values = _extract_values(model, z3_vars, var_types)
                key = tuple(values)
                if key not in seen:
                    seen.add(key)
                    inputs.append(values)
            smt.solver.pop()


def _fp_value_to_float(val: z3.FPRef) -> float:
    """Convert a Z3 FloatingPoint model value to a Python float (#797).

    The model value is an ``FPNumRef``: NaN / +/-Inf map to their Python
    counterparts, and a finite value goes through ``fpToReal`` (exact), with the
    sign of zero preserved.
    """
    if val.isNaN():
        return math.nan
    if val.isInf():
        return -math.inf if val.isNegative() else math.inf
    f = float(z3.simplify(z3.fpToReal(val)).as_fraction())
    return -0.0 if (f == 0.0 and val.isNegative()) else f


def _extract_values(
    model: z3.ModelRef,
    z3_vars: list[z3.ExprRef],
    var_types: list[Type],
) -> list[int | float | str]:
    """Extract Python values from a Z3 model."""
    values: list[int | float | str] = []
    for var, bt in zip(z3_vars, var_types):
        val = model.evaluate(var, model_completion=True)
        if bt == BOOL:
            # Convert to 0/1 for WASM
            values.append(1 if z3.is_true(val) else 0)
        elif bt == STRING:
            values.append(z3.simplify(val).as_string())
        elif bt == FLOAT64:
            values.append(_fp_value_to_float(val))
        else:
            values.append(int(str(val)))
    return values


# =====================================================================
# Test execution
# =====================================================================

def _run_trials(
    compile_result: object,
    fn_name: str,
    inputs: list[list[int | float | str]],
    param_types: list[Type],
    decl: ast.FnDecl,
    alias_env: AliasEnv,
) -> list[TrialResult]:
    """Execute test trials against the compiled WASM module.

    Labels each argument in the function's own slot scope — the module
    environment narrowed by its ``forall`` variables (#1216) — so a reported
    failure names the argument the way the source's own `@T.n` references do.
    """
    from vera.codegen import execute

    # String uses i32_pair ABI (two WASM params); Float64 has string→float
    # parsing. Both require the raw_args calling convention.
    needs_raw = any(base_type(pt) in _NEEDS_RAW for pt in param_types)
    scope = fn_slot_scope(alias_env, decl.forall_vars)

    results: list[TrialResult] = []
    for args in inputs:
        # Build descriptive arg dict
        arg_dict: dict[str, int | float | str] = {}
        slot_counts: dict[str, int] = {}
        for param_te, val in zip(decl.params, args):
            tname = _type_expr_to_slot_name(param_te, scope)
            idx = slot_counts.get(tname, 0)
            arg_dict[f"@{tname}.{idx}"] = val
            slot_counts[tname] = idx + 1

        try:
            if needs_raw:
                execute(compile_result, fn_name=fn_name, raw_args=[str(v) for v in args])  # type: ignore[arg-type]
            else:
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
        except Exception as e:  # pragma: no cover — WASM traps, stack overflow, etc.  # noqa: BLE001
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

def _type_expr_to_slot_name(te: ast.TypeExpr, alias_env: AliasEnv) -> str:
    """The slot-binding name of *te*, as the checker binds it (#1208).

    Delegates to :func:`vera.naming.slot_name` against the checked program's
    naming environment, so a generated input is labelled with the slot name
    the source's own `@T.n` references resolve to (`@Option<Int>.0` for a
    parameter written `@Option<Cnt>`).  Already total: an unresolvable type
    expression renders `"?"`, which is the tester's contract.
    """
    return naming.slot_name(te, alias_env)


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
