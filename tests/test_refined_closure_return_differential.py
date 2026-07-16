"""Verifier<->codegen behavioural differential for #1032 — the REFINEMENT
dual of the #984 @Int -> @Nat closure-return narrowing.

A closure whose declared return is a refinement ``{ @Base | P }`` can return a
raw ``@Base`` value that violates ``P``.  Pre-fix ``fn(@Int -> @Pos) { @Int.0 }``
(where ``Pos = { @Nat | @Nat.0 > 0 }``) applied to ``-5`` verified CLEAN — a
false Tier-1 — and returned ``-5`` through the ``@Pos`` slot with no runtime
backstop, the return-side analogue of the closure-argument refinement gap.

The closure body is opaque to the verifier's SMT layer, so — like the #820
widening and #984 narrowing duals — the refined return is obligated
SHALLOW-syntactically (always ``tier3``, never a false Tier-1) and codegen guards
the return value in ``_compile_lifted_closure`` (the closure analogue of the
named-function refined-return guard in ``_compile_postconditions``).  Each program
wraps the closure in a ``mk`` producer and a ``go`` driver that ``apply_fn``s it
and converts the ``@Pos`` result back to ``@Int`` — so ``go`` itself does NOT
return ``@Pos`` and its named-return guard cannot mask the closure-return guard
under test.
"""

from __future__ import annotations

import tempfile
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path

import pytest

from vera.ast import Program
from vera.checker import CheckArtifacts, typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver, ResolvedModule
from vera.verifier import verify

_KIND = "refine_bind"

_PRE = "type Pos = { @Nat | @Nat.0 > 0 };\n"


@contextmanager
def _resolved_pipeline(
    source: str,
) -> Iterator[tuple[Program, CheckArtifacts, list[ResolvedModule], str]]:
    """Parse + resolve + typecheck through the real CLI pipeline (temp file,
    ``ModuleResolver``, ``file=`` + ``resolved_modules=``), so verify and
    compile measure the same program the CLI drives."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        path = f.name
    try:
        program = parse_to_ast(source)
        resolver = ModuleResolver(_root=Path(path).parent)
        resolved = resolver.resolve_imports(program, Path(path))
        _diags, arts = typecheck_with_artifacts(
            program, source, file=path, resolved_modules=resolved,
        )
        yield program, arts, resolved, path
    finally:
        Path(path).unlink(missing_ok=True)


def _refine_bind_statuses(source: str) -> list[str]:
    """The status of every ``refine_bind`` obligation the verifier emits.

    The corpus below has exactly ONE refinement site — the closure return — so
    every ``refine_bind`` obligation is the return-position one under test."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = verify(
            program, source, file=path, resolved_modules=resolved,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        return [o.status for o in result.obligations if o.kind == _KIND]


def _run(source: str, fn: str, arg: int) -> int | None:
    """Compile + execute *fn* with one i64 arg; ``None`` if it traps (the
    refinement guard reports via ``$vera.contract_fail``, which surfaces as a
    ``RuntimeError`` — ``WasmTrapError`` is a subclass)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
        )
        try:
            exec_result = execute(result, fn_name=fn, args=[arg])
        except RuntimeError:
            return None
        return exec_result.value


# (label, source) — a closure whose refined return CAN violate the predicate.
# The verifier records the closure-return refine_bind `tier3` (opaque ->
# guarded), and codegen's boundary guard traps on a violating value.
_CLOSURE_TRAP = [
    ("closure_bare_pos", _PRE + """
type F = fn(Int -> Pos) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Pos) effects(pure) { @Int.0 } }
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); let @Pos = apply_fn(@F.0, @Int.0); nat_to_int(@Pos.0) }
"""),
    # A per-leaf refined return: the else-arm @Int.0 leaf can violate, so the
    # guard must reach into the join, not only wrap a trivially-safe then-arm.
    ("closure_if_else_leaf", _PRE + """
type F = fn(Int -> Pos) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Pos) effects(pure) { if @Int.0 > 100 then { 1 } else { @Int.0 } } }
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); let @Pos = apply_fn(@F.0, @Int.0); nat_to_int(@Pos.0) }
"""),
]

# (label, source) — a NON-refined closure return: no refine_bind obligation and
# no guard, so a negative flows through untouched (proves the arm fires ONLY for
# a refined return, never over-obligating an ordinary one).
_CLOSURE_UNOBLIGATED = [
    ("closure_intint", """
type F = fn(Int -> Int) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Int) effects(pure) { @Int.0 } }
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
"""),
]

# A refined PAIR-base (String) closure return: codegen represents `@String` as
# an `(i32 ptr, i32 len)` pair, so the guard must save/reload both halves and
# check the predicate on the ptr (the length is read from memory).  Proves the
# `guarded` promise is honest for pair bases too, not only scalars — the guard
# mirrors the named-function `_compile_postconditions` i32_pair return guard.
_PAIR_STRING = """
type NonEmptyStr = { @String | string_length(@String.0) > 0 };
type F = fn(String -> NonEmptyStr) effects(pure);

private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@String -> @NonEmptyStr) effects(pure) { @String.0 } }

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  let @String = if @Int.0 > 0 then { "ok" } else { "" };
  let @F = mk(0);
  let @NonEmptyStr = apply_fn(@F.0, @String.0);
  nat_to_int(string_length(@NonEmptyStr.0))
}
"""


class TestRefinedClosureReturnDifferential1032:
    @pytest.mark.parametrize("label,source", _CLOSURE_TRAP,
                             ids=[c[0] for c in _CLOSURE_TRAP])
    def test_refined_closure_return_obligated_tier3_and_run_traps(
        self, label: str, source: str,
    ) -> None:
        # Opaque closure body -> obligated shallow-syntactically as exactly ONE
        # tier3 (a runtime-guard promise), NEVER a false Tier-1 (which silenced
        # the real violation before #1032).
        statuses = _refine_bind_statuses(source)
        assert statuses == ["tier3"], f"{label}: {statuses}"
        # ...and codegen makes good on the promise.  A strictly-negative input
        # violates both `>= 0` and `> 0`; a zero satisfies `>= 0` but violates
        # the strict `> 0` — proving the FULL predicate is enforced at the
        # closure boundary, not merely the @Nat base's `>= 0`.
        assert _run(source, "go", -5) is None, (
            f"{label}: run(-5) returned a value — a silent refinement violation "
            f"through the @Pos slot (the #1032 bug)"
        )
        assert _run(source, "go", 0) is None, (
            f"{label}: run(0) returned a value — the strict `> 0` predicate was "
            f"not enforced (only the @Nat `>= 0` base)"
        )
        # ...while a value satisfying the predicate passes the guard unharmed.
        assert _run(source, "go", 7) == 7, (
            f"{label}: a satisfying (> 0) input must pass the guard"
        )

    @pytest.mark.parametrize("label,source", _CLOSURE_UNOBLIGATED,
                             ids=[c[0] for c in _CLOSURE_UNOBLIGATED])
    def test_non_refined_closure_return_unobligated_and_not_trapped(
        self, label: str, source: str,
    ) -> None:
        assert _refine_bind_statuses(source) == [], (
            f"{label}: a non-refined closure return must carry no refine_bind"
        )
        assert _run(source, "go", -5) == -5, (
            f"{label}: the value was altered or trapped — a spurious guard on a "
            f"non-refined closure return"
        )

    def test_refined_pair_closure_return_obligated_and_guarded(self) -> None:
        # A refined PAIR base (String) closure return is obligated `tier3` just
        # like a scalar, and codegen now emits the i32_pair boundary guard, so
        # the verifier's guarded promise is honest for pairs (not a false
        # `tier3_runtime` over an unguarded passthrough).
        assert _refine_bind_statuses(_PAIR_STRING) == ["tier3"]
        # An empty string violates `string_length > 0` and traps at the closure
        # boundary; a non-empty string passes and its length flows out.
        assert _run(_PAIR_STRING, "go", -1) is None, (
            "an empty-string refined closure return was not guarded — the "
            "i32_pair boundary guard is missing"
        )
        assert _run(_PAIR_STRING, "go", 1) == 2, (
            "a satisfying (non-empty) string must pass the pair guard"
        )
