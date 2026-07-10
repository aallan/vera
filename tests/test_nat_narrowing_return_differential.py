"""Verifier<->codegen behavioural differential for #758 — the @Int -> @Nat
narrowing obligation at the RETURN position.

The soundness contract (the return-position dual of the #813 widening
differential): at the function-return coercion slot the verifier's static
`nat_bind` verdict must AGREE with what code generation actually does at run
time —

  * an UNPROVEN narrowing (the value can be negative) leaves the return
    `nat_bind` obligation undischarged — a loud E503 `violated` when Z3
    witnesses a negative input, or `tier3` for an opaque value — and codegen
    MUST emit the return guard, so ``vera run`` with a negative input TRAPS
    rather than storing a negative in the @Nat slot (pre-#758 it returned the
    negative silently: `to_nat(0 - 5)` = -5).
  * a PROVEN narrowing (a `requires`/path-condition bound) discharges the
    return `nat_bind` at Tier 1, and codegen's guard is DEAD — ``vera run``
    returns the value with no trap.

A green per-site unit suite (``test_codegen_nat_guards`` asserts the trap,
``test_verifier_nat_obligations`` asserts the obligation status) can still hide
a desync between the two surfaces — the verifier obligating a site codegen
never guards (an unsound silent negative), or codegen guarding a site the
verifier proved Tier-1 (a spurious trap on a valid value).  This is the
required cross-component differential (project rule): for one corpus run BOTH
sides and compare, so "the verifier obligates this return" is checked against
the actual runtime guard, site for site.
"""

from __future__ import annotations

import tempfile
from pathlib import Path

import pytest

from vera.codegen.api import WasmTrapError

from collections.abc import Iterator
from contextlib import contextmanager

from vera.ast import Program
from vera.checker import CheckArtifacts, typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver, ResolvedModule
from vera.verifier import verify

_KIND = "nat_bind"


@contextmanager
def _resolved_pipeline(
    source: str,
) -> Iterator[tuple[Program, CheckArtifacts, list[ResolvedModule], str]]:
    """Parse + resolve imports + typecheck *source* through the REAL CLI
    pipeline — a temp file, ``ModuleResolver``, and ``file=`` +
    ``resolved_modules=`` threaded into ``typecheck_with_artifacts`` — then
    yield ``(program, artifacts, resolved, path)`` for the verify / compile
    stages to reuse.

    The 48cbc1f fidelity principle: every side of this differential must
    measure the same pipeline the CLI drives, so a bare in-memory verify (no
    ``file`` / ``resolved_modules``) can never disagree with ``vera run`` for a
    reason the CLI would never hit."""
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


def _return_nat_bind_statuses(source: str) -> list[str]:
    """The status of every ``nat_bind`` obligation the verifier emits.

    Threads ``file=`` + ``resolved_modules=`` through BOTH typecheck and verify,
    exactly as the ``_run`` / ``_statuses_and_wat`` siblings do (the 48cbc1f
    fidelity principle) — a bare ``verify(program, source)`` skipped the
    side-tables the CLI supplies.  The corpus shapes below have exactly ONE @Nat
    narrowing site — the return slot — so every ``nat_bind`` obligation is the
    return-position one under test (no body-internal narrowing to filter out)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = verify(
            program, source, file=path, resolved_modules=resolved,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        return [o.status for o in result.obligations if o.kind == _KIND]


def _statuses_and_wat(source: str) -> tuple[list[str], str]:
    """Verify AND compile the SAME program in ONE pipeline run, returning the
    ``nat_bind`` statuses and the compiled WAT — so a single call cross-checks
    the verifier's tier verdict against the codegen guard it promises (the
    tier3 quadrant of the differential: verify says ``tier3`` / promises a
    runtime guard, codegen must emit one)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = verify(
            program, source, file=path, resolved_modules=resolved,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        statuses = [o.status for o in result.obligations if o.kind == _KIND]
        comp = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
        )
        return statuses, comp.wat


def _run(source: str, fn: str, arg: int) -> int | None:
    """Compile + execute *fn* with one i64 arg; ``None`` if it traps."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
        )
        try:
            exec_result = execute(result, fn_name=fn, args=[arg])
        except WasmTrapError:
            return None
        return exec_result.value


# (label, source, fn, neg_input) — an @Int -> @Nat narrowing at the return
# position where the value CAN be negative.  The verifier leaves the return
# nat_bind undischarged (not "verified"), and codegen guards it so
# run(neg_input) TRAPS.  A non-negative input passes the guard unchanged.
_UNPROVEN = [
    ("bare_slot", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "f", -5),
    ("if_neg_arm", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ if @Int.0 >= 0 then { 0 } else { @Int.0 } }
""", "f", -5),
    # The narrowing `_` arm returns the raw @Int scrutinee.  The whole match is
    # target-typed to the @Nat return, so the verifier's side-table reports it
    # @Nat — the return-boundary detection must descend to the arm to catch it,
    # exactly the site codegen's syntactic guard covers (pre-fix this desynced:
    # codegen trapped while the verifier stayed silent).
    ("match_wildcard_arm", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ match @Int.0 { 0 -> 0, _ -> @Int.0 } }
""", "f", -5),
    # A leading `let` statement before the narrowing tail: the return-boundary
    # descent must skip block statements and reach the trailing @Int leaf (the
    # let value flows straight through), matching where codegen guards it.
    ("let_before_tail", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @Int = @Int.0; @Int.0 }
""", "f", -5),
    # A NESTED if-in-if join: the innermost else leaf `@Int.0` is unguarded, so
    # the descent must recurse through both join levels to obligate it — the
    # per-leaf codegen guard covers the same nested leaf (a whole-body-only
    # check would mask it behind the target-typed @Nat join).
    ("nested_if_join", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ if @Int.0 == 0 then { 0 } else { if @Int.0 > 5 then { @Int.0 } else { @Int.0 } } }
""", "f", -5),
    # #983 review — a bare @Nat return through a `type Count = Nat` ALIAS must
    # behave IDENTICALLY to the bare-@Nat `bare_slot` case above: the verifier's
    # 7d gate resolves the alias, and (post-fix) codegen's alias-aware gate
    # guards it too — so the differential holds through the alias.
    ("alias_bare_slot", """
type Count = Nat;
public fn f(@Int -> @Count) requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "f", -5),
]

# (label, source, fn, neg_input, expect) — a PROVEN @Int -> @Nat return
# narrowing: the verifier discharges the return nat_bind at Tier 1, codegen's
# guard is dead, and run returns the value with no trap.
_PROVEN = [
    ("abs_if", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ if @Int.0 >= 0 then { @Int.0 } else { 0 - @Int.0 } }
""", "f", -5, 5),
    ("requires_bound", """
public fn f(@Int -> @Nat) requires(@Int.0 >= 0) ensures(true) effects(pure)
{ @Int.0 }
""", "f", 5, 5),
]

# (label, source, fn) — the TIER-3 quadrant: an OPAQUE @Int -> @Nat return
# narrowing the solver cannot translate (`float_to_int` parses a machine float,
# which Z3 does not model), so the verifier records the return nat_bind `tier3`
# — a PROMISE that codegen guards it at run time — and codegen MUST emit the
# guard.  (`array_length` is NOT tier3: the verifier models its `>= 0`
# postcondition and proves the narrowing at Tier 1 — so it is a `verified`
# case, not the opaque one this quadrant needs; `float_to_int` is a genuine
# codegen-supported builtin whose result Z3 leaves opaque.)
_TIER3 = [
    ("float_to_int", """
public fn f(@Float64 -> @Nat) requires(true) ensures(true) effects(pure)
{ float_to_int(@Float64.0) }
""", "f"),
]


class TestNatReturnNarrowingDifferential758:
    @pytest.mark.parametrize("label,source,fn,neg", _UNPROVEN,
                             ids=[c[0] for c in _UNPROVEN])
    def test_unproven_return_obligated_and_run_traps(
        self, label: str, source: str, fn: str, neg: int,
    ) -> None:
        statuses = _return_nat_bind_statuses(source)
        # The verifier obligates the return slot (exactly one narrowing site)...
        assert statuses, f"{label}: no return nat_bind obligation emitted"
        assert all(s != "verified" for s in statuses), (
            f"{label}: an unprovable narrowing must not verify Tier-1: {statuses}"
        )
        # ...and codegen makes good on it: a negative input traps rather than
        # storing a reinterpreted negative in the @Nat slot.
        assert _run(source, fn, neg) is None, (
            f"{label}: the verifier obligated this return, but run({neg}) did "
            f"NOT trap — an unsound silent negative @Nat"
        )
        # A non-negative input takes a non-negative return path, so the guard
        # does NOT trip (it returns some value, not None) — the guard fires only
        # on the bad path, never spuriously on a valid one.
        assert _run(source, fn, 4) is not None, (
            f"{label}: a valid (non-negative) input must pass the guard"
        )

    @pytest.mark.parametrize("label,source,fn,neg,expect", _PROVEN,
                             ids=[c[0] for c in _PROVEN])
    def test_proven_return_verified_and_run_no_trap(
        self, label: str, source: str, fn: str, neg: int, expect: int,
    ) -> None:
        statuses = _return_nat_bind_statuses(source)
        # The verifier proves the return narrowing at Tier 1...
        assert statuses == ["verified"], f"{label}: {statuses}"
        # ...and codegen's guard is dead — run returns the value, never traps.
        assert _run(source, fn, neg) == expect, (
            f"{label}: verifier proved Tier-1 but run({neg}) trapped or gave "
            f"the wrong value — a spurious trap or a codegen<->verifier desync"
        )

    @pytest.mark.parametrize("label,source,fn", _TIER3,
                             ids=[c[0] for c in _TIER3])
    def test_tier3_return_promised_guard_is_emitted(
        self, label: str, source: str, fn: str,
    ) -> None:
        """The tier-3 quadrant, cross-checked in ONE pipeline run: the verifier
        records the opaque return narrowing ``tier3`` (a runtime-guard promise)
        AND the SAME compiled program carries the codegen guard — so ``tier3``
        can never mean "promised but never emitted" (the alias-blind gate's
        exact soundness gap: verify obligated ``tier3`` while codegen emitted
        nothing through the alias)."""
        statuses, wat = _statuses_and_wat(source)
        assert statuses == ["tier3"], (
            f"{label}: expected a single tier3 return nat_bind, got {statuses}"
        )
        idx = wat.find(f"(func ${fn} ")
        assert idx >= 0, f"{label}: function {fn} not found in WAT"
        end = wat.find("\n  (func ", idx + 1)
        body = wat[idx:end if end >= 0 else len(wat)]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"{label}: the verifier promised a tier3 runtime guard, but codegen "
            f"emitted none:\n{body}"
        )
