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

from tests.codegen_helpers import wat_calls, wat_fn_names
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

#: The `@Int` -> `@Nat` narrowing guard's trap kind.  It was the generic
#: `unreachable` until #754 gave the guard its own `vera.nat_guard_trap`
#: signal; pinning the dedicated kind is a STRONGER reading, since
#: `unreachable` is also what a non-exhaustive match and a shadow-stack
#: overflow produce and either would have read as "the guard fired".
_NAT_GUARD_KIND = "nat_guard"

# u64.MAX stored in an i64 slot reads back as -1; used by the #984 closure
# controls to prove an @Nat -> @Nat closure return is NOT false-trapped.
U64_MAX = 18446744073709551615


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
        diags, arts = typecheck_with_artifacts(
            program, source, file=path, resolved_modules=resolved,
        )
        # Check-clean is part of every differential's premise ("a
        # check-green program must ..."): a fixture the checker rejects
        # would silently exercise nothing (a round-3 reviewer caught a
        # test validating a check-rejected program through exactly this
        # gap).
        errors = [d for d in diags if d.severity == "error"]
        assert not errors, (
            "differential fixture must type-check cleanly, got: "
            f"{[(d.error_code, d.description[:70]) for d in errors]}"
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


def _trap_kind(source: str, fn: str, arg: int | None) -> str | None:
    """The normalized trap kind for running *fn(arg)*, or ``None`` if no trap
    — so trap assertions can pin the narrowing guard's bare ``unreachable``
    net specifically (the widen dual's convention), not just "some trap".

    ``arg=None`` calls with NO arguments, for a ``@Unit``-parameter entry
    point.  Distinct from passing a null: a `@Unit` parameter is erased, so
    the compiled function takes nothing and handing it one value is an arity
    error, which would surface as a failure to run rather than as a verdict
    about the guard."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
        )
        try:
            execute(result, fn_name=fn, args=[] if arg is None else [arg])
        except WasmTrapError as exc:
            return exc.kind
        return None


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


# ---------------------------------------------------------------------------
# #984 — the @Int -> @Nat narrowing at a LIFTED CLOSURE's return.  The #758
# return nat-bind hole reachable only through `_compile_lifted_closure`: pre-fix
# `fn(@Int -> @Nat) { @Int.0 }` applied to -5 returned -5 through the @Nat slot
# on a verify-clean program (no obligation, no guard).  The closure body is
# opaque to the verifier's SMT layer, so — like the #820 widening dual — the
# return narrowing is obligated SHALLOW-syntactically (always `tier3`, never a
# false Tier-1 / E503) and codegen guards it PER NARROWING LEAF in the lifted
# body (the whole-body wrap would false-trap a legitimate @Nat leaf).  Each
# program wraps the closure in a `mk` producer and a `go` driver that
# `apply_fn`s it, so `_run(source, "go", arg)` exercises the real closure path
# end to end.
# ---------------------------------------------------------------------------

# (label, source, neg_input) — a closure whose return genuinely narrows: the
# verifier records the closure-return nat_bind `tier3` (opaque -> guarded), and
# codegen's per-leaf guard traps on the negative; a non-negative input passes.
_CLOSURE_TRAP = [
    ("closure_bare", """
type F = fn(Int -> Nat) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Nat) effects(pure) { @Int.0 } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
""", -5),
    # A per-leaf narrowing: only the else-arm @Int.0 leaf is a genuine narrowing
    # (the then-arm literal 0 is not), so the guard must sit on the else leaf, not
    # wrap the whole body.  -5 routes to else -> traps; +7 routes to then -> 0.
    ("closure_if_else_leaf", """
type F = fn(Int -> Nat) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Nat) effects(pure) { if @Int.0 >= 0 then { 0 } else { @Int.0 } } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
""", -5),
    # A @Nat-alias return must behave identically to the bare-@Nat case: the
    # verifier's `_is_nat_type` resolves the alias and codegen's alias-aware
    # `_type_expr_base_is_nat` guards it.
    ("closure_alias", """
type Count = Nat;
type F = fn(Int -> Count) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Count) effects(pure) { @Int.0 } }
public fn go(@Int -> @Count) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
""", -5),
]

# (label, source, neg_input, expect) — an abs-style closure body: BOTH leaves
# narrow (both guarded; tier3 because the closure is opaque, never proven
# Tier-1), yet the abs logic keeps every returned value non-negative, so the
# live guard never trips — sound over-guarding, no spurious trap.
_CLOSURE_SAFE = [
    ("closure_abs", """
type F = fn(Int -> Nat) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Nat) effects(pure) { if @Int.0 >= 0 then { @Int.0 } else { 0 - @Int.0 } } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
""", -5, 5),
]

# (label, source, input, expect) — a closure whose return does NOT narrow: no
# closure-return nat_bind obligation, no guard, and no false trap.
_CLOSURE_UNOBLIGATED = [
    # @Nat -> @Nat: the return is already @Nat, so no narrowing; a u64.MAX value
    # (reads as -1 i64) MUST pass through without a guard false-trapping it.
    ("closure_natnat", """
type F = fn(Nat -> Nat) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { @Nat.0 } }
public fn go(@Nat -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(0); apply_fn(@F.0, @Nat.0) }
""", U64_MAX, -1),
    # @Int -> @Int: no @Nat slot in sight; a negative flows through untouched.
    ("closure_intint", """
type F = fn(Int -> Int) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Int) effects(pure) { @Int.0 } }
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ let @F = mk(0); apply_fn(@F.0, @Int.0) }
""", -5, -5),
    # An intrinsically-@Nat body (`let @Nat = 5` bound, then returned): the
    # trailing @Nat.0 does not narrow, so the closure-return gate adds NO second
    # guard on top of the already-clean value.
    ("closure_intrinsic_nat", """
type F = fn(Int -> Nat) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Nat) effects(pure) { let @Nat = 5; @Nat.0 } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
""", -5, 5),
]

# A closure nested inside ANOTHER closure's body — the #985 reporting gap, now
# confirmed for the narrowing direction.
_NESTED_CLOSURE = """
type Inner = fn(Int -> Nat) effects(pure);
type Outer = fn(Int -> Inner) effects(pure);
private fn mk(@Int -> @Outer) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Inner) effects(pure) { fn(@Int -> @Nat) effects(pure) { @Int.0 } } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @Outer = mk(@Int.0); let @Inner = apply_fn(@Outer.0, @Int.0); apply_fn(@Inner.0, @Int.0) }
"""


class TestClosureReturnNarrowingDifferential984:
    @pytest.mark.parametrize("label,source,neg", _CLOSURE_TRAP,
                             ids=[c[0] for c in _CLOSURE_TRAP])
    def test_closure_narrowing_obligated_tier3_and_run_traps(
        self, label: str, source: str, neg: int,
    ) -> None:
        statuses = _return_nat_bind_statuses(source)
        # The closure body is opaque, so the return narrowing is obligated
        # shallow-syntactically — exactly ONE tier3 (a runtime-guard promise),
        # NEVER a false Tier-1 "verified" (which would silence a real negative).
        assert statuses == ["tier3"], f"{label}: {statuses}"
        # ...and codegen makes good on the promise: a negative input traps
        # rather than returning it silently through the @Nat slot (the #984 bug).
        kind = _trap_kind(source, "go", neg)
        assert kind == _NAT_GUARD_KIND, (
            f"{label}: the verifier obligated this closure return, but "
            f"run({neg}) gave trap kind {kind!r} — expected the narrowing "
            f"guard's own kind (None = no trap at all: an unsound silent "
            f"negative @Nat)"
        )
        # ...while a non-negative input passes the per-leaf guard unharmed.
        assert _run(source, "go", 7) is not None, (
            f"{label}: a valid (non-negative) input must pass the guard"
        )

    @pytest.mark.parametrize("label,source,neg,expect", _CLOSURE_SAFE,
                             ids=[c[0] for c in _CLOSURE_SAFE])
    def test_closure_overguard_tier3_but_no_spurious_trap(
        self, label: str, source: str, neg: int, expect: int,
    ) -> None:
        # The closure is opaque, so even a provably-abs body is tier3 (over-
        # guarded, never proven Tier-1)...
        assert _return_nat_bind_statuses(source) == ["tier3"], label
        # ...but every returned value stays non-negative, so the live guard
        # never trips — over-guarding is sound, not a false-positive trap.
        assert _run(source, "go", neg) == expect, (
            f"{label}: run({neg}) trapped or gave the wrong value — a spurious "
            f"trap on a value the abs body keeps non-negative"
        )
        assert _run(source, "go", 5) == 5, f"{label}: +5 path altered"

    @pytest.mark.parametrize("label,source,inp,expect", _CLOSURE_UNOBLIGATED,
                             ids=[c[0] for c in _CLOSURE_UNOBLIGATED])
    def test_closure_non_narrowing_unobligated_and_not_trapped(
        self, label: str, source: str, inp: int, expect: int,
    ) -> None:
        # No @Nat narrowing at the closure return -> the verifier records NO
        # nat_bind, so codegen must emit no guard: the value flows through
        # unchanged.  A false guard on `closure_natnat` would trap a legitimate
        # @Nat above i64.MAX (the widen dual's false-trap hazard).
        assert _return_nat_bind_statuses(source) == [], (
            f"{label}: a non-narrowing closure return must carry no obligation"
        )
        assert _run(source, "go", inp) == expect, (
            f"{label}: the value was altered or trapped — a spurious guard on a "
            f"non-narrowing closure return"
        )

    def test_nested_closure_verifier_and_codegen_agree_985(
        self,
    ) -> None:
        """A closure nested inside ANOTHER closure's body: codegen guards its
        @Int -> @Nat return (every lifted closure passes through
        ``_compile_lifted_closure``) AND the verifier reports the matching
        ``nat_bind`` obligation — the #779 fresh-scope descent re-enters the
        ``AnonFn`` arm for the nested closure, closing the #985
        reporting-completeness residual.  The strict verifier↔codegen
        differential now holds at every closure depth: one runtime-guarded
        Tier-3 record per guard, and the guard itself still traps a
        negative."""
        statuses = _return_nat_bind_statuses(_NESTED_CLOSURE)
        assert statuses == ["tier3"], (
            "nested: the return-narrowing obligation vanished — the #985 "
            "under-reporting regressed"
        )
        # ...and codegen still guards it, so a negative traps (sound).
        assert _run(_NESTED_CLOSURE, "go", -5) is None, (
            "nested: codegen guard missing -> a silent negative @Nat"
        )
        assert _run(_NESTED_CLOSURE, "go", 7) is not None, (
            "nested: a valid (non-negative) input must pass the guard"
        )

_CLOSURE_BOUNDARY = """\
type F = fn(Int -> Nat) effects(pure);
private fn mk(@Unit -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Nat) effects(pure) { @Int.0 } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(()); apply_fn(@F.0, @Int.0) }
"""

_CLOSURE_REFINED = """\
type Pos = { @Nat | @Nat.0 > 0 };
type F = fn(Int -> Pos) effects(pure);
private fn mk(@Unit -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Pos) effects(pure) { if @Int.0 > 0 then { @Int.0 } else { 1 } } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(()); apply_fn(@F.0, @Int.0) }
"""


class TestClosureNarrowingBoundary984:
    """Sign-boundary behavior of the closure return guard (`result >= 0`):
    zero must SURVIVE (an off-by-one `i64.le_s` mutant would false-trap it),
    the tightest negative and i64.MIN must trap with the narrowing guard's
    own kind.  Behavioral pins — not WAT-string matches — so a guard-comparison
    regression is caught by execution, not by implementation coupling."""

    def test_zero_survives_the_guard(self) -> None:
        assert _run(_CLOSURE_BOUNDARY, "go", 0) == 0

    def test_minus_one_traps(self) -> None:
        assert _trap_kind(_CLOSURE_BOUNDARY, "go", -1) == _NAT_GUARD_KIND

    def test_i64_min_traps(self) -> None:
        assert (_trap_kind(_CLOSURE_BOUNDARY, "go", -(2 ** 63))
                == _NAT_GUARD_KIND)

    def test_i64_max_passes(self) -> None:
        assert _run(_CLOSURE_BOUNDARY, "go", 2 ** 63 - 1) == 2 ** 63 - 1

    def test_refined_return_single_guard_no_double(self) -> None:
        """A refinement-over-@Nat closure return is guarded EXACTLY ONCE — by
        the #1032 refined-return guard in the lifted body — and the #984
        narrowing gate must NOT add a second sign check on top
        (`_refinement_guard_parts is None` exclusion: removing it compiles a
        redundant `i64.lt_s`; the refinement guard's predicate already
        conjoins the @Nat base's `>= 0`).  Pin by guard counts in the lifted
        closure's WAT, plus behavior: 5 round-trips, 0 takes the clamping arm.
        (Pre-#1032 this pinned ZERO guards of any kind, on the then-false
        assumption that a boundary guard existed at the call/return site.)"""
        statuses, wat = _statuses_and_wat(_CLOSURE_REFINED)
        anon = wat[wat.index("(func $anon_"):]
        depth = 0
        for i, ch in enumerate(anon):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    anon = anon[: i + 1]
                    break
        # Exactly ZERO narrowing sign checks in the lifted body: ANY i64.lt_s
        # here is the #984 leaf gate wrongly firing on a refined return
        # (measured: 0 at head, 1 with the `_refinement_guard_parts is None`
        # exclusion removed) — the refinement guard below uses ge_s/gt_s.
        assert anon.count("i64.lt_s") == 0, (
            f"refined closure return picked up a narrowing guard: "
            f"{anon.count('i64.lt_s')} sign checks in the lifted body"
        )
        # ...and exactly ONE refinement guard: the #1032 return-value check.
        # 0 would be the pre-#1032 silent leak; 2+ would be double-guarding
        # (e.g. the #984 gate un-excluded, or the return guard emitted twice).
        assert anon.count("call $vera.contract_fail") == 1, (
            f"expected exactly one refinement return guard in the lifted "
            f"body, found {anon.count('call $vera.contract_fail')}"
        )
        assert _run(_CLOSURE_REFINED, "go", 5) == 5
        # 0 takes the else arm and returns the clamped 1 — the body never
        # produces a refinement-violating value, so the (now-live) return
        # guard does not trip; the guard-count pins above are what this test
        # exists for.
        assert _run(_CLOSURE_REFINED, "go", 0) == 1


# ---------------------------------------------------------------------------
# #1017 — the @Int -> @Nat narrowing at an apply_fn ARGUMENT position (into the
# closure's @Nat FORMAL), the narrowing dual of the #820 apply_fn @Nat -> @Int
# argument WIDENING.  Pre-fix `apply_fn(clo_with_nat_formal, 0 - 5)` verified
# clean (the verifier's apply_fn branch obligated only the widening direction)
# AND `_translate_apply_fn` emitted only the widen guard — so a provably-
# negative @Int flowed into the @Nat formal with NO obligation and NO runtime
# backstop: a false Tier-1 AND a silent negative (`apply_fn(clo, @Int.0)` on -5
# returned the body value rather than trapping).  The verifier now obligates the
# argument narrowing at its apply_fn branch (mirroring the generic call-argument
# narrowing) and codegen guards the call_indirect argument (mirroring its
# @Int-formal widen guard).  Every closure body below returns a CONSTANT, so the
# ONLY narrowing/guard in play is the ARGUMENT — any trap is the arg guard, not
# a closure-return guard (the #984 corpus above covers that dual).
# ---------------------------------------------------------------------------

# (label, source) — a provably-NEGATIVE apply_fn arg narrowing into a @Nat
# formal: the verifier witnesses the negative constant and reports the arg
# nat_bind `violated` (a loud E503), never the pre-fix empty obligation list.
_APPLYFN_ARG_VIOLATED = [
    # The #1017 issue repro verbatim: a @NatToInt closure PARAMETER (formal
    # recovered from its declared fn-type) applied to a constant-negative arg.
    ("issue_param_closure", """
type NatToInt = fn(Nat -> Int) effects(pure);
private fn f(@NatToInt -> @Int) requires(true) ensures(true) effects(pure)
{ apply_fn(@NatToInt.0, 0 - 5) }
"""),
    # A locally-constructed closure literal applied to a constant-negative arg —
    # the formal is recovered from the inline AnonFn's declared parameter type.
    ("literal_closure_const_neg", """
type NatToNat = fn(Nat -> Nat) effects(pure);
private fn mk(@Unit -> @NatToNat) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { 5 } }
public fn go(@Unit -> @Nat) requires(true) ensures(true) effects(pure)
{ let @NatToNat = mk(()); apply_fn(@NatToNat.0, 0 - 5) }
"""),
]

# (label, source, fn) — a RUNTIME @Int argument (unknown sign) narrowing into a
# @Nat formal.  The verifier obligates it (never "verified"), and codegen guards
# the call_indirect argument, so run(-5) TRAPS (pre-fix it silently returned the
# closure body's constant) while run(4) passes the guard.
_APPLYFN_ARG_TRAP = [
    ("runtime_arg", """
type NatToNat = fn(Nat -> Nat) effects(pure);
private fn mk(@Unit -> @NatToNat) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { 5 } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @NatToNat = mk(()); apply_fn(@NatToNat.0, @Int.0) }
""", "go"),
]

# (label, source, fn, arg, expect) — a PROVABLY non-negative narrowing (a
# `requires(@Int.0 >= 0)` bound): the verifier discharges the arg nat_bind at
# Tier 1, codegen's guard is dead, and run returns the body constant, no trap.
_APPLYFN_ARG_PROVEN = [
    ("requires_bound", """
type NatToNat = fn(Nat -> Nat) effects(pure);
private fn mk(@Unit -> @NatToNat) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { 5 } }
public fn go(@Int -> @Nat) requires(@Int.0 >= 0) ensures(true) effects(pure)
{ let @NatToNat = mk(()); apply_fn(@NatToNat.0, @Int.0) }
""", "go", 4, 5),
]

# (label, source, fn, arg, expect) — a @Nat argument into a @Nat formal: NO
# narrowing, so no obligation and no guard.  A u64.MAX value (reads as -1 in the
# i64 slot) must pass through unguarded — the narrowing-side dual of the widen
# guard's false-trap hazard.
_APPLYFN_ARG_UNOBLIGATED = [
    ("nat_arg_nat_formal", """
type NatToNat = fn(Nat -> Nat) effects(pure);
private fn mk(@Unit -> @NatToNat) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { 5 } }
public fn go(@Nat -> @Nat) requires(true) ensures(true) effects(pure)
{ let @NatToNat = mk(()); apply_fn(@NatToNat.0, @Nat.0) }
""", "go", U64_MAX, 5),
]

# (label, source, fn) — the TIER-3 quadrant: an OPAQUE @Int argument the solver
# cannot translate (`float_to_int` parses a machine float, which Z3 does not
# model) narrowing into a @Nat formal, so the verifier records the arg nat_bind
# `tier3` — a PROMISE that codegen guards it at run time — and codegen MUST emit
# the guard.  Directly exercises the `guarded=True` deferral path (the crux of
# the cross-component soundness argument); the mirror of the #758 return `_TIER3`
# quadrant.  Not run (the int-arg `_run` helper cannot drive a @Float64 param).
_APPLYFN_ARG_TIER3 = [
    ("opaque_float_arg", """
type NatToNat = fn(Nat -> Nat) effects(pure);
private fn mk(@Unit -> @NatToNat) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { 5 } }
public fn go(@Float64 -> @Nat) requires(true) ensures(true) effects(pure)
{ let @NatToNat = mk(()); apply_fn(@NatToNat.0, float_to_int(@Float64.0)) }
""", "go"),
]


class TestApplyFnArgNarrowingDifferential1017:
    @pytest.mark.parametrize("label,source", _APPLYFN_ARG_VIOLATED,
                             ids=[c[0] for c in _APPLYFN_ARG_VIOLATED])
    def test_provably_negative_arg_obligated_violated(
        self, label: str, source: str,
    ) -> None:
        # The verifier now emits the argument nat_bind and Z3 witnesses the
        # negative constant, so it is `violated` (E503) — never the pre-fix
        # empty obligation list (the #1017 silent Tier-1 pass).
        statuses = _return_nat_bind_statuses(source)
        assert statuses == ["violated"], (
            f"{label}: expected one violated arg nat_bind, got {statuses} "
            f"(pre-fix: [] — the #1017 false Tier-1)"
        )

    @pytest.mark.parametrize("label,source,fn", _APPLYFN_ARG_TRAP,
                             ids=[c[0] for c in _APPLYFN_ARG_TRAP])
    def test_runtime_arg_obligated_and_run_traps(
        self, label: str, source: str, fn: str,
    ) -> None:
        statuses = _return_nat_bind_statuses(source)
        assert statuses and all(s != "verified" for s in statuses), (
            f"{label}: an unprovable arg narrowing must be obligated, not "
            f"verified: {statuses}"
        )
        # ...and codegen makes good on it: a negative argument traps at the
        # call_indirect boundary rather than entering the @Nat formal silently.
        assert _trap_kind(source, fn, -5) == _NAT_GUARD_KIND, (
            f"{label}: the verifier obligated this arg, but run(-5) did not "
            f"trap with the narrowing guard's kind — a silent negative @Nat "
            f"(the #1017 hole)"
        )
        # ...while a non-negative argument passes the guard unharmed.
        assert _run(source, fn, 4) is not None, (
            f"{label}: a valid (non-negative) argument must pass the guard"
        )

    @pytest.mark.parametrize("label,source,fn,arg,expect", _APPLYFN_ARG_PROVEN,
                             ids=[c[0] for c in _APPLYFN_ARG_PROVEN])
    def test_proven_arg_verified_and_run_no_trap(
        self, label: str, source: str, fn: str, arg: int, expect: int,
    ) -> None:
        # A requires-bounded argument proves the narrowing at Tier 1 (exactly one
        # nat_bind, discharged)...
        assert _return_nat_bind_statuses(source) == ["verified"], (
            f"{label}: a requires-bounded arg narrowing must prove Tier-1"
        )
        # ...and codegen's guard is dead — run returns the value, never traps.
        assert _run(source, fn, arg) == expect, (
            f"{label}: verifier proved Tier-1 but run({arg}) trapped or gave the "
            f"wrong value — a spurious trap or codegen<->verifier desync"
        )

    @pytest.mark.parametrize("label,source,fn,arg,expect",
                             _APPLYFN_ARG_UNOBLIGATED,
                             ids=[c[0] for c in _APPLYFN_ARG_UNOBLIGATED])
    def test_nat_arg_unobligated_and_not_trapped(
        self, label: str, source: str, fn: str, arg: int, expect: int,
    ) -> None:
        # A @Nat->@Nat argument does not narrow -> no obligation, no guard: the
        # value flows through unchanged.  A false guard here would trap a
        # legitimate @Nat above i64.MAX (the widen dual's false-trap hazard).
        assert _return_nat_bind_statuses(source) == [], (
            f"{label}: a @Nat->@Nat argument does not narrow — no obligation"
        )
        assert _run(source, fn, arg) == expect, (
            f"{label}: a non-narrowing @Nat argument was altered or trapped — a "
            f"spurious guard (u64.MAX reads as -1 in the i64 slot)"
        )

    @pytest.mark.parametrize("label,source,fn", _APPLYFN_ARG_TIER3,
                             ids=[c[0] for c in _APPLYFN_ARG_TIER3])
    def test_tier3_arg_promised_guard_is_emitted(
        self, label: str, source: str, fn: str,
    ) -> None:
        """The tier-3 quadrant, cross-checked in ONE pipeline run: an opaque @Int
        argument the solver cannot translate records the arg narrowing `tier3` (a
        runtime-guard promise) AND the SAME compiled program carries the codegen
        guard in the applying function — so `guarded=True` can never mean
        "promised but never emitted" (the false-tier3 soundness hole this whole
        differential exists to catch)."""
        statuses, wat = _statuses_and_wat(source)
        assert statuses == ["tier3"], (
            f"{label}: expected a single tier3 arg nat_bind, got {statuses}"
        )
        idx = wat.find(f"(func ${fn} ")
        assert idx >= 0, f"{label}: function {fn} not found in WAT"
        end = wat.find("\n  (func ", idx + 1)
        body = wat[idx:end if end >= 0 else len(wat)]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"{label}: the verifier promised a tier3 runtime guard, but codegen "
            f"emitted none in {fn}:\n{body}"
        )


# ---------------------------------------------------------------------------
# #1024 — the refinement-PREDICATE narrowing at an apply_fn ARGUMENT position
# (into the closure's REFINED formal), the refinement dual of the #1017 @Nat
# argument narrowing.  Pre-fix `apply_fn(clo, 0)` where the closure formal is
# `{ @Nat | @Nat.0 > 0 }` verified CLEAN and ran silently (returned the body
# value): the #1017 apply_fn arm obligated the formal as a bare @Nat — proving
# only the base's `>= 0` (which 0 satisfies) — so the STRICT `> 0` predicate was
# unchecked (a false Tier-1), and `_compile_lifted_closure` emitted no
# param-entry guard.  The verifier now obligates the argument against the FULL
# predicate at its apply_fn branch (refined-FIRST, ahead of the #1017 @Nat arm,
# mirroring the generic call-argument path) and codegen guards each refined
# closure formal at the lifted body's prologue (`_compile_lifted_closure`,
# mirroring `_compile_fn`'s refined-param guard).  The named-call equivalent
# (`take(0)` into a `@Pos` param) already behaved this way — E505 at verify, a
# `contract_violation` trap at run — so these pin the apply_fn path to the same
# contract.  The discriminating input is 0: it clears the #1017 `>= 0` backstop
# but violates `> 0`, so any test that traps/obligates 0 is exercising the
# refined predicate specifically, not the @Nat base.
# ---------------------------------------------------------------------------

_REFINE_KIND = "refine_bind"
_POS = "type Pos = { @Nat | @Nat.0 > 0 };"


def _refine_bind_statuses(source: str) -> list[str]:
    """The status of every ``refine_bind`` obligation the verifier emits — the
    refinement-predicate analogue of :func:`_return_nat_bind_statuses` (#1024).

    Threads ``file=`` + ``resolved_modules=`` through BOTH typecheck and verify
    (the 48cbc1f fidelity principle).  The corpus shapes below apply a closure
    whose formal is a refinement, so the only ``refine_bind`` site is the
    apply_fn argument under test (the closure body returns a constant, and a
    closure-param declaration raises no narrowing obligation of its own)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = verify(
            program, source, file=path, resolved_modules=resolved,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        return [o.status for o in result.obligations if o.kind == _REFINE_KIND]


def _trap_message(source: str, fn: str, arg: int) -> str | None:
    """The trap MESSAGE for running *fn(arg)*, or ``None`` if it does not trap —
    so a refinement-guard trap can be pinned by its ``Refinement violation``
    message text, not merely "some trap" (#1024, the refined dual of
    :func:`_trap_kind`)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
        )
        try:
            execute(result, fn_name=fn, args=[arg])
        except WasmTrapError as exc:
            return str(exc)
        return None


# (label, source) — a provably-refinement-violating CONSTANT arg into a refined
# closure formal: the verifier witnesses the constant and reports the argument
# refine_bind `violated` (a loud E505), never the pre-fix empty list (the #1024
# false Tier-1, where the #1017 @Nat arm silently proved only `>= 0`).
_APPLYFN_REFINED_ARG_VIOLATED = [
    # The #1024 issue repro: a @PosToInt closure PARAMETER (refined formal
    # recovered from its declared fn-type alias) applied to a constant 0, which
    # satisfies the @Nat base's `>= 0` but violates the strict `> 0`.
    ("issue_param_closure", f"""
{_POS}
type PosToInt = fn(Pos -> Int) effects(pure);
private fn f(@PosToInt -> @Int) requires(true) ensures(true) effects(pure)
{{ apply_fn(@PosToInt.0, 0) }}
"""),
    # A locally-constructed closure literal applied to a constant 0 — the refined
    # formal is recovered from the inline AnonFn's declared parameter type.
    ("literal_closure_zero", f"""
{_POS}
type PosToNat = fn(Pos -> Nat) effects(pure);
private fn mk(@Unit -> @PosToNat) requires(true) ensures(true) effects(pure)
{{ fn(@Pos -> @Nat) effects(pure) {{ 5 }} }}
public fn go(@Unit -> @Nat) requires(true) ensures(true) effects(pure)
{{ let @PosToNat = mk(()); apply_fn(@PosToNat.0, 0) }}
"""),
]

# (label, source, fn) — a RUNTIME arg (unknown sign) narrowing into a refined
# formal.  The verifier obligates it (never "verified"), and codegen guards the
# closure's refined formal at its prologue, so run(0) — which clears `>= 0` but
# fails `> 0` — TRAPS with a `contract_violation` Refinement-violation message
# (pre-fix it silently returned the body constant) while run(7) passes.
_APPLYFN_REFINED_ARG_TRAP = [
    ("runtime_arg", f"""
{_POS}
type PosToNat = fn(Pos -> Nat) effects(pure);
private fn mk(@Unit -> @PosToNat) requires(true) ensures(true) effects(pure)
{{ fn(@Pos -> @Nat) effects(pure) {{ 5 }} }}
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{{ let @PosToNat = mk(()); apply_fn(@PosToNat.0, @Int.0) }}
""", "go"),
]

# (label, source, fn, arg, expect) — a PROVEN refined arg narrowing: a constant
# satisfying the predicate, or a `requires`-bounded arg, discharges the refine
# _bind at Tier 1, codegen's guard is dead, and run returns the body value with
# no trap.  `const_satisfying` is the #1024 c2 healthy pin (arg 5 > 0, body 42).
_APPLYFN_REFINED_ARG_PROVEN = [
    ("const_satisfying", f"""
{_POS}
type PosToInt = fn(Pos -> Int) effects(pure);
private fn mk(@Unit -> @PosToInt) requires(true) ensures(true) effects(pure)
{{ fn(@Pos -> @Int) effects(pure) {{ 42 }} }}
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{{ let @PosToInt = mk(()); apply_fn(@PosToInt.0, 5) }}
""", "go", 0, 42),
    ("requires_bound", f"""
{_POS}
type PosToNat = fn(Pos -> Nat) effects(pure);
private fn mk(@Unit -> @PosToNat) requires(true) ensures(true) effects(pure)
{{ fn(@Pos -> @Nat) effects(pure) {{ 5 }} }}
public fn go(@Int -> @Nat) requires(@Int.0 > 0) ensures(true) effects(pure)
{{ let @PosToNat = mk(()); apply_fn(@PosToNat.0, @Int.0) }}
""", "go", 7, 5),
]

# (label, source, fn, arg, expect) — a @Pos arg into a @Pos formal: the source
# already carries the EXACT refinement (base AND predicate), so
# `_narrows_into_refined` does not fire — no refine_bind, no guard, the value
# flows through.  Guards against the refined-first arm over-firing on a value
# whose refinement was already discharged where it was produced.
_APPLYFN_REFINED_ARG_UNOBLIGATED = [
    ("pos_arg_pos_formal", f"""
{_POS}
type PosToNat = fn(Pos -> Nat) effects(pure);
private fn mk(@Unit -> @PosToNat) requires(true) ensures(true) effects(pure)
{{ fn(@Pos -> @Nat) effects(pure) {{ 5 }} }}
public fn go(@Pos -> @Nat) requires(true) ensures(true) effects(pure)
{{ let @PosToNat = mk(()); apply_fn(@PosToNat.0, @Pos.0) }}
""", "go", 7, 5),
]


class TestApplyFnArgRefinedNarrowing1024:
    @pytest.mark.parametrize("label,source", _APPLYFN_REFINED_ARG_VIOLATED,
                             ids=[c[0] for c in _APPLYFN_REFINED_ARG_VIOLATED])
    def test_provably_violating_arg_obligated_violated(
        self, label: str, source: str,
    ) -> None:
        # The verifier now emits the argument refine_bind and Z3 witnesses the
        # violating constant, so it is `violated` (E505) — never the pre-fix
        # empty list (the #1024 false Tier-1).  0 clears the @Nat base's `>= 0`,
        # so ONLY the refined-first arm (the FULL predicate) catches it — the
        # #1017 @Nat arm's `>= 0` alone would have proved it "verified".
        statuses = _refine_bind_statuses(source)
        assert statuses == ["violated"], (
            f"{label}: expected one violated arg refine_bind, got {statuses} "
            f"(pre-fix: [] — the #1024 false Tier-1)"
        )

    @pytest.mark.parametrize("label,source,fn", _APPLYFN_REFINED_ARG_TRAP,
                             ids=[c[0] for c in _APPLYFN_REFINED_ARG_TRAP])
    def test_runtime_arg_obligated_and_run_traps(
        self, label: str, source: str, fn: str,
    ) -> None:
        statuses = _refine_bind_statuses(source)
        assert statuses and all(s != "verified" for s in statuses), (
            f"{label}: an unprovable refined arg narrowing must be obligated, "
            f"not verified: {statuses}"
        )
        # The crux of #1024: 0 clears the @Nat base's `>= 0` but fails the strict
        # `> 0`, so the closure's refined-formal prologue guard must trap it — the
        # #1017 `>= 0` backstop alone would let it through silently.
        assert _trap_kind(source, fn, 0) == "contract_violation", (
            f"{label}: run(0) did not trap at the closure's refined-formal guard "
            f"— the strict predicate `> 0` is unguarded (the #1024 hole)"
        )
        assert "Refinement violation" in (_trap_message(source, fn, 0) or ""), (
            f"{label}: the trap did not carry a refinement-violation message"
        )
        # ...while a value satisfying the predicate passes the guard unharmed.
        assert _run(source, fn, 7) is not None, (
            f"{label}: a valid (> 0) argument must pass the guard"
        )

    @pytest.mark.parametrize("label,source,fn,arg,expect",
                             _APPLYFN_REFINED_ARG_PROVEN,
                             ids=[c[0] for c in _APPLYFN_REFINED_ARG_PROVEN])
    def test_proven_arg_verified_and_run_no_trap(
        self, label: str, source: str, fn: str, arg: int, expect: int,
    ) -> None:
        # A constant satisfying the predicate, or a `requires`-bounded arg, proves
        # the narrowing at Tier 1 (exactly one refine_bind, discharged)...
        assert _refine_bind_statuses(source) == ["verified"], (
            f"{label}: a provable refined arg narrowing must prove Tier-1"
        )
        # ...and codegen's guard is dead — run returns the value, never traps.
        assert _run(source, fn, arg) == expect, (
            f"{label}: verifier proved Tier-1 but run({arg}) trapped or gave the "
            f"wrong value — a spurious trap or codegen<->verifier desync"
        )

    @pytest.mark.parametrize("label,source,fn,arg,expect",
                             _APPLYFN_REFINED_ARG_UNOBLIGATED,
                             ids=[c[0] for c in _APPLYFN_REFINED_ARG_UNOBLIGATED])
    def test_matching_refined_arg_unobligated_and_not_trapped(
        self, label: str, source: str, fn: str, arg: int, expect: int,
    ) -> None:
        # A @Pos arg into a @Pos formal already carries the exact refinement, so
        # `_narrows_into_refined` does not fire — no obligation, no guard: the
        # value flows through unchanged (a spurious guard would re-check a value
        # the source already established, and could false-trap).
        assert _refine_bind_statuses(source) == [], (
            f"{label}: a @Pos->@Pos argument does not narrow — no obligation"
        )
        assert _run(source, fn, arg) == expect, (
            f"{label}: a non-narrowing refined argument was altered or trapped"
        )


# ---------------------------------------------------------------------------
# #1032 — the refinement-predicate narrowing at a LIFTED CLOSURE's RETURN, the
# return-side dual of the #1024 formal narrowing above (found while fixing it).
# Pre-fix `fn(@Int -> @Pos) { @Int.0 }` (Pos = `{ @Nat | @Nat.0 > 0 }`) applied
# to -5 or 0 returned the violating value through the refined slot on a
# verify-CLEAN program: the verifier's AnonFn walk had widen (#820) and
# bare-@Nat narrow (#984) arms but no refined arm, and `_compile_lifted_closure`
# guarded the @Nat/@Int returns but not the refinement's predicate — while the
# #984 leaf-guard gate excluded refinements on the (then-false) assumption that
# "the refinement's own boundary guard lives at the call/return boundary".  The
# verifier now records the refined closure return `tier3` guarded (the closure
# body is opaque to SMT — same shallow-syntactic, never-false-Tier-1 treatment
# as the #820/#984 arms) and codegen guards the lifted body's return value,
# mirroring the named path's refined-return guard (`_compile_postconditions`).
# 0 is the discriminating input again: it clears any `>= 0` backstop but
# violates the strict `> 0`.
# ---------------------------------------------------------------------------

_CLOSURE_REFINED_RET_LEAK = f"""
{_POS}
type F = fn(Int -> Pos) effects(pure);
private fn mk(@Unit -> @F) requires(true) ensures(true) effects(pure)
{{ fn(@Int -> @Pos) effects(pure) {{ @Int.0 }} }}
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{{ let @F = mk(()); apply_fn(@F.0, @Int.0) }}
"""


class TestClosureRefinedReturn1032:
    def test_refined_return_obligated_tier3(self) -> None:
        # The closure body is opaque to the SMT layer, so the refined return is
        # obligated shallow-syntactically — exactly ONE tier3 refine_bind (a
        # runtime-guard promise), NEVER a false Tier-1 and never the pre-fix
        # empty list (no obligation at all: the #1032 hole).
        statuses = _refine_bind_statuses(_CLOSURE_REFINED_RET_LEAK)
        assert statuses == ["tier3"], (
            f"expected one tier3 closure-return refine_bind, got {statuses} "
            f"(pre-fix: [] — the #1032 silent clean verify)"
        )

    @pytest.mark.parametrize("bad", [-5, 0], ids=["neg", "zero"])
    def test_violating_return_traps(self, bad: int) -> None:
        # ...and codegen makes good on the promise: a body value violating the
        # predicate traps at the closure's return guard with the refinement
        # message (pre-fix it flowed out silently).  0 is the crux: it clears
        # the @Nat base's `>= 0`, so only the FULL predicate catches it.
        kind = _trap_kind(_CLOSURE_REFINED_RET_LEAK, "go", bad)
        assert kind == "contract_violation", (
            f"run({bad}) gave trap kind {kind!r} — expected the refinement "
            f"return guard (None = no trap: the #1032 silent leak)"
        )
        msg = _trap_message(_CLOSURE_REFINED_RET_LEAK, "go", bad) or ""
        assert "Refinement violation" in msg and "return value" in msg, (
            f"trap message did not name the refined return: {msg!r}"
        )

    def test_satisfying_return_passes_guard(self) -> None:
        # A body value satisfying the predicate passes the guard unharmed.
        assert _run(_CLOSURE_REFINED_RET_LEAK, "go", 5) == 5

    def test_healthy_refined_return_tier3_and_no_trap(self) -> None:
        # The always-satisfying body (`if @Int.0 > 0 then { @Int.0 } else
        # { 1 }`): still tier3 (the closure is opaque — over-guarded, never
        # proven Tier-1, matching the #984 `_CLOSURE_SAFE` philosophy), verify
        # stays non-erroring, and the live guard never trips.
        assert _refine_bind_statuses(_CLOSURE_REFINED) == ["tier3"], (
            "a healthy refined closure return must be an honest tier3, "
            "never E505-violated"
        )
        assert _run(_CLOSURE_REFINED, "go", 5) == 5
        assert _run(_CLOSURE_REFINED, "go", 0) == 1


_CLOSURE_REFINED_STR_RET = """\
type NonEmptyStr = { @String | string_length(@String.0) > 0 };
type IntToStr = fn(Int -> NonEmptyStr) effects(pure);

private fn call_it(@IntToStr, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @NonEmptyStr = apply_fn(@IntToStr.0, @Int.0);
  string_length(@NonEmptyStr.0)
}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  call_it(fn(@Int -> @NonEmptyStr) effects(pure) {
    if @Int.0 > 0 then { "vera" } else { "" }
  }, @Int.0)
}
"""

_CLOSURE_REFINED_STR_FORMAL = """\
type NonEmptyStr = { @String | string_length(@String.0) > 0 };
type StrToInt = fn(NonEmptyStr -> Int) effects(pure);

private fn call_it(@StrToInt, @String -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@StrToInt.0, @String.0)
}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then {
    call_it(fn(@NonEmptyStr -> @Int) effects(pure) {
      string_length(@NonEmptyStr.0)
    }, "abc")
  } else {
    call_it(fn(@NonEmptyStr -> @Int) effects(pure) {
      string_length(@NonEmptyStr.0)
    }, "")
  }
}
"""


class TestClosureRefinedPair1032:
    """The i32_pair (String/Array) halves of the #1032/#1024 closure guards.

    A pair value is (ptr, len) on the WASM stack; the guards must save BOTH
    halves, run the predicate over the ptr (`string_length` reads the length
    from memory, as the named-function pair guard does), and re-push in the
    right order — an ordering bug would corrupt the value or read garbage.
    The scalar tests above cannot see any of that, so the pair paths carry
    their own end-to-end pins.
    """

    def test_pair_return_obligated_and_guarded(self) -> None:
        # Verifier half: the refined String RETURN records the same honest
        # guarded tier3 as the scalar shape.
        statuses = _refine_bind_statuses(_CLOSURE_REFINED_STR_RET)
        assert statuses == ["tier3"], (
            f"expected one tier3 pair-return refine_bind, got {statuses}"
        )
        # Codegen half: the empty string violates `string_length > 0` at the
        # closure's return guard...
        kind = _trap_kind(_CLOSURE_REFINED_STR_RET, "go", 0)
        assert kind == "contract_violation", (
            f"go(0) gave trap kind {kind!r} — the pair return guard must trap "
            f"an empty NonEmptyStr (None = the value leaked through)"
        )
        # ...and a satisfying value survives the save-guard-reload INTACT:
        # length 4 proves the (ptr, len) pair was re-pushed unharmed.
        assert _run(_CLOSURE_REFINED_STR_RET, "go", 5) == 4

    def test_pair_formal_obligated_and_guarded(self) -> None:
        # The argument-side (#1024) pair dual: a refined String FORMAL through
        # apply_fn — entry guard traps the empty string, passes "abc" with the
        # value intact (length 3 read through the guarded param).
        statuses = _refine_bind_statuses(_CLOSURE_REFINED_STR_FORMAL)
        assert statuses == ["tier3"], (
            f"expected one tier3 pair-formal refine_bind, got {statuses}"
        )
        kind = _trap_kind(_CLOSURE_REFINED_STR_FORMAL, "go", 0)
        assert kind == "contract_violation", (
            f"go(0) gave trap kind {kind!r} — the pair entry guard must trap "
            f"an empty NonEmptyStr argument"
        )
        assert _run(_CLOSURE_REFINED_STR_FORMAL, "go", 1) == 3


_REFINED_NONPLAIN_PRELUDE = """\
type NEPosArr = { @Array<{ @Int | @Int.0 > 0 }> | array_length(@Array<{ @Int | @Int.0 > 0 }>.0) > 0 };
"""

_NONPLAIN_CLOSURE_RET = _REFINED_NONPLAIN_PRELUDE + """\
type MK = fn(Array<{ @Int | @Int.0 > 0 }> -> NEPosArr) effects(pure);

public fn go(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @MK = fn(@Array<{ @Int | @Int.0 > 0 }> -> @NEPosArr) effects(pure) {
    @Array<{ @Int | @Int.0 > 0 }>.0
  };
  let @Array<{ @Int | @Int.0 > 0 }> = apply_fn(@MK.0, []);
  array_length(@Array<{ @Int | @Int.0 > 0 }>.0)
}
"""

_NONPLAIN_CLOSURE_FORMAL = _REFINED_NONPLAIN_PRELUDE + """\
type TK = fn(NEPosArr -> Nat) effects(pure);

public fn go(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @TK = fn(@NEPosArr -> @Nat) effects(pure) {
    array_length(@NEPosArr.0)
  };
  apply_fn(@TK.0, [])
}
"""

_NONPLAIN_NAMED_FORMAL = _REFINED_NONPLAIN_PRELUDE + """\
private fn take(@NEPosArr -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@NEPosArr.0)
}

public fn go(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  take([])
}
"""

_NONPLAIN_NAMED_RET = _REFINED_NONPLAIN_PRELUDE + """\
public fn mk(@Array<{ @Int | @Int.0 > 0 }> -> @NEPosArr)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<{ @Int | @Int.0 > 0 }>.0
}
"""


class TestRefinedNonPlainBaseParity1036:
    """A refinement base with a NON-PLAIN type argument (a nested refinement
    or fn type, e.g. `Array<{ @Int | ... }>`) IS guarded, at every boundary.

    #1036 recorded these as `tier3_unguarded` on the premise that
    `_refinement_guard_parts` could not spell the binder slot and bailed.
    Since #1208 the binder is named by `vera.naming.slot_name`, whose
    ARGUMENTS go through the checker's own renderer, so a refinement or a
    function type in argument position renders like any other and the guard
    is emitted.  The disclosure was then wrong in the opposite direction to
    the one PR #1034 fixed: it under-counted a runtime check that does fire
    and told the reader to add a bound they already had.

    The cells below are a PARITY differential rather than a flag assertion:
    each shape is COMPILED and RUN on an empty array — the value the
    predicate forbids — and the verifier's classification is compared with
    what the artifact does.  A flag assertion alone would move with the flag;
    only running it can say the flag is true.
    """

    @pytest.mark.parametrize(
        ("src", "site"),
        [
            (_NONPLAIN_CLOSURE_RET, "closure return"),
            (_NONPLAIN_CLOSURE_FORMAL, "closure argument"),
            (_NONPLAIN_NAMED_FORMAL, "call argument"),
        ],
        ids=["closure-ret", "closure-formal", "named-formal"],
    )
    def test_the_classification_equals_what_the_module_does(
        self, src: str, site: str,
    ) -> None:
        statuses = _refine_bind_statuses(src)
<<<<<<< HEAD
        # The property is the ABSENCE of a guarded promise, asserted directly
        # rather than through "every status is the unguarded one".  Since #1410
        # a call whose formal writes a refinement INSIDE its type raises an
        # obligation of its own, and two of these fixtures make such a call —
        # `array_length(@Array<{ @Int | ... }>.0)`, whose argument's declared
        # type IS the formal, so it proves modularly.  That `verified` is a
        # different obligation about a different site; folding it into this
        # assertion would make the fixture's incidental calls part of a
        # statement about the boundary's guard.
        assert "tier3_unguarded" in statuses, (
            f"a non-plain-arg refined {site} must DISCLOSE — expected a "
            f"tier3_unguarded record, got {statuses} (#1036)"
        )
        assert "tier3" not in statuses, (
            f"a non-plain-arg refined {site} has no codegen guard, so a "
            f"'tier3' is an unfulfilled runtime-guard promise: {statuses} "
            "(#1036)"
=======
        assert statuses, f"{site}: no refine_bind obligation to classify"
        # ONE obligation per shape today, pinned so the `all(...)` below keeps
        # meaning what it says: with several, a mixed verdict would be read as
        # "guarded" by the any-not-unguarded reading and the comparison would
        # silently weaken.  Future hardening, not a current failure.
        assert len(statuses) == 1, (
            f"{site}: expected one refine_bind, got {statuses} — the parity "
            f"comparison below assumes a single site"
        )
        verifier_says_guarded = all(s != "tier3_unguarded" for s in statuses)
        kind = _trap_kind(src, "go", None)
        codegen_guards = kind == "contract_violation"
        assert codegen_guards == verifier_says_guarded, (
            f"{site}: the module "
            f"{'traps' if codegen_guards else 'does NOT trap'} on the empty "
            f"array (trap kind {kind!r}), verifier says "
            f"{'guarded' if verifier_says_guarded else 'unguarded'} "
            f"({statuses}) — the two sides have drifted"
        )

    def test_the_return_position_carries_the_guard_too(self) -> None:
        """The one shape with no empty-array entry point of its own.

        `mk` takes the array it returns, so a caller supplying an empty one
        would trap at `mk`'s own boundary either way; the emitted module is
        the oracle instead, and the classification is read beside it.
        """
        statuses = _refine_bind_statuses(_NONPLAIN_NAMED_RET)
        assert statuses and all(s != "tier3_unguarded" for s in statuses), (
            f"the return boundary discloses unguarded: {statuses}"
        )
        with _resolved_pipeline(_NONPLAIN_NAMED_RET) as (prog, arts, res, path):
            wat = codegen_compile(
                prog, source=_NONPLAIN_NAMED_RET, file=path,
                resolved_modules=res,
                expr_semantic_types=arts.expr_semantic_types,
            ).wat
        assert "call $vera.contract_fail" in wat, (
            "the classification claims a guard the emitted module lacks"
>>>>>>> 6bcf5a9e (Stop disclosing a guard that fires, for a refined base with a non-plain type argument)
        )

    def test_plain_base_still_promises_guard(self) -> None:
        # The control: a PLAIN NamedType base keeps its honest guarded tier3
        # (the closure guards fire for these — pinned by the classes above).
        assert _refine_bind_statuses(_CLOSURE_REFINED_RET_LEAK) == ["tier3"]


def _obligation_kinds_statuses(source: str) -> set[tuple[str, str]]:
    """Every (kind, status) pair in the verifier's obligation stream — for
    intersection shapes where ONE value carries obligations of two kinds
    (a refinement over `@Int` receiving an intrinsically-`@Nat` value gets
    both the predicate obligation and the widen obligation)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = verify(
            program, source, file=path, resolved_modules=resolved,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        return {
            (o.kind, o.status) for o in result.obligations
            if o.kind in (_REFINE_KIND, "nat_to_int_coerce", "int_widen")
        }


_CAP_RET_INTERSECTION = """\
type Cap = { @Int | @Int.0 < 100 };
type F = fn(Nat -> Cap) effects(pure);

public fn go(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @F = fn(@Nat -> @Cap) effects(pure) { @Nat.0 };
  apply_fn(@F.0, @Nat.0)
}
"""

_CAP_FORMAL_INTERSECTION = """\
type Cap = { @Int | @Int.0 < 100 };
type F = fn(Cap -> Int) effects(pure);

public fn go(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @F = fn(@Cap -> @Int) effects(pure) { @Cap.0 };
  apply_fn(@F.0, @Nat.0)
}
"""


class TestRefinedOverIntWidenIntersection:
    """A refinement OVER `@Int` receiving an intrinsically-`@Nat` value is an
    INTERSECTION: codegen emits BOTH the refinement guard (the predicate) and
    the #820 widen guard (`value < 0` = a u64 above i64.MAX reinterpreted) —
    the predicate may not imply fit-in-i64 (`< 100` is SATISFIED by a
    reinterpreted negative), so the widen guard is not subsumable.  The
    obligation stream must describe both guards (PR #1034 review): the
    refined-first arm records the predicate obligation AND the widen
    obligation, never an either/or.
    """

    def test_refined_int_return_with_nat_body_records_both(self) -> None:
        kinds = _obligation_kinds_statuses(_CAP_RET_INTERSECTION)
        assert (_REFINE_KIND, "tier3") in kinds, kinds
        assert any(k != _REFINE_KIND and s == "tier3" for k, s in kinds), (
            f"the #820 widen guard codegen emits for this return has no "
            f"obligation describing it — got only {kinds}"
        )

    def test_refined_int_formal_with_nat_arg_records_both(self) -> None:
        # The formal side discharges via full SMT (unlike the opacity-shallow
        # return), so the refine_bind here is a correct E505 `violated` — an
        # unconstrained @Nat can exceed the `< 100` predicate.  The pin is
        # the WIDEN kind's presence: the call-site widen guard codegen emits
        # must have an obligation describing it, whatever the predicate
        # obligation resolved to.
        kinds = _obligation_kinds_statuses(_CAP_FORMAL_INTERSECTION)
        assert any(k == _REFINE_KIND for k, _ in kinds), kinds
        assert any(
            k != _REFINE_KIND and s in ("tier3", "verified")
            for k, s in kinds
        ), (
            f"the #820 call-site widen guard for this formal has no "
            f"obligation describing it — got only {kinds}"
        )

    def test_intersection_runtime_behavior_pinned(self) -> None:
        # The guards themselves: a satisfying value passes intact; a value
        # violating the predicate traps at the refinement guard.  (The widen
        # guard's own firing needs a u64 above i64.MAX and is pinned by the
        # #820 suites; here we pin that adding the obligation changed no
        # runtime behavior.)
        assert _run(_CAP_RET_INTERSECTION, "go", 5) == 5
        kind = _trap_kind(_CAP_RET_INTERSECTION, "go", 150)
        assert kind == "contract_violation", kind


class TestRefinedBoundaryGuardableHelper:
    """Direct pins on `_refined_boundary_codegen_guardable` — the semantic
    mirror of codegen's `_refinement_guard_parts` bail set (#1036).  The
    erased-base arm must key on REPRESENTATION (`erases_to_unit`), not the
    bare `Unit` name: a `Future<Unit>` base erases identically (#841), so
    claiming it guardable would be the same unfulfilled-promise class
    (PR #1034 full review)."""

    def test_erased_bases_unguardable(self) -> None:
        from vera.types import (
            INT, UNIT, AdtType, PrimitiveType, RefinedType,
        )
        from vera.verifier import ContractVerifier

        pred = object()  # predicate payload is irrelevant to the keying
        g = ContractVerifier._refined_boundary_codegen_guardable
        assert not g(RefinedType(UNIT, pred))
        assert not g(RefinedType(AdtType("Future", (UNIT,)), pred))
        # A refinement OVER a refinement is codegen's other bail (E618).
        assert not g(RefinedType(RefinedType(INT, pred), pred))
        assert g(RefinedType(INT, pred))
        assert g(RefinedType(AdtType("Array", (PrimitiveType("Int"),)), pred))
        # #1036: a NON-PLAIN type argument is guardable — the binder renders
        # through `slot_name`, whose arguments go through the checker's own
        # renderer, so the guard is emitted and the parity cells run it.
        assert g(RefinedType(AdtType("Array", (RefinedType(INT, pred),)), pred))


class TestClosureInteriorBindingDifferential779:
    """PR #1202: the #779 fresh-scope descent records interior closure
    binding sites (`let @Nat = <closure Int param>`) as tier3 with
    guarded=True — this differential proves the claimed guard exists:
    the lifted closure's compiled body traps the negative narrowing and
    passes the non-negative one.  The verifier side of the pair is
    pinned in tests/test_verifier_fresh_scope.py
    (test_nat_bind_in_closure_body_is_tier3_guarded)."""

    _INTERIOR_LET = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map([@Int.0], fn(@Int -> @Int) effects(pure) { let @Nat = @Int.0; nat_to_int(@Nat.0) });
  @Array<Int>.0[0]
}
"""

    def test_negative_traps(self) -> None:
        assert _run(self._INTERIOR_LET, "go", -5) is None, (
            "interior closure let-narrowing guard missing -> silent negative"
        )

    def test_non_negative_passes(self) -> None:
        assert _run(self._INTERIOR_LET, "go", 7) == 7

    def test_zero_survives(self) -> None:
        assert _run(self._INTERIOR_LET, "go", 0) == 0


class TestNestedSubpatternDifferential:
    """PR #1202 silent-failure review: the nested `@Nat` sub-pattern bind
    (`MkWrap(MkBox(@Nat))`) IS codegen-guarded — this differential proves
    the guard the verifier's static fallback claims (guarded tier3 on an
    unprojectable scrutinee, pinned in tests/test_verifier_fresh_scope.py
    TestNestedSubpatternFallback).  The refined nested bind is the
    UNGUARDED residual (#765) and is disclosed as tier3_unguarded/E506
    instead."""

    _NESTED_NAT = """\
private data Box {
  MkBox(Int)
}

private data Wrap {
  MkWrap(Box)
}

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  let @Wrap = MkWrap(MkBox(@Int.0));
  match @Wrap.0 {
    MkWrap(MkBox(@Nat)) -> nat_to_int(@Nat.0)
  }
}
"""

    def test_negative_traps(self) -> None:
        assert _run(self._NESTED_NAT, "go", -5) is None, (
            "nested @Nat sub-pattern guard missing -> silent negative"
        )

    def test_non_negative_passes(self) -> None:
        assert _run(self._NESTED_NAT, "go", 7) == 7

    def test_zero_survives(self) -> None:
        assert _run(self._NESTED_NAT, "go", 0) == 0

    _NESTED_NAT_CLOSURE = """\
private data Box {
  MkBox(Int)
}

private data Wrap {
  MkWrap(Box)
}

private fn mk(@Int -> @Wrap) requires(true) ensures(true) effects(pure)
{ MkWrap(MkBox(@Int.0)) }

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map([@Int.0], fn(@Int -> @Int) effects(pure) { match mk(@Int.0) { MkWrap(MkBox(@Nat)) -> nat_to_int(@Nat.0) } });
  @Array<Int>.0[0]
}
"""

    def test_closure_position_negative_traps(self) -> None:
        """The CLOSURE-position twin — the exact combination the static
        fallback covers (unprojectable scrutinee under the fresh-scope
        descent, guarded=True record): the runtime guard it claims must
        trap here too, not only in direct position."""
        assert _run(self._NESTED_NAT_CLOSURE, "go", -5) is None, (
            "closure nested @Nat sub-pattern guard missing -> silent negative"
        )

    def test_closure_position_non_negative_passes(self) -> None:
        assert _run(self._NESTED_NAT_CLOSURE, "go", 7) == 7

    def test_closure_position_zero_survives(self) -> None:
        """Zero must SURVIVE the closure-position nested guard — an
        off-by-one `> 0` guard mutant would trap valid @Nat zero."""
        assert _run(self._NESTED_NAT_CLOSURE, "go", 0) == 0


class TestHandlerStateBoundaryDifferential1203:
    """#1203: every handler write boundary into a @Nat state cell is
    runtime-guarded — state-init, the builtin `put` argument, the `with`
    state update, and the `resume` argument.  Each traps a negative and
    passes the non-negative control; the verifier stream twins live in
    tests/test_verifier_fresh_scope.py
    (TestHandlerStateBoundaryObligations)."""

    _INIT = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = @Int.0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    nat_to_int(get(()))
  }
}
"""
    _PUT = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    put(@Int.0);
    nat_to_int(get(()))
  }
}
"""
    _WITH = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) } with @Nat = @Int.0
  } in {
    put(5);
    nat_to_int(get(()))
  }
}
"""
    _RESUME = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Nat) -> { resume(()) }
  } in {
    nat_to_int(get(()))
  }
}
"""

    def test_init_negative_traps(self) -> None:
        assert _run(self._INIT, "go", -7) is None
    def test_init_non_negative_passes(self) -> None:
        assert _run(self._INIT, "go", 9) == 9
    def test_init_zero_survives(self) -> None:
        assert _run(self._INIT, "go", 0) == 0
    def test_put_negative_traps(self) -> None:
        assert _run(self._PUT, "go", -7) is None
    def test_put_non_negative_passes(self) -> None:
        assert _run(self._PUT, "go", 9) == 9
    def test_with_negative_traps(self) -> None:
        assert _run(self._WITH, "go", -7) is None
    def test_with_non_negative_passes(self) -> None:
        assert _run(self._WITH, "go", 9) == 9
    def test_resume_negative_traps(self) -> None:
        assert _run(self._RESUME, "go", -7) is None
    def test_resume_non_negative_passes(self) -> None:
        assert _run(self._RESUME, "go", 9) == 9

    def test_put_zero_survives(self) -> None:
        """The four boundaries are wired independently in codegen — each
        needs its own zero-boundary probe (a `> 0` off-by-one at any one
        would reject valid @Nat zero and pass the others' probes)."""
        assert _run(self._PUT, "go", 0) == 0

    def test_with_zero_survives(self) -> None:
        assert _run(self._WITH, "go", 0) == 0

    def test_resume_zero_survives(self) -> None:
        assert _run(self._RESUME, "go", 0) == 0

    _PUT_NO_CLAUSE = """\
public fn go(@Int -> @Bool) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) }
  } in {
    put(@Int.0);
    get(()) < 0
  }
}
"""

    def test_bare_put_negative_traps(self) -> None:
        """The BARE intrinsic dispatch path (no `put` clause declared) —
        the adversarial round's critical find: the clause-inlined guard
        never runs here, so this fixture stored -7 and returned true
        through the @Nat cell.  The guard now lives on the bare path too
        (keyed off the state-cell type in the dispatch target)."""
        assert _run(self._PUT_NO_CLAUSE, "go", -7) is None
    def test_bare_put_non_negative_passes(self) -> None:
        assert _run(self._PUT_NO_CLAUSE, "go", 9) == 0
    def test_bare_put_zero_survives(self) -> None:
        assert _run(self._PUT_NO_CLAUSE, "go", 0) == 0

    # The handler is `State<Bool>` while the DECLARED row is `State<Nat>`, so
    # the get clause's bare `put(@Int.0)` resolves outward to the declared
    # `State<Nat>` row (#1211) and takes the bare intrinsic dispatch path —
    # which is what this pair pins, on the @Nat cell whose narrowing guard is
    # the subject.  It used to handle `State<Nat>` here, i.e. the SAME family
    # as the row it routes to; that shape is unaddressable by construction
    # (the intrinsics reach only the innermost cell of a family, so the store
    # would land in the handler's own cell rather than the caller's) and is
    # now a loud codegen skip — see #1233.  Two families keep the routing
    # honest AND the boundary under test unchanged.
    _PUT_IN_CLAUSE_BODY = """\
public fn go(@Int -> @Bool) requires(true) ensures(true) effects(<State<Nat>>)
{
  handle[State<Bool>](@Bool = false) {
    get(@Unit) -> { put(@Int.0); resume(@Bool.0) },
    put(@Bool) -> { resume(()) }
  } in {
    get(())
  }
}
"""

    def test_clause_body_put_negative_traps(self) -> None:
        """A put INSIDE another clause's body takes the bare path too
        (the clause body compiles against the handler's DECLARATION scope,
        whose `put` here is the declared row's) — same guard."""
        assert _run(self._PUT_IN_CLAUSE_BODY, "go", -5) is None
    def test_clause_body_put_non_negative_passes(self) -> None:
        assert _run(self._PUT_IN_CLAUSE_BODY, "go", 9) == 0

    def test_clause_body_put_zero_survives(self) -> None:
        """Zero is the guard's boundary, and every sibling pair pins it.

        `@Nat`'s range starts AT zero, so a guard written `<= 0` instead of
        `< 0` traps here while both the negative and the positive case above
        stay green — the one input that separates the correct comparison from
        the off-by-one (round-5 review; this pair was the only boundary
        differential in the class missing it)."""
        assert _run(self._PUT_IN_CLAUSE_BODY, "go", 0) == 0


class TestHandlerStateWidenDifferential1203:
    """The widen DUAL of the boundary differentials: a `State<Int>` cell
    receiving an intrinsically-@Nat value is guarded at every boundary —
    a @Nat above i64.MAX would bit-reinterpret to a negative @Int.  The
    adversarial round's mutation battery showed every widen arm was
    deletable without detection; these pin each arm at U64_MAX with
    in-range and i64.MAX boundary controls."""

    _WIDEN_INIT = """\
public fn go(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = @Nat.0) {
    get(@Unit) -> { resume(@Int.0) }
  } in {
    get(())
  }
}
"""
    _WIDEN_PUT = """\
public fn go(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) }
  } in {
    put(@Nat.0);
    get(())
  }
}
"""
    _WIDEN_RESUME = """\
public fn go(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(nat_to_int(@Nat.0)) }
  } in {
    get(())
  }
}
"""

    def test_widen_init_u64max_traps(self) -> None:
        assert _run(self._WIDEN_INIT, "go", U64_MAX) is None
    def test_widen_init_in_range_passes(self) -> None:
        assert _run(self._WIDEN_INIT, "go", 42) == 42
    def test_widen_put_u64max_traps(self) -> None:
        assert _run(self._WIDEN_PUT, "go", U64_MAX) is None
    def test_widen_put_in_range_passes(self) -> None:
        assert _run(self._WIDEN_PUT, "go", 42) == 42
    def test_widen_resume_i64max_passes(self) -> None:
        """Boundary control: exactly i64.MAX survives (the suite's
        established no-trap-at-i64-max convention)."""
        assert _run(self._WIDEN_RESUME, "go", 2**63 - 1) == 2**63 - 1

    def test_widen_resume_u64max_traps(self) -> None:
        """The resume widen arm's own U64_MAX probe — the class
        docstring's promise; deleting the get-resume widen guard was
        green without it (PR #1202 review)."""
        assert _run(self._WIDEN_RESUME, "go", U64_MAX) is None

    _WIDEN_WITH = """\
public fn go(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Nat.0
  } in {
    put(1);
    get(())
  }
}
"""

    def test_widen_with_update_u64max_traps(self) -> None:
        """The `with @Int = <@Nat>` state-update widen arm — obligated
        `widen_guarded=True`, so the guard promise needs its trap
        witness."""
        assert _run(self._WIDEN_WITH, "go", U64_MAX) is None
    def test_widen_with_update_in_range_passes(self) -> None:
        assert _run(self._WIDEN_WITH, "go", 42) == 42

    _TAIL_MATCH_RESUME = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { match 1 { @Int -> resume(@Int.1) } },
    put(@Nat) -> { resume(()) }
  } in {
    nat_to_int(get(()))
  }
}
"""

    def test_tail_match_resume_negative_traps(self) -> None:
        """`_tail_resume_arg`'s single-arm-match descent — deleting the
        MatchExpr arm silently un-guards this legal, lowerable form."""
        assert _run(self._TAIL_MATCH_RESUME, "go", -7) is None
    def test_tail_match_resume_non_negative_passes(self) -> None:
        assert _run(self._TAIL_MATCH_RESUME, "go", 9) == 9

    _ALIAS_ANNOTATION = """\
type Count = Nat;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Count = @Int.0) {
    get(@Unit) -> { resume(@Count.0) },
    put(@Nat) -> { resume(()) }
  } in {
    nat_to_int(get(()))
  }
}
"""

    def test_alias_annotation_init_traps(self) -> None:
        """The legal annotation-vs-argument NAME divergence (#1205/#1206):
        `(@Count = ...)` on `State<Nat>` with `type Count = Nat` passes
        E336 (resolution-equal) while the annotation's slot NAME differs
        from the cell family — the init guard must key off the effect's
        cell type, not the annotation's name.  (The truly divergent
        `(@Int = ...)` shape this fixture previously used is now
        check-rejected outright — see the E336 pin below.)"""
        assert _run(self._ALIAS_ANNOTATION, "go", -5) is None
    def test_alias_annotation_init_passes(self) -> None:
        """And the clause scope binds the state under the ANNOTATION's own
        slot name: `resume(@Count.0)` reads the cell through the alias."""
        assert _run(self._ALIAS_ANNOTATION, "go", 9) == 9

    _DIVERGENT_ANNOTATION = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Int = @Int.0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    nat_to_int(get(()))
  }
}
"""

    def test_divergent_annotation_rejected_e336(self) -> None:
        """The lying-annotation shape (`(@Int = ...)` on `State<Nat>`) is
        now unreachable from checked source: E336 (#1206).  This is what
        retired the runtime differential this fixture used to drive — the
        guards-key-off-the-cell-type property lives on in the legal alias
        shape above, and the full E336 accept/reject matrix lives in
        tests/test_checker_types.py."""
        diags, _arts = typecheck_with_artifacts(
            parse_to_ast(self._DIVERGENT_ANNOTATION))
        assert any(d.error_code == "E336" for d in diags)


class TestScalarAliasFamilyDifferential1205:
    """#1205 compile-and-run differentials: a scalar type alias as
    ``State<T>`` / ``Exn<E>`` joins the BASE import/tag family (name and
    WASM type resolve together), the clause scope binds slots under
    SOURCE names, and every #1203 boundary guard keys through the alias.
    Each fixture was invalid WASM (i32/i64 type mismatch), a dangling
    slot ref (E699), or a silent wrong-binding before the fix."""

    _ALIAS_CELL = """\
type Count = Nat;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Count>](@Count = 6) {
    get(@Unit) -> { resume(@Count.0) },
    put(@Count) -> { resume(()) }
  } in {
    nat_to_int(get(()))
  }
}
"""

    def test_alias_cell_compiles_and_runs(self) -> None:
        """`State<Count>` with `type Count = Nat` — the issue repro —
        was invalid WASM (family typed i32 against i64 values).  The
        init (6) cannot coincide with a default-initialised cell, a
        dropped read, or the argument (0)."""
        assert _run(self._ALIAS_CELL, "go", 0) == 6

    _REFINED_ALIAS_CELL = """\
type Pos = { @Int | @Int.0 > 0 };

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Pos>](@Pos = 1) {
    get(@Unit) -> { resume(@Pos.0) },
    put(@Pos) -> { resume(()) }
  } in {
    get(())
  }
}
"""

    def test_refined_alias_cell_compiles_and_runs(self) -> None:
        """A refined alias erases to its base scalar family (`Pos` →
        `Int`)."""
        assert _run(self._REFINED_ALIAS_CELL, "go", 0) == 1

    _ALIAS_INIT_GUARD = """\
type Count = Nat;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Count>](@Count = @Int.0) {
    get(@Unit) -> { resume(@Count.0) },
    put(@Count) -> { resume(()) }
  } in {
    nat_to_int(get(()))
  }
}
"""

    def test_alias_init_guard_traps(self) -> None:
        """The #1203 init guard keys through the alias: a negative @Int
        into the `Count`(=Nat) cell traps."""
        assert _run(self._ALIAS_INIT_GUARD, "go", -5) is None
    def test_alias_init_guard_passes(self) -> None:
        assert _run(self._ALIAS_INIT_GUARD, "go", 9) == 9

    _ALIAS_PUT_GUARD = """\
type Count = Nat;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Count>](@Count = 0) {
    get(@Unit) -> { resume(@Count.0) },
    put(@Count) -> { resume(()) }
  } in {
    put(@Int.0);
    nat_to_int(get(()))
  }
}
"""

    def test_alias_put_guard_traps(self) -> None:
        """put's argument boundary through the alias: a negative @Int
        into the `Count`(=Nat) cell traps at the clause-inlined store."""
        assert _run(self._ALIAS_PUT_GUARD, "go", -5) is None
    def test_alias_put_guard_passes(self) -> None:
        assert _run(self._ALIAS_PUT_GUARD, "go", 9) == 9

    _ALIAS_WIDEN_INIT = """\
type Whole = Int;

public fn go(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Whole>](@Whole = @Nat.0) {
    get(@Unit) -> { resume(@Whole.0) }
  } in {
    get(())
  }
}
"""

    def test_alias_widen_init_u64max_traps(self) -> None:
        """The widen dual through an Int alias: a @Nat above i64.MAX
        into the `Whole`(=Int) cell traps."""
        assert _run(self._ALIAS_WIDEN_INIT, "go", U64_MAX) is None
    def test_alias_widen_init_in_range_passes(self) -> None:
        assert _run(self._ALIAS_WIDEN_INIT, "go", 42) == 42

    _STATELESS_CLAUSE_ARG = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Int>] {
    put(@Int) -> { assert(@Int.0 == 7); resume(()) }
  } in {
    put(7);
    get(())
  }
}
"""

    def test_stateless_clause_binds_op_arg(self) -> None:
        """A STATELESS handler's clause scope has no state binding — the
        checker binds `@Int.0` to put's ARGUMENT.  Pre-fix codegen
        pushed the pre-store cell capture anyway, so the assert read the
        cell (0), not the argument (7): silently wrong values wherever
        the types align, this trap where the assert caught it."""
        assert _run(self._STATELESS_CLAUSE_ARG, "go", 0) == 7

    _STATELESS_CLAUSE_ARG_NEG = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Int>] {
    put(@Int) -> { assert(@Int.0 == 0); resume(()) }
  } in {
    put(7);
    get(())
  }
}
"""

    _PUT_PATTERN_NAME = """\
type Count = Nat;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Count) -> { assert(@Count.0 == 7); resume(()) }
  } in {
    put(7);
    nat_to_int(get(()))
  }
}
"""

    def test_put_param_binds_under_pattern_name(self) -> None:
        """A put clause whose PATTERN names an alias of the argument type
        (`put(@Count)` on `State<Nat>`) binds the argument under the
        pattern's own slot name — `@Count.0` is the argument in the
        clause body (the state binds under the annotation's `@Nat`), and
        codegen must push under the same name or the ref dangles."""
        assert _run(self._PUT_PATTERN_NAME, "go", 0) == 7

    def test_stateless_clause_arg_not_cell(self) -> None:
        """The mirror pin: asserting the CELL's pre-store value (0) —
        what the pre-fix skew read — must now trap, proving `@Int.0`
        reaches the argument and not the capture."""
        assert _run(self._STATELESS_CLAUSE_ARG_NEG, "go", 0) is None

    _EXN_ALIAS = """\
type Code = Int;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[Exn<Code>] {
    throw(@Code) -> { 0 - @Code.0 }
  } in {
    throw(42)
  }
}
"""

    def test_exn_alias_compiles_and_runs(self) -> None:
        """`Exn<Code>` with `type Code = Int` — the Exn twin of the
        State family split (tag typed i64, catch local i32) — and the
        caught payload binds under the clause pattern's own name."""
        assert _run(self._EXN_ALIAS, "go", 0) == -42

    _EXN_PATTERN_NAME = """\
type Code = Int;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[Exn<Code>] {
    throw(@Int) -> { 0 - @Int.0 }
  } in {
    throw(42)
  }
}
"""

    def test_exn_caught_binds_under_pattern_name(self) -> None:
        """A clause pattern naming the RESOLVED base (`throw(@Int)` on
        `Exn<Code>`) binds the caught payload under the PATTERN's own
        slot name — `@Int.0` is the payload, `@Int.1` the enclosing
        function's parameter (checker binding order), and codegen must
        agree or the ref lands one slot off."""
        assert _run(self._EXN_PATTERN_NAME, "go", 0) == -42

    _OLD_ALIAS = """\
type Count = Nat;

public fn bump(@Nat -> @Int)
  requires(true)
  ensures(new(State<Count>) >= old(State<Count>))
  effects(<State<Count>>)
{
  put(get(()) + @Nat.0);
  nat_to_int(get(()))
}
"""

    def test_old_state_alias_snapshot(self) -> None:
        """`old(State<Count>)` snapshots (and the postcondition compares)
        through the collapsed family — the comparison previously typed
        its operands off the unresolved name (i32) against i64 reads."""
        assert _run(self._OLD_ALIAS, "bump", 5) == 5


class TestClauseScopeCheckerParity:
    """The adversarial round's clause-scope findings, pinned: clause
    slot names use the CHECKER's rule (top name syntactic, type
    arguments canonicalized), a patternless clause binds nothing, and
    clause bodies compile against the HANDLER-DECLARATION scope — each
    shape below either silently produced the wrong value or dangled
    (E699) on a check-green program before the round-2 fixes."""

    _MIXED_ARG_REF = """\
type Cnt = Int;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(100)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Cnt>) -> { resume(()) } with @Option<Int> = @Option<Int>.1
  } in {
    put(Some(7));
    match get(()) {
      Some(@Int) -> @Int.0,
      None -> 0 - 1
    }
  }
}
"""

    def test_alias_arg_pattern_canonical_ref(self) -> None:
        """`put(@Option<Cnt>)` binds under canonical `Option<Int>` (the
        checker's rule), so the with-expr's `@Option<Int>.1` is the put
        ARGUMENT — the with-override stores it (7).  Pre-fix the pattern
        bound under the opaque spelling and the ref dangled (E699)."""
        assert _run(self._MIXED_ARG_REF, "go", 0) == 7

    _MIXED_ANNOTATION = """\
type Cnt = Int;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Int>>](@Option<Cnt> = Some(100)) {
    get(@Unit) -> { resume(@Option<Int>.0) }
  } in {
    match get(()) {
      Some(@Int) -> @Int.0,
      None -> 0 - 1
    }
  }
}
"""

    def test_alias_annotation_canonical_state(self) -> None:
        """An alias inside the composite ANNOTATION (E336-equal): the
        state binds under canonical `Option<Int>`, so the natural
        `@Option<Int>.0` spelling reads the state (100).  Pre-fix:
        E699."""
        assert _run(self._MIXED_ANNOTATION, "go", 0) == 100

    _EXN_MIXED_PATTERN = """\
type Cnt = Int;

private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Option<Int>>>)
{
  throw(Some(7))
}

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Some(100);
  handle[Exn<Option<Int>>] {
    throw(@Option<Cnt>) -> {
      match @Option<Int>.0 {
        Some(@Int) -> @Int.0,
        None -> 0 - 1
      }
    }
  } in {
    boom(())
  }
}
"""

    def test_exn_alias_pattern_canonical_payload(self) -> None:
        """The Exn twin: `throw(@Option<Cnt>)` binds the payload under
        canonical `Option<Int>`, so `@Option<Int>.0` is the CAUGHT value
        (7), not the enclosing binding (100) — the pre-fix opaque
        binding silently read the outer one."""
        assert _run(self._EXN_MIXED_PATTERN, "go", 0) == 7

    _PATTERNLESS_PUT = """\
type Count = Nat;

public fn go(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Count = 100) {
    get(@Unit) -> { resume(@Count.0) },
    put() -> { resume(()) } with @Count = @Nat.0
  } in {
    put(5);
    nat_to_int(get(()))
  }
}
"""

    def test_patternless_put_binds_nothing(self) -> None:
        """A patternless `put()` clause binds NO op-param slot (the
        checker's zip has nothing to bind), so the with-expr's `@Nat.0`
        is the enclosing fn parameter (9) — pre-fix codegen pushed the
        argument anyway and the with stored 5."""
        assert _run(self._PATTERNLESS_PUT, "go", 9) == 9

    _PATTERNLESS_THROW = """\
private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Int>>)
{
  throw(7)
}

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw() -> { @Int.0 }
  } in {
    boom(())
  }
}
"""

    def test_patternless_throw_binds_nothing(self) -> None:
        """The Exn twin: a patternless `throw()` binds no payload, so
        `@Int.0` in the clause is the enclosing fn parameter — pre-fix
        the payload was pushed anyway and the body read 7."""
        assert _run(self._PATTERNLESS_THROW, "go", 100) == 100

    _CALL_SITE_SHADOW = """\
public fn go(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.1) },
    put(@Nat) -> { resume(()) }
  } in {
    let @Nat = 777;
    nat_to_int(get(()))
  }
}
"""

    def test_clause_compiles_at_declaration_scope(self) -> None:
        """A clause body reaching past its own bindings resolves against
        the HANDLER-DECLARATION scope, as the checker checks it:
        `@Nat.1` is the fn parameter (9), not the `let @Nat = 777` the
        handled body made before the op call — pre-fix the clause
        inlined against the call-site env and read 777."""
        assert _run(self._CALL_SITE_SHADOW, "go", 9) == 9


class TestParameterizedAliasFamily:
    """The #1205 residual the adversarial round surfaced: a
    PARAMETERISED alias resolving to a scalar (`type Id<T> = T` at
    `Id<Nat>`, an alias of that, and the Exn twin) still split the
    family — registration substituted (import declared i64) while the
    name-level collapse left the compound name opaque (WT fell to the
    unknown-name i32 default).  All three were invalid WASM."""

    _PARAM_ALIAS = """\
type Id<T> = T;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Id<Nat>>](@Id<Nat> = 4) {
    put(@Id<Nat>) -> { resume(()) }
  } in {
    put(9);
    nat_to_int(get(()))
  }
}
"""

    def test_parameterized_alias_cell(self) -> None:
        assert _run(self._PARAM_ALIAS, "go", 0) == 9

    _ALIAS_OF_GENERIC = """\
type Id<T> = T;
type IdN = Id<Nat>;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<IdN>](@IdN = 4) {
    put(@IdN) -> { resume(()) }
  } in {
    put(9);
    nat_to_int(get(()))
  }
}
"""

    def test_alias_of_generic_alias_cell(self) -> None:
        assert _run(self._ALIAS_OF_GENERIC, "go", 0) == 9

    _EXN_PARAM_ALIAS = """\
type Id<T> = T;

private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Id<Int>>>)
{
  throw(7)
}

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[Exn<Id<Int>>] {
    throw(@Id<Int>) -> { 0 - @Id<Int>.0 }
  } in {
    boom(())
  }
}
"""

    def test_exn_parameterized_alias(self) -> None:
        assert _run(self._EXN_PARAM_ALIAS, "go", 0) == -7


class TestByteStateCell:
    """`State<Byte>` cells (adversarial round, finding 3): the family
    imports were correctly i32 all along, but an int LITERAL at any
    write boundary emitted the default `i64.const` into them — invalid
    WASM on every literal-writing Byte handler.  The #865 width
    coercion (the `let @Byte = 0` arm's sibling) now covers the init,
    both put dispatch paths, the `with` update, and the get-clause
    resume value."""

    _BYTE_CELL = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Byte>](@Byte = 0) {
    get(@Unit) -> { resume(@Byte.0) },
    put(@Byte) -> { resume(()) }
  } in {
    put(42);
    byte_to_int(get(()))
  }
}
"""

    def test_byte_cell_init_and_clause_put_literals(self) -> None:
        """Init literal + CLAUSE-inlined put literal (a put clause is
        present, so the argument takes the inlined path)."""
        assert _run(self._BYTE_CELL, "go", 0) == 42

    _BYTE_RESUME_LITERAL = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Byte>](@Byte = 5) {
    get(@Unit) -> { resume(9) },
    put(@Byte) -> { resume(()) }
  } in {
    byte_to_int(get(()))
  }
}
"""

    def test_byte_resume_literal(self) -> None:
        """`resume(9)` in a `State<Byte>` get clause is the op's i32
        result — the literal previously widened to i64."""
        assert _run(self._BYTE_RESUME_LITERAL, "go", 0) == 9

    _BYTE_WITH_LITERAL = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Byte>](@Byte = 5) {
    get(@Unit) -> { resume(@Byte.0) },
    put(@Byte) -> { resume(()) } with @Byte = 77
  } in {
    put(1);
    byte_to_int(get(()))
  }
}
"""

    def test_byte_with_update_literal(self) -> None:
        assert _run(self._BYTE_WITH_LITERAL, "go", 0) == 77

    _BYTE_BARE_PUT = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Byte>](@Byte = 5) {
    get(@Unit) -> { resume(@Byte.0) }
  } in {
    put(33);
    byte_to_int(get(()))
  }
}
"""

    def test_byte_bare_put_literal(self) -> None:
        """No put clause — the bare intrinsic dispatch path's literal."""
        assert _run(self._BYTE_BARE_PUT, "go", 0) == 33


class TestQualifiedStatePut:
    """`State.put(...)` — the QUALIFIED spelling — routes through the
    same dispatcher as bare `put(...)` (round-4 review): it previously
    took a bare unguarded call, silently skipping the clause's `with`
    transform, storing a negative into a @Nat cell, and emitting a Byte
    literal at i64."""

    _QUAL_WITH = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) } with @Nat = @Nat.1 * 2
  } in {
    State.put(4);
    nat_to_int(get(()))
  }
}
"""

    def test_qualified_put_applies_clause_transform(self) -> None:
        """The doubling `with` fires on the qualified spelling too —
        pre-fix `State.put(4)` stored 4 while `put(4)` stored 8."""
        assert _run(self._QUAL_WITH, "go", 0) == 8

    _QUAL_GUARD = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) }
  } in {
    State.put(@Int.0);
    nat_to_int(get(()))
  }
}
"""

    def test_qualified_put_negative_traps(self) -> None:
        """The #1203 narrowing guard covers the qualified dispatch —
        pre-fix -5 round-tripped through the @Nat cell silently."""
        assert _run(self._QUAL_GUARD, "go", -5) is None
    def test_qualified_put_non_negative_passes(self) -> None:
        assert _run(self._QUAL_GUARD, "go", 9) == 9

    _QUAL_BYTE = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Byte>](@Byte = 5) {
    get(@Unit) -> { resume(@Byte.0) }
  } in {
    State.put(33);
    byte_to_int(get(()))
  }
}
"""

    def test_qualified_put_byte_literal(self) -> None:
        """The #865 Byte-literal width coercion covers the qualified
        dispatch — pre-fix the literal emitted i64 into the i32 family."""
        assert _run(self._QUAL_BYTE, "go", 0) == 33


class TestNestedParameterizedAliasResolution:
    """Round-3's resolver root cause: marking an alias head as \"seen\"
    BEFORE substituting truncated legitimate finite expansions
    (`Id<Id<Nat>>` substitutes to `Id<Nat>`, whose head re-entry a
    seen-set misread as a cycle) — a silent handler bypass, an
    invalid-WASM family split reachable via an innocent wrapper alias,
    and a silent wrong clause binding.  Arguments now resolve FIRST
    (the checker's order), depth-bounded."""

    _NESTED_APPLICATION = """\
type Id<T> = T;

public fn go(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Id<Id<Nat>>>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    put(@Nat.0);
    nat_to_int(get(()))
  }
}
"""

    def test_nested_application_cell(self) -> None:
        """`State<Id<Id<Nat>>>` — one substitution produced `Id<Nat>`
        and the walk stopped there: registration typed the import i64
        while the lowering derived i32 from the opaque compound name.
        Invalid WASM pre-fix."""
        assert _run(self._NESTED_APPLICATION, "go", 7) == 7

    _WRAPPER_ALIAS = """\
type Id<T> = T;
type Two<T> = Id<Id<T>>;

public fn go(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Two<Nat>>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    put(@Nat.0);
    nat_to_int(get(()))
  }
}
"""

    def test_wrapper_alias_cell(self) -> None:
        """A single user application (`Two<Nat>` = `Id<Id<Nat>>`) hit
        the same truncation — entirely innocent source."""
        assert _run(self._WRAPPER_ALIAS, "go", 7) == 7

    _HANDLER_BYPASS = """\
type Id<T> = T;

private fn bump(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(<State<Id<Id<Nat>>>>)
{
  put(@Nat.0);
  get(())
}

public fn go(@Nat -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    bump(@Nat.0);
    nat_to_int(get(()))
  }
}
"""

    def test_effect_spelling_shares_the_handler_cell(self) -> None:
        """Two spellings of ONE resolved effect (`State<Id<Id<Nat>>>`
        declared, `State<Nat>` handled): the callee's ops must land in
        the handler's cell.  Pre-fix they routed to an unmanaged opaque
        family — the callee's put vanished and the handler's get read 0
        with valid WASM (the round's silent handler bypass)."""
        assert _run(self._HANDLER_BYPASS, "go", 7) == 7

    _EXN_NESTED_APPLICATION = """\
type Id<T> = T;

private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Id<Id<Int>>>>)
{
  throw(41)
}

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[Exn<Id<Id<Int>>>] {
    throw(@Int) -> { @Int.0 }
  } in {
    boom(())
  }
}
"""

    def test_exn_nested_application(self) -> None:
        assert _run(self._EXN_NESTED_APPLICATION, "go", 0) == 41

    _REFINED_ARG_PATTERN = """\
type Pos = { @Int | @Int.0 > 0 };

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Pos>>](@Option<Pos> = Some(5)) {
    get(@Unit) -> { resume(@Option<Pos>.0) },
    put(@Option<Pos>) -> { resume(()) }
  } in {
    put(Some(9));
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""

    def test_refined_arg_clause_binding_reachable(self) -> None:
        """A REFINED-resolving type argument in clause/annotation
        position (`Option<Pos>`): round-3's checker-mirrored bind key
        rendered the predicate-elided form no writable reference can
        spell, turning this working program into a dangling E699.  The
        source-spelling deviation keeps bind and ref meeting at the one
        spelling the checker accepts."""
        assert _run(self._REFINED_ARG_PATTERN, "go", 0) == 9


class TestResumeInWithExprRejected:
    """A `resume(...)` inside a `with` state-update expression was
    silently IGNORED (the lowering counts only the body's tail resume;
    the with-expr just evaluates for its value) — now a loud E602 skip
    with move-it-to-the-body guidance (round-3 review, F5)."""

    _RESUME_IN_WITH = """\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) } with @Int = { resume(77); @Int.0 + 1 },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""

    def test_resume_in_with_is_loud_skip(self) -> None:
        with _resolved_pipeline(self._RESUME_IN_WITH) as (
                program, arts, resolved, path):
            result = codegen_compile(
                program, source=self._RESUME_IN_WITH, file=path,
                resolved_modules=resolved,
                expr_semantic_types=arts.expr_semantic_types,
            )
            msgs = [d.description for d in result.diagnostics]
            assert any(
                "'with' state-update expression has no effect" in m
                for m in msgs
            ), msgs


class TestClauseScopeMixedSpellings:
    """Round-5/6: the ref layer resolves OPAQUE-only (both canonical-first
    attempts were unsound — a canonical hit can land on the wrong member
    of the checker's merged class whenever any same-class binding is
    spelled differently), so mixed-spelling shapes are either CORRECT
    under the shared opaque rule or LOUD.  These pin the shapes round 5
    proved silently wrong under canonical-first resolution."""

    _CLAUSE_LET_SHADOW = """\
type Cnt = Int;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(5)) {
    get(@Unit) -> {
      let @Option<Cnt> = Some(77);
      resume(@Option<Cnt>.0)
    }
  } in {
    match get(()) {
      Some(@Int) -> @Int.0,
      None -> 0 - 1
    }
  }
}
"""

    def test_clause_body_let_shadows_correctly(self) -> None:
        """A clause-body `let` of the same checker-class as the state:
        `@Option<Cnt>.0` is the let (most recent member — 77) under the
        checker AND under opaque resolution.  Canonical-first resolution
        silently returned the state (5)."""
        assert _run(self._CLAUSE_LET_SHADOW, "go", 0) == 77

    _OUTER_MIXED_PARAMS = """\
type Cnt = Int;

public fn go(@Option<Int>, @Option<Cnt> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> {
      resume(match @Option<Cnt>.0 {
        Some(@Int) -> @Int.0,
        None -> 0 - 1
      })
    }
  } in {
    get(())
  }
}

public fn drive(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  go(Some(111), Some(222))
}
"""

    def test_clause_ref_to_alias_spelled_outer_param(self) -> None:
        """A clause-body ref to an alias-spelled OUTER param: opaque
        resolution finds the `@Option<Cnt>` param (222) — canonical-first
        silently hit the canonically-spelled sibling (111)."""
        assert _run(self._OUTER_MIXED_PARAMS, "drive", 0) == 222

    _REFINED_CLASS_MIXED = """\
type Pos = { @Int | @Int.0 > 0 };
type P2 = Pos;

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Pos>>](@Option<Pos> = %s) {
    get(@Unit) -> { resume(@Option<Pos>.0) },
    put(@Option<P2>) -> { resume(()) } with @Option<Pos> = @Option<P2>.%d
  } in {
    put(Some(9));
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""

    _REFINED_CLASS_SINGLE = """\
type Pos = { @Int | @Int.0 > 0 };

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Pos>>](@Option<Pos> = Some(5)) {
    get(@Unit) -> { resume(@Option<Pos>.0) },
    put(@Option<Pos>) -> { resume(()) } with @Option<Pos> = @Option<Pos>.0
  } in {
    put(Some(9));
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""

    def test_refined_class_two_spellings_are_one_stack(self) -> None:
        """Two aliases of ONE refined class as pattern and annotation
        (`put(@Option<P2>)` under `(@Option<Pos> = ...)`) are one slot stack
        to the checker, and now to codegen (#1208) — both spellings render
        `Option<{@Int | ...}>`.

        Pre-#1208 they bound under two DIFFERENT codegen keys, so a mixed
        reference resolved against the wrong member silently; the clause
        translator refused the shape with spell-both-with-one-alias
        guidance.  With one renderer on both the bind and the reference
        side the workaround IS the semantics: the mixed spelling and the
        single-alias spelling the guidance asked for now agree, which is
        the property the skip could only approximate by refusing."""
        mixed = _run(self._REFINED_CLASS_MIXED % ("Some(5)", 0), "go", 0)
        assert mixed == _run(self._REFINED_CLASS_SINGLE, "go", 0)
        assert mixed == 5

    def test_refined_class_one_stack_orders_state_over_argument(self) -> None:
        """The merged stack is the CHECKER's, in the checker's order: the
        clause pushes the op parameter and then the handler state, so index
        0 is the state (`Some(5)`) and index 1 the put argument
        (`Some(9)`) — reached through the OTHER alias, which is what makes
        this one stack rather than two that happen to agree."""
        assert _run(self._REFINED_CLASS_MIXED % ("Some(5)", 0), "go", 0) == 5
        assert _run(self._REFINED_CLASS_MIXED % ("Some(5)", 1), "go", 0) == 9

    _DEEP_CHAIN = "type A0 = Nat;\n" + "".join(
        f"type A{i} = A{i - 1};\n" for i in range(1, 34)) + """
public fn go(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(<State<A33>>)
{
  put(@Nat.0);
  nat_to_int(get(()))
}
"""

    def test_deep_alias_chain_joins_the_base_family(self) -> None:
        """A 33-deep (legal, acyclic) alias chain as a State cell resolves.

        The depth bound this chain used to trip belonged to the
        TypeExpr-level walk the family named itself through before #1209.
        ``vera.naming``'s resolution is bounded by DECLARATION ORDER
        instead — each alias body resolves against a strictly shorter
        prefix of the table, so the recursion is well-founded with no
        arbitrary limit, exactly as the checker's own registration is.  A
        chain the checker resolves therefore joins the ``Nat`` family the
        checker typed, instead of being refused with a loud per-function
        skip.

        That refusal was never the goal: it was the least-bad answer while
        the family could fall back OPAQUELY, where an overflow at one site
        and a resolution at a sibling site split one cell in two silently
        (round-5 F4).  Resolving it removes the hazard at the root, so the
        assertion is the family name AND the round-trip value, not the
        absence of a diagnostic.
        """
        with _resolved_pipeline(self._DEEP_CHAIN) as (
                program, arts, resolved, path):
            result = codegen_compile(
                program, source=self._DEEP_CHAIN, file=path,
                resolved_modules=resolved,
                expr_semantic_types=arts.expr_semantic_types,
            )
            hard = [(d.error_code, d.description) for d in result.diagnostics
                    if d.severity == "error"]
            assert not hard, hard
            assert '(import "vera" "state_get_Nat"' in result.wat, (
                "the chain must join the base family, not mint its own: "
                f"{result.wat[:400]}"
            )
            # JOINED, not merely present alongside: a renderer that minted the
            # chain's own family would satisfy the positive above while still
            # splitting the cell in two (PR #1224 review).
            assert "state_get_A33" not in result.wat, (
                "the chain minted its own family beside the base one: "
                f"{result.wat[:400]}"
            )
        assert _run(self._DEEP_CHAIN, "go", 7) == 7

    _QUAL_USER_SHADOW = """\
private fn put(@Int -> @Unit) requires(true) ensures(true) effects(pure)
{
  ()
}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  State.put(5);
  get(())
}
"""

    def test_qualified_put_reaches_the_cell_past_a_user_shadow(self) -> None:
        """A user fn named `put` alongside a QUALIFIED `State.put(5)`.

        The checker's semantics have always been the builtin op — the
        qualifier names the effect, so no declaration can shadow it — and
        this now lowers that way.  It could not before #1284: the effect-op
        registry was withheld whenever a user function owned the name, which
        answered "whose name is this?" and "which cell does the op reach?"
        with one table, so the qualified spelling lost its cell too and the
        module failed to link (`unknown func: $vera.put`).  The registry is
        now complete and ownership is asked at the bare dispatch, so the two
        spellings differ only where the language says they do.

        The bare `get(())` beside it is NOT shadowed and reads the same
        cell, so the value is the one `State.put` stored.
        """
        with _resolved_pipeline(self._QUAL_USER_SHADOW) as (
                program, arts, resolved, path):
            result = codegen_compile(
                program, source=self._QUAL_USER_SHADOW, file=path,
                resolved_modules=resolved,
                expr_semantic_types=arts.expr_semantic_types,
            )
            assert result.ok, [d.description for d in result.diagnostics]
            assert wat_calls(result.wat, "vera.state_put_Int")
            # The user's own `put` is still emitted and still callable — it
            # is simply not what the qualified site denotes.  Exact
            # membership, not a substring: `"(func $put " in wat` depends on
            # a space following the symbol and would also accept a longer
            # mangled name under a different emitter layout.
            emitted = wat_fn_names(result.wat)
            assert "put" in emitted, emitted
        assert _run(self._QUAL_USER_SHADOW, "go", 7) == 5


class TestClauseClassCollisionBothDirections:
    """Round-7: the collision gate's two directions and the renderer
    ordering bug that dodged it.  Direction 1 (one checker class, two
    bind keys) includes PARAMETERISED refined aliases — the strict
    renderer must substitute params before eliding predicates or
    `Ref<Int>` renders `{@T | ...}` against the checker's
    `{@Int | ...}` and the gate never fires.  Direction 2 (two checker
    classes, one bind key): a refinement LITERAL erases to its base in
    codegen keys, merging what the checker splits."""

    def _compile_msgs(self, src: str) -> list[str]:
        with _resolved_pipeline(src) as (program, arts, resolved, path):
            result = codegen_compile(
                program, source=src, file=path, resolved_modules=resolved,
                expr_semantic_types=arts.expr_semantic_types,
            )
            return [d.description for d in result.diagnostics]

    def test_parameterised_refined_alias_is_one_stack_with_the_literal(
        self,
    ) -> None:
        """A parameterised refined alias applied (`Ref<Int>`) and the
        refinement literal it substitutes to are ONE class — the round-7 F1
        ordering (substitute the alias parameters BEFORE the refinement
        branch) is what makes both render `Option<{@Int | ...}>`.  Pre-#1208
        this was the loud collision skip; now the mixed spelling agrees with
        the single-alias spelling the skip's guidance asked for."""
        mixed = _run("""\
type Ref<T> = { @T | true };

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Ref<Int>>>](@Option<Ref<Int>> = Some(5)) {
    get(@Unit) -> { resume(@Option<Ref<Int>>.0) },
    put(@Option<{ @Int | true }>) -> { resume(()) } with @Option<Ref<Int>> = @Option<{ @Int | true }>.0
  } in {
    put(Some(9));
    option_unwrap_or(get(()), 0 - 1)
  }
}
""", "go", 0)
        single = _run("""\
type Ref<T> = { @T | true };

public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Ref<Int>>>](@Option<Ref<Int>> = Some(5)) {
    get(@Unit) -> { resume(@Option<Ref<Int>>.0) },
    put(@Option<Ref<Int>>) -> { resume(()) } with @Option<Ref<Int>> = @Option<Ref<Int>>.0
  } in {
    put(Some(9));
    option_unwrap_or(get(()), 0 - 1)
  }
}
""", "go", 0)
        assert mixed == single
        assert mixed == 5

    def test_reverse_skew_binds_two_classes_as_the_checker_does(self) -> None:
        """The DUAL direction: a refined-literal annotation and a plain
        `Option<Int>` pattern are two DISTINCT classes to the checker, and
        now to codegen — the annotation renders `Option<{@Int | ...}>`, the
        pattern `Option<Int>`.

        Pre-#1208 codegen erased the refinement literal to its base and bound
        both under one key, so the `with` expression's `@Option<Int>.0`
        landed on the merged stack's other member (the handler state,
        `Some(5)`) where the checker means the put ARGUMENT — a silent wrong
        value, which is why the shape was refused.  The argument is
        `Some(9)`, distinct from the state, so the returned value names
        which binding was reached: 9 is the checker's."""
        assert _run("""\
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{
  handle[State<Option<{ @Int | @Int.0 > 0 }>>](@Option<{ @Int | @Int.0 > 0 }> = Some(5)) {
    get(@Unit) -> { resume(@Option<{ @Int | @Int.0 > 0 }>.0) },
    put(@Option<Int>) -> { resume(()) } with @Option<{ @Int | @Int.0 > 0 }> = @Option<Int>.0
  } in {
    put(Some(9));
    option_unwrap_or(get(()), 0 - 1)
  }
}
""", "go", 0) == 9

    def test_old_state_cross_spelling_reads_the_same_snapshot(self) -> None:
        """`old(State<A33>)` against an `effects(<State<Nat>>)` function.

        The `old` reference and the effect name ONE cell — `A33` is a
        33-hop alias chain ending at `Nat` — so the snapshot the
        postcondition reads must be the snapshot the `Nat` family
        registered.  Both sides resolve through `naming.family_name`, so
        they agree by construction (#1209); before, this was the ONE
        family-resolution door outside every CodegenSkip net and the
        chain's depth error escaped as a raw crash on a check-green
        program, later degraded to an E602 skip (round-7 F2).

        Asserted as a CLEAN compile with the `Nat` snapshot read emitted:
        a spelling that resolved to its own key would either skip the
        function or emit a `state_get_A33` the module never imports.
        """
        chain = "type A0 = Nat;\n" + "".join(
            f"type A{i} = A{i - 1};\n" for i in range(1, 34))
        src = chain + """
public fn bump(@Nat -> @Int)
  requires(true)
  ensures(new(State<Nat>) >= old(State<A33>))
  effects(<State<Nat>>)
{
  put(@Nat.0);
  nat_to_int(get(()))
}
"""
        with _resolved_pipeline(src) as (program, arts, resolved, path):
            result = codegen_compile(
                program, source=src, file=path, resolved_modules=resolved,
                expr_semantic_types=arts.expr_semantic_types,
            )
        hard = [(d.error_code, d.description) for d in result.diagnostics
                if d.severity == "error"]
        assert not hard, hard
        assert "call $vera.state_get_Nat" in result.wat, result.wat[:400]
        assert "state_get_A33" not in result.wat, result.wat[:400]
