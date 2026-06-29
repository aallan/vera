"""Verifier<->codegen behavioural differential for #813 @Nat -> @Int widening.

The soundness contract: at every @Nat -> @Int coercion site the verifier's
static classification of the ``nat_to_int_coerce`` obligation must AGREE with
what code generation actually does at run time —

  * ``tier3`` (tier3_runtime, codegen-guarded): ``vera run`` with a @Nat above
    i64.MAX MUST trap (the runtime widening guard fires) rather than silently
    return the bit-reinterpreted negative @Int.
  * ``tier3_unguarded`` (E531): codegen architecturally cannot guard the site
    (a tuple / array / generic-ADT component coercion), so ``vera run`` does
    NOT trap — the widening is *disclosed*, not guarded.  This case is honest
    about the residual rather than claiming a runtime check it never emits.

A green per-site unit suite (``test_int_widening_codegen`` asserts traps,
``test_nat_int_widening`` asserts obligation status) can still hide a desync
between the two surfaces — the verifier deferring a site to a runtime guard the
codegen never emits (an unsound silent -1), or guarding a site the verifier
proved Tier-1 (a spurious trap).  This is the required cross-component
differential (project rule): for one corpus, run BOTH sides and compare, so the
"verifier says runtime-guarded" claim is checked against the actual trap.

In every case an in-range input returns the value unchanged on both sides.
"""

from __future__ import annotations

import tempfile
from pathlib import Path

import pytest
import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.verifier import verify

U64_MAX = 18446744073709551615
_MASK64 = (1 << 64) - 1
_KIND = "nat_to_int_coerce"


def _verify_statuses(source: str) -> list[str]:
    """The status of every ``nat_to_int_coerce`` obligation the verifier emits."""
    program = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(program, source)
    result = verify(
        program, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    return [o.status for o in result.obligations if o.kind == _KIND]


def _run(source: str, fn: str, arg: int) -> int | None:
    """Compile + execute *fn* with one i64 arg; ``None`` if it traps."""
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
        result = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
        )
        try:
            exec_result = execute(result, fn_name=fn, args=[arg])
        except (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError):
            return None
        return exec_result.value
    finally:
        Path(path).unlink(missing_ok=True)


# (label, source, fn, guarded)
#   guarded=True  -> verifier tier3_runtime + codegen traps on u64.MAX
#   guarded=False -> verifier tier3_unguarded (E531) + codegen does NOT trap
_GUARDED = [
    ("return", """
public fn widen(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
""", "widen"),
    ("let", """
public fn f(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Int = @Nat.0; @Int.0 }
""", "f"),
    ("call_arg", """
public fn takes_int(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
public fn caller(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ takes_int(@Nat.0) }
""", "caller"),
    ("ctor_field", """
private data WrapInt { WrapInt(Int) }
public fn cf(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @WrapInt = WrapInt(@Nat.0); match @WrapInt.0 { WrapInt(@Int) -> @Int.0 } }
""", "cf"),
    ("adt_subpattern", """
private data Box { Box(Nat) }
public fn be(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Box = Box(@Nat.0); match @Box.0 { Box(@Int) -> @Int.0 } }
""", "be"),
    ("match_bind", """
public fn mb(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Nat.0 { @Int -> @Int.0 } }
""", "mb"),
]

_DISCLOSED = [
    ("tuple_construct", """
public fn tc(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = Tuple(@Nat.0, @Nat.0); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 } }
""", "tc"),
    ("tuple_destr", """
public fn td(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(@Nat.0, @Nat.0); @Int.0 }
""", "td"),
    ("array_elem", """
public fn ae(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [@Nat.0]; @Array<Int>.0[0] }
""", "ae"),
    ("generic_field", """
public fn gf(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Option<Int> = Some(@Nat.0); match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> 0 } }
""", "gf"),
]


class TestWideningDifferential813:
    @pytest.mark.parametrize("label,source,fn", _GUARDED,
                             ids=[c[0] for c in _GUARDED])
    def test_guarded_site_verifier_tier3_and_run_traps(
        self, label: str, source: str, fn: str,
    ) -> None:
        statuses = _verify_statuses(source)
        assert statuses, f"{label}: no coerce obligation emitted"
        # Every coerce obligation at a guarded site is runtime-deferred.
        assert all(s == "tier3" for s in statuses), f"{label}: {statuses}"
        # ...and codegen makes good on that: u64.MAX traps, in-range is exact.
        assert _run(source, fn, U64_MAX) is None, (
            f"{label}: verifier deferred to a runtime guard, but run(u64.MAX) "
            f"did NOT trap — an unsound silent reinterpretation"
        )
        assert _run(source, fn, 42) == 42, f"{label}: in-range widen not exact"

    @pytest.mark.parametrize("label,source,fn", _DISCLOSED,
                             ids=[c[0] for c in _DISCLOSED])
    def test_disclosed_site_verifier_e531_and_run_does_not_trap(
        self, label: str, source: str, fn: str,
    ) -> None:
        statuses = _verify_statuses(source)
        assert statuses, f"{label}: no coerce obligation emitted"
        # A disclosed site is honestly unguarded — never silently tier3_runtime.
        assert all(s == "tier3_unguarded" for s in statuses), (
            f"{label}: expected all tier3_unguarded (E531), got {statuses}"
        )
        # ...and codegen indeed does NOT guard it: u64.MAX returns the
        # bit-reinterpreted value (no trap), confirming the disclosure is honest
        # rather than the verifier claiming a runtime check codegen never emits.
        assert _run(source, fn, U64_MAX) is not None, (
            f"{label}: verifier disclosed UNGUARDED (E531) but run(u64.MAX) "
            f"trapped — classification disagrees with codegen"
        )
        assert _run(source, fn, 42) == 42, f"{label}: in-range widen not exact"
