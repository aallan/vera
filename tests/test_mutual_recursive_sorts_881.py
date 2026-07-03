"""Regression tests for #881 — mutually-recursive ``data`` declarations must
not crash ``vera verify`` with a raw ``RecursionError`` during Z3 sort
construction.

The self-recursive case (``Cons(Int, Self)``) was already handled by a single
``self_ref_key``/``self_ref_dt`` pair threaded through sort creation, but that
pair could only name ONE in-progress sort.  A mutually-recursive pair — ``A``
with a field of type ``B``, ``B`` with a field of type ``A`` — therefore
entered unbounded field-sort resolution before any cycle guard: building ``A``
recursed into building ``B``, which recursed into building ``A`` again, and so
on until Python's recursion limit tripped.  ``vera check`` and ``vera run``
handled the same program fine, so this was a "check-green program → raw
pipeline traceback" soundness-of-tooling defect (DESIGN.md: loud over silent,
never a raw interpreter trace on a check-green program).

The fix (PR for #881) declares every datatype reachable through constructor
fields together via ``z3.CreateDatatypes`` — a mutually-recursive group is
resolved in one pass, with self-recursion the singleton-group case.  Tier-1
static reasoning is preserved (the sound, complete option).  The #871
Float64-cycle guard still fires for a *recursive* FP-containing datatype: the
sort now BUILDS, so equality decomposition reaches the no-finite-expansion
check and demotes to an honest Tier-3 runtime check rather than a false Tier-1
proof.

Written test-first: every test below raises ``RecursionError`` on the pre-fix
verifier (sort construction) and passes only once the group is built together.
"""

from __future__ import annotations

import pytest

from vera.checker import typecheck_with_artifacts
from vera.parser import parse_to_ast
from vera.verifier import VerifyResult, verify


def _verify(source: str) -> VerifyResult:
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast, source)
    return verify(
        ast, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


def _ensures(result: VerifyResult) -> list:
    return [o for o in result.obligations if o.kind == "ensures"]


class TestMutualRecursiveSorts881:
    def test_issue_repro_verifies_without_recursionerror(self) -> None:
        # RED: the issue's exact repro.  Pre-fix, `verify()` raises a raw
        # RecursionError inside `_get_or_create_adt_sort` while creating the
        # A/B sorts — before any obligation is discharged.  Post-fix the two
        # trivial obligations discharge Tier-1.
        result = _verify("""
private data A { MkA, WrapB(B) }

private data B { MkB, WrapA(A) }

public fn f(@A -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{
  true
}
""")
        assert result.summary.tier1_verified >= 1
        # No violated obligation: the contract is trivially true.
        assert all(o.status != "violated" for o in result.obligations)

    def test_three_cycle_a_b_c_a(self) -> None:
        # RED: a 3-cycle A -> B -> C -> A also blows the stack pre-fix.  The
        # whole strongly-connected group must be declared together.
        result = _verify("""
private data A { MkA, WrapB(B) }

private data B { MkB, WrapC(C) }

private data C { MkC, WrapA(A) }

public fn f(@A -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{
  true
}
""")
        assert result.summary.tier1_verified >= 1
        assert all(o.status != "violated" for o in result.obligations)

    def test_mutual_pair_only_one_base_case(self) -> None:
        # RED: Q has no nullary constructor (its only ctor references P).  The
        # group still has to be built together; a missing base case is fine at
        # the sort level (Z3 permits it) — the point is no RecursionError.
        result = _verify("""
private data P { MkP, WrapQ(Q) }

private data Q { WrapP(P) }

public fn f(@P -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{
  true
}
""")
        assert result.summary.tier1_verified >= 1
        assert all(o.status != "violated" for o in result.obligations)

    def test_mutual_pair_with_float64_field_builds(self) -> None:
        # RED: a mutual pair carrying a Float64 field crashed identically
        # pre-fix (the crash is in sort CONSTRUCTION, FP-independent).  The
        # trivial contract still discharges without a RecursionError.
        result = _verify("""
private data FA { MkFA(Float64), WrapFB(FB) }

private data FB { MkFB, WrapFA(FA) }

public fn f(@FA -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{
  true
}
""")
        assert result.summary.tier1_verified >= 1
        assert all(o.status != "violated" for o in result.obligations)

    def test_non_fp_mutual_equality_proves_tier1(self) -> None:
        # Pins the fix's model choice: structural datatype `=` matches the
        # runtime for a NON-FP mutually-recursive datatype, so reflexivity
        # `@A.0 == @A.0` proves Tier-1 (not demoted).  Pre-fix this raised
        # RecursionError before the equality was ever translated.
        result = _verify("""
private data A { MkA, WrapB(B) }

private data B { MkB, WrapA(A) }

public fn refl(@A -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{
  @A.0 == @A.0
}
""")
        ens = _ensures(result)
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_fp_mutual_equality_demotes_to_tier3(self) -> None:
        # The #871 interaction, now reachable because the sort BUILDS: a
        # RECURSIVE FP-containing datatype has no finite equality expansion, so
        # `@FA.0 == @FA.0` must demote to a loud Tier-3 runtime check — NOT a
        # false Tier-1 proof (structural `=` would wrongly prove NaN == NaN).
        result = _verify("""
private data FA { MkFA(Float64), WrapFB(FB) }

private data FB { MkFB, WrapFA(FA) }

public fn refl(@FA -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{
  @FA.0 == @FA.0
}
""")
        ens = _ensures(result)
        assert ens, [(o.kind, o.status) for o in result.obligations]
        # The FP-over-recursive-mutual ensures is a runtime check, never a
        # static (verified) proof.
        assert all(o.status == "tier3" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert result.summary.tier3_runtime >= 1

    def test_self_recursive_still_verifies(self) -> None:
        # Guard against regressing the singleton-group (self-recursive) path:
        # a plain recursive list must still build and discharge Tier-1.
        result = _verify("""
private data IntList { Nil, Cons(Int, IntList) }

public fn f(@IntList -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{
  true
}
""")
        assert result.summary.tier1_verified >= 1
        assert all(o.status != "violated" for o in result.obligations)


@pytest.mark.parametrize(
    "source",
    [
        # issue repro
        """
private data A { MkA, WrapB(B) }
private data B { MkB, WrapA(A) }
public fn f(@A -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{ true }
""",
        # 3-cycle
        """
private data A { MkA, WrapB(B) }
private data B { MkB, WrapC(C) }
private data C { MkC, WrapA(A) }
public fn f(@A -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{ true }
""",
    ],
)
def test_verify_does_not_raise(source: str) -> None:
    # Mutation kill: reverting the group construction re-raises RecursionError
    # here (the discriminating signal is "verify() completes" vs "verify()
    # raises RecursionError").
    _verify(source)  # must not raise
