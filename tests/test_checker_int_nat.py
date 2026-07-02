"""Regression tests for #755 — mixed ``Int <op> Nat`` arithmetic must type as
``Int``, not ``Nat``.

The type checker used to join a mixed ``Int``/``Nat`` binary-arithmetic
expression to ``Nat`` (``vera/checker/expressions.py``): the join at the ADD /
SUB / MUL / DIV / MOD branch consulted the *bidirectional* ``is_subtype``, and
because the checker permits ``Int <: Nat`` as a verifier-mediated relaxation
(spec §2.8 rule 5 implementation note), ``is_subtype(Int, Nat)`` returns
``True`` — so ``Int <op> Nat`` picked the *right* operand's ``Nat`` base.

That is dishonest: only ``Nat <: Int`` is a *formal* subtyping rule (``Nat`` is
``{ @Int | @Int.0 >= 0 }``, a refinement subtype of ``Int`` — spec §2.2.1).
The least-upper-bound of ``{Int, Nat}`` under the formal lattice is ``Int``.
Typing ``@Int.0 - 2`` as ``Nat`` silently asserts non-negativity with no
verifier obligation, violating §0.2.2 ("no implicit behaviour"), and drives
spurious ``@Nat`` narrowings downstream (see the #747 tuple-destructure note on
the issue).

Written test-first: :meth:`test_int_minus_literal_types_as_int` and the sibling
join cases FAIL on the unfixed checker (they synthesise ``Nat``) and pass once
the join returns the formal LUB (``Int``).
"""
from __future__ import annotations

from vera.checker.core import typecheck_with_artifacts
from vera.parser import parse_to_ast


def _synth_type(source: str, line: int, col: int, end_col: int) -> str:
    """Pretty-printed synthesised type of the expression spanning
    ``line:col..end_col`` (1-based, matching ``ast.Span``).

    Reads the ``expr_types`` side-table the checker populates for every
    synthesised expression — the exact type the binop join produced, so a
    wrong join (``Nat``) cannot masquerade as a fallback/default.
    """
    prog = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(prog, source=source)
    key = (line, col, line, end_col)
    assert key in arts.expr_types, (
        f"no expr recorded at {key}; recorded spans: "
        f"{sorted(arts.expr_types)}"
    )
    return arts.expr_types[key]


class TestMixedIntNatJoin755:
    """The formal LUB of a mixed ``Int``/``Nat`` binop is ``Int`` (#755)."""

    def test_int_minus_literal_types_as_int(self) -> None:
        # `@Int.0 - 2` (the literal `2` is checked against the @Nat return, so
        # it types as Nat): Int <op> Nat must join to Int, not Nat.  Pre-fix:
        # synthesised Nat.
        src = """public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 - 2
}
"""
        # `@Int.0 - 2` spans line 6, cols 3..13 (1-based, end exclusive of the
        # newline per ast.Span).
        assert _synth_type(src, 6, 3, 13) == "Int"

    def test_int_plus_nat_slot_types_as_int(self) -> None:
        # `@Int.0 + @Nat.0`: a genuine mixed-slot join, no literal involved.
        src = """public fn h(@Int, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + @Nat.0
}
"""
        assert _synth_type(src, 6, 3, 18) == "Int"

    def test_nat_plus_int_slot_types_as_int(self) -> None:
        # Order-independent: `@Nat.0 + @Int.0` also joins to Int.
        src = """public fn h(@Int, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0 + @Int.0
}
"""
        assert _synth_type(src, 6, 3, 18) == "Int"

    def test_int_times_nat_slot_types_as_int(self) -> None:
        # Multiplication (a non-subtractive op) still joins mixed to Int.
        src = """public fn h(@Int, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 * @Nat.0
}
"""
        assert _synth_type(src, 6, 3, 18) == "Int"

    def test_int_div_nat_slot_types_as_int(self) -> None:
        # Division joins mixed to Int too.  The ADD/SUB/MUL/DIV/MOD branch is
        # one shared join, but nothing else pins `/`: a per-operator bypass
        # reintroducing the bidirectional is_subtype for DIV alone survived
        # the entire suite until this test existed.
        src = """public fn h(@Int, @Nat -> @Int)
  requires(@Nat.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0 / @Nat.0
}
"""
        assert _synth_type(src, 6, 3, 18) == "Int"

    def test_int_mod_nat_slot_types_as_int(self) -> None:
        # Modulo likewise: `Int % Nat` joins to Int.  The result has the sign
        # of the dividend (spec §4.4), so it can be negative — typing it Nat
        # would be the same silent non-negativity assertion as `-`.
        src = """public fn h(@Int, @Nat -> @Int)
  requires(@Nat.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0 % @Nat.0
}
"""
        assert _synth_type(src, 6, 3, 18) == "Int"

    def test_nat_plus_nat_stays_nat(self) -> None:
        # Guard against over-correction: a pure Nat/Nat join is still Nat.
        src = """public fn h(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.1 + @Nat.0
}
"""
        assert _synth_type(src, 6, 3, 18) == "Nat"

    def test_int_plus_int_stays_int(self) -> None:
        # And a pure Int/Int join is still Int.
        src = """public fn h(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.1 + @Int.0
}
"""
        assert _synth_type(src, 6, 3, 18) == "Int"
