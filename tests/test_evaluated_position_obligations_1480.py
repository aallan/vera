"""Every runtime check the compiled program performs has an obligation (#1480).

The verifier's obligation walks descended a hand-listed set of roots: the
body, and since #801 each ``requires`` and ``ensures`` (primitive operations
only).  Code generation evaluates more than that, and every check it emits
where no walk reached let ``vera verify`` pass a program that traps:

* a ``decreases`` measure, evaluated at entry and again on a self-recursive
  tail call's captured arguments (#1172);
* a refinement predicate, evaluated by every §2.6.5 guard (#762);
* a trapping built-in's argument check (``string_char_code``'s index);
* a call precondition and an ``@Int``-to-``@Nat`` narrowing inside a
  ``requires`` or ``ensures`` predicate.

This file holds the issue's own programs as named cells.  Each asserts the
RECORD (kind, status, error code and location of every obligation the
position carries) and the RUN on an admitted input, because the claim under
test is that the two agree.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile, execute
from vera.obligations.core import ProofObligation
from vera.parser import parse_to_ast
from vera.runtime.traps import WasmTrapError
from vera.verifier import verify


# =====================================================================
# Helpers
# =====================================================================


@dataclass(frozen=True)
class Verified:
    """One program's verification outcome."""

    obligations: list[ProofObligation]
    errors: list[tuple[str, int, int]]  # (code, line, column)
    ok: bool


def _verify(source: str) -> Verified:
    """Parse, type-check (must be clean) and verify *source* in-process."""
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source)
    check_errors = [d for d in diags if d.severity == "error"]
    assert not check_errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:80]) for d in check_errors]}"
    )
    result = verify(
        program, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    errors = [
        (d.error_code, d.location.line, d.location.column)
        for d in result.diagnostics if d.severity == "error"
    ]
    return Verified(result.obligations, errors, not errors)


@dataclass(frozen=True)
class Ran:
    """One run's outcome: a value, or a trap with its kind and message."""

    value: object | None
    trap_kind: str | None = None
    trap_message: str = ""


def _run(source: str, fn: str, args: list[int | float]) -> Ran:
    """Compile *source* and call *fn* with *args*, catching a trap.

    Through the pipeline `vera run` uses: the checker's type tables are
    threaded into code generation, which decides from them where a
    `@Nat` subtraction or an overflow is guarded.  Without them a guard
    can be missing that the real artifact carries, and a cell would read
    the absence as the record's error.
    """
    program = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(program, source)
    compiled = compile(
        program, source=source,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    errors = [d for d in compiled.diagnostics if d.severity == "error"]
    assert not errors, (
        f"fixture must compile, got: "
        f"{[(d.error_code, d.description[:80]) for d in errors]}"
    )
    try:
        out = execute(compiled, fn_name=fn, args=args)
    except WasmTrapError as trap:
        return Ran(None, trap.kind, str(trap))
    return Ran(out.value)


def _at(source: str, needle: str, occurrence: int = 0) -> tuple[int, int]:
    """1-based (line, column) of the *occurrence*-th *needle* in *source*."""
    start = -1
    for _ in range(occurrence + 1):
        start = source.index(needle, start + 1)
    line = source.count("\n", 0, start) + 1
    column = start - (source.rfind("\n", 0, start) + 1) + 1
    return line, column


def _records(v: Verified, kind: str, where: tuple[int, int]) -> list[str]:
    """``status[/code]`` of every *kind* obligation located at *where*."""
    return sorted(
        f"{o.status}/{o.error_code}" if o.error_code else o.status
        for o in v.obligations
        if o.kind == kind and (o.line, o.column) == where
    )


# =====================================================================
# The issue's three items, as measured on release/v0.2.0 at 82f00584
# =====================================================================


# Item 1: the idiom VeraBench found in every model target.  The last call has
# `@Nat.0 = n + 1`, so the measure's `@Nat.1 - @Nat.0` is `n - (n + 1)`.
COUNT_TO = """\
public fn count_to(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  loop(@Nat.0, 1)
}
where {
  fn loop(@Nat, @Nat -> @Nat)
    requires(true)
    ensures(true)
    decreases(@Nat.1 - @Nat.0 + 1)
    effects(pure)
  {
    if @Nat.0 > @Nat.1 then { @Nat.0 } else { loop(@Nat.1, @Nat.0 + 1) }
  }
}
"""

# The same loop with the invariant stated and the subtraction reordered: the
# form the Fix text names, which must verify and run.
COUNT_TO_FIXED = """\
public fn count_to(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  loop(@Nat.0, 1)
}
where {
  fn loop(@Nat, @Nat -> @Nat)
    requires(@Nat.0 <= @Nat.1 + 1)
    ensures(true)
    decreases(@Nat.1 + 1 - @Nat.0)
    effects(pure)
  {
    if @Nat.0 > @Nat.1 then { @Nat.0 } else { loop(@Nat.1, @Nat.0 + 1) }
  }
}
"""


class TestMeasureIsObligated:
    """Item 1: the measure's operations are obligated where it is evaluated."""

    def test_subtraction_obligated_at_entry_and_at_the_tail_call(self) -> None:
        v = _verify(COUNT_TO)
        measure = _at(COUNT_TO, "@Nat.1 - @Nat.0 + 1")
        tail_call = _at(COUNT_TO, "loop(@Nat.1, @Nat.0 + 1)")
        assert _records(v, "nat_sub", measure) == ["violated/E502"]
        assert _records(v, "nat_sub", tail_call) == ["violated/E502"]
        # The measure's own `+ 1` is a checked add in the WAT at both points.
        assert _records(v, "int_overflow", measure) == ["tier3"]
        assert _records(v, "int_overflow", tail_call) == ["tier3"]
        assert ("E502", *measure) in v.errors
        assert ("E502", *tail_call) in v.errors
        assert not v.ok

    def test_the_run_traps_where_the_record_says(self) -> None:
        ran = _run(COUNT_TO, "count_to", [3])
        assert ran.trap_kind is not None, f"expected a trap, got {ran.value}"
        assert ran.trap_kind != "contract_violation", ran.trap_message

    def test_the_stated_invariant_verifies_and_runs(self) -> None:
        v = _verify(COUNT_TO_FIXED)
        measure = _at(COUNT_TO_FIXED, "@Nat.1 + 1 - @Nat.0")
        tail_call = _at(COUNT_TO_FIXED, "loop(@Nat.1, @Nat.0 + 1)")
        assert _records(v, "nat_sub", measure) == ["verified"]
        assert _records(v, "nat_sub", tail_call) == ["verified"]
        assert v.ok, v.errors
        assert _run(COUNT_TO_FIXED, "count_to", [3]).value == 4
        assert _run(COUNT_TO_FIXED, "count_to", [0]).value == 1


DEC_DIV = """\
public fn loop(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.1 / @Nat.0)
  effects(pure)
{
  if @Nat.1 == 0 then { 0 } else { loop(@Nat.1 - 1, @Nat.0) }
}
"""

DEC_CALL_PRE = """\
public fn pred(@Nat -> @Nat)
  requires(@Nat.0 > 0)
  ensures(true)
  effects(pure)
{
  @Nat.0 - 1
}

public fn loop(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(pred(@Nat.0))
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { loop(@Nat.0 - 1) }
}
"""


class TestMeasureOperations:
    """The issue's table: division and a call precondition in a measure."""

    def test_division_by_zero_obligated(self) -> None:
        v = _verify(DEC_DIV)
        measure = _at(DEC_DIV, "@Nat.1 / @Nat.0")
        tail_call = _at(DEC_DIV, "loop(@Nat.1 - 1, @Nat.0)")
        assert _records(v, "div_zero", measure) == ["violated/E526"]
        assert _records(v, "div_zero", tail_call) == ["violated/E526"]
        assert not v.ok
        assert _run(DEC_DIV, "loop", [3, 0]).trap_kind == "divide_by_zero"

    def test_call_precondition_obligated(self) -> None:
        v = _verify(DEC_CALL_PRE)
        in_measure = _at(DEC_CALL_PRE, "pred(@Nat.0))")
        tail_call = _at(DEC_CALL_PRE, "loop(@Nat.0 - 1)")
        assert _records(v, "call_pre", in_measure) == ["violated/E501"]
        assert _records(v, "call_pre", tail_call) == ["violated/E501"]
        assert not v.ok
        ran = _run(DEC_CALL_PRE, "loop", [3])
        assert ran.trap_kind == "contract_violation"
        assert "Precondition violation in pred" in ran.trap_message


# Item 2: a guard evaluates the left disjunct first, and `3 - 5` underflows on
# a value that satisfies the type.
ODD3 = """\
type Odd3 = { @Nat | @Nat.0 - 5 > 0 || @Nat.0 == 3 };

public fn mk(@Nat -> @Odd3)
  requires(@Nat.0 == 3)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn take(@Odd3 -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Odd3.0
}
"""

# The same membership written so the subtraction is evaluated only where it
# is defined: the `if` is lazy in the compiled guard.
ODD3_GUARDED = """\
type Odd3 = { @Nat | if @Nat.0 >= 5 then { @Nat.0 - 5 > 0 } else { @Nat.0 == 3 } };

public fn mk(@Nat -> @Odd3)
  requires(@Nat.0 == 3)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn take(@Odd3 -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Odd3.0
}
"""

# `||` is NOT a guard in the compiled predicate: both operands are evaluated
# (`i32.or`), so a left operand that decides the result does not stop the
# right one from trapping.
ODD3_OR_FIRST = """\
type Odd3 = { @Nat | @Nat.0 == 3 || @Nat.0 - 5 > 0 };

public fn take(@Odd3 -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Odd3.0
}
"""


class TestRefinementPredicateIsObligated:
    """Item 2: a predicate is discharged once, at its declaration."""

    def test_ill_formed_predicate_is_one_error_at_the_declaration(self) -> None:
        v = _verify(ODD3)
        sub = _at(ODD3, "@Nat.0 - 5")
        assert _records(v, "nat_sub", sub) == ["violated/E502"]
        # Once: neither guard position repeats it.
        assert [o for o in v.obligations if o.kind == "nat_sub"] == [
            o for o in v.obligations
            if o.kind == "nat_sub" and (o.line, o.column) == sub
        ]
        assert v.errors.count(("E502", *sub)) == 1
        assert not v.ok

    def test_both_guards_trap_on_a_value_the_type_admits(self) -> None:
        assert _run(ODD3, "mk", [3]).trap_kind is not None
        assert _run(ODD3, "take", [3]).trap_kind is not None
        assert _run(ODD3, "take", [9]).value == 9

    def test_an_if_in_the_predicate_discharges_it(self) -> None:
        v = _verify(ODD3_GUARDED)
        assert _records(v, "nat_sub", _at(ODD3_GUARDED, "@Nat.0 - 5")) == [
            "verified"]
        assert v.ok, v.errors
        assert _run(ODD3_GUARDED, "mk", [3]).value == 3
        assert _run(ODD3_GUARDED, "take", [3]).value == 3
        assert _run(ODD3_GUARDED, "take", [9]).value == 9

    def test_an_or_is_not_a_guard(self) -> None:
        v = _verify(ODD3_OR_FIRST)
        assert _records(v, "nat_sub", _at(ODD3_OR_FIRST, "@Nat.0 - 5")) == [
            "violated/E502"]
        assert _run(ODD3_OR_FIRST, "take", [3]).trap_kind is not None


# A call in a predicate, with two uses of the type: its precondition is the
# declaration's one obligation, not one per function that reads the type.
PRED_CALL_TWO_USES = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

type T = { @Int | need_pos(@Int.0) > 0 };

public fn take(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn also(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
"""


def test_a_call_in_a_predicate_is_one_obligation_not_one_per_use() -> None:
    v = _verify(PRED_CALL_TWO_USES)
    call = _at(PRED_CALL_TWO_USES, "need_pos(@Int.0) > 0")
    assert _records(v, "call_pre", call) == ["violated/E501"]
    assert v.errors.count(("E501", *call)) == 1
    assert _run(PRED_CALL_TWO_USES, "take", [-3]).trap_kind is not None


# Item 3: the index check code generation emits, with nothing behind it.
CHAR_CODE = """\
public fn c3(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_char_code("abc", @Int.0)
}
"""

CHAR_CODE_BOUNDED = """\
public fn c3(@Int -> @Nat)
  requires(@Int.0 >= 0 && @Int.0 < 3)
  ensures(true)
  effects(pure)
{
  string_char_code("abc", @Int.0)
}
"""


class TestBuiltinDomainIsObligated:
    """Item 3: a trapping built-in declares its domain as a precondition."""

    def test_unbounded_index_is_e501(self) -> None:
        v = _verify(CHAR_CODE)
        call = _at(CHAR_CODE, 'string_char_code("abc", @Int.0)')
        assert _records(v, "call_pre", call) == ["violated/E501"]
        assert ("E501", *call) in v.errors
        assert _run(CHAR_CODE, "c3", [7]).trap_kind is not None
        assert _run(CHAR_CODE, "c3", [-1]).trap_kind is not None

    def test_bounded_index_is_proved_and_recorded(self) -> None:
        v = _verify(CHAR_CODE_BOUNDED)
        call = _at(CHAR_CODE_BOUNDED, 'string_char_code("abc", @Int.0)')
        assert _records(v, "call_pre", call) == ["verified"]
        assert v.ok, v.errors
        assert _run(CHAR_CODE_BOUNDED, "c3", [1]).value == 98


# The substitution behind a built-in's domain (and behind E501's "At this
# call site" text) rebuilds a precondition with the call's arguments in place
# of the parameters.  Where it cannot do that exactly it refuses: a parameter
# slot left in place would be resolved against the CALLER's scope, so a
# half-substituted tree is a goal about the wrong values.

_SUBSTITUTION_SIGNATURE = """\
private fn f(@Int, @String -> @Unit)
  requires({pre})
  ensures(true)
  effects(pure)
{{
  ()
}}
"""


def _substituted(pre: str) -> object:
    from vera import ast as A
    from vera.naming import EMPTY_ALIAS_ENV
    from vera.slots import substitute_parameters

    source = _SUBSTITUTION_SIGNATURE.format(pre=pre)
    fn = parse_to_ast(source).declarations[0].decl
    assert isinstance(fn, A.FnDecl)
    requires = next(c for c in fn.contracts if isinstance(c, A.Requires))
    args = (A.IntLit(value=5, span=None), A.StringLit(value="x", span=None))
    return substitute_parameters(
        requires.expr, fn.params, args, EMPTY_ALIAS_ENV, None)


def _slot_refs(node: object) -> list[object]:
    """Every slot reference reachable from *node*, through any field."""
    import dataclasses

    from vera import ast as A

    found: list[object] = []

    def walk(value: object) -> None:
        if isinstance(value, A.SlotRef):
            found.append(value)
        if isinstance(value, tuple):
            for item in value:
                walk(item)
        elif dataclasses.is_dataclass(value) and not isinstance(value, type):
            for f in dataclasses.fields(value):
                walk(getattr(value, f.name))

    walk(node)
    return found


class TestParameterSubstitution:
    """A precondition rebuilt in call-site terms is exact, or refused."""

    def test_a_parameter_inside_an_interpolation_is_substituted(self) -> None:
        from vera import ast as A

        rebuilt = _substituted('string_length("n=\\(@Int.0)") > 0')
        assert isinstance(rebuilt, A.Expr)
        assert _slot_refs(rebuilt) == []
        assert A.format_expr(rebuilt) == 'string_length("n=\\(5)") > 0'

    @pytest.mark.parametrize("pre", [
        # The branch's `@Int.0` is the `let`, not the parameter.
        "if true then { let @Int = 1; @Int.0 > 0 } else { false }",
        # The arm binds an `@Int`; its `@String.0` is still the parameter.
        "match @Int.0 { @Int -> string_length(@String.0) > @Int.0 }",
        # The quantifier's function binds its own `@Int`.
        "forall(@Int, 3, fn(@Int -> @Bool) effects(pure) {"
        " @Int.0 < string_length(@String.0) })",
    ])
    def test_a_binder_is_refused_not_half_substituted(self, pre: str) -> None:
        assert _substituted(pre) is None


# =====================================================================
# Contract predicates: the walks #801 did not extend
# =====================================================================


ENSURES_CALL_PRE = """\
public fn pred(@Nat -> @Nat)
  requires(@Nat.0 > 0)
  ensures(true)
  effects(pure)
{
  @Nat.0 - 1
}

public fn f(@Nat -> @Nat)
  requires(true)
  ensures(pred(@Nat.result) >= 0)
  effects(pure)
{
  @Nat.0
}
"""

REQUIRES_NARROWING = """\
public fn g(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn f(@Int -> @Int)
  requires(g(@Int.0) >= 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""

ENSURES_NARROWING = """\
public fn g(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(g(@Int.result) >= 0)
  effects(pure)
{
  @Int.0
}
"""


class TestContractPredicates:
    """A call precondition and an `@Int`->`@Nat` narrowing in a contract."""

    def test_call_precondition_in_ensures(self) -> None:
        v = _verify(ENSURES_CALL_PRE)
        call = _at(ENSURES_CALL_PRE, "pred(@Nat.result)")
        assert _records(v, "call_pre", call) == ["violated/E501"]
        assert not v.ok
        ran = _run(ENSURES_CALL_PRE, "f", [0])
        assert "Precondition violation in pred" in ran.trap_message

    def test_narrowing_in_requires(self) -> None:
        v = _verify(REQUIRES_NARROWING)
        arg = _at(REQUIRES_NARROWING, "@Int.0) >= 0")
        assert _records(v, "nat_bind", arg) == ["violated/E503"]
        assert not v.ok
        assert _run(REQUIRES_NARROWING, "f", [-3]).trap_kind is not None

    def test_narrowing_in_ensures(self) -> None:
        v = _verify(ENSURES_NARROWING)
        arg = _at(ENSURES_NARROWING, "@Int.result) >= 0")
        assert _records(v, "nat_bind", arg) == ["violated/E503"]
        assert not v.ok
        assert _run(ENSURES_NARROWING, "f", [-3]).trap_kind is not None


# Two call-site preconditions at one tail call, spelled alike: the recursive
# call's own, and the precondition of the call its measure makes there.  They
# are two obligations, so they are two records — matched by text rather than
# by the precondition itself, the second was taken for the first.
SAME_TEXT_AT_A_TAIL_CALL = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn f(@Int, @Nat -> @Nat)
  requires(@Int.0 > 0)
  ensures(true)
  decreases(@Nat.0, need_pos(@Int.0))
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { f(-3, @Nat.0 - 1) }
}
"""


def test_two_preconditions_spelled_alike_at_one_call_are_two() -> None:
    v = _verify(SAME_TEXT_AT_A_TAIL_CALL)
    call = _at(SAME_TEXT_AT_A_TAIL_CALL, "f(-3, @Nat.0 - 1)")
    assert _records(v, "call_pre", call) == ["violated/E501", "violated/E501"]
    ran = _run(SAME_TEXT_AT_A_TAIL_CALL, "f", [1, 1])
    # The measure is evaluated on the arguments first, so it is
    # `need_pos`'s precondition that stops the hop, not `f`'s.
    assert "Precondition violation in need_pos" in ran.trap_message


# =====================================================================
# The recursive-call walk: the env a call's arguments are read in
# =====================================================================
#
# The measure at a tail call is evaluated on the call's arguments, read in
# the env the recursive-call walk builds as it crosses the body — the same
# walk the termination proof reads.  Two things can go wrong there, and each
# is a verdict about a value the compiled program never computes.

# A call in a tail call's argument, guarded by an enclosing `if`.  The walk
# re-translates the body to find the call, without the `if` among the
# solver's path conditions; what that translation found is the body's, which
# the body walk has already recorded under the right facts.
GUARDED_CALL_IN_TAIL_ARGUMENT = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}

public fn walk(@Int, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    if @Int.0 > 0 then {
      walk(need_pos(@Int.0), @Nat.0 - 1)
    } else {
      0
    }
  }
}
"""

# The same call, bound by a `let` before the tail call.
GUARDED_CALL_IN_TAIL_LET = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}

public fn walk(@Int, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    if @Int.0 > 0 then {
      let @Int = need_pos(@Int.0);
      walk(@Int.0, @Nat.0 - 1)
    } else {
      0
    }
  }
}
"""


@pytest.mark.parametrize("source", [GUARDED_CALL_IN_TAIL_ARGUMENT,
                                    GUARDED_CALL_IN_TAIL_LET])
def test_a_guarded_call_before_a_tail_call_is_not_charged_to_it(
        source: str) -> None:
    v = _verify(source)
    tail = _at(source, "walk(", 1)
    assert _records(v, "call_pre", tail) == []
    assert v.ok, v.errors
    assert _run(source, "walk", [3, 4]).value == 0


# The same calls unguarded: a violation the body walk records at the call
# itself, once.  The walk that finds the tail call translates the argument
# again, and the `let` before it, and what it found there was reported a
# second time, at the tail call.
UNGUARDED_CALL_IN_TAIL_ARGUMENT = GUARDED_CALL_IN_TAIL_ARGUMENT.replace(
    """    if @Int.0 > 0 then {
      walk(need_pos(@Int.0), @Nat.0 - 1)
    } else {
      0
    }""", "    walk(need_pos(@Int.0), @Nat.0 - 1)")
UNGUARDED_CALL_IN_TAIL_LET = GUARDED_CALL_IN_TAIL_LET.replace(
    """    if @Int.0 > 0 then {
      let @Int = need_pos(@Int.0);
      walk(@Int.0, @Nat.0 - 1)
    } else {
      0
    }""", """    let @Int = need_pos(@Int.0);
    walk(@Int.0, @Nat.0 - 1)""")


@pytest.mark.parametrize("source", [UNGUARDED_CALL_IN_TAIL_ARGUMENT,
                                    UNGUARDED_CALL_IN_TAIL_LET])
def test_a_violated_call_before_a_tail_call_is_one_record_at_the_call(
        source: str) -> None:
    assert source.count("if @Int.0 > 0") == 0
    v = _verify(source)
    call = _at(source, "need_pos(@Int.0)")
    assert _records(v, "call_pre", call) == ["violated/E501"]
    assert _records(v, "call_pre", _at(source, "walk(", 1)) == []
    assert [e for e in v.errors if e[0] == "E501"] == [("E501", *call)]
    assert "need_pos" in _run(source, "walk", [-1, 2]).trap_message


# A tail call whose argument a `let` binds to a value the SMT layer cannot
# read (an effect operation's result).  Read against the enclosing env, the
# argument was the PARAMETER, whose path proves the measure's subtraction —
# a Tier-1 claim about a value the program never passes.  The compiled
# measure is evaluated on the value `get` returns, and traps on 0.
OPAQUE_TAIL_ARGUMENT = """\
public fn f(@Nat -> @Nat)
  requires(@Nat.0 >= 1)
  ensures(true)
  decreases(@Nat.0 - 1)
  effects(<State<Nat>>)
{
  if @Nat.0 <= 1 then {
    0
  } else {
    let @Nat = get(());
    f(@Nat.0)
  }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    f(5)
  }
}
"""


def test_an_opaque_tail_argument_leaves_the_measure_to_its_guard() -> None:
    v = _verify(OPAQUE_TAIL_ARGUMENT)
    tail = _at(OPAQUE_TAIL_ARGUMENT, "f(@Nat.0)")
    assert _records(v, "nat_sub", tail) == ["tier3"]
    # `0` also fails `f`'s precondition, which the compiled call checks
    # only after the measure, so the trap must be the measure's own.
    ran = _run(OPAQUE_TAIL_ARGUMENT, "main", [])
    assert _not_the_callers_precondition(ran), ran


# A `Map` field gives an ADT no SMT sort, so its value is declared an `Int`
# and a constructor pattern has nothing to project: the scrutinee translates
# and the pattern does not bind.  Read against the enclosing env, the arm's
# `@Nat.0` was the PARAMETER, the termination proof held over it, and the
# arm's own subtraction was proved from the parameter's path.
ARM_OF_AN_UNSORTED_ADT = """\
private data Box {
  MkBox(Map<Int, Int>, Nat)
}

public fn f(@Box, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    match @Box.0 {
      MkBox(@Map<Int, Int>, @Nat) -> f(@Box.0, @Nat.0 - 1)
    }
  }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(MkBox(map_new(), 100), 5)
}

public fn main0(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(MkBox(map_new(), 0), 5)
}
"""


def test_an_arm_of_an_unsorted_adt_reads_its_own_binders() -> None:
    v = _verify(ARM_OF_AN_UNSORTED_ADT)
    assert _records(v, "nat_sub", _at(ARM_OF_AN_UNSORTED_ADT,
                                      "@Nat.0 - 1)")) == ["tier3"]
    ran = _run(ARM_OF_AN_UNSORTED_ADT, "main0", [])
    assert ran.trap_kind is not None, ran
    assert "failed to decrease" not in ran.trap_message, ran


# #1222's other half: a call inside a measure, nested where no translation
# reaches it, so its precondition was never obligated and the loop was
# verify-clean while its measure trapped in `need_pos`.
MEASURE_CALL_NESTED = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn loop(@Int, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0, string_length(show(need_pos(@Int.0))))
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { loop(@Int.0, @Nat.0 - 1) }
}
"""


def test_a_call_nested_in_a_measure_is_obligated() -> None:
    v = _verify(MEASURE_CALL_NESTED)
    call = _at(MEASURE_CALL_NESTED, "need_pos(@Int.0)")
    assert _records(v, "call_pre", call) == ["violated/E501"]
    assert ("E501", *call) in v.errors
    assert "need_pos" in _run(MEASURE_CALL_NESTED, "loop", [-3, 2]).trap_message


# A piped call is the call its desugaring makes, located at the pipe.
PIPED_CALL = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_length(show(@Int.0 |> need_pos()))
}
"""


def test_a_piped_call_is_obligated() -> None:
    v = _verify(PIPED_CALL)
    pipe = _at(PIPED_CALL, "@Int.0 |> need_pos()")
    assert _records(v, "call_pre", pipe) == ["violated/E501"]
    assert "need_pos" in _run(PIPED_CALL, "f", [-3]).trap_message


# The built-in's domain in an interpolated part, over a `let`-bound string:
# an interpolated expression cannot hold the literal, and a string's byte
# length is modelled only for a literal (#802), so the domain cannot be
# stated here and the call is recorded Tier 3, with the built-in's own check
# behind it.
INTERPOLATED_BUILT_IN = """\
public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @String = "abc";
  string_length("v=\\(string_char_code(@String.0, @Int.0))")
}
"""


def test_a_built_in_domain_in_an_interpolated_part() -> None:
    v = _verify(INTERPOLATED_BUILT_IN)
    call = _at(INTERPOLATED_BUILT_IN, "string_char_code(@String.0, @Int.0)")
    assert _records(v, "call_pre", call) == ["tier3/E532"]
    assert _run(INTERPOLATED_BUILT_IN, "f", [7]).trap_kind is not None
    assert _run(INTERPOLATED_BUILT_IN, "f", [1]).trap_kind is None


# A call over a value the walk cannot know — an arm's binder under a
# scrutinee that does not translate — is a check #1480 records, and it is not
# refused on a placeholder (§6.4.2): Tier 3 (E532), the callee's own check
# stopping a violating value, until an `assume` about the binder discharges
# it.
OPAQUE_ARGUMENT = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match map_get(map_insert(map_new(), 1, @Int.0), 1) {
    Some(@Int) -> need_pos(@Int.0),
    None -> 1
  }
}

public fn g(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match map_get(map_insert(map_new(), 1, @Int.0), 1) {
    Some(@Int) -> string_char_code("abc", @Int.0),
    None -> 1
  }
}
"""


@pytest.mark.parametrize(("fn", "call", "dom", "bad", "good"), [
    ("f", "need_pos(@Int.0)", "@Int.0 > 0", -5, 5),
    ("g", 'string_char_code("abc", @Int.0)', "@Int.0 >= 0 && @Int.0 < 3",
     7, 1),
])
def test_a_call_over_an_unknown_arm_binder_is_tier3(
        fn: str, call: str, dom: str, bad: int, good: int) -> None:
    v = _verify(OPAQUE_ARGUMENT)
    where = _at(OPAQUE_ARGUMENT, call)
    assert _records(v, "call_pre", where) == ["tier3/E532"]
    assert v.ok, v.errors
    assert _run(OPAQUE_ARGUMENT, fn, [good]).trap_kind is None
    assert _run(OPAQUE_ARGUMENT, fn, [bad]).trap_kind is not None
    assumed = OPAQUE_ARGUMENT.replace(
        f"Some(@Int) -> {call},", f"Some(@Int) -> {{ assume({dom}); {call} }},")
    assert assumed != OPAQUE_ARGUMENT
    av = _verify(assumed)
    assert _records(av, "call_pre", _at(assumed, call)) == (
        ["verified"] if fn == "g" else [])
    assert _run(assumed, fn, [good]).trap_kind is None


# #1199's repair: the value an effect operation returns is unknown, and an
# `assume` about it is how an author vouches for it.  The walk binds that
# unknown value in its slot even where no outer binding shadows it, so the
# `assume`'s fact reaches the call's check and discharges it.
ASSUMED_LET = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn g(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  let @Int = get(());
  assume(@Int.0 > 0);
  need_pos(@Int.0)
}
"""


def test_an_assumed_let_value_discharges_the_call() -> None:
    v = _verify(ASSUMED_LET)
    assert _records(v, "call_pre", _at(ASSUMED_LET, "need_pos(@Int.0)")) == []
    assert v.ok, v.errors


def test_an_unassumed_let_value_leaves_the_call_refuted() -> None:
    """The twin that makes the cell above non-vacuous: without the `assume`
    the call is reached and its precondition is NOT established.  It is
    E501: the call sits where the function body's own translation checks
    it, which recorded it before #1480 and keeps #804's strict posture
    (§6.4.2, `SmtContext.strict_preconditions`)."""
    src = ASSUMED_LET.replace("  assume(@Int.0 > 0);\n", "")
    assert "assume" not in src
    v = _verify(src)
    call = _at(src, "need_pos(@Int.0)")
    assert _records(v, "call_pre", call) == ["violated/E501"]
    assert ("E501", *call) in v.errors


# The same, for a value of an array type: the walk binds a placeholder of the
# array's own sort, so an `assume` about its length reaches the call's check.
ASSUMED_ARRAY_LET = """\
private fn need_len(@Array<Int> -> @Int)
  requires(array_length(@Array<Int>.0) > 0)
  ensures(true)
  effects(pure)
{
  0
}

public fn g(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = map_values(map_insert(map_new(), 1, 2));
  assume(array_length(@Array<Int>.0) > 0);
  need_len(@Array<Int>.0)
}
"""


def test_an_assumed_array_let_discharges_the_call() -> None:
    v = _verify(ASSUMED_ARRAY_LET)
    call = _at(ASSUMED_ARRAY_LET, "need_len(@Array<Int>.0)")
    assert _records(v, "call_pre", call) == []
    assert v.ok, v.errors
    twin = ASSUMED_ARRAY_LET.replace(
        "  assume(array_length(@Array<Int>.0) > 0);\n", "")
    assert "assume" not in twin
    # Without it the call is reached, over the array's placeholder, which
    # only the obligation walk binds: a check #1480 records, refuted only
    # over a value the verifier cannot state, so Tier 3 (§6.4.2).
    tv = _verify(twin)
    assert _records(tv, "call_pre", _at(twin, "need_len(@Array<Int>.0)")) \
        == ["tier3/E532"]
    assert tv.ok, tv.errors


# The termination proof reads the same walk, so every binder it crossed
# wrongly was a `decreases` proved over the wrong value.  Each program below
# was reported `decreases`/verified while its runtime measure guard trapped
# on the first call: the call's argument was read against the enclosing
# PARAMETER, or the call was not seen at all.
UNTRANSLATABLE_LET_BEFORE_CALL = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(<State<Nat>>)
{
  if @Nat.0 == 0 then {
    0
  } else {
    let @Nat = get(());
    f(@Nat.0 - 1)
  }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 10) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    f(2)
  }
}
"""

# A destructure: its right-hand side hides a call that does not decrease, and
# the call after it reads the destructured slot, not the parameter.
CALL_IN_A_DESTRUCTURE = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    let Tuple<@Nat, @Nat> = Tuple(f(@Nat.0), 1);
    f(@Nat.0 - 1)
  }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(3)
}
"""

# A closure's `@Nat.0` is its own parameter.
CALL_IN_A_CLOSURE = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    apply_fn(fn(@Nat -> @Nat) effects(pure) { f(@Nat.0 - 1) }, @Nat.0 + 5)
  }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(2)
}
"""

# A handler clause's `@Nat.0` is the handler's state.
CALL_IN_A_HANDLER_CLAUSE = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    handle[State<Nat>](@Nat = @Nat.0 + 5) {
      get(@Unit) -> { resume(f(@Nat.0 - 1)) },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    }
  }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(2)
}
"""


# A call in an `if` condition: evaluated before either branch.
CALL_IN_A_CONDITION = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    if f(@Nat.0) > 100 then {
      0
    } else {
      f(@Nat.0 - 1)
    }
  }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(2)
}
"""

# A call in a quantifier's predicate, a closure called on each element.
CALL_IN_A_QUANTIFIER = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    if forall(@Nat, 1, fn(@Nat -> @Bool) effects(pure) {
      f(@Nat.1 + 1) > 0
    }) then {
      f(@Nat.0 - 1)
    } else {
      f(@Nat.0 - 1)
    }
  }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(2)
}
"""


@pytest.mark.parametrize("source", [
    UNTRANSLATABLE_LET_BEFORE_CALL, CALL_IN_A_DESTRUCTURE,
    CALL_IN_A_CLOSURE, CALL_IN_A_HANDLER_CLAUSE, CALL_IN_A_CONDITION,
    CALL_IN_A_QUANTIFIER, ARM_OF_AN_UNSORTED_ADT,
], ids=["untranslatable-let", "destructure", "closure", "handler-clause",
        "if-condition", "quantifier", "arm-of-an-unsorted-adt"])
def test_the_termination_proof_sees_every_call_in_its_scope(
        source: str) -> None:
    v = _verify(source)
    decreases = sorted(
        f"{o.status}/{o.error_code}" if o.error_code else o.status
        for o in v.obligations if o.kind == "decreases")
    assert decreases == ["tier3/E525"]
    ran = _run(source, "main", [])
    assert "failed to decrease" in ran.trap_message, ran


# The rendering walk behind `show` asks whether a type holds a `@Float64`
# by descending its constructor fields.  A non-regular declaration gives that
# descent no fixed point, and `verify()` is a public entry point whose
# check-clean precondition is its caller's to keep, so the walk must decline
# the type rather than recurse without end (#1429's rule).
NON_REGULAR_SHOWN = """\
private data Nest<T> { N(Nest<Option<T>>), Z }

public fn f(@Nest<Int> -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(@Nest<Int>.0)
}
"""


def test_a_non_regular_type_is_declined_by_the_rendering_walk() -> None:
    import time

    started = time.monotonic()
    result = verify(parse_to_ast(NON_REGULAR_SHOWN), NON_REGULAR_SHOWN)
    assert time.monotonic() - started < 60
    show = _at(NON_REGULAR_SHOWN, "show(")
    assert [o.status for o in result.obligations
            if o.kind == "float_to_int_domain"
            and (o.line, o.column) == show] == ["tier3"]


def test_the_call_pre_table_keeps_no_record_alive() -> None:
    """The identity table behind `_call_pre_recorded` must not keep a
    record alive once the buffer holding it is discarded, as a disclosure
    rerun's or a generic instance's buffer is."""
    import gc
    import weakref

    from vera.verifier import ContractVerifier

    program = parse_to_ast(CHAR_CODE)
    _diags, arts = typecheck_with_artifacts(program, CHAR_CODE)
    verifier = ContractVerifier(
        source=CHAR_CODE,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    verifier.verify_program(program)
    refs = [weakref.ref(o) for o in verifier.obligations
            if o.kind == "call_pre"]
    assert refs
    verifier.obligations = []
    gc.collect()
    assert [r() for r in refs] == [None] * len(refs)


# A predicate is checked where it is declared, whatever the declaration.
DECLARATION_POSITIONS = """\
type Pos = { @Int | @Int.0 > 0 };

type OverPos = { @Pos | 10 / @Pos.0 > 0 };

type Unused = { @Nat | @Nat.0 - 1 >= 0 };

private data Box {
  MkBox({ @Int | 10 / @Int.0 > 0 })
}

effect Log {
  op log({ @Nat | @Nat.0 - 2 >= 0 } -> Unit);
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @{ @Int | 100 / @Int.0 > 0 } = 5;
  @Int.0
}
"""


class TestDeclarationPositions:
    """Every place a refinement can be written is a declaration checked."""

    def test_a_refinement_over_a_refinement_assumes_its_base(self) -> None:
        # `@Pos.0 > 0` is a fact of the base type, so the division is safe.
        v = _verify(DECLARATION_POSITIONS)
        assert _records(v, "div_zero",
                        _at(DECLARATION_POSITIONS, "10 / @Pos.0")) == [
            "verified"]

    def test_a_call_in_the_predicate_is_checked_under_the_base(self) -> None:
        """A call's precondition is checked as the SMT layer translates the
        call, against what the solver holds, so the base type's facts have
        to be IN it: `need_pos(@Pos.0)` holds because `@Pos.0 > 0` does."""
        source = _NEED_POS + (
            "\ntype Pos = { @Int | @Int.0 > 0 };\n\n"
            "type NeedsPos = { @Pos | need_pos(@Pos.0) > 0 };\n")
        v = _verify(source)
        assert v.ok, v.errors
        assert not [o for o in v.obligations if o.kind == "call_pre"]

    def test_a_type_used_nowhere_is_checked(self) -> None:
        v = _verify(DECLARATION_POSITIONS)
        assert _records(v, "nat_sub",
                        _at(DECLARATION_POSITIONS, "@Nat.0 - 1")) == [
            "violated/E502"]

    @pytest.mark.parametrize(("kind", "needle", "code"), [
        ("div_zero", "10 / @Int.0", "E526"),        # a constructor field
        ("nat_sub", "@Nat.0 - 2", "E502"),          # an operation's formal
        ("div_zero", "100 / @Int.0", "E526"),       # a `let` annotation
    ])
    def test_a_refinement_written_inline(
        self, kind: str, needle: str, code: str,
    ) -> None:
        v = _verify(DECLARATION_POSITIONS)
        where = _at(DECLARATION_POSITIONS, needle)
        assert _records(v, kind, where) == [f"violated/{code}"]
        assert (code, *where) in v.errors


@pytest.mark.parametrize("source", [COUNT_TO_FIXED, ODD3_GUARDED,
                                    CHAR_CODE_BOUNDED])
def test_fixed_forms_are_verify_clean(source: str) -> None:
    """The corrected forms carry no error: the fix is not a blanket refusal."""
    assert _verify(source).ok


# =====================================================================
# The matrix: every evaluated position x every trapping operation
# =====================================================================
#
# Axis 1, the OPERATIONS a compiled check traps on (`_OPS`), each written
# over a value `{v}` of its base type, with the domain it is defined on, a
# value inside it, and one outside it that the base type still admits.
#
# Axis 2, the POSITIONS code generation evaluates an expression in
# (`_POSITIONS`), enumerated from its evaluation roots and held to them by
# `test_every_evaluation_root_is_a_position`.  The refinement predicate is one
# root reached from every guard position, so its cells are crossed with the
# guard routes `test_boundary_guard_correctness_1466` holds to
# `binders.GUARD_SITES`.
#
# Each cell names a status and asserts both halves of the claim: the record
# (the obligation exists, at the operation, with that status and code) and
# the run (a `verified` cell never traps on an input its premises admit; a
# `violated` or `tier3` cell traps on a violating one).  No cell is excused:
# the matrix has no xfail.

_NEED_POS = """
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""

_NAT_ID = """
private fn nat_id(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}
"""

# An array whose length the verifier knows, from a call: code generation does
# not infer the element type of an array LITERAL indexed in place (E602).
_ARR3 = """
private fn arr3(@Unit -> @Array<Int>)
  requires(true)
  ensures(array_length(@Array<Int>.result) == 3)
  effects(pure)
{
  [1, 2, 3]
}
"""

_FLOAT_DOMAIN = (
    "!float_is_nan({v}) && {v} < 1000000.0 && {v} > 0.0 - 1000000.0"
)


@dataclass(frozen=True)
class Op:
    """One trapping operation, written over a value ``{v}`` of *base*."""

    name: str
    #: The obligation kind the operation is recorded under, and its code
    #: when refuted.
    kind: str
    code: str
    base: str
    #: A value-producing expression over ``{v}`` that performs it.
    value: str
    #: Over ``{v}``: the values it is defined on.
    domain: str
    #: Literals inside and outside that domain, and the same values as
    #: arguments to a compiled function.  A negative is spelled `-3`, never
    #: `0 - 3`: the pure-literal subtraction types as `@Nat`, and a tuple
    #: component or a `Map` value then widens it as a `@Nat` above
    #: i64.MAX — a trap of its own that would stand in for the cell's.
    good: str
    bad: str
    good_arg: int | float
    bad_arg: int | float
    #: How an operand no premise bounds is recorded: ``violated`` for a
    #: kind discharged by one check, ``tier3`` for a two-check kind or a
    #: concrete-gated conversion.
    unbounded: str
    #: A premise over ``{v}`` under which it provably traps, for a kind
    #: refuted only when that is provable.
    provably_bad: str = ""
    #: Where the obligation sits inside ``value``: a narrowing is located
    #: at its argument, everything else at the operation.
    offset: int = 0
    helpers: str = ""
    #: The float conversions decide a CONCRETE argument and leave a
    #: symbolic one to the trap, whatever the premises (#807).
    concrete_only: bool = False
    #: The precondition text a `call_pre` obligation carries, to tell it
    #: from another at the same site.
    pre_text: str = ""
    #: Whether a DISCHARGED obligation is recorded.  Phase A records a user
    #: callee's precondition only when it is not discharged — its check is
    #: in the callee's prologue, whose own `requires` record stands for it —
    #: so a `verified` cell of that kind asserts the record ABSENT, and its
    #: `violated` twin is what shows the walk reaches the position.  A
    #: built-in's domain is checked inline at the call and IS recorded.
    records_discharge: bool = True

    def statuses(self) -> tuple[str, ...]:
        if self.unbounded == "violated":
            return ("verified", "violated")
        return ("verified", "violated", "tier3")


_OPS: tuple[Op, ...] = (
    Op("nat_sub", "nat_sub", "E502", "Nat", "{v} - 5", "{v} >= 5",
       "7", "3", 7, 3, "violated"),
    Op("div", "div_zero", "E526", "Int", "10 / {v}", "{v} != 0",
       "2", "0", 2, 0, "violated"),
    Op("mod", "div_zero", "E526", "Int", "10 % {v}", "{v} != 0",
       "3", "0", 3, 0, "violated"),
    Op("index", "index_bounds", "E527", "Int", "arr3(())[{v}]",
       "{v} >= 0 && {v} < 3", "1", "5", 1, 5, "tier3",
       provably_bad="{v} == 5", helpers=_ARR3),
    Op("overflow", "int_overflow", "E528", "Int",
       "9223372036854775807 + {v}", "{v} >= 0 - 100 && {v} <= 0",
       "0", "1", 0, 1, "tier3", provably_bad="{v} == 1"),
    Op("call_pre", "call_pre", "E501", "Int", "need_pos({v})", "{v} >= 1",
       "2", "-3", 2, -3, "violated", helpers=_NEED_POS,
       pre_text="@Int.0 > 0", records_discharge=False),
    Op("nat_bind", "nat_bind", "E503", "Int", "nat_id({v})", "{v} >= 0",
       "2", "-3", 2, -3, "violated", offset=len("nat_id("),
       helpers=_NAT_ID),
    Op("string_char_code", "call_pre", "E501", "Int",
       'string_char_code("abc", {v})', "{v} >= 0 && {v} < 3",
       "1", "7", 1, 7, "violated",
       pre_text="@Int.0 >= 0 && @Int.0 < string_length(@String.0)"),
    *(
        Op(name, "float_to_int_domain", "E529", "Float64",
           f"{name}({{v}})", _FLOAT_DOMAIN, "1.5", "nan()",
           1.5, float("nan"), "tier3", concrete_only=True)
        for name in ("float_to_int", "floor", "ceil", "round")
    ),
    # Rendering a `@Float64` as text truncates its integer part with the
    # same instruction: `float_to_string`, and the `show` and the
    # interpolated part that lower to it.  NaN and the infinities render;
    # a finite magnitude of 2^63 or more traps.
    *(
        Op(name, "float_to_int_domain", "E529", "Float64", value,
           _FLOAT_DOMAIN, "1.5", "10000000000000000000.0", 1.5, 1e19,
           "tier3", offset=offset, concrete_only=True)
        for name, value, offset in (
            ("float_to_string", "string_length(float_to_string({v}))",
             len("string_length(")),
            ("show", "string_length(show({v}))", len("string_length(")),
            ("interpolation", 'string_length("\\({v})")',
             len('string_length("\\(')),
        )
    ),
)


def _variant(op: Op, status: str) -> tuple[str, str, str, int | float]:
    """(premise, value, input literal, input argument) for one status.

    The premise is what the position's facts establish about ``{v}``; the
    input is a value those facts admit, chosen so that a cell which should
    trap does so and one which should not is tested where it could.
    """
    if op.concrete_only:
        if status == "verified":
            return ("true", op.value.format(v=op.good), op.good, op.good_arg)
        if status == "violated":
            return ("true", op.value.format(v=op.bad), op.good, op.good_arg)
        return ("true", op.value, op.bad, op.bad_arg)
    if status == "verified":
        return (op.domain, op.value, op.good, op.good_arg)
    if status == "violated" and op.unbounded == "violated":
        return ("true", op.value, op.bad, op.bad_arg)
    if status == "violated":
        return (op.provably_bad, op.value, op.bad, op.bad_arg)
    return ("true", op.value, op.bad, op.bad_arg)


@dataclass(frozen=True)
class Cell:
    """One program, the record it must produce, and the run it must make."""

    source: str
    kind: str
    status: str
    code: str
    #: Where the record is located: the text it starts at, the occurrence,
    #: and an offset into that text.
    at: str
    at_occurrence: int = 0
    at_offset: int = 0
    pre_text: str = ""
    fn: str = "f"
    args: tuple[int | float, ...] = ()
    #: `None`: the run returns.  Otherwise a predicate over the trap.
    trap: object | None = None
    #: Further (kind, status-or-None, text-at) assertions: `None` status
    #: means no record of that kind may be located there.
    also: tuple[tuple[str, str | None, str], ...] = ()
    #: See `Op.records_discharge`.
    absent_when_discharged: bool = False
    #: The code a `tier3` record carries, where it carries one: a call-site
    #: precondition the run cannot check is E532.
    tier3_code: str = ""


def _slot(op: Op, position: str) -> str:
    # The ensures cell reads the PARAMETER, not `@T.result`: a `@Nat`
    # subtraction on the result is neither guarded nor obligated (both sides
    # agree it is not a `@Nat` subtraction), so it is no trapping operation.
    if op.base == "Nat" and position.startswith("measure"):
        return "@Nat.1"
    return f"@{op.base}.0"


def _any_trap(ran: Ran) -> bool:
    return ran.trap_kind is not None


def _not_the_callers_precondition(ran: Ran) -> bool:
    """The trap is the measure's own, not `f`'s precondition: a tail call
    evaluates the measure on its arguments BEFORE the callee checks its
    `requires`."""
    return (ran.trap_kind is not None
            and "Precondition violation in f(" not in ran.trap_message)


def _the_callers_precondition(ran: Ran) -> bool:
    """The callee's `requires` stopped it: a non-tail call evaluates the
    measure on the callee's entry, after its `requires` is checked."""
    return "Precondition violation in f(" in ran.trap_message


def _cell_body(op: Op, status: str) -> Cell:
    premise, value, _lit, arg = _variant(op, status)
    v = _slot(op, "body")
    val = value.format(v=v)
    src = op.helpers + f"""
public fn f(@{op.base} -> @Bool)
  requires({premise.format(v=v)})
  ensures(true)
  effects(pure)
{{
  {val} >= 0 || true
}}
"""
    return Cell(src, op.kind, status, op.code, at=val, at_offset=op.offset,
                pre_text=op.pre_text, args=(arg,),
                trap=None if status == "verified" else _any_trap)


def _cell_requires(op: Op, status: str) -> Cell:
    premise, value, _lit, arg = _variant(op, status)
    v = _slot(op, "requires")
    val = value.format(v=v)
    src = op.helpers + f"""
public fn f(@{op.base} -> @Int)
  requires({premise.format(v=v)})
  requires({val} >= 0 || true)
  ensures(true)
  effects(pure)
{{
  0
}}
"""
    return Cell(src, op.kind, status, op.code, at=val, at_offset=op.offset,
                pre_text=op.pre_text, args=(arg,),
                trap=None if status == "verified" else _any_trap)


def _cell_ensures(op: Op, status: str) -> Cell:
    premise, value, _lit, arg = _variant(op, status)
    p = _slot(op, "body")
    val = value.format(v=_slot(op, "ensures"))
    src = op.helpers + f"""
public fn f(@{op.base} -> @{op.base})
  requires({premise.format(v=p)})
  ensures({val} >= 0 || true)
  effects(pure)
{{
  {p}
}}
"""
    return Cell(src, op.kind, status, op.code, at=val, at_offset=op.offset,
                pre_text=op.pre_text, args=(arg,),
                trap=None if status == "verified" else _any_trap)


def _measure_fn(op: Op, premise: str, val: str, call: str,
                ret: str = "@Nat") -> str:
    return op.helpers + f"""
public fn f(@{op.base}, @Nat -> {ret})
  requires({premise})
  ensures(true)
  decreases(@Nat.0, {val})
  effects(pure)
{{
  if @Nat.0 == 0 then {{ 0 }} else {{ {call} }}
}}
"""


def _cell_measure_entry(op: Op, status: str) -> Cell:
    premise, value, _lit, arg = _variant(op, status)
    v = _slot(op, "measure")
    val = value.format(v=v)
    src = _measure_fn(op, premise.format(v=v), val, f"f({v}, @Nat.0 - 1)")
    return Cell(src, op.kind, status, op.code, at=val, at_offset=op.offset,
                pre_text=op.pre_text, args=(arg, 0),
                trap=None if status == "verified" else _any_trap)


def _cell_measure_tail(op: Op, status: str) -> Cell:
    """The measure on a tail call's arguments.  The `violated` cell passes a
    value outside the domain to a callee whose entry measure is proved: the
    site is the one evaluation that traps, and it traps before the callee's
    `requires` could."""
    v = _slot(op, "measure")
    if status == "violated":
        val = op.value.format(v=v)
        call = f"f({op.bad}, @Nat.0 - 1)"
        src = _measure_fn(op, op.domain.format(v=v), val, call)
        return Cell(src, op.kind, status, op.code, at=call,
                    pre_text=op.pre_text, args=(op.good_arg, 1),
                    trap=_not_the_callers_precondition)
    premise, value, _lit, arg = _variant(op, status)
    val = value.format(v=v)
    call = f"f({v}, @Nat.0 - 1)"
    src = _measure_fn(op, premise.format(v=v), val, call)
    return Cell(src, op.kind, status, op.code, at=call,
                pre_text=op.pre_text,
                args=(arg, 0 if status != "verified" else 2),
                trap=None if status == "verified" else _any_trap)


def _cell_measure_nontail(op: Op, status: str) -> Cell:
    """The measure where a NON-tail call's arguments land: evaluated on the
    callee's entry, after its `requires`.  Nothing is obligated at the call,
    and a value outside the domain is stopped by the callee's precondition
    before its measure is evaluated."""
    v = _slot(op, "measure")
    val = op.value.format(v=v)
    call = f"1 + f({op.bad}, @Nat.0 - 1)"
    src = _measure_fn(op, op.domain.format(v=v), val, call, ret="@Int")
    entry = "tier3" if op.concrete_only else "verified"
    return Cell(src, op.kind, entry, op.code, at=val, at_offset=op.offset,
                pre_text=op.pre_text, args=(op.good_arg, 1),
                trap=_the_callers_precondition,
                also=((op.kind, None, f"f({op.bad}, @Nat.0 - 1)"),))


#: The positions, each the verifier-side name of one evaluation root of code
#: generation (`_ROOTS` below maps every root to one of these).
_POSITIONS: dict[str, tuple[object, tuple[str, ...] | None]] = {
    "body": (_cell_body, None),
    "requires": (_cell_requires, None),
    "ensures": (_cell_ensures, None),
    "measure at entry": (_cell_measure_entry, None),
    "measure at a tail call": (_cell_measure_tail, None),
    "measure at a non-tail call": (_cell_measure_nontail, ("verified",)),
}


def _plain_cells() -> list[object]:
    cells = []
    for position, (build, only) in _POSITIONS.items():
        for op in _OPS:
            for status in (only or op.statuses()):
                cells.append(pytest.param(
                    position, op, status,
                    id=f"{position}|{op.name}|{status}"))
    return cells


def _record_matches(v: Verified, cell_kind: str, where: tuple[int, int],
                    pre_text: str) -> list[str]:
    return sorted(
        f"{o.status}/{o.error_code}" if o.error_code else o.status
        for o in v.obligations
        if o.kind == cell_kind and (o.line, o.column) == where
        and (not pre_text or o.expr_text == pre_text)
    )


def _check_cell(cell: Cell) -> Verified:
    v = _verify(cell.source)
    line, col = _at(cell.source, cell.at, cell.at_occurrence)
    where = (line, col + cell.at_offset)
    want = (f"{cell.status}/{cell.code}" if cell.status == "violated"
            else f"tier3/{cell.tier3_code}"
            if cell.status == "tier3" and cell.tier3_code
            else cell.status)
    expected = [] if cell.absent_when_discharged and want == "verified" \
        else [want]
    got = _record_matches(v, cell.kind, where, cell.pre_text)
    assert got == expected, (
        f"record at {where}: expected [{want}], got {got}\n"
        f"all: {[(o.kind, o.status, o.error_code, o.line, o.column) for o in v.obligations]}\n"
        f"{cell.source}"
    )
    if cell.status == "violated":
        assert (cell.code, *where) in v.errors, (cell.code, where, v.errors)
    for kind, status, text in cell.also:
        also_at = _at(cell.source, text)
        also_got = _record_matches(v, kind, also_at, cell.pre_text)
        assert also_got == ([] if status is None else [status]), (
            kind, text, also_got)
    ran = _run(cell.source, cell.fn, list(cell.args))
    if cell.trap is None:
        assert ran.trap_kind is None, (
            f"a {cell.status} cell trapped on an admitted input: "
            f"{ran.trap_kind}: {ran.trap_message}\n{cell.source}")
    else:
        assert cell.trap(ran), (
            f"expected the run to trap as the record says; got "
            f"{ran.value!r} / {ran.trap_kind}: {ran.trap_message}\n"
            f"{cell.source}")
    return v


@pytest.mark.parametrize(("position", "op", "status"), _plain_cells())
def test_plain_position_cell(position: str, op: Op, status: str) -> None:
    build, _only = _POSITIONS[position]
    cell = build(op, status)  # type: ignore[operator]
    _check_cell(replace(cell,
                        absent_when_discharged=not op.records_discharge))


# ---------------------------------------------------------------------
# The sub-position axis: a call's precondition wherever the call sits
# ---------------------------------------------------------------------
#
# The cells above put the operation at the top of its position.  A call's
# precondition, a user callee's `requires` or `string_char_code`'s declared
# domain, is the operation whose obligation depended on WHERE in the
# position it sits: it was obligated as a side effect of the SMT
# translation, and translation stops early.  It does not translate the
# arguments of a built-in it does not model, stops at an argument that does
# not translate, stops at a `let` or a pattern it cannot bind, and never
# enters a closure, an interpolated part, a `handle` body or a quantifier.
# The walk that obligates a call reaches every evaluated expression, and
# this axis holds it there: the two call-precondition operations nested in
# each of those sub-positions, at a body, a measure and a predicate.

_PICK = """
private fn pick(@Map<Int, Int>, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


@dataclass(frozen=True)
class SubPosition:
    """Where a call sits inside the expression its position evaluates."""

    name: str
    #: A `@Bool` expression with the call ``{c}`` nested in it.
    wrap: str
    #: Whether the walk reads the enclosing slots there.  A closure body and
    #: a quantifier's predicate are fresh scopes, which the walk enters with
    #: an empty env: a call over an enclosing slot is recorded Tier 3
    #: (E532), with the callee's own check behind it.
    reads_enclosing: bool = True
    helpers: str = ""


_SUB_POSITIONS: tuple[SubPosition, ...] = (
    SubPosition("top", "{c} >= 0 || true"),
    SubPosition("argument of an unmodelled built-in",
                "string_length(show({c})) >= 0 || true"),
    SubPosition("interpolated part",
                'string_length("v=\\({c})") >= 0 || true'),
    SubPosition("argument after one that does not translate",
                "pick(map_insert(map_new(), 1, 2), {c}) >= 0 || true",
                helpers=_PICK),
    SubPosition("after a let that does not translate",
                "if true then {{ let @Map<Int, Int> = "
                "map_insert(map_new(), 1, 2); {c} >= 0 || true }} "
                "else {{ false }}"),
    SubPosition("arm under a scrutinee that does not translate",
                "match map_get(map_insert(map_new(), 1, true), 1) {{ "
                "Some(@Bool) -> {c} >= 0 || @Bool.0, None -> true }}"),
    SubPosition("handle body",
                "handle[State<Bool>](@Bool = true) {{ "
                "get(@Unit) -> {{ resume(@Bool.0) }}, "
                "put(@Bool) -> {{ resume(()) }} }} in {{ {c} >= 0 || true }}"),
    SubPosition("effect operation's argument",
                "handle[State<Int>](@Int = 0) {{ "
                "get(@Unit) -> {{ resume(@Int.0) }}, "
                "put(@Int) -> {{ resume(()) }} }} in {{ put({c}); true }}"),
    SubPosition("closure body",
                "apply_fn(fn(@Int -> @Int) effects(pure) {{ {c} }}, @Int.0) "
                ">= 0 || true",
                reads_enclosing=False),
    SubPosition("quantifier predicate",
                "forall(@Nat, 1, fn(@Nat -> @Bool) effects(pure) {{ "
                "{c} >= 0 || true }})",
                reads_enclosing=False),
)

_CALL_OPS: tuple[Op, ...] = tuple(
    op for op in _OPS if op.name in ("call_pre", "string_char_code"))

# The user callee called by the file's own path (#1558): inside
# `module ma;`, `ma::need_pos(x)` is the call `need_pos(x)` is, so its
# precondition is obligated at every sub-position the bare call's is.
_CALL_OPS = (*_CALL_OPS, *(
    replace(op, name="call_pre by own path", value="ma::need_pos({v})",
            helpers="module ma;\n\n" + op.helpers)
    for op in _CALL_OPS if op.name == "call_pre"))

_SUB_AT = ("body", "measure at entry", "refinement predicate")


def _sub_position_cell(sub: SubPosition, op: Op, position: str,
                       status: str) -> Cell:
    premise, value, _lit, arg = _variant(op, status)
    call = value.format(v="@Int.0")
    expr = sub.wrap.format(c=call)
    helpers = op.helpers + sub.helpers
    fn, args = "f", (arg,)
    if position == "body":
        src = helpers + f"""
public fn f(@Int -> @Bool)
  requires({premise.format(v="@Int.0")})
  ensures(true)
  effects(pure)
{{
  {expr}
}}
"""
    elif position == "measure at entry":
        src = helpers + f"""
public fn f(@Int, @Nat -> @Nat)
  requires({premise.format(v="@Int.0")})
  ensures(true)
  decreases(@Nat.0, if {expr} then {{ @Nat.0 }} else {{ @Nat.0 }})
  effects(pure)
{{
  if @Nat.0 == 0 then {{ 0 }} else {{ f(@Int.0, @Nat.0 - 1) }}
}}
"""
        args = (arg, 0)
    else:
        # A predicate has no `requires`: the domain is the condition of an
        # `if` around the call, the one guard a predicate has.
        if status == "verified":
            expr = (f"if {op.domain.format(v='@Int.0')} then {{ {expr} }} "
                    f"else {{ false }}")
        src = helpers + f"""
type T = {{ @Int | {expr} }};

public fn take(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  0
}}
"""
        fn = "take"
    return Cell(src, op.kind, status, op.code, at=call, pre_text=op.pre_text,
                fn=fn, args=args,
                trap=None if status == "verified" else _any_trap,
                absent_when_discharged=not op.records_discharge,
                tier3_code="E532")


def _sub_position_cells() -> list[object]:
    cells = []
    for position in _SUB_AT:
        for sub in _SUB_POSITIONS:
            statuses = (("verified", "violated") if sub.reads_enclosing
                        else ("tier3",))
            for op in _CALL_OPS:
                if sub.name == "interpolated part" and '"' in op.value:
                    # An interpolated expression cannot hold a string
                    # literal (a parse error), and `string_char_code`'s
                    # domain is statable only over one (#802): its cell is
                    # `test_a_built_in_domain_in_an_interpolated_part`.
                    continue
                for status in statuses:
                    cells.append(pytest.param(
                        sub, op, position, status,
                        id=f"{position}|{sub.name}|{op.name}|{status}"))
    return cells


@pytest.mark.parametrize(("sub", "op", "position", "status"),
                         _sub_position_cells())
def test_sub_position_cell(sub: SubPosition, op: Op, position: str,
                           status: str) -> None:
    _check_cell(_sub_position_cell(sub, op, position, status))


# ---------------------------------------------------------------------
# A check #1480 records is not refused on a value it cannot state
# ---------------------------------------------------------------------
#
# Spec §6.4.2.  The value here is an effect operation's result, which the
# verifier cannot know.  Where the function body's own translation checks a
# user callee's precondition over it (the call at the top of the `let`'s
# body), the check predates #1480 and keeps #804's strict posture: E501, and
# an `assume` about the value is the repair.  Every other check is one #1480
# records, and the compiled program makes it at the call, so a refutation
# that rests only on the value's placeholder is Tier 3 (E532), never a
# refusal: in an argument of a built-in the SMT layer does not model, in an
# interpolated part, in a pipe, in an arm whose binder is the unknown value,
# and `string_char_code`'s declared domain wherever the call sits.  The
# `assume` discharges either.  A binder of a closure, of a quantifier's
# predicate or of a handler clause is read without its value at all, and its
# call is E532 as well.

_UNKNOWN_PRELUDE = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn f(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  let @Int = get(());
"""

_UNKNOWN_MAIN = """
public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = {state}) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    f(())
  }
}
"""

#: The two call-precondition operations, over the unknown `@Int.0`: the
#: call, its piped spelling, the domain an `assume` states, and a value of
#: the state inside that domain and one outside it.
_UNKNOWN_OPS = {
    "call_pre": ("need_pos(@Int.0)", "@Int.0 |> need_pos()",
                 "@Int.0 > 0", 2, -5),
    "string_char_code": ('string_char_code("abc", @Int.0)',
                         '"abc" |> string_char_code(@Int.0)',
                         "@Int.0 >= 0 && @Int.0 < 3", 1, 7),
}

#: position -> (the body after the `let`, over ``{c}``; whether it holds the
#: piped spelling; whether the `assume` goes inside the arm).
_UNKNOWN_POSITIONS = {
    "top of the let's body": ("{c} >= 0 || true", False, False),
    "argument of an unmodelled built-in":
        ("string_length(show({c})) >= 0 || true", False, False),
    "interpolated part": ('string_length("v=\\({c})") >= 0 || true',
                          False, False),
    "piped call": ("string_length(show({c})) >= 0 || true", True, False),
    "arm whose binder is the unknown value":
        ("match map_get(map_insert(map_new(), 1, @Int.0), 1) {{\n"
         "    Some(@Int) -> {arm},\n    None -> true\n  }}", False, True),
}


def _unknown_program(position: str, op: str, assumed: bool,
                     state: int) -> tuple[str, str]:
    """The program, and the text its call's record is located at."""
    call, piped, dom, _good, _bad = _UNKNOWN_OPS[op]
    body, is_piped, in_arm = _UNKNOWN_POSITIONS[position]
    c = piped if is_piped else call
    if in_arm:
        arm = (f"{{ assume({dom}); {c} >= 0 || true }}" if assumed
               else f"{c} >= 0 || true")
        text = body.format(arm=arm)
        stmt = ""
    else:
        text = body.format(c=c)
        stmt = f"  assume({dom});\n" if assumed else ""
    src = (_UNKNOWN_PRELUDE + stmt + f"  {text}\n}}\n"
           + _UNKNOWN_MAIN.replace("{state}", str(state)))
    return src, c


def _unknown_cells() -> list[object]:
    cells = []
    for position in _UNKNOWN_POSITIONS:
        for op in _UNKNOWN_OPS:
            if position == "interpolated part" and op == "string_char_code":
                # An interpolated expression cannot hold a string literal.
                continue
            cells.append(pytest.param(position, op,
                                      id=f"{position}|{op}"))
    return cells


#: The one cell the function body's own translation checks, which keeps
#: #804's E501 (`SmtContext.strict_preconditions`).
_BODY_TRANSLATION_CHECKS = {("top of the let's body", "call_pre")}


@pytest.mark.parametrize(("position", "op"), _unknown_cells())
def test_an_unknown_value_is_tier3_where_1480_records_the_check(
        position: str, op: str) -> None:
    _call, _piped, _dom, good, bad = _UNKNOWN_OPS[op]
    src, at = _unknown_program(position, op, assumed=False, state=bad)
    v = _verify(src)
    where = _at(src, at)
    strict = (position, op) in _BODY_TRANSLATION_CHECKS
    assert _records(v, "call_pre", where) == (
        ["violated/E501"] if strict else ["tier3/E532"]), (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations], src)
    assert (("E501", *where) in v.errors) is strict
    assert v.ok is not strict, v.errors
    # The check the compiled program makes at the call stops a violating
    # value and passes one inside the domain, recorded either way.
    assert _run(src, "main", []).trap_kind is not None
    good_src, _ = _unknown_program(position, op, assumed=False, state=good)
    assert _run(good_src, "main", []).trap_kind is None
    # ... and the `assume` about the value discharges it, wherever it sits.
    src, at = _unknown_program(position, op, assumed=True, state=good)
    v = _verify(src)
    assert _records(v, "call_pre", _at(src, at)) == (
        ["verified"] if op == "string_char_code" else [])
    assert v.ok, v.errors
    assert _run(src, "main", []).trap_kind is None


# ---------------------------------------------------------------------
# Every kind #1480 records, over a placeholder
# ---------------------------------------------------------------------
#
# Each obligation #1480 records is a check the compiled program makes where
# it evaluates it, so a refutation of one that rests on a value the verifier
# cannot state (a placeholder for a `let`, destructure or `match` binder
# whose value does not translate) is Tier 3, never a refusal.  One program
# per kind that can meet one: a correct program records Tier 3 and runs, and
# the same program given a violating value traps on that check.
#
# The kinds that cannot meet one, and why, stated rather than counted: an
# array index and an overflow are refused only when the violation holds for
# every value (their two-check), and a float truncation only on a constant
# argument, so a placeholder never refutes them.  The float cell below pins
# the second.  A `let` or `match` written inside a measure or a refinement
# predicate reaches the same gates as one in a body.

_ARRAY_LET_CALL = """\
private fn head_of(@Array<Int> -> @Int)
  requires(array_length(@Array<Int>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<Int>.0[0]
}

public fn f(@Array<Int> -> @Int)
  requires(array_length(@Array<Int>.0) > 0)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = apply_fn(fn(@Unit -> @Array<Int>) effects(pure) { [1, 2, 3] }, ());
  head_of(@Array<Int>.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f([9])
}
"""

_REQUIRES_CALL = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn f(@Int -> @Bool)
  requires(match map_get(map_insert(map_new(), 1, @Int.0), 1) {
    Some(@Int) -> need_pos(@Int.0) > 0,
    None -> true
  })
  ensures(true)
  effects(pure)
{
  true
}
"""

_MEASURE_CHAR_CODE = """\
public fn f(@Nat, @Int -> @Nat)
  requires(@Int.0 >= 0 && @Int.0 < 3)
  ensures(true)
  decreases(@Nat.0 + string_char_code("abc", @Int.0))
  effects(<State<Option<Int>>>)
{
  if @Nat.0 == 0 then {
    0
  } else {
    match get(()) {
      Some(@Int) -> f(@Nat.0 - 1, @Int.0),
      None -> 0
    }
  }
}

public fn main(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(@Int.0)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    f(3, 1)
  }
}
"""

_MEASURE_DIVISION = """\
public fn f(@Nat, @Nat -> @Nat)
  requires(@Nat.0 > 0)
  ensures(true)
  decreases(@Nat.1, 100 / @Nat.0)
  effects(<State<Option<Nat>>>)
{
  if @Nat.1 == 0 then {
    0
  } else {
    match get(()) {
      Some(@Nat) -> f(@Nat.2 - 1, @Nat.0),
      None -> 0
    }
  }
}

public fn main(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Nat>>](@Option<Nat> = Some(@Nat.0)) {
    get(@Unit) -> { resume(@Option<Nat>.0) },
    put(@Option<Nat>) -> { resume(()) }
  } in {
    f(3, 1)
  }
}
"""

_REQUIRES_NAT = """\
private fn nat_id(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn f(@Int -> @Bool)
  requires(match map_get(map_insert(map_new(), 1, @Int.0), 1) {
    Some(@Int) -> nat_id(@Int.0) >= 0,
    None -> true
  })
  ensures(true)
  effects(pure)
{
  true
}
"""

_REQUIRES_LET_NAT = """\
private fn nat_id(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn f(@Int -> @Bool)
  requires({
    let @Int = apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }, @Int.0);
    nat_id(@Int.0) >= 0
  })
  ensures(true)
  effects(pure)
{
  true
}
"""

_ENSURES_NAT = """\
private fn nat_id(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn f(@Int -> @Bool)
  requires(true)
  ensures(match map_get(map_insert(map_new(), 1, @Int.0), 1) {
    Some(@Int) -> nat_id(@Int.0) >= 0,
    None -> true
  })
  effects(pure)
{
  true
}
"""

_REQUIRES_REFINEMENT = """\
type Pos = { @Int | @Int.0 > 0 };

private fn take_pos(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Pos.0
}

public fn f(@Int -> @Bool)
  requires(match map_get(map_insert(map_new(), 1, @Int.0), 1) {
    Some(@Int) -> take_pos(@Int.0) > 0,
    None -> true
  })
  ensures(true)
  effects(pure)
{
  true
}
"""

_COMPUTED_FLOOR = """\
public fn f(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Float64 = apply_fn(fn(@Float64 -> @Float64) effects(pure) { @Float64.0 * 2.0 }, @Float64.0);
  floor(@Float64.0)
}
"""

# A refinement narrowing of a PROJECTED value: an arm's sub-pattern binder
# under a `match` whose scrutinee is itself a binder of an arm the verifier
# cannot translate (the map lookup).  POSITION is where the `match` sits.
_SUBPATTERN_OVER_A_PLACEHOLDER = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Option<Int>, @Int -> @Bool)
  REQUIRES
  ENSURES
  effects(pure)
{
  BODY
}

public fn main(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(None, @Int.0)
}
"""

_SUBPATTERN_MATCH = """match map_get(map_insert(map_new(), 1, Some(@Int.0)), 1) {
    Some(@Option<Int>) -> match @Option<Int>.0 {
      Some(@Pos) -> true,
      None -> true
    },
    None -> true
  }"""


def _subpattern_over_a_placeholder(position: str, match: str) -> str:
    slots = {"REQUIRES": "requires(true)", "ENSURES": "ensures(true)",
             "BODY": "true"}
    slots[position] = (match if position == "BODY"
                       else f"{position.lower()}({match})")
    src = _SUBPATTERN_OVER_A_PLACEHOLDER
    for slot, text in slots.items():
        src = src.replace(slot, text)
    return src


#: name -> (program, the record's needle and its occurrence, kind, the
#: records there, the function run, a correct call's arguments and the
#: violating program and arguments, the violating run's trap message).
_PLACEHOLDER_KINDS = {
    "call precondition, after an array let": (
        _ARRAY_LET_CALL, ("head_of(@Array<Int>.0)", 0), "call_pre",
        ["tier3/E532"], "main", [],
        (_ARRAY_LET_CALL.replace("[1, 2, 3]", "[]"), []),
        "Precondition violation in head_of"),
    "call precondition, in a requires": (
        _REQUIRES_CALL, ("need_pos(", 1), "call_pre", ["tier3/E532"],
        "f", [5], (_REQUIRES_CALL, [-5]), "Precondition violation in need_pos"),
    "built-in domain, in a measure at a tail call": (
        _MEASURE_CHAR_CODE, ("f(@Nat.0 - 1", 0), "call_pre",
        ["tier3/E532", "tier3/E532"], "main", [1],
        (_MEASURE_CHAR_CODE, [7]), "String index out of bounds"),
    "division, in a measure at a tail call": (
        _MEASURE_DIVISION, ("f(@Nat.2 - 1", 0), "div_zero", ["tier3"],
        "main", [5], (_MEASURE_DIVISION, [0]), "division by zero"),
    "@Nat narrowing, in a requires": (
        _REQUIRES_NAT, ("@Int.0) >= 0", 0), "nat_bind", ["tier3"],
        "f", [5], (_REQUIRES_NAT, [-5]), "Negative value bound"),
    "@Nat narrowing, over a let in a requires": (
        _REQUIRES_LET_NAT, ("@Int.0) >= 0", 0), "nat_bind", ["tier3"],
        "f", [5], (_REQUIRES_LET_NAT, [-5]), "Negative value bound"),
    "@Nat narrowing, in an ensures": (
        _ENSURES_NAT, ("@Int.0) >= 0", 0), "nat_bind", ["tier3"],
        "f", [5], (_ENSURES_NAT, [-5]), "Negative value bound"),
    "refinement narrowing, in a requires": (
        _REQUIRES_REFINEMENT, ("@Int.0) > 0", 0), "refine_bind",
        ["tier3/E506"], "f", [5], (_REQUIRES_REFINEMENT, [-5]),
        "Refinement violation"),
    "float truncation, of a computed value": (
        _COMPUTED_FLOOR, ("floor(", 0), "float_to_int_domain", ["tier3"],
        "f", [2.5], (_COMPUTED_FLOOR, [1e300]),
        "Float64 to Int conversion out of range"),
    # `_check_refined_binding_obligation_term`, the refinement twin of the
    # `@Nat` narrowing above (#1480 review): E505 in a `requires` and an
    # `ensures` on programs that run.  In a body too, where the release
    # branch refused it before this change; one rule for every narrowing.
    **{
        f"refinement narrowing of a sub-pattern, in {where}": (
            _subpattern_over_a_placeholder(slot, _SUBPATTERN_MATCH),
            ("@Option<Int>.0 {", 0), "refine_bind",
            ["tier3/E506"], "main", [5],
            (_subpattern_over_a_placeholder(slot, _SUBPATTERN_MATCH), [-3]),
            "Refinement violation")
        for where, slot in (("a requires", "REQUIRES"),
                            ("an ensures", "ENSURES"), ("a body", "BODY"))
    },
}


@pytest.mark.parametrize("name", list(_PLACEHOLDER_KINDS))
def test_a_check_1480_records_is_not_refused_on_a_placeholder(
        name: str) -> None:
    (src, (needle, occurrence), kind, records, fn, args, (bad_src, bad_args),
     trap) = _PLACEHOLDER_KINDS[name]
    v = _verify(src)
    assert _records(v, kind, _at(src, needle, occurrence)) == records, (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert v.ok, v.errors
    assert _run(src, fn, args).trap_kind is None
    assert trap in _run(bad_src, fn, bad_args).trap_message


#: The other half of the gate: a check refuted for EVERY value the
#: placeholder could take is still refused, by the negated re-ask #1460's
#: refinement gate makes.  name -> (the body over the unknown `@Int.0` in
#: `_UNKNOWN_PRELUDE`'s `f`, the refused text, kind, code).
_REFUTED_FOR_EVERY_VALUE = {
    "call precondition": (
        "string_length(show(need_pos(@Int.0 * 0))) >= 0 || true",
        "need_pos(@Int.0 * 0)", "call_pre", "E501"),
    "built-in domain": (
        'string_length(show(string_char_code("abc", @Int.0 * 0 + 7))) >= 0'
        " || true",
        "string_char_code(", "call_pre", "E501"),
}


@pytest.mark.parametrize("name", list(_REFUTED_FOR_EVERY_VALUE))
def test_a_check_refuted_for_every_placeholder_value_is_refused(
        name: str) -> None:
    body, at, kind, code = _REFUTED_FOR_EVERY_VALUE[name]
    src = (_UNKNOWN_PRELUDE + f"  {body}\n}}\n"
           + _UNKNOWN_MAIN.replace("{state}", "5"))
    v = _verify(src)
    where = _at(src, at)
    assert _records(v, kind, where) == [f"violated/{code}"], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert (code, *where) in v.errors
    assert _run(src, "main", []).trap_kind is not None


def test_a_narrowing_refuted_for_every_placeholder_value_is_refused() -> None:
    src = _REQUIRES_NAT.replace("nat_id(@Int.0)", "nat_id(@Int.0 * 0 - 1)")
    assert src != _REQUIRES_NAT
    v = _verify(src)
    where = _at(src, "@Int.0 * 0 - 1")
    assert _records(v, "nat_bind", where) == ["violated/E503"], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert "Negative value bound" in _run(src, "f", [5]).trap_message


#: A call over a binder the walk reads without its value: E532, with the
#: callee's own check behind it.
_BINDER_POSITIONS = {
    "closure binder": """\
public fn f(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Int -> @Int) effects(pure) { need_pos(@Int.0) }, @Int.0)
    >= 0 || true
}
""",
    "quantifier binder": """\
public fn f(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  forall(@Nat, 3, fn(@Nat -> @Bool) effects(pure) {
    need_pos(nat_to_int(@Nat.0)) >= 0 || true
  })
}
""",
    "handler clause binder": """\
public fn f(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = handle[Exn<Int>] {
    throw(@Int) -> { need_pos(@Int.0) }
  } in {
    throw(-5)
  };
  @Int.0 >= 0 || true
}
""",
}


@pytest.mark.parametrize("position", sorted(_BINDER_POSITIONS))
def test_a_binder_no_assume_can_reach_is_tier3(position: str) -> None:
    src = _NEED_POS + _BINDER_POSITIONS[position]
    v = _verify(src)
    call = _at(src, "need_pos(", 1)
    assert _records(v, "call_pre", call) == ["tier3/E532"], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations], src)
    assert v.ok, v.errors
    assert "need_pos" in _run(src, "f", [-3]).trap_message


# A module-qualified call is obligated by the same walk: an imported
# callee's precondition, in an argument of a built-in the SMT layer does not
# model (E501), and in a closure (E532).
_LIB = """\
public fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""

_MODULE_CALLER = """\
import lib;

public fn nested(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_length(show(lib::need_pos(@Int.0)))
}

public fn in_closure(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Int -> @Int) effects(pure) { lib::need_pos(@Int.0) }, @Int.0)
}
"""


def _cli_json(*args: str) -> tuple[dict, str]:
    import json
    import os
    import subprocess
    import sys

    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    proc = subprocess.run(
        [sys.executable, "-m", "vera.cli", *args], capture_output=True,
        text=True, encoding="utf-8", check=False, env=env, timeout=600)
    out = json.loads(proc.stdout) if args[0] == "verify" else {}
    return out, proc.stdout + proc.stderr


@pytest.mark.parametrize(("fn", "occurrence", "status"), [
    ("nested", 0, "violated/E501"),
    ("in_closure", 1, "tier3/E532"),
])
def test_a_module_call_is_obligated(tmp_path, fn: str, occurrence: int,
                                    status: str) -> None:
    (tmp_path / "lib.vera").write_text(_LIB, encoding="utf-8")
    main = tmp_path / "main.vera"
    main.write_text(_MODULE_CALLER, encoding="utf-8")
    out, _raw = _cli_json("verify", "--json", str(main))
    line, col = _at(_MODULE_CALLER, "lib::need_pos(@Int.0)", occurrence)
    got = sorted(
        f"{o['status']}/{o['error_code']}" if o.get("error_code")
        else o["status"]
        for o in out["obligations"]
        if o["kind"] == "call_pre"
        and (o["location"]["line"], o["location"]["column"]) == (line, col))
    assert got == [status], out["obligations"]
    _out, ran = _cli_json("run", str(main), "--fn", fn, "--", "-3")
    assert "need_pos" in ran, ran


# A binder whose value does not translate is bound to a value the verifier
# cannot know, but a binder DECLARED at a refinement type is not unknown in
# that respect: code generation guards every refined bind (spec §2.6.5)
# before anything in the binder's scope runs, so its predicate holds wherever
# the value can be read.  The strict posture above is for what no guard
# establishes; a precondition the binder's own refinement entails is
# discharged, and a violating value traps at the bind, never at the call.
_REFINED_BINDER_TYPES = """\
type Pos = { @Int | @Int.0 > 0 };
type Idx = { @Int | @Int.0 >= 0 && @Int.0 < 3 };
type Small = { @Pos | @Pos.0 < 10 };
type Impossible = { @Int | @Int.0 > 0 && @Int.0 < 0 };
"""


def _refined_binder_program(sty: str, init: str, body: str) -> str:
    """*body* over a state of type *sty*, whose value no query can read."""
    return (_REFINED_BINDER_TYPES + _NEED_POS + f"""
public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<{sty}>](@{sty} = {init}) {{
    get(@Unit) -> {{ resume(@{sty}.0) }},
    put(@{sty}) -> {{ resume(()) }}
  }} in {{
    {body}
  }}
}}
""")


def _arm(pattern: str, use: str, *others: str) -> str:
    arms = [f"{pattern} -> {use}", *(f"{o} -> 0" for o in others)]
    return "match get(()) {\n      " + ",\n      ".join(arms) + "\n    }"


#: binder position -> (state type, a state inside the binder's refinement,
#: one outside it or None where the state's own type rules that out, the
#: body, and the call whose record is asserted).
_REFINED_BINDERS = {
    "constructor sub-pattern": (
        "Option<Pos>", "Some(5)", None,
        _arm("Some(@Pos)", "need_pos(@Pos.0)", "None"), "need_pos("),
    "narrowing sub-pattern": (
        "Option<Int>", "Some(5)", "Some(-5)",
        _arm("Some(@Pos)", "need_pos(@Pos.0)", "None"), "need_pos("),
    "nested sub-pattern": (
        "Option<Option<Int>>", "Some(Some(5))", "Some(Some(-5))",
        _arm("Some(Some(@Pos))", "need_pos(@Pos.0)", "Some(None)", "None"),
        "need_pos("),
    "tuple sub-pattern": (
        "Option<Tuple<Int, Int>>", "Some(Tuple(5, 7))", "Some(Tuple(-5, 7))",
        _arm("Some(Tuple(@Pos, @Int))", "need_pos(@Pos.0)", "None"),
        "need_pos("),
    "match binding": (
        "Int", "5", "-5", _arm("@Pos", "need_pos(@Pos.0)"), "need_pos("),
    "let": ("Int", "5", "-5", "let @Pos = get(());\n    need_pos(@Pos.0)",
            "need_pos("),
    "destructure": (
        "Tuple<Int, Int>", "Tuple(5, 7)", "Tuple(-5, 7)",
        "let Tuple<@Pos, @Int> = get(());\n    need_pos(@Pos.0)", "need_pos("),
    "call only the walk reaches": (
        "Option<Int>", "Some(5)", "Some(-5)",
        _arm("Some(@Pos)",
             "nat_to_int(string_length(show(need_pos(@Pos.0))))", "None"),
        "need_pos("),
    "built-in domain": (
        "Option<Int>", "Some(1)", "Some(7)",
        _arm("Some(@Idx)", 'string_char_code("abc", @Idx.0)', "None"),
        "string_char_code("),
}


@pytest.mark.parametrize("position", list(_REFINED_BINDERS))
def test_a_refined_binder_carries_its_refinement(position: str) -> None:
    sty, good, bad, body, call = _REFINED_BINDERS[position]
    src = _refined_binder_program(sty, good, body)
    v = _verify(src)
    # A discharged user callee's precondition is not recorded (its check is
    # the callee's prologue); a built-in's domain is, since its check is at
    # the call.
    discharged = ["verified"] if call == "string_char_code(" else []
    # `need_pos(` first occurs in its own declaration.
    where = _at(src, call, 1 if call == "need_pos(" else 0)
    assert _records(v, "call_pre", where) == discharged, (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations], src)
    assert v.ok, v.errors
    assert _run(src, "f", []).trap_kind is None
    if bad is None:
        return
    # The bind's own obligation is over the state, which the fact never
    # mentions: it stays a runtime guard, and that guard is what stops a
    # violating value, before the call can see it.
    bind_line = _at(src, "get(())")[0]
    assert "tier3" in [o.status for o in v.obligations
                       if o.kind == "refine_bind" and o.line == bind_line]
    ran = _run(_refined_binder_program(sty, bad, body), "f", [])
    assert "Refinement violation" in ran.trap_message, ran


#: What the binder's refinement does NOT establish stays unproved: a Tier-3
#: record, since each call here is one only the obligation walk reaches and
#: its value is a placeholder, never a discharge.  position -> (state type,
#: state, body, the call or assertion, its kind, and the record).
_REFINED_BINDER_CONTROLS = {
    "unrefined binder": (
        "Option<Int>", "Some(5)",
        _arm("Some(@Int)", "need_pos(@Int.0)", "None"), "need_pos(",
        "call_pre", ["tier3/E532"]),
    "refinement over a refinement": (
        "Option<Small>", "Some(5)",
        _arm("Some(@Small)", "need_pos(@Small.0)", "None"), "need_pos(",
        "call_pre", ["tier3/E532"]),
    "a goal beyond the refinement": (
        "Option<Int>", "Some(5)",
        _arm("Some(@Pos)", "{ assert(@Pos.0 < 10); 1 }", "None"), "assert(",
        "assert", ["tier3/E535"]),
    "a call outside an empty refinement's arm": (
        "Option<Int>", "None",
        "let @Int = " + _arm("Some(@Impossible)", "1", "None")
        + ";\n    need_pos(@Int.0)", "need_pos(@Int.0)",
        "call_pre", ["tier3/E532"]),
    # Code generation does not guard a bind of a refinement over a
    # refinement (`_emit_bind_refine_guard`), so nothing establishes the
    # predicate there: the second `let` shadows the first, and a violating
    # state reaches the call.
    "a refinement whose bind has no guard": (
        "Int", "-5",
        "let @Small = 5;\n    let @Small = get(());\n    need_pos(@Small.0)",
        "need_pos(", "call_pre", ["tier3/E532"]),
}


@pytest.mark.parametrize("position", list(_REFINED_BINDER_CONTROLS))
def test_what_a_binders_refinement_does_not_establish(position: str) -> None:
    sty, init, body, at, kind, want = _REFINED_BINDER_CONTROLS[position]
    src = _refined_binder_program(sty, init, body)
    v = _verify(src)
    occurrence = 1 if at == "need_pos(" else 0
    assert _records(v, kind, _at(src, at, occurrence)) == want, (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations], src)
    if position == "a refinement whose bind has no guard":
        assert "need_pos" in _run(src, "f", []).trap_message


# ---------------------------------------------------------------------
# A narrowing arm binder under a scrutinee that DOES translate
# ---------------------------------------------------------------------
#
# The binder would read the projection of the scrutinee, which is what the
# bind's own obligation is over, so the predicate cannot be recorded on it
# without proving the guard from itself.  It is bound to a fresh value equal
# to the projection instead, and that value's predicate is given only to a
# query that reads it (`ContractVerifier._guarded_binder_values`).

_MK_NARROWING = """\
type Pos = { @Int | @Int.0 > 0 };
type Idx = { @Int | @Int.0 >= 0 && @Int.0 < 3 };
type Small = { @Pos | @Pos.0 < 10 };
""" + _NEED_POS + """
private fn mk(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0 - 5)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(POST)
  effects(pure)
{
  match mk(@Int.0) {
    PATTERN -> USE,
    None -> 1
  }
}
"""


def _mk_narrowing(post: str, pattern: str, use: str) -> str:
    return (_MK_NARROWING.replace("POST", post)
            .replace("PATTERN", pattern).replace("USE", use))

_LET_NARROWING = """\
type Pos = { @Int | @Int.0 > 0 };
""" + _NEED_POS + """
public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Option<Int>>>)
{
  let @Option<Int> = get(());
  match @Option<Int>.0 {
    Some(@Pos) -> need_pos(@Pos.0),
    None -> 0
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = STATE) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    f(())
  }
}
"""


def test_a_let_bound_scrutinees_narrowing_binder_carries_its_refinement(
) -> None:
    """The coordinator's program: the scrutinee is a `let`'s placeholder,
    which translates, so the binder is a projection of it.  The call cannot
    fail, because the bind is guarded before the arm runs; the bind's own
    obligation stays the runtime guard, `tier3`, never proved."""
    src = _LET_NARROWING.replace("STATE", "Some(5)")
    v = _verify(src)
    assert _records(v, "call_pre", _at(src, "need_pos(", 1)) == []
    assert v.ok, v.errors
    bind = [o.status for o in v.obligations if o.kind == "refine_bind"
            and o.line == _at(src, "match @Option<Int>.0")[0]]
    assert bind == ["tier3"], bind
    assert _run(src, "main", []).value == 5
    bad = _run(_LET_NARROWING.replace("STATE", "Some(-5)"), "main", [])
    assert "Refinement violation" in bad.trap_message, bad


#: arm -> (pattern, what the arm does with the binder, the text its record
#: is located at, the record's kind, and the record once discharged).
_MK_ARMS = {
    "call": ("Some(@Pos)", "need_pos(@Pos.0)", "need_pos(@Pos.0)",
             "call_pre", []),
    "call only the walk reaches": (
        "Some(@Pos)", "nat_to_int(string_length(show(need_pos(@Pos.0))))",
        "need_pos(@Pos.0)", "call_pre", []),
    "built-in domain": (
        "Some(@Idx)", 'nat_to_int(string_char_code("abc", @Idx.0))',
        "string_char_code(", "call_pre", ["verified"]),
    "assertion": ("Some(@Pos)", "{ assert(@Pos.0 > 0); 1 }", "assert(",
                  "assert", ["verified"]),
}


@pytest.mark.parametrize("arm", list(_MK_ARMS))
def test_a_call_scrutinees_narrowing_binder_carries_its_refinement(
        arm: str) -> None:
    """`match mk(..)`: the arm's use of the binder is discharged, and the
    bind's own obligation is still refuted (E505: `mk`'s contract does not
    say its payload is positive), because it reads the projection and never
    the fresh value.  A payload the refinement forbids traps at the bind."""
    pattern, use, at, kind, record = _MK_ARMS[arm]
    src = _mk_narrowing("true", pattern, use)
    v = _verify(src)
    assert _records(v, kind, _at(src, at)) == record, (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations], src)
    match_line = _at(src, "match mk(")[0]
    assert [(e[0], e[1]) for e in v.errors] == [("E505", match_line)], (
        v.errors)
    assert _run(src, "f", [6]).trap_kind is None
    assert "Refinement violation" in _run(src, "f", [2]).trap_message


def test_a_postcondition_over_what_the_arm_returns_reads_the_refinement(
) -> None:
    """The fresh value outlives the arm inside the `match`'s own value, where
    its fact is guarded by the arm being taken: returned through the arm, it
    is positive, since a payload that is not traps at the bind."""
    src = _mk_narrowing("@Int.result > 0", "Some(@Pos)", "@Pos.0")
    v = _verify(src)
    assert _records(v, "ensures", _at(src, "ensures(@Int.result")) == [
        "verified"]
    assert _run(src, "f", [6]).value == 1


#: Where the arm's bind does NOT run, its binder's predicate must say
#: nothing.  Each postcondition is false, and each program returns a value
#: that breaks it: name -> (the program, the call, its argument).
_UNTAKEN_ARM_CONTROLS = {
    # The fact is guarded by the path to the `match`: the other branch reads
    # the same payload unrefined.
    "another branch": ("""\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Bool, @Option<Int> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  if @Bool.0 then {
    match @Option<Int>.0 {
      Some(@Pos) -> @Pos.0,
      None -> 1
    }
  } else {
    match @Option<Int>.0 {
      Some(@Int) -> @Int.0,
      None -> 1
    }
  }
}

public fn g(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(false, Some(0 - 3))
}
""", "g"),
    # ... and by no earlier arm matching.
    "an earlier arm": ("""\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Option<Int> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    Some(@Pos) -> @Pos.0,
    None -> 1
  }
}

public fn g(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(Some(0 - 3))
}
""", "g"),
    # A nested pattern's If-chain condition is its outer constructor alone,
    # which holds of `Some(None)` too, so its arm binds no fresh value.
    "a nested pattern": ("""\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Option<Option<Int>> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Option<Option<Int>>.0 {
    Some(Some(@Pos)) -> @Pos.0,
    Some(None) -> 0 - 7,
    None -> 1
  }
}

public fn g(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(Some(None))
}
""", "g"),
}


def test_a_binder_whose_bind_has_no_guard_carries_nothing() -> None:
    """Code generation does not guard the bind of a refinement over a
    refinement, so its binder is left the projection: the call stays
    refuted, and a violating payload reaches the callee's own check."""
    src = _mk_narrowing("true", "Some(@Small)", "need_pos(@Small.0)")
    v = _verify(src)
    assert _records(v, "call_pre", _at(src, "need_pos(@Small.0)")) == [
        "violated/E501"]
    assert "need_pos" in _run(src, "f", [2]).trap_message


@pytest.mark.parametrize("name", list(_UNTAKEN_ARM_CONTROLS))
def test_an_untaken_arms_refinement_says_nothing(name: str) -> None:
    src, fn = _UNTAKEN_ARM_CONTROLS[name]
    v = _verify(src)
    assert _records(v, "ensures", _at(src, "ensures(@Int.result")) == [
        "violated"], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert "Postcondition violation" in _run(src, fn, []).trap_message


# Where an ENCLOSING `match`'s arm does not run (#1480 review).  The fact is
# guarded by what under-approximates the arm's bind running: each enclosing
# arm's own condition AND no earlier arm's, and nothing under an arm whose
# condition is inexact (a nested pattern's is its outer constructor alone,
# #1562).  Guarded by the path conditions instead, which hold an enclosing
# arm's own condition only, each `ensures` below was `verified` and each run
# fails it: the first arm returns the payload the second arm's `@Pos` binds.
_ENCLOSING = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@SCRUT, @Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Option<Int> = apply_fn(fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0) }, @Int.0);
  match @SCRUT.0 {
    FIRST -> match @Option<Int>.0 {
      Some(@FIRST_T) -> @FIRST_T.0,
      None -> 1
    },
    SECOND -> match @Option<Int>.0 {
      Some(@SECOND_T) -> @SECOND_T.0,
      None -> 1
    },
    LAST -> 1
  }
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(ARG, @Int.0)
}
"""


def _enclosing(**slots: str) -> str:
    src = _ENCLOSING
    for slot in ("SCRUT", "FIRST_T", "SECOND_T", "FIRST", "SECOND", "LAST",
                 "ARG"):
        src = src.replace(slot, slots[slot])
    return src


_OO = "Option<Option<Bool>>"
_ENCLOSING_ARM_CONTROLS = {
    "an earlier enclosing arm with a nested pattern": _enclosing(
        SCRUT=_OO, FIRST="Some(Some(@Bool))", FIRST_T="Int",
        SECOND="Some(@Option<Bool>)", SECOND_T="Pos", LAST="None",
        ARG="Some(Some(true))"),
    "a repeated enclosing arm": _enclosing(
        SCRUT="Bool", FIRST="true", FIRST_T="Int", SECOND="true",
        SECOND_T="Pos", LAST="false", ARG="true"),
    "an enclosing arm with a nested pattern": _enclosing(
        SCRUT=_OO, FIRST="Some(Some(@Bool))", FIRST_T="Pos",
        SECOND="Some(None)", SECOND_T="Int", LAST="None",
        ARG="Some(None)"),
}


@pytest.mark.parametrize("name", list(_ENCLOSING_ARM_CONTROLS))
def test_an_enclosing_arm_that_does_not_run_says_nothing(name: str) -> None:
    src = _ENCLOSING_ARM_CONTROLS[name]
    v = _verify(src)
    assert _records(v, "ensures", _at(src, "ensures(@Int.result")) == [
        "tier3/E522"], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert _run(src, "main", [3]).value == 3
    assert "Postcondition violation" in _run(src, "main", [-3]).trap_message


#: The fact still reaches past an enclosing arm that runs: the earlier arm's
#: condition is disjoint from it, so the postcondition over the payload is
#: proved, and a payload the refinement forbids traps at the bind.
_ENCLOSING_ARM_TAKEN = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Option<Option<Bool>>, @Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Option<Int> = apply_fn(fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0) }, @Int.0);
  match @Option<Option<Bool>>.0 {
    None -> 1,
    Some(@Option<Bool>) -> match @Option<Int>.0 {
      Some(@Pos) -> @Pos.0,
      None -> 1
    }
  }
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(Some(Some(true)), @Int.0)
}
"""


def test_an_enclosing_arm_that_runs_keeps_the_fact() -> None:
    src = _ENCLOSING_ARM_TAKEN
    v = _verify(src)
    assert _records(v, "ensures", _at(src, "ensures(@Int.result")) == [
        "verified"]
    assert _run(src, "main", [3]).value == 3
    assert "Refinement violation" in _run(src, "main", [-3]).trap_message


#: A `match` in `&&`'s right operand binds whichever the left operand is,
#: because the reference compiler evaluates both operands (#1501), so its
#: fact needs no left operand in its antecedent, and the postcondition is
#: proved.  PINNED: once `&&` short-circuits, `main(false, -3)` skips the
#: bind and fails the postcondition, and the antecedent needs the left
#: operand (`SmtContext._arm_guarded_binders`).
_AND_RIGHT_OPERAND = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Bool, @Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Option<Int> = apply_fn(fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0) }, @Int.0);
  let @Bool = @Bool.0 && match @Option<Int>.0 {
    Some(@Pos) -> @Pos.0 > 0,
    None -> true
  };
  match @Option<Int>.0 {
    Some(@Int) -> if @Bool.0 then { @Int.0 } else { @Int.0 },
    None -> 1
  }
}

public fn main(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(@Bool.0, @Int.0)
}
"""


def test_a_match_in_a_right_operand_binds_whatever_the_left_is() -> None:
    src = _AND_RIGHT_OPERAND
    v = _verify(src)
    assert _records(v, "ensures", _at(src, "ensures(@Int.result")) == [
        "verified"]
    assert _run(src, "main", [0, 3]).value == 3
    assert "Refinement violation" in _run(src, "main", [0, -3]).trap_message


#: A `match` in an `if` condition is evaluated before either branch, so its
#: binder's fact reaches the branch the condition selects.
_MATCH_IN_A_CONDITION = """\
type Pos = { @Int | @Int.0 > 0 };
""" + _NEED_POS + """
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Int> = apply_fn(fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0) }, @Int.0);
  if match @Option<Int>.0 { Some(@Pos) -> @Pos.0 < 100, None -> false } then {
    match @Option<Int>.0 {
      Some(@Int) -> need_pos(@Int.0),
      None -> 0
    }
  } else {
    0
  }
}
"""


def test_a_match_in_a_condition_carries_its_fact_into_the_branch() -> None:
    src = _MATCH_IN_A_CONDITION
    v = _verify(src)
    assert _records(v, "call_pre", _at(src, "need_pos(@Int.0)")) == []
    assert v.ok, v.errors
    assert _run(src, "f", [5]).value == 5
    assert "Refinement violation" in _run(src, "f", [-3]).trap_message


# An ASSUMED contract's `match` (#1480 review).  The contract is asserted
# into the solver, and a fresh binder's fact reaches only a query that reads
# the fresh value, which no later query about the payload does: each of these
# was refused at the review's head, and each verifies at `main`.  An
# assumption is stated over the projections (`SmtContext.assume`).
_MK_GT5 = """\
type Pos = { @Int | @Int.0 > 0 };

private fn need_gt5(@Int -> @Int)
  requires(@Int.0 > 5)
  ensures(true)
  effects(pure)
{
  @Int.0
}

private fn mk(@Int -> @Option<Int>)
  requires(true)
  ensures(match @Option<Int>.result {
    Some(@Pos) -> @Pos.0 > 5,
    None -> true
  })
  effects(pure)
{
  if @Int.0 > 5 then {
    Some(@Int.0)
  } else {
    None
  }
}
"""

_ASSUMED_CONTRACTS = {
    "a callee's ensures, at a call": (_MK_GT5 + """
public fn use_it(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mk(@Int.0) {
    Some(@Int) -> need_gt5(@Int.0),
    None -> 0
  }
}
""", "use_it", "call_pre", ("need_gt5(@Int.0)", 0), []),
    "a callee's ensures, under the caller's ensures": (_MK_GT5 + """
public fn use_it(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 5 || @Int.result == 0)
  effects(pure)
{
  match mk(@Int.0) {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
""", "use_it", "ensures", ("ensures(@Int.result", 0), ["verified"]),
    "the function's own requires": (_MK_GT5 + """
public fn f(@Option<Int> -> @Int)
  requires(match @Option<Int>.0 {
    Some(@Int) -> @Int.0 > 0,
    None -> true
  })
  requires(match @Option<Int>.0 {
    Some(@Pos) -> @Pos.0 > 5,
    None -> true
  })
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> need_gt5(@Int.0),
    None -> 0
  }
}

public fn use_it(@Int -> @Int)
  requires(@Int.0 > 5)
  ensures(true)
  effects(pure)
{
  f(Some(@Int.0))
}
""", "use_it", "call_pre", ("need_gt5(@Int.0)", 0), []),
}


@pytest.mark.parametrize("name", list(_ASSUMED_CONTRACTS))
def test_an_assumed_contract_states_its_binders_projection(name: str) -> None:
    src, fn, kind, (at, occurrence), want = _ASSUMED_CONTRACTS[name]
    v = _verify(src)
    assert v.ok, v.errors
    assert _records(v, kind, _at(src, at, occurrence)) == want, (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert _run(src, fn, [7]).value == 7


#: The gate's other half at the sub-pattern twin: a bind refuted for every
#: value the placeholder could take is refused.
def test_a_subpattern_bind_refuted_for_every_value_is_refused() -> None:
    # The payload is -1 whichever arm of the inner scrutinee runs, and the
    # projection still embeds the placeholder, so the gate asks, and the
    # negated re-ask refuses.
    constant = ("match (match @Option<Int>.0 { Some(@Int) -> "
                "Some(@Int.0 * 0 - 1), None -> Some(@Int.0 * 0 - 1) }) {")
    match = _SUBPATTERN_MATCH.replace("match @Option<Int>.0 {", constant)
    src = _subpattern_over_a_placeholder("REQUIRES", match)
    assert constant in src
    v = _verify(src)
    where = _at(src, "Some(@Option<Int>) -> match")
    assert ("E505", where[0]) in [(c, line) for c, line, _ in v.errors], (
        v.errors)
    assert "Refinement violation" in _run(src, "main", [5]).trap_message


#: `_check_nested_refinement_obligation`, the third refinement narrowing (a
#: payload a call argument's type refines), behind the same gate.  Its site
#: has no guard (spec §6.4.3), so the placeholder leaves it disclosed rather
#: than Tier 3: `tier3_unguarded`, and a violating payload runs unchecked.
_NESTED_OVER_A_PLACEHOLDER = """\
type Pos = { @Int | @Int.0 > 0 };

private fn takes(@Option<Pos> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  true
}

public fn f(@Option<Int>, @Int -> @Bool)
  requires(match map_get(map_insert(map_new(), 1, Some(@Int.0)), 1) {
    Some(@Option<Int>) -> takes(@Option<Int>.0),
    None -> true
  })
  ensures(true)
  effects(pure)
{
  true
}

public fn main(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(None, @Int.0)
}
"""


def test_a_nested_refinement_over_a_placeholder_is_disclosed() -> None:
    src = _NESTED_OVER_A_PLACEHOLDER
    v = _verify(src)
    assert _records(v, "refine_bind", _at(src, "@Option<Int>.0)")) == [
        "tier3_unguarded/E506"], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert v.ok, v.errors
    assert _run(src, "main", [-3]).trap_kind is None


# ---------------------------------------------------------------------
# The refinement predicate, at every guard position
# ---------------------------------------------------------------------
#
# One evaluation root (`_emit_refinement_check`) reached from every position
# a §2.6.5 guard is planted at.  The positions are the routes the #1466
# instrument holds to `binders.GUARD_SITES`, so a guard position added there
# is added here.  The predicate is obligated ONCE, at the `type R` line, and
# the cells assert that: a record there with the cell's status, and none of
# the operation's kind anywhere else — whatever the route, the obligation is
# the declaration's.

from tests.test_boundary_guard_correctness_1466 import (  # noqa: E402
    _ALL_ROUTES,
    _Instance,
)


def _predicate_cell(op: Op, status: str, route: object) -> Cell:
    premise, value, _lit, _arg = _variant(op, status)
    b = f"@{op.base}.0"
    probe = f"{value.format(v=b)} >= 0 || true"
    predicate = (
        probe if premise == "true"
        else f"if {premise.format(v=b)} then {{ {probe} }} else {{ true }}"
    )
    decls = f"type R = {{ @{op.base} | {predicate} }};\n" + op.helpers
    # The value the guard is handed.  Outside the domain in every cell: a
    # `verified` predicate must accept it (its `if` keeps the operation from
    # being evaluated), and a `violated` or `tier3` one must trap on it.
    x = _Instance(decls, op.bad, op.base, op.good)
    source = route.build(x)  # type: ignore[attr-defined]
    return Cell(source, op.kind, status, op.code,
                at=value.format(v=b), at_offset=op.offset,
                pre_text=op.pre_text,
                trap=None if status == "verified" else _any_trap,
                absent_when_discharged=not op.records_discharge)


def _route_cells() -> list[object]:
    cells = []
    for position, routes in _ALL_ROUTES.items():
        for route in routes:
            for op in _OPS:
                for status in op.statuses():
                    name = f"{position}[{route.name}]" if route.name \
                        else position
                    cells.append(pytest.param(
                        op, status, route,
                        id=f"predicate at {name}|{op.name}|{status}"))
    return cells


def _check_predicate_cell(cell: Cell) -> None:
    v = _check_cell(cell)
    decl_line = _at(cell.source, "type R")[0]
    stray = [
        (o.kind, o.status, o.line, o.column) for o in v.obligations
        if o.kind == cell.kind and o.line != decl_line
        and (not cell.pre_text or o.expr_text == cell.pre_text)
    ]
    assert not stray, (
        f"the predicate's obligation was repeated at a use site: {stray}")


@pytest.mark.parametrize(("op", "status", "route"), _route_cells())
def test_predicate_cell(op: Op, status: str, route: object) -> None:
    _check_predicate_cell(_predicate_cell(op, status, route))


# ---------------------------------------------------------------------
# The positions are code generation's evaluation roots
# ---------------------------------------------------------------------

import ast as _pyast  # noqa: E402

from tests import guard_emitter_scan  # noqa: E402
from vera import binders  # noqa: E402
from vera.builtin_domains import BUILTIN_DOMAINS  # noqa: E402

#: Every place code generation hands a SOURCE expression to the translator —
#: an evaluation root — and the matrix position it is.  Everything the
#: compiled program evaluates is reached from one of these (the translator
#: recurses from there), so a root with no position is an evaluated
#: expression no walk is held to, which is the class #1480 is.
_ROOTS: dict[tuple[str, str, str], str] = {
    ("functions.py", "_compile_fn", "decl.body"): "body",
    # A closure body is walked by the body walks' fresh-scope descent (#779).
    ("closures.py", "_compile_lifted_closure", "anon_fn.body"): "body",
    ("contracts.py", "_compile_preconditions", "contract.expr"): "requires",
    ("contracts.py", "_compile_postconditions", "ensures.expr"): "ensures",
    ("contracts.py", "_dec_translate_measure", "expr"): "measure",
    # The range check where the chain guard is declined (#1222).
    ("contracts.py", "_dec_bound_checks_only", "contract.exprs[k]"):
        "measure at entry",
    ("contracts.py", "_emit_refinement_check", "predicate"):
        "refinement predicate",
}

#: `_dec_translate_measure` is reached from two places, which are two
#: positions: the entry check, and a self-recursive tail call's site check.
#: A NON-tail call reaches the callee's entry check, after its `requires` —
#: the matrix's "measure at a non-tail call" position is that root, reached
#: that way.
_MEASURE_CALLERS: dict[str, str] = {
    "_compile_decreases_entry": "measure at entry",
    "_dec_self_tail_prefix": "measure at a tail call",
}


def _codegen_calls(method: str) -> set[tuple[str, str, str]]:
    """``(file, enclosing function, first argument)`` of every call to a
    method named *method*, on any receiver, in the code-generation DRIVER
    (`vera/codegen/`), enumerated as `guard_emitter_scan` enumerates it.

    The receiver is not read: a root is a call that hands a source
    expression to the translator, whatever the variable holding the
    translator is called.  The translator's own recursion, in `vera/wasm/`,
    descends from those roots and is not one.
    """
    found: set[tuple[str, str, str]] = set()
    for path in guard_emitter_scan.codegen_sources():
        if path.parent.name != "codegen":
            continue
        tree = _pyast.parse(path.read_text(encoding="utf-8"))
        for fn in _pyast.walk(tree):
            if not isinstance(fn, (_pyast.FunctionDef,
                                   _pyast.AsyncFunctionDef)):
                continue
            for node in _pyast.walk(fn):
                if (isinstance(node, _pyast.Call)
                        and isinstance(node.func, _pyast.Attribute)
                        and node.func.attr == method):
                    first = (_pyast.unparse(node.args[0])
                             if node.args else "")
                    found.add((path.name, fn.name, first))
    return found


def test_every_evaluation_root_is_a_position() -> None:
    """The roster above IS code generation's set of roots, both ways.

    A root added to code generation without a position here reddens this
    cell, and so does a roster entry whose root is gone.
    """
    found = (_codegen_calls("translate_expr")
             | _codegen_calls("translate_block"))
    assert found == set(_ROOTS), (
        f"unrostered roots: {sorted(found - set(_ROOTS))}; "
        f"stale entries: {sorted(set(_ROOTS) - found)}")
    callers = {fn for _f, fn, _a in _codegen_calls(
        "_dec_translate_measure")}
    assert callers == set(_MEASURE_CALLERS), callers


def test_every_position_is_reached_from_a_root() -> None:
    """Each position the matrix crosses is an evaluation root, and each
    root's position is one the matrix crosses."""
    positions = {p for p in _ROOTS.values() if p != "measure"} | set(
        _MEASURE_CALLERS.values())
    crossed = (set(_POSITIONS) - {"measure at a non-tail call"}) | {
        "refinement predicate"}
    assert positions == crossed, (positions ^ crossed)


def test_the_predicate_is_crossed_with_every_guard_position() -> None:
    """The refinement-predicate root is reached from every guard position,
    and the routes this file borrows cover `binders.GUARD_SITES`."""
    assert set(binders.GUARD_SITES) <= set(_ALL_ROUTES)


def test_every_declared_domain_is_an_operation() -> None:
    """A built-in given a domain has a row on the operation axis.

    The axis reads what the compiler declares, so a domain added to
    `vera.builtin_domains` without a matrix row reddens here.
    """
    ops = {op.name for op in _OPS}
    declared = {d.name for d in BUILTIN_DOMAINS}
    assert declared <= ops, declared - ops
    from vera.verifier import _FLOAT_CONVERSIONS
    assert set(_FLOAT_CONVERSIONS) <= ops, set(_FLOAT_CONVERSIONS) - ops


# ---------------------------------------------------------------------
# Wiring: the refusals, and the solver's assumptions (#1480 review)
# ---------------------------------------------------------------------
#
# Derived from the code, not listed by hand: each scan below enumerates a
# construct in the verifier's two modules, and the table beside it says what
# keeps that construct honest.  A new site reddens the scan until it is
# classified.


def _enclosing_functions(path: str, is_site: object) -> dict[str, str]:
    """Each call *is_site* accepts in *path*, keyed by its innermost
    enclosing function, with that function's source."""
    import pathlib

    text = (pathlib.Path(__file__).resolve().parent.parent / path).read_text(
        encoding="utf-8")
    tree = _pyast.parse(text)
    parents: dict[object, object] = {}
    for node in _pyast.walk(tree):
        for child in _pyast.iter_child_nodes(node):
            parents[child] = node
    found: dict[str, str] = {}
    for node in _pyast.walk(tree):
        if isinstance(node, _pyast.Call) and is_site(node):  # type: ignore[operator]
            up = parents.get(node)
            while up is not None and not isinstance(up, _pyast.FunctionDef):
                up = parents.get(up)
            assert isinstance(up, _pyast.FunctionDef), _pyast.unparse(node)
            found[up.name] = _pyast.unparse(up)
    return found


def _records_violated(node: object) -> bool:
    f = node.func  # type: ignore[attr-defined]
    args = node.args  # type: ignore[attr-defined]
    return (isinstance(f, _pyast.Attribute) and f.attr == "_record_obligation"
            and len(args) > 3 and isinstance(args[3], _pyast.Constant)
            and args[3].value == "violated")


#: Every site that records `violated`, and why a placeholder cannot make it
#: refuse (the ruling: a check #1480 records falls to Tier 3 when it is
#: refuted only over a value the verifier cannot state, unless it is refuted
#: for every such value).  "gate": `_refuted_only_over_a_placeholder` or the
#: opaque-shadow re-ask; "two-check": refused only when the violation itself
#: is valid, i.e. for every value; "no placeholder": a position #1480 records
#: nothing at, or a literal value.
_VIOLATED_SITES = {
    "_verify_fn": "no placeholder: the function's own `ensures` and "
                  "refined return, recorded before #1480",
    "_check_decreases_bound": "two-check",
    "_record_call_obligations": "gate: SmtContext._rests_on_unknown",
    "_check_state_decl_divergence": "no placeholder: a handler's state",
    "_check_subtraction_obligation": "gate",
    "_check_div_zero_obligation": "gate",
    "_check_assert_obligation": "two-check",
    "_check_index_bounds_obligation": "two-check",
    "_check_overflow_obligation": "two-check",
    "_check_float_to_int_domain_obligation": "no placeholder: a constant",
    "_check_nat_binding_obligation": "gate",
    "_check_nat_binding_obligation_term": "gate",
    "_check_int_widening_obligation": "two-check",
    "_check_int_widening_obligation_term": "two-check",
    "_check_refined_binding_obligation": "gate",
    "_check_nested_refinement_obligation": "gate",
    "_reject_or_excuse_concrete_violation": "no placeholder: a literal",
    "_check_generic_refined_return": "no placeholder: a generic's return",
    "_check_refined_binding_obligation_term": "gate",
}


def test_every_refusal_is_classified_against_a_placeholder() -> None:
    sites = _enclosing_functions("vera/verifier.py", _records_violated)
    assert set(sites) == set(_VIOLATED_SITES), set(sites) ^ set(
        _VIOLATED_SITES)
    for name, how in _VIOLATED_SITES.items():
        source = sites[name]
        if how == "gate":
            assert ("_refuted_only_over_a_placeholder(" in source
                    or "_contains_opaque_shadow(" in source), name
        elif how == "two-check":
            assert source.count("check_valid(") >= 2, name
    # The call-site refusals are built in the SMT layer, each behind the
    # placeholder test.
    calls = _enclosing_functions(
        "vera/smt.py",
        lambda n: isinstance(n.func, _pyast.Name)
        and n.func.id == "CallViolation")
    assert set(calls) == {"_check_builtin_domain",
                          "_check_call_preconditions"}, set(calls)
    assert all("_rests_on_unknown(" in s for s in calls.values())


def _adds_to_the_solver(node: object) -> bool:
    f = node.func  # type: ignore[attr-defined]
    return (isinstance(f, _pyast.Attribute) and f.attr == "add"
            and isinstance(f.value, _pyast.Attribute)
            and f.value.attr == "solver")


def test_every_assumption_is_stated_over_the_projections() -> None:
    """The solver's base context is written only by `SmtContext.assume`,
    which states a guarded binder's fresh value as its projection; the other
    writers are queries, inside their own push/pop."""
    writers = {
        **{f"smt.{k}": v for k, v in _enclosing_functions(
            "vera/smt.py", _adds_to_the_solver).items()},
        **{f"verifier.{k}": v for k, v in _enclosing_functions(
            "vera/verifier.py", _adds_to_the_solver).items()},
    }
    assert set(writers) == {"smt.assume", "smt._check_refutation",
                            "verifier._full_premises_satisfiable"}, set(
        writers)
    for query in ("smt._check_refutation",
                  "verifier._full_premises_satisfiable"):
        assert "solver.push()" in writers[query], query


# ---------------------------------------------------------------------
# The char-code measure at the i64 bound the runtime compares in
# ---------------------------------------------------------------------
#
# `_MEASURE_CHAR_CODE`'s measure is a `@Nat` sum, and the termination guard
# compares a `@Nat` measure in signed i64 (`decreases_bound`, E536): a sum
# just below i64.MAX runs, one just above it traps on entry.  Neither side is
# provable of an unconstrained `@Nat`, so the bound is Tier 3.  The state is
# `None`, so the function returns after the entry check rather than counting
# down from 2^63.

_MEASURE_CHAR_CODE_AT_THE_BOUND = _MEASURE_CHAR_CODE.split(
    "public fn main")[0] + """public fn main(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = None) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    f(@Nat.0, 1)
  }
}
"""

_I64_MAX = 2**63 - 1


@pytest.mark.parametrize(("nat", "traps"), [
    (_I64_MAX - ord("b"), False),
    (_I64_MAX - ord("b") + 1, True),
])
def test_the_char_code_measure_at_the_i64_bound(nat: int, traps: bool) -> None:
    src = _MEASURE_CHAR_CODE_AT_THE_BOUND
    v = _verify(src)
    assert _records(v, "decreases_bound", _at(src, "@Nat.0 + string_char_code")
                    ) == ["tier3"], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert v.ok, v.errors
    ran = _run(src, "main", [nat])
    if traps:
        assert "outside the i64 range" in ran.trap_message, ran
    else:
        assert ran.value == 0, ran


# =====================================================================
# The facts a walk carries: an earlier statement's, an earlier arm's
# =====================================================================
#
# A check the obligation walks record is decided under the facts that hold
# where the compiled program makes it, which are the facts the body's own
# translation reads there.  Two of them were missing from the walks, and
# each refused programs that run clean on every input.
#
# * A bare `assert` or `assume` makes its predicate hold for the rest of
#   its block (#804).  The recursive-call walk never added it, so the
#   measure a self-recursive tail call evaluates was checked without it.
# * A `match` arm runs only when no earlier arm matched.  No walk added
#   that, so an arm selected by it lost the fact that selects it: a call's
#   precondition, a `@Nat` subtraction, a division or a narrowing in a `_`
#   arm after a literal arm was refused (#1576).  Only an EXACT earlier
#   condition is negated.  A nested pattern's condition is its outer
#   constructor alone (#1562), so its negation would also exclude values
#   that do reach the later arm.

# The measure a tail call evaluates, `@Nat.1 - (@Nat.0 + 1)`, needs
# `@Nat.0 < @Nat.1`, and only the statement before the call says so: the
# branch condition goes through a closure, which the SMT layer cannot read.
_STEP_AFTER_A_STATEMENT = """\
private fn step(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  decreases(@Nat.1 - @Nat.0)
  effects(pure)
{
  if apply_fn(fn(@Nat -> @Bool) effects(pure) { @Nat.0 > 0 }, @Nat.1 - @Nat.0) then {
    STMT(@Nat.0 < @Nat.1);
    step(@Nat.1, @Nat.0 + 1)
  } else {
    @Nat.0
  }
}

public fn main(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  step(@Nat.0, 0)
}
"""

# The same statement at the top of the body.  The branch condition is the
# value the closure returned, which the statement relates to the parameters.
_STEP_AFTER_A_TOP_LEVEL_STATEMENT = """\
private fn step(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  decreases(@Nat.1 - @Nat.0)
  effects(pure)
{
  let @Bool = apply_fn(fn(@Nat -> @Bool) effects(pure) { @Nat.0 > 0 }, @Nat.1 - @Nat.0);
  STMT(@Bool.0 == (@Nat.0 < @Nat.1));
  if @Bool.0 then {
    step(@Nat.1, @Nat.0 + 1)
  } else {
    @Nat.0
  }
}

public fn main(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  step(@Nat.0, 0)
}
"""


@pytest.mark.parametrize("stmt", ["assert", "assume"])
@pytest.mark.parametrize("shape", [_STEP_AFTER_A_STATEMENT,
                                   _STEP_AFTER_A_TOP_LEVEL_STATEMENT],
                         ids=["nested", "top_level"])
def test_a_tail_measure_reads_the_statements_before_it(
        shape: str, stmt: str) -> None:
    src = shape.replace("STMT", stmt)
    v = _verify(src)
    assert _records(v, "nat_sub", _at(src, "step(@Nat.1")) == ["verified"], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert v.ok, v.errors
    assert _run(src, "main", [5]).value == 5


# The statement in the OTHER branch says nothing about this one.  Here the
# tail call runs exactly when `@Nat.0 == @Nat.1`, so its measure underflows,
# and a fact carried out of the sibling branch would prove it.
_STEP_AFTER_A_SIBLING_STATEMENT = """\
private fn step(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  decreases(@Nat.1 - @Nat.0)
  effects(pure)
{
  if apply_fn(fn(@Nat -> @Bool) effects(pure) { @Nat.0 > 0 }, @Nat.1 - @Nat.0) then {
    assert(@Nat.0 < @Nat.1);
    @Nat.0
  } else {
    step(@Nat.1, @Nat.0 + 1)
  }
}

public fn main(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  step(@Nat.0, @Nat.0)
}
"""


def test_a_statement_in_a_sibling_branch_says_nothing_at_a_tail_call() -> None:
    src = _STEP_AFTER_A_SIBLING_STATEMENT
    v = _verify(src)
    tail = _at(src, "step(@Nat.1")
    assert _records(v, "nat_sub", tail) == ["violated/E502"]
    ran = _run(src, "main", [5])
    assert ran.trap_kind is not None, ran
    assert "Precondition violation" not in ran.trap_message, ran


_NEED_POS_DECL = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}

"""

_UNWRAP_DECL = """\
private fn unwrap(@Option<Int> -> @Int)
  requires(match @Option<Int>.0 { Some(@Int) -> true, None -> false })
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}

"""


@dataclass(frozen=True)
class ArmCell:
    """A check in an arm that only the earlier arms' failure selects."""

    source: str
    #: The obligation kind, and the text the site starts at.
    kind: str
    site: str
    #: (function, arguments, the value it returns) for each run.
    runs: tuple[tuple[str, tuple[int, ...], object], ...]


# `count(n, i)` counts `i` up to `n`: the `_` arm runs only when
# `@Nat.0 == @Nat.1` failed, which with `requires(@Nat.0 <= @Nat.1)` makes
# the recursive call's precondition and its measure hold.
_COUNT_UP = """\
private fn count(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  decreases(@Nat.1 - @Nat.0)
  effects(pure)
{
  match @Nat.0 == @Nat.1 {
    true -> @Nat.0,
    _ -> count(@Nat.1, @Nat.0 + 1)
  }
}

public fn main(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  count(@Nat.0, 0)
}
"""

# The same loop over the gap, with a `@Nat` literal arm before a binder.
_COUNT_UP_OVER_THE_GAP = """\
private fn count(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  decreases(@Nat.1 - @Nat.0)
  effects(pure)
{
  match @Nat.1 - @Nat.0 {
    0 -> @Nat.0,
    @Nat -> count(@Nat.2, @Nat.1 + 1)
  }
}

public fn main(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  count(@Nat.0, 0)
}
"""

_ARM_CELLS: dict[str, ArmCell] = {
    "int_literal": ArmCell(_NEED_POS_DECL + """\
public fn f(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    0 -> 0,
    _ -> need_pos(@Int.0)
  }
}
""", "call_pre", "need_pos(@Int.0)\n", (("f", (0,), 0), ("f", (5,), 5))),
    "bool_literal": ArmCell(_NEED_POS_DECL + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Int.0 > 0 {
    false -> 0,
    _ -> need_pos(@Int.0)
  }
}
""", "call_pre", "need_pos(@Int.0)\n", (("f", (-3,), 0), ("f", (5,), 5))),
    "constructor": ArmCell(_UNWRAP_DECL + """\
public fn f(@Option<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    None -> 0,
    _ -> unwrap(@Option<Int>.0)
  }
}

public fn main_some(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(Some(7))
}

public fn main_none(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(None)
}
""", "call_pre", "unwrap(@Option<Int>.0)\n",
        (("main_some", (), 7), ("main_none", (), 0))),
    "nat_literal_then_binder": ArmCell(_NEED_POS_DECL + """\
public fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Nat.0 {
    0 -> 0,
    @Nat -> need_pos(@Nat.0)
  }
}
""", "call_pre", "need_pos(@Nat.0)\n", (("f", (0,), 0), ("f", (5,), 5))),
    "built_in_domain": ArmCell("""\
public fn f(@Int -> @Nat)
  requires(@Int.0 >= 0 && @Int.0 <= 3)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    0 -> 0,
    _ -> string_char_code("abc", @Int.0 - 1)
  }
}
""", "call_pre", "string_char_code(",
        (("f", (0,), 0), ("f", (1,), 97), ("f", (3,), 99))),
    "requires": ArmCell(_NEED_POS_DECL + """\
public fn f(@Nat -> @Int)
  requires(match @Nat.0 { 0 -> true, _ -> need_pos(@Nat.0) > 0 })
  ensures(true)
  effects(pure)
{
  1
}
""", "call_pre", "need_pos(@Nat.0)", (("f", (0,), 1), ("f", (5,), 1))),
    "ensures": ArmCell(_NEED_POS_DECL + """\
public fn f(@Nat -> @Int)
  requires(true)
  ensures(match @Nat.0 { 0 -> true, _ -> need_pos(@Nat.0) > 0 })
  effects(pure)
{
  1
}
""", "call_pre", "need_pos(@Nat.0)", (("f", (0,), 1), ("f", (5,), 1))),
    "predicate": ArmCell(_NEED_POS_DECL + """\
type Q = { @Nat | match @Nat.0 { 0 -> true, _ -> need_pos(@Nat.0) > 0 } };

public fn f(@Q -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
""", "call_pre", "need_pos(@Nat.0)", (("f", (0,), 1), ("f", (5,), 1))),
    "count_up_precondition": ArmCell(
        _COUNT_UP, "call_pre", "count(@Nat.1", (("main", (5,), 5),)),
    "count_up_measure": ArmCell(
        _COUNT_UP, "nat_sub", "count(@Nat.1", (("main", (5,), 5),)),
    "count_up_over_the_gap": ArmCell(
        _COUNT_UP_OVER_THE_GAP, "nat_sub", "count(@Nat.2",
        (("main", (5,), 5),)),
    # #1576: the body walk's own operations.
    "nat_subtraction": ArmCell("""\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Nat.0 {
    0 -> 0,
    _ -> @Nat.0 - 1
  }
}
""", "nat_sub", "@Nat.0 - 1", (("f", (0,), 0), ("f", (5,), 4))),
    "division": ArmCell("""\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    0 -> 0,
    _ -> 100 / @Int.0
  }
}
""", "div_zero", "100 / @Int.0", (("f", (0,), 0), ("f", (5,), 20))),
    "narrowing": ArmCell("""\
public fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    0 -> 0,
    _ -> {
      let @Nat = @Int.0 - 1;
      @Nat.0
    }
  }
}
""", "nat_bind", "@Int.0 - 1", (("f", (0,), 0), ("f", (5,), 4))),
    "refined_store": ArmCell("""\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Option<Pos>)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    0 -> None,
    _ -> Some(@Int.0)
  }
}

public fn g(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  match f(@Int.0) {
    Some(@Pos) -> @Pos.0,
    None -> 0
  }
}
""", "refine_bind", "@Int.0)\n", (("g", (0,), 0), ("g", (5,), 5))),
}


@pytest.mark.parametrize("name", list(_ARM_CELLS))
def test_an_arm_reads_that_no_earlier_arm_matched(name: str) -> None:
    cell = _ARM_CELLS[name]
    v = _verify(cell.source)
    site = _at(cell.source, cell.site)
    records = _records(v, cell.kind, site)
    assert all(r == "verified" for r in records), (
        records, [(o.kind, o.status, o.error_code, o.line, o.column)
                  for o in v.obligations])
    assert v.ok, v.errors
    for fn, args, value in cell.runs:
        ran = _run(cell.source, fn, list(args))
        assert ran.trap_kind is None, (fn, args, ran)
        assert ran.value == value, (fn, args, ran)


# What no earlier arm matching does NOT establish.  Without the `requires`,
# `-3` reaches the `_` arm; and a NESTED earlier arm matches only some of
# its constructor's values, so `Some(Some(5))` reaches the `_` arm and fails
# `need_none`'s precondition, which the whole constructor's negation
# would prove (#1562).
_ARM_CONTROLS: dict[str, tuple[str, str, str, tuple[int, ...]]] = {
    "unguarded": (_NEED_POS_DECL + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    0 -> 0,
    _ -> need_pos(@Int.0)
  }
}
""", "need_pos(@Int.0)\n", "f", (-3,)),
    "nested_earlier_arm": ("""\
private fn need_none(@Option<Option<Int>> -> @Int)
  requires(match @Option<Option<Int>>.0 { None -> true, _ -> false })
  ensures(true)
  effects(pure)
{
  0
}

public fn f(@Option<Option<Int>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Option<Int>>.0 {
    Some(None) -> 0,
    _ -> need_none(@Option<Option<Int>>.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(Some(Some(5)))
}
""", "need_none(@Option<Option<Int>>.0)\n", "main", ()),
}


@pytest.mark.parametrize("name", list(_ARM_CONTROLS))
def test_what_no_earlier_arm_matching_does_not_establish(name: str) -> None:
    source, site, fn, args = _ARM_CONTROLS[name]
    v = _verify(source)
    assert _records(v, "call_pre", _at(source, site)) == ["violated/E501"], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    ran = _run(source, fn, list(args))
    assert "Precondition violation in need_" in ran.trap_message, ran


# =====================================================================
# The recursive-call walk's binding of a `let` it cannot translate
# =====================================================================
#
# A fresh value of the binding's type, carrying that type's invariant:
# the `@Nat` binding is `>= 0`, which is what the termination proof needs
# of the argument `f(@Nat.0)` passes.  A bare const of the stale outer's
# sort does not carry it, and the proof fell to Tier 3 with E525.
_NAT_LET_BEFORE_A_RECURSIVE_CALL = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  let @Nat = apply_fn(fn(@Nat -> @Nat) effects(pure) { @Nat.0 }, 3);
  if @Nat.0 < @Nat.1 then {
    f(@Nat.0)
  } else {
    0
  }
}

public fn main(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(@Nat.0)
}
"""


def test_an_untranslatable_let_keeps_its_types_invariant_for_decreases(
        ) -> None:
    src = _NAT_LET_BEFORE_A_RECURSIVE_CALL
    v = _verify(src)
    assert [o.status for o in v.obligations if o.kind == "decreases"] == [
        "verified"], [(o.kind, o.status, o.error_code, o.line)
                      for o in v.obligations]
    assert v.ok, v.errors
    assert _run(src, "main", [5]).value == 0


# =====================================================================
# #1566: an untranslatable ADT `let` over a same-typed parameter
# =====================================================================
#
# The `let` rebinds `@Option<Int>.0` to a value the SMT layer cannot read.
# A `Some(@Pos)` arm over it narrows that value, not the parameter, so the
# parameter's `requires` says nothing about the payload: the narrowing is
# checked by its guard, which traps on `Some(0 - 5)`.  It was proved from
# the parameter's `requires`, a Tier-1 claim the run refuted.
_ADT_LET_OVER_A_PARAMETER_BODY = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Option<Int> -> @Int)
  requires(match @Option<Int>.0 {
    Some(@Int) -> @Int.0 > 0,
    None -> false
  })
  ensures(true)
  effects(<State<Option<Int>>>)
{
  let @Option<Int> = get(());
  match @Option<Int>.0 {
    Some(@Pos) -> @Pos.0,
    None -> 1
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(0 - 5)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    f(Some(3))
  }
}
"""

# The same narrowing in a `requires`, over a closure's result.
_ADT_LET_OVER_A_PARAMETER_REQUIRES = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Option<Int>, @Int -> @Int)
  requires(match @Option<Int>.0 {
    Some(@Int) -> @Int.0 > 0,
    None -> false
  })
  requires({
    let @Option<Int> = apply_fn(fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0) }, @Int.0);
    match @Option<Int>.0 {
      Some(@Pos) -> true,
      None -> true
    }
  })
  ensures(true)
  effects(pure)
{
  1
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(Some(3), @Int.0)
}
"""


@pytest.mark.parametrize(("source", "args", "value"), [
    (_ADT_LET_OVER_A_PARAMETER_BODY, [], None),
    (_ADT_LET_OVER_A_PARAMETER_REQUIRES, [-5], None),
    (_ADT_LET_OVER_A_PARAMETER_REQUIRES, [5], 1),
], ids=["body", "requires_traps", "requires_runs"])
def test_a_narrowing_over_an_untranslatable_adt_let_is_its_guards(
        source: str, args: list[int], value: object) -> None:
    v = _verify(source)
    # Located at the narrowed value: the second `match`'s scrutinee.
    scrutinee = _at(source, "@Option<Int>.0 {\n", 1)
    assert _records(v, "refine_bind", scrutinee) == ["tier3/E506"], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert v.ok, v.errors
    ran = _run(source, "main", args)
    if value is None:
        assert ran.trap_kind is not None, ran
    else:
        assert ran.trap_kind is None and ran.value == value, ran


# =====================================================================
# E529's rationale names the values that reach the trap
# =====================================================================
#
# `float_to_string` renders NaN and the infinities before it truncates, so
# only a finite magnitude of 2^63 or more reaches `i64.trunc_f64_s`.
def _e529_rationale(call: str) -> str:
    source = f"""\
public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {call}
}}
"""
    program = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(program, source)
    result = verify(
        program, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    [diag] = [d for d in result.diagnostics if d.error_code == "E529"]
    return diag.rationale


def test_the_e529_rationale_says_what_float_to_string_traps_on() -> None:
    rationale = _e529_rationale("float_to_string(100000000000000000000000.0)")
    assert "outside the i64 range" in rationale
    assert "NaN and +/-infinity are rendered" in rationale
    assert "on NaN" not in rationale
    ran = _run("""\
public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  float_to_string(0.0 / 0.0)
}
""", "main", [])
    assert ran.trap_kind is None, ran


def test_the_e529_rationale_says_what_float_to_int_traps_on() -> None:
    rationale = _e529_rationale(
        "int_to_string(float_to_int(100000000000000000000000.0))")
    assert "on NaN, +/-infinity, or a value whose truncation" in rationale


# =====================================================================
# A tail call by the module's own path evaluates the measure too
# =====================================================================
#
# Inside `module ma;`, `ma::step(...)` is the bare call to the top-level
# `step` (#1558), lowered to the same `return_call`, so the measure is
# evaluated on its arguments at the site exactly as for `step(...)`.
_STEP_TAIL_BY_PATH = """\
module ma;

private fn step(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  decreases(@Nat.1 - @Nat.0)
  effects(pure)
{
  if @Nat.0 COND @Nat.1 then {
    @Nat.0
  } else {
    CALL(@Nat.1, @Nat.0 + 1)
  }
}

public fn main(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  step(@Nat.0, 0)
}
"""


@pytest.mark.parametrize("call", ["step", "ma::step"])
@pytest.mark.parametrize(("cond", "status"), [
    (">", "violated/E502"),  # the call runs when `@Nat.0 == @Nat.1`
    ("==", "verified"),
])
def test_a_tail_call_by_the_modules_own_path_evaluates_the_measure(
        call: str, cond: str, status: str) -> None:
    src = _STEP_TAIL_BY_PATH.replace("CALL", call).replace("COND", cond)
    v = _verify(src)
    site = _at(src, f"{call}(@Nat.1")
    assert _records(v, "nat_sub", site) == [status], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    ran = _run(src, "main", [3])
    if status == "verified":
        assert ran.trap_kind is None and ran.value == 3, ran
    else:
        # The measure is evaluated before the callee's `requires`.
        assert ran.trap_kind is not None, ran
        assert "Precondition violation" not in ran.trap_message, ran


# From a `where` helper, the own path names the TOP-LEVEL function, never
# the helper (#1558): the call below goes to the top-level `step`, and code
# generation evaluates no measure of the helper's at it.
_HELPER_CALLS_THE_TOP_LEVEL_BY_PATH = """\
module ma;

private fn step(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn outer(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  step(@Nat.0, 0)
}
where {
  fn step(@Nat, @Nat -> @Nat)
    requires(@Nat.0 <= @Nat.1)
    ensures(true)
    decreases(@Nat.1 - @Nat.0)
    effects(pure)
  {
    if @Nat.0 > @Nat.1 then {
      @Nat.0
    } else {
      ma::step(@Nat.1, @Nat.0 + 1)
    }
  }
}
"""


def test_an_own_path_call_from_a_helper_is_no_self_tail_call() -> None:
    src = _HELPER_CALLS_THE_TOP_LEVEL_BY_PATH
    v = _verify(src)
    assert _records(v, "nat_sub", _at(src, "ma::step(")) == [], (
        [(o.kind, o.status, o.error_code, o.line, o.column)
         for o in v.obligations])
    assert v.ok, v.errors
    assert _run(src, "outer", [3]).value == 1


# A refinement predicate is read in the scope its guard is emitted in, the
# file's own path included (#1558): `ma::need_pos(@Int.0)` in a predicate
# is the call `need_pos(@Int.0)` is, and a predicate that calls it on every
# value of `@Int` traps on `-3` at the boundary guard.
_PREDICATE_CALL_BY_PATH = """\
module ma;

private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}

type R = { @Int | CALL(@Int.0) > 0 };

public fn g(@R -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""


@pytest.mark.parametrize("call", ["need_pos", "ma::need_pos"])
def test_a_predicate_call_by_the_modules_own_path_is_obligated(
        call: str) -> None:
    src = _PREDICATE_CALL_BY_PATH.replace("CALL", call)
    v = _verify(src)
    assert _records(v, "call_pre", _at(src, f"{call}(@Int.0)")) == [
        "violated/E501"], [(o.kind, o.status, o.error_code, o.line, o.column)
                           for o in v.obligations]
    ran = _run(src, "g", [-3])
    assert "Precondition violation in need_pos" in ran.trap_message, ran


# A measure that calls a function with a `requires` is evaluated at entry
# and at the tail call, and both are obligated there: the entry from
# `requires(@Nat.0 < 1000)`, the tail call from the `assume` about the value
# the untranslatable `let` binds.  The termination proof translates the
# measure again at the recursive call, and a demotion it met there is about
# no evaluation codegen makes; it was reported as a second E532, at the
# measure's own call.
_MEASURE_CALL_AFTER_AN_UNTRANSLATABLE_LET = """\
private fn g(@Nat -> @Nat)
  requires(@Nat.0 < 1000)
  ensures(@Nat.result == @Nat.0)
  effects(pure)
{
  @Nat.0
}

public fn f(@Nat -> @Nat)
  requires(@Nat.0 < 1000)
  ensures(true)
  decreases(g(@Nat.0))
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    let @Nat = apply_fn(fn(@Nat -> @Nat) effects(pure) { @Nat.0 - 1 }, @Nat.0);
    assume(@Nat.0 < 1000);
    f(@Nat.0)
  }
}
"""


def test_the_termination_proof_reports_no_call_of_its_own() -> None:
    src = _MEASURE_CALL_AFTER_AN_UNTRANSLATABLE_LET
    v = _verify(src)
    assert [
        (o.status, o.error_code, o.line, o.column)
        for o in v.obligations if o.kind == "call_pre"
    ] == [], [(o.kind, o.status, o.error_code, o.line, o.column)
              for o in v.obligations]
    assert v.ok, v.errors
    assert _run(src, "f", [5]).value == 0
