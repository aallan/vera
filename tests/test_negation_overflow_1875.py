"""A unary negation of an `Int` is `0 - x`: one `int_overflow` row, one guard (#1875).

`-@Int.0` at `INT_MIN` is `2^63`, which no `Int` holds.  The negation lowered
to an unchecked `i64.sub` from zero, the obligation table listed no row for it
and the verifier translated it over unbounded integers, so a bare negation
returned `INT_MIN` there and every contract proved over a negation was false at
that one input with `vera verify` clean.

The rule is the subtraction's: a negation of an `Int` operand has the
`int_overflow` row `0 - x` has, the same guarded lowering and the same range
two-check.  A negated literal is that literal's value (spec §4.2), the
negation of a `Nat` cannot leave the range, and a `Float64` negation is
`f64.neg`; none of the three has a row.
"""

from __future__ import annotations

import functools
from collections.abc import Callable
from pathlib import Path

import pytest

from tests import pipeline
from vera.runtime.traps import WasmTrapError

pytestmark = pytest.mark.matrix(decides=[
    "vera/obligations/table.py", "vera/verifier.py", "vera/wasm/operators.py"])

INT_MIN = -(2**63)
INT_MAX = 2**63 - 1
_EXAMPLES = Path(__file__).resolve().parent.parent / "examples"

# The program the issue reports, every member of its checklist but the example.
_REPORTED = """\
type NegPositive = { @Int | -@Int.0 > 0 };

public fn plain_neg(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  -@Int.0
}

public fn magnitude(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 < 0 then {
    -@Int.0
  } else {
    @Int.0
  }
}

public fn into_refined(@Int -> @NegPositive)
  requires(@Int.0 < 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

private fn wants_negative(@Int -> @Int)
  requires(-@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  7
}

public fn calls_it(@Int -> @Int)
  requires(@Int.0 < 0)
  ensures(true)
  effects(pure)
{
  wants_negative(@Int.0)
}
"""


def _overflow_rows(source: str) -> list[tuple[str, int]]:
    """Each `int_overflow` obligation `vera verify` records: its status and line."""
    verified = pipeline.verify(source)
    assert verified.ok, verified.diagnostics
    return [(o.status, o.line) for o in verified.obligations
            if o.kind == "int_overflow"]


def _trap_kind(source: str, fn: str, arg: int) -> str | None:
    """The trap kind ``fn(arg)`` ends with, or ``None`` when it returns."""
    ran = pipeline.run(source, fn, [arg], capture_stderr=False)
    try:
        _ = ran.execution
    except WasmTrapError as trap:
        return trap.kind
    return None


def test_repro_1875_reported_program_records_a_row_per_negation() -> None:
    """Every negation of an `Int` operand in the reported program carries the
    row: the refinement predicate (line 1), `plain_neg`'s body (line 8),
    `magnitude`'s branch (line 17) and `wants_negative`'s `requires`
    (line 32).  None is proved: each admits `INT_MIN`, and each is the
    run-time check that stops it there."""
    rows = _overflow_rows(_REPORTED)
    assert sorted(rows) == [("tier3", 1), ("tier3", 8), ("tier3", 17),
                            ("tier3", 32)], rows


@pytest.mark.parametrize("fn", ["plain_neg", "magnitude", "into_refined", "calls_it"])
def test_repro_1875_each_function_traps_with_overflow_at_int_min(fn: str) -> None:
    """At `INT_MIN` each function stops at the negation with the overflow
    trap, not with a wrong value or a contract proved at Tier 1."""
    assert _trap_kind(_REPORTED, fn, INT_MIN) == "overflow"


@pytest.mark.parametrize("fn", ["plain_neg", "magnitude", "into_refined", "calls_it"])
def test_repro_1875_each_function_is_unchanged_one_above_int_min(fn: str) -> None:
    """One above `INT_MIN` no negation leaves the range: each function returns."""
    assert _trap_kind(_REPORTED, fn, INT_MIN + 1) is None


def test_repro_1875_absolute_value_example_proves_under_its_precondition() -> None:
    """`examples/absolute_value.vera` excludes `INT_MIN` in its `requires`,
    so each negation's row is proved and nothing is left to run time."""
    verified = pipeline.verify(_EXAMPLES / "absolute_value.vera")
    assert verified.ok, verified.diagnostics
    rows = [o.status for o in verified.obligations if o.kind == "int_overflow"]
    assert rows == ["verified", "verified"], rows


def test_repro_1875_a_negation_provably_out_of_range_is_e528() -> None:
    """`-(-9223372036854775808)` is `2^63`: the outer negation's row is
    refuted at compile time and the diagnostic names a negation."""
    verified = pipeline.verify(_body("-(-9223372036854775808)", "@Unit"))
    assert not verified.ok
    errors = [d for d in verified.diagnostics if d.error_code == "E528"]
    assert errors and "negation" in errors[0].description, verified.diagnostics


def test_named_1875_a_refinement_declaration_obligates_its_negation() -> None:
    """A predicate is verified once at its declaration (spec §6.4.3) under
    its base type's facts alone; for a type no guard reads, the table lists
    no copy, and the declaration takes the negation's row by the table's
    own rule.  A predicate that pins its binder away from `INT_MIN` proves
    it, one that does not leaves it to run time."""
    verified = pipeline.verify(
        "type Odd = { @Int | -@Int.0 != 5 };\n\n"
        "type Small = { @Int | @Int.0 > -1000 && @Int.0 < 1000 && -@Int.0 != 5 };\n\n"
        + _body("@Int.0"))
    assert verified.ok, verified.diagnostics
    rows = sorted((o.line, o.status) for o in verified.obligations
                  if o.kind == "int_overflow")
    assert rows == [(1, "tier3"), (3, "verified")], verified.obligations


#: A type no guard reads, one per operation a declaration takes by its own
#: rule (`ContractVerifier._declaration_takes`), the line each stands on.
_DECLARED = """\
type IntSum = { @Int | @Int.0 + 1 > 0 };

type NatSum = { @Nat | @Nat.0 + @Nat.0 >= 0 };

type NatDiff = { @Nat | @Nat.0 - @Nat.0 == 0 };

type NatNeg = { @Nat | -@Nat.0 <= 0 };

type Magnitude = { @Int | abs(@Int.0) > 0 };

type Truncated = { @Float64 | float_to_int(@Float64.0) > 0 };

type Headed = { @Array<Int> | @Array<Int>.0[0] > 0 };

type Asserted = { @Int | { assert(@Int.0 > 0); true } };

type Called = { @Int | @Int.0 > 0 && positive(@Int.0) };

type FloatSum = { @Float64 | @Float64.0 + 1.5 > 0.0 };

type Pos = { @Int | @Int.0 > 0 };

type Wrapped = { @Int | takes(mk(@Int.0)) };

private fn positive(@Int -> @Bool)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  true
}

private fn mk(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

private fn takes(@Option<Pos> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  true
}
"""


def test_repro_1875_each_declaration_takes_its_operations_rows() -> None:
    """Verified at its declaration, each predicate holds exactly the rows
    of the operations it performs: an `Int` sum's and a `Nat` sum's range,
    a `Nat` difference's sign (no range), an `abs`, a float truncation, an
    index, an `assert` and a call's precondition.  A `Nat` negation and a
    `Float64` sum have none, and a call's argument is not the declaration's
    narrowing to take."""
    verified = pipeline.verify(_DECLARED)
    assert verified.ok, verified.diagnostics
    rows = sorted((o.line, o.kind, o.status) for o in verified.obligations
                  if o.line < 24)
    assert rows == [
        (1, "int_overflow", "tier3"),
        (3, "int_overflow", "tier3"),
        (5, "nat_sub", "verified"),
        (9, "int_overflow", "tier3"),
        (11, "float_to_int_domain", "tier3"),
        (13, "index_bounds", "tier3"),
        (15, "assert", "tier3"),
        (17, "call_pre", "verified"),
    ], verified.obligations


# =====================================================================
# The class: a negation at every position, against its `0 - x` twin
# =====================================================================
#
# The oracle is the subtraction the rule says a negation is.  Each cell
# builds a program with the negation and its twin with `0 - x` in its place,
# and holds the two to the same obligations (kind and status, all of them)
# and the same run at the cell's value.  On top of the twin: the negation
# traps with the overflow kind at `INT_MIN` wherever the compiled program
# evaluates it, and nowhere else; where it traps, no `int_overflow` row
# reads `verified`; and no cell's program is refused.

_HEADER = "  requires(true)\n  ensures(true)\n  effects(pure)\n"
_IDENT = ("\n\nprivate fn ident(@Int -> @Int)\n" + _HEADER
          + "{\n  @Int.0\n}\n")


def _body(expr: str, param: str = "@Int", ret: str = "@Int") -> str:
    return f"public fn f({param} -> {ret})\n{_HEADER}{{\n  {expr}\n}}\n"


def _position(pos: str, n: str) -> str:
    """The program with the negated expression *n* at *pos*."""
    if pos == "body":
        return _body(n)
    if pos == "requires":
        return (f"public fn f(@Int -> @Int)\n  requires({n} != 5 || true)\n"
                f"  ensures(true)\n  effects(pure)\n{{\n  @Int.0\n}}\n")
    if pos == "ensures":
        return (f"public fn f(@Int -> @Int)\n  requires(@Int.0 != -5)\n"
                f"  ensures({n} != 5 || true)\n  effects(pure)\n{{\n  @Int.0\n}}\n")
    if pos == "refinement":
        return (f"type T = {{ @Int | {n} != 5 || true }};\n\n"
                f"public fn f(@Int -> @Int)\n  requires(@Int.0 != -5)\n"
                f"  ensures(true)\n  effects(pure)\n{{\n  let @T = @Int.0;\n"
                f"  @Int.0\n}}\n")
    if pos == "decreases":
        return (f"public fn f(@Int -> @Int)\n  requires(@Int.0 <= 0)\n"
                f"  ensures(true)\n  decreases({n})\n  effects(pure)\n{{\n"
                f"  if @Int.0 >= -1 then {{\n    0\n  }} else {{\n"
                f"    f(@Int.0 / 2)\n  }}\n}}\n")
    if pos == "assert":
        return _body(f"assert({n} != 5 || true);\n  @Int.0")
    if pos == "assume":
        return _body(f"assume({n} != 5 || true);\n  @Int.0")
    if pos == "closure":
        return ("type IntToInt = fn(Int -> Int) effects(pure);\n\n"
                + _body("let @IntToInt = fn(@Int -> @Int) effects(pure) "
                        f"{{ {n} }};\n  apply_fn(@IntToInt.0, @Int.0)"))
    if pos == "where":
        return (_body("g(@Int.0)") + "where {\n  fn g(@Int -> @Int)\n"
                "    requires(true)\n    ensures(true)\n    effects(pure)\n"
                f"  {{\n    {n}\n  }}\n}}\n")
    raise AssertionError(pos)


def _unary(e: str) -> str:
    return f"-({e})" if e.startswith("-") else f"-{e}"


def _twin(e: str) -> str:
    return f"(0 - {e})"


#: The operand forms, each as the negated expression a negator builds.
_FORMS: dict[str, Callable[[Callable[[str], str]], str]] = {
    "slot": lambda neg: neg("@Int.0"),
    "call": lambda neg: neg("ident(@Int.0)"),
    "nested": lambda neg: neg(neg("@Int.0")),
    "arith": lambda neg: neg("(@Int.0 * 1)"),
}
#: Where the compiled program evaluates nothing, nothing is obligated.
_UNEVALUATED = {"assume"}
_POSITIONS = ["body", "requires", "ensures", "refinement", "decreases",
              "assert", "assume", "closure", "where"]
_VALUES = {"int_min": INT_MIN, "int_min_plus_1": INT_MIN + 1, "minus_1": -1,
           "zero": 0, "int_max": INT_MAX}


def _program(pos: str, form: str, neg: Callable[[str], str]) -> str:
    return _position(pos, _FORMS[form](neg)) + _IDENT


@functools.cache
def _verified(source: str) -> tuple[bool, tuple[tuple[str, str], ...], str]:
    v = pipeline.verify(source)
    obligations = tuple(sorted((o.kind, o.status) for o in v.obligations)) if v.ok else ()
    return v.ok, obligations, repr(v.diagnostics)


@functools.cache
def _compiled(source: str) -> pipeline.Compiled:
    return pipeline.compile(source)


def _outcome(source: str, arg: int) -> tuple[str, object]:
    ran = pipeline.run(_compiled(source), "f", [arg], capture_stderr=False)
    try:
        return ("value", ran.execution.value)
    except WasmTrapError as trap:
        return ("trap", trap.kind)


@pytest.mark.parametrize("value", list(_VALUES))
@pytest.mark.parametrize("form", list(_FORMS))
@pytest.mark.parametrize("pos", _POSITIONS)
def test_negation_is_its_subtraction(pos: str, form: str, value: str) -> None:
    neg, twin = _program(pos, form, _unary), _program(pos, form, _twin)
    n_ok, n_obligations, n_diags = _verified(neg)
    t_ok, t_obligations, t_diags = _verified(twin)
    assert n_ok, n_diags
    assert t_ok, t_diags
    assert n_obligations == t_obligations
    arg = _VALUES[value]
    got = _outcome(neg, arg)
    assert got == _outcome(twin, arg)
    traps = got == ("trap", "overflow")
    assert traps == (arg == INT_MIN and pos not in _UNEVALUATED), got
    if traps:
        statuses = [s for k, s in n_obligations if k == "int_overflow"]
        assert statuses and set(statuses) != {"verified"}, n_obligations


# =====================================================================
# The operand's type, and the literal
# =====================================================================


_TYPED = {
    # name: (program, the int_overflow statuses, [(argument, outcome)])
    "nat": (_body("-@Nat.0", "@Nat"), [],
            [(0, ("value", 0)), (INT_MAX, ("value", -INT_MAX))]),
    "float64": (_body("-@Float64.0", "@Float64", "@Float64"), [],
                [(1.5, ("value", -1.5))]),
    "refined_nat": ("type Small = { @Nat | @Nat.0 < 10 };\n\n"
                    + _body("-@Small.0", "@Small"), [],
                    [(9, ("value", -9))]),
    "refined_bounded_int": ("type Small = { @Int | @Int.0 > -1000 && @Int.0 < 1000 };\n\n"
                            + _body("-@Small.0", "@Small"), ["verified"],
                            [(-999, ("value", 999))]),
    "refined_negative_int": ("type Neg = { @Int | @Int.0 < 0 };\n\n"
                             + _body("-@Neg.0", "@Neg"), ["tier3"],
                             [(INT_MIN, ("trap", "overflow")),
                              (INT_MIN + 1, ("value", INT_MAX))]),
    "int_under_precondition": (
        "public fn f(@Int -> @Int)\n  requires(@Int.0 > -9223372036854775808)\n"
        "  ensures(@Int.result >= 0)\n  effects(pure)\n"
        "{\n  if @Int.0 < 0 then {\n    -@Int.0\n  } else {\n    0\n  }\n}\n",
        ["verified"], [(INT_MIN + 1, ("value", INT_MAX))]),
}


@pytest.mark.parametrize("name", list(_TYPED))
def test_negation_by_operand_type(name: str) -> None:
    """A `Nat` operand, a `Float64` and a refinement of `Nat` have no row; a
    refinement of `Int` has the row, proved where its predicate excludes
    `INT_MIN` and guarded where it does not."""
    source, statuses, runs = _TYPED[name]
    ok, obligations, diags = _verified(source)
    assert ok, diags
    assert [s for k, s in obligations if k == "int_overflow"] == statuses
    for arg, outcome in runs:
        assert _outcome(source, arg) == outcome  # type: ignore[arg-type]


_MAGNITUDES = {"two_pow_63": 2**63, "int_max": INT_MAX, "one": 1, "zero": 0}
_LITERAL_POSITIONS = ["body", "requires", "assert", "closure", "where"]


@pytest.mark.parametrize("magnitude", list(_MAGNITUDES))
@pytest.mark.parametrize("pos", _LITERAL_POSITIONS)
def test_negated_literal_is_its_value(pos: str, magnitude: str) -> None:
    """`-m` for a literal `m` is the constant `-m` (spec §4.2), `INT_MIN`
    included: no row, no guard, at every position."""
    lit = _MAGNITUDES[magnitude]
    source = _position(pos, f"-{lit}") + _IDENT
    ok, obligations, diags = _verified(source)
    assert ok, diags
    assert [s for k, s in obligations if k == "int_overflow"] == []
    expected = -lit if pos in ("body", "closure", "where") else 3
    assert _outcome(source, 3) == ("value", expected)


# =====================================================================
# E528 as written, for each operation it reports
# =====================================================================

_E528_RATIONALE = (
    "@Int / @Nat arithmetic carries a Tier-1 proof obligation that the result "
    "stays within the i64 range.  The SMT solver proved the result is always "
    "out of range; `+`/`-`/`*`, negation and `abs` trap at runtime on "
    "overflow (#798).")
_E528_SPEC_REF = 'Chapter 6, Section 6.4.3 "Primitive Operation Safety"'


def _e528_fix(written: str) -> str:
    return (f"Constrain the operands so `{written}` cannot overflow — add a "
            "precondition bounding them, give an operand a refinement type "
            "that bounds its range, or guard the operation with a path "
            "condition the obligation can discharge.")


def _refuted(params: str, requires: str, ret: str, body: str) -> str:
    return (f"public fn f({params} -> {ret})\n  requires({requires})\n"
            f"  ensures(true)\n  effects(pure)\n{{\n  {body}\n}}\n")


#: Each operation `_report_overflow` names, refuted at line 6, column 3:
#: (the program, the operation's word, the operation as written, the
#: counterexample's lines).
_E528_FORMS = {
    "addition": (_refuted("@Int", "@Int.0 == 9223372036854775807", "@Int", "@Int.0 + 1"),
                 "addition", "@Int.0 + 1", ["@Int.0 = 9223372036854775807"]),
    "subtraction": (_refuted("@Int", "@Int.0 == -9223372036854775807", "@Int", "@Int.0 - 2"),
                    "subtraction", "@Int.0 - 2", ["@Int.0 = -9223372036854775807"]),
    "multiplication": (_refuted("@Int", "@Int.0 == 9223372036854775807", "@Int", "@Int.0 * 2"),
                       "multiplication", "@Int.0 * 2", ["@Int.0 = 9223372036854775807"]),
    "negation": (_refuted("@Int", "@Int.0 == -9223372036854775808", "@Int", "-@Int.0"),
                 "negation", "-@Int.0", ["@Int.0 = -9223372036854775808"]),
    "abs": (_refuted("@Int", "@Int.0 == -9223372036854775808", "@Nat", "abs(@Int.0)"),
            "`abs`", "abs(@Int.0)", ["@Int.0 = -9223372036854775808"]),
    "quotient": (_refuted("@Int, @Int", "@Int.1 == -9223372036854775808 && @Int.0 == -1",
                          "@Int", "@Int.1 / @Int.0"),
                 "operation", "@Int.1 / @Int.0",
                 ["@Int.0 = -1", "@Int.1 = -9223372036854775808"]),
}


@pytest.mark.parametrize("form", list(_E528_FORMS))
def test_repro_1875_e528_as_written(form: str) -> None:
    """The refuted overflow's diagnostic, every field whole: the operation's
    word, its counterexample, the rationale, the fix naming the operation
    as written, the section, and where it stands."""
    source, word, written, counterexample = _E528_FORMS[form]
    verified = pipeline.verify(source)
    found = [(d.description, d.rationale, d.fix, d.spec_ref, d.severity,
              d.location.line, d.location.column)
             for d in verified.diagnostics if d.error_code == "E528"]
    description = (f"Integer {word} in 'f' provably overflows.\n"
                   "  Counterexample:\n"
                   + "\n".join(f"      {line}" for line in counterexample))
    assert found == [(description, _E528_RATIONALE, _e528_fix(written),
                      _E528_SPEC_REF, "error", 6, 3)]
