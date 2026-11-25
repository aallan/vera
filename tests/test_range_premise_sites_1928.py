"""The queries that ask under a call's range premise (#1928), one cell a site.

A call imports its callee's facts under a guard: what the arguments owe the
parameters.  The guard's range part (an argument's i64 range, a `Nat`'s
`>= 0` inside its type) is required only by a query that asks what a type
states of a value, the ones that pass ``in_range=True`` to
``SmtContext.check_valid``: a callee's postcondition proved from its
parameter's range is not evidence of the argument's.  Each site below has a
program in which the guarded query and the unguarded one answer differently,
so dropping ``in_range=True`` at the site (``False``, ``None``, the keyword
removed) changes a row, a diagnostic or a fix:

- `_check_subtraction_obligation`: the `nat_sub` row, and its `lhs < rhs`
  re-ask over an operand that embeds an opaque shadow;
- `_check_quotient_obligation`: the quotient's `int_overflow` row;
- `_check_nat_binding_obligation_term`: a projected value's `nat_bind` row,
  and its placeholder re-ask;
- `_no_new_trap`: whether a fix may offer a `requires` holding arithmetic;
- `SmtContext._ranges`: a disclosed stand-in still states its ranges.

The callee `c` restates its parameter's range (`@Int.0 <= <max>` or
`@Int.0 >= <min>`), proved from that range; the caller passes an expression
that leaves the range at a boundary, where the run traps.
"""

from __future__ import annotations

from typing import Any

import pytest

from tests import pipeline
from vera.verifier import ContractVerifier

INT_MAX = 2**63 - 1
INT_MIN = -(2**63)
FILE = "cell.vera"

_MAX = "9223372036854775807"
_MIN = "-9223372036854775807 - 1"


def _callee(ensures: str) -> str:
    return (f"private fn c(@Int -> @Int)\n  requires(true)\n"
            f"  ensures({ensures})\n  effects(pure)\n{{\n  @Int.0\n}}\n\n")


#: `c`'s postcondition, proved from its parameter's range alone.
_BELOW_MAX = _callee(f"@Int.0 <= {_MAX}")
_ABOVE_MIN = _callee(f"@Int.0 >= {_MIN}")

_MKSUB = """\
private fn mksub(@Nat -> @Tuple<Nat, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Nat.0, @Nat.0)
}

"""

_MKT = """\
private fn mkt(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Int.0, @Int.0)
}

"""

#: `mk`'s payload is narrowed from a composite it did not build: no check
#: guards it, so a value read from it is disclosed (#1406's fixture).
_DISCLOSED_MK = """\
type PosNat = { @Nat | @Nat.0 > 0 };

private fn mk(@Float64 -> @Option<PosNat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Int> = Some(float_to_int(@Float64.0));
  @Option<Int>.0
}

"""


#: A term holding a stand-in (a random value) whose value is 0: added to a
#: call's argument, the argument's range parts mention a stand-in, and the
#: run is the stand-in-free argument's.
_STAND_IN = " + Random.random_int(0, 10) * 0"


def _k(sig: str, requires: str, body: str, effects: str = "pure") -> str:
    return (f"public fn k({sig})\n  requires({requires})\n  ensures(true)\n"
            f"  effects({effects})\n{{\n{body}\n}}\n")


def _verify(source: str) -> pipeline.Verified:
    verified = pipeline.verify(source, file=FILE)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    return verified


def _rows(verified: pipeline.Verified, kind: str) -> list[tuple[str, str]]:
    return [(o.expr_text, o.status) for o in verified.obligations
            if o.fn_name == "k" and o.kind == kind]


def _trap(source: str, arg: int) -> str:
    ran = pipeline.run(source, "k", [arg], file=FILE)
    assert ran.trap is not None, ran
    return str(ran.trap).lower()


def _codes(verified: pipeline.Verified) -> set[str]:
    return {d.error_code for d in verified.diagnostics}


# =====================================================================
# `_check_subtraction_obligation`: the `nat_sub` row
# =====================================================================


def _subtraction(requires: str, stand_in: str = "") -> str:
    # `9223372036854775806 - @Nat.0` needs `@Nat.0 < <max>`, which `c`'s
    # postcondition states of `@Nat.0 + 1` only where that sum is in range.
    return _BELOW_MAX + _k(
        "@Nat -> @Nat", requires,
        f"  let @Int = c(@Nat.0 + 1{stand_in});\n"
        "  let @Nat = 9223372036854775806;\n"
        "  @Nat.0 - @Nat.1", "<Random>" if stand_in else "pure")


def test_repro_a_nat_sub_row_requires_the_range_premise() -> None:
    """At `@Nat.0 = <max>` the argument `@Nat.0 + 1` overflows and the run
    traps: the `nat_sub` row is not proved from `c`'s postcondition."""
    source = _subtraction("true")
    rows = _rows(_verify(source), "nat_sub")
    assert rows == [("@Nat.0 - @Nat.1", "violated")], rows
    assert "overflow" in _trap(source, INT_MAX)


def test_repro_a_nat_sub_row_over_a_stand_in_argument_keeps_its_guard() -> None:
    """The same attack with a stand-in in the argument: its range parts
    mention the stand-in and were stripped from the guard, so `c`'s
    postcondition proved the row (verified at 57b6e0c6, and at main)."""
    source = _subtraction("true", _STAND_IN)
    rows = _rows(_verify(source), "nat_sub")
    assert rows == [("@Nat.0 - @Nat.1", "violated")], rows
    assert "overflow" in _trap(source, INT_MAX)


def test_a_nat_sub_row_whose_premise_holds_is_proved() -> None:
    rows = _rows(_verify(_subtraction("@Nat.0 < 100")), "nat_sub")
    assert rows == [("@Nat.0 - @Nat.1", "verified")], rows


def _shadowed_subtraction(arm: str) -> str:
    # The operands embed the opaque shadows a non-literal destructure binds,
    # and `@PosNat.0`'s `> 0` is disclosed (#1406), so `lhs >= rhs` is
    # proved only with the disclosed fact.  Where `lhs < rhs` is proved the
    # row reports that disclosure (E534); where it is not, the row is the
    # shadow's plain Tier 3.
    return _BELOW_MAX + _DISCLOSED_MK + _MKSUB + _k(
        "@Float64, @Nat -> @Nat", "@Nat.0 == 1",
        "  let Tuple<@Nat, @Nat> = mksub(@Nat.0);\n"
        "  match mk(@Float64.0) {\n"
        f"    Some(@PosNat) -> {{\n{arm}\n    }},\n"
        "    None -> 0\n"
        "  }")


_SHADOWED_ROW = "@Nat.0 + @PosNat.0 - (@Nat.0 + @Nat.2)"


def test_repro_the_shadow_re_ask_requires_the_range_premise() -> None:
    """`lhs < rhs` is `@PosNat.0 < 1`, which `c`'s postcondition states of
    `@PosNat.0 + <max>` only where that sum is in range: the re-ask is not
    proved, so the row stays the shadow's Tier 3 with no E534."""
    verified = _verify(_shadowed_subtraction(
        f"      let @Int = c(@PosNat.0 + {_MAX});\n"
        f"      {_SHADOWED_ROW}"))
    rows = _rows(verified, "nat_sub")
    assert rows == [(_SHADOWED_ROW, "tier3")], rows
    assert "E534" not in _codes(verified), _codes(verified)


def test_the_shadow_re_ask_asks_lhs_below_rhs() -> None:
    """Under `@PosNat.0 <= 1`, `lhs <= rhs` holds and `lhs < rhs` does not
    (`@PosNat.0 = 1`): the re-ask is the strict one."""
    verified = _verify(_shadowed_subtraction(
        f"      if @PosNat.0 <= 1 then {{ {_SHADOWED_ROW} }} else {{ 0 }}"))
    rows = _rows(verified, "nat_sub")
    assert rows == [(_SHADOWED_ROW, "tier3")], rows
    assert "E534" not in _codes(verified), _codes(verified)


# =====================================================================
# `_check_quotient_obligation`: the quotient's `int_overflow` row
# =====================================================================


def _quotient(requires: str, stand_in: str = "") -> str:
    # `@Int.1 / -1` overflows at `<min>` alone; `c`'s postcondition states
    # `@Int.1 - 1 >= <min>` only where that difference is in range.
    return _ABOVE_MIN + _k(
        "@Int -> @Int", requires,
        f"  let @Int = c(@Int.0 - 1{stand_in});\n  @Int.1 / -1",
        "<Random>" if stand_in else "pure")


def test_repro_a_quotient_row_requires_the_range_premise() -> None:
    source = _quotient("true")
    rows = [r for r in _rows(_verify(source), "int_overflow")
            if r[0] == "@Int.1 / -1"]
    assert rows == [("@Int.1 / -1", "tier3")], rows
    assert "overflow" in _trap(source, INT_MIN)


def test_repro_a_quotient_row_over_a_stand_in_argument_keeps_its_guard(
        ) -> None:
    """Verified at 57b6e0c6 (the stripped range parts left `c`'s
    postcondition unguarded), and at main, which held no guard."""
    source = _quotient("true", _STAND_IN)
    rows = [r for r in _rows(_verify(source), "int_overflow")
            if r[0] == "@Int.1 / -1"]
    assert rows == [("@Int.1 / -1", "tier3")], rows
    assert "overflow" in _trap(source, INT_MIN)


def test_a_quotient_row_whose_premise_holds_is_proved() -> None:
    rows = [r for r in _rows(_verify(_quotient("@Int.0 > -100")),
                             "int_overflow") if r[0] == "@Int.1 / -1"]
    assert rows == [("@Int.1 / -1", "verified")], rows


# =====================================================================
# `_check_nat_binding_obligation_term`: a projected value's `nat_bind` row
# =====================================================================


def _projected(requires: str, stand_in: str = "") -> str:
    # The destructured component `@Int.1 + <max>` is `>= 0` only where
    # `@Int.1 > <min>`, which `c` states of `@Int.1 - 1` only in range.
    return _ABOVE_MIN + _k(
        "@Int -> @Nat", requires,
        f"  let @Int = c(@Int.0 - 1{stand_in});\n"
        f"  let @Tuple<Int, Int> = Tuple(@Int.1 + {_MAX}, 0);\n"
        "  let Tuple<@Nat, @Int> = @Tuple<Int, Int>.0;\n"
        "  @Nat.0", "<Random>" if stand_in else "pure")


def test_repro_a_projected_nat_bind_row_requires_the_range_premise() -> None:
    source = _projected("true")
    rows = _rows(_verify(source), "nat_bind")
    assert rows == [("@Nat", "violated")], rows
    assert "overflow" in _trap(source, INT_MIN)


def test_repro_a_projected_nat_bind_over_a_stand_in_argument_keeps_its_guard(
        ) -> None:
    """Verified at 57b6e0c6 (the stripped range parts left `c`'s
    postcondition unguarded), and at main, which held no guard."""
    source = _projected("true", _STAND_IN)
    rows = _rows(_verify(source), "nat_bind")
    assert rows == [("@Nat", "violated")], rows
    assert "overflow" in _trap(source, INT_MIN)


def test_a_projected_nat_bind_row_whose_premise_holds_is_proved() -> None:
    rows = _rows(_verify(_projected("@Int.0 > -100")), "nat_bind")
    assert rows == [("@Nat", "verified")], rows


def test_repro_the_placeholder_re_ask_requires_the_range_premise(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """The component `s - s - @Int.0` embeds a destructure's shadow `s`, and
    is negative exactly where `@Int.0 >= 1`, which `c` states of
    `<max> - @Int.0 + 1` only in range: the re-ask `term < 0` is not proved,
    so the refutation is one over a placeholder.  The row is Tier 3 either
    way (a projection is codegen-guarded); the judgement is what the range
    premise decides, so it is read off the method."""
    seen: list[bool] = []
    real = ContractVerifier._refuted_only_over_a_placeholder

    def spy(self: ContractVerifier, *args: Any, **kwargs: Any) -> bool:
        answer = real(self, *args, **kwargs)
        seen.append(answer)
        return answer

    monkeypatch.setattr(
        ContractVerifier, "_refuted_only_over_a_placeholder", spy)
    verified = _verify(_BELOW_MAX + _MKT + _k(
        "@Int -> @Nat", "true",
        f"  let @Int = c({_MAX} - @Int.0 + 1);\n"
        "  let Tuple<@Int, @Int> = mkt(@Int.1);\n"
        "  let @Tuple<Int, Int> = Tuple(@Int.0 - @Int.0 - @Int.3, 0);\n"
        "  let Tuple<@Nat, @Int> = @Tuple<Int, Int>.0;\n"
        "  @Nat.0"))
    rows = _rows(verified, "nat_bind")
    assert rows == [("@Nat", "tier3")], rows
    assert True in seen, seen


# =====================================================================
# `_no_new_trap`: a fix's `requires` traps on no new input
# =====================================================================


def _divides(requires: str, callee: str = "") -> str:
    return callee + _k(
        "@Int -> @Int", requires,
        "  if @Int.0 < 100 then {\n    10 / (@Int.0 + 1)\n"
        "  } else {\n    0\n  }")


def _e526_fix(verified: pipeline.Verified) -> str:
    fixes = [d.fix or "" for d in verified.diagnostics
             if d.error_code == "E526"]
    assert len(fixes) == 1, _codes(verified)
    return fixes[0]


def test_repro_a_fix_clause_is_not_kept_in_range_by_a_callee() -> None:
    """`requires(@Int.0 + 1 != 0)` evaluates `@Int.0 + 1` at the entry,
    where `<max>` overflows; `c(@Int.0 + 1)`'s postcondition in the entry's
    `requires` states it in range only where it is.  The clause is not
    offered; the counterexample's is."""
    fix = _e526_fix(_verify(_divides(
        f"c(@Int.0 + 1) >= {_MIN}", _BELOW_MAX)))
    assert "requires(@Int.0 + 1 != 0)" not in fix, fix
    assert "requires(@Int.0 >= 0)" in fix, fix


def test_a_fix_clause_the_entry_keeps_in_range_is_offered() -> None:
    """Off the site's path (`@Int.0 >= 100`) the entry's `@Int.0 < 1000`
    keeps `@Int.0 + 1` in range: the site's own clause is offered."""
    fix = _e526_fix(_verify(_divides("@Int.0 < 1000")))
    assert "requires(@Int.0 + 1 != 0)" in fix, fix


# =====================================================================
# `SmtContext._ranges`: a disclosed stand-in states its ranges
# =====================================================================


def test_repro_a_disclosed_stand_in_states_its_range() -> None:
    """`float_to_int(..)` has no term, and its argument reads `mk`'s
    disclosed payload, so its stand-in is disclosed: what its type states
    beyond its base and ranges is withheld.  Its `Int` range is stated, and
    is the only fact that proves `@Int.result <= <max>`."""
    verified = _verify(_DISCLOSED_MK + (
        "public fn k(@Float64 -> @Int)\n  requires(true)\n"
        f"  ensures(@Int.result <= {_MAX})\n  effects(pure)\n{{\n"
        "  float_to_int(match mk(@Float64.0) {\n"
        "    Some(@PosNat) -> @Float64.0,\n    None -> 0.0\n  })\n}\n"))
    rows = _rows(verified, "ensures")
    assert rows == [(f"@Int.result <= {_MAX}", "verified")], rows
    assert "E534" not in _codes(verified), _codes(verified)
