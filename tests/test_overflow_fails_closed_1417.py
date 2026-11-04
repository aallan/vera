"""An operand with no type the table can read is guarded as an `Int` (#1417).

The obligation table (#1695) lists the `int_overflow` row of an `+`/`-`/`*`
from the checker's types of its operands.  When it cannot read one it reads
the operand as an `Int` — the wider signed interpretation, whose guard
fires on exactly the values that would wrap — and lists the row, so the
guard is emitted rather than skipped: an unclassified pair is the case
nobody can enumerate, and a guard skipped there wrapped in silence while
the verifier's obligation claimed a runtime check (#1417).

There is no whole-program reproducer: every operand of a checked program
has a type in the checker's table.  So the lever is the table's reading of
the operand, patched at its own seam (`_Builder.sem`), and what is measured
is the row listed and the module emitted on it — the only thing the fix
changed.
"""

from __future__ import annotations

import dataclasses

from vera import ast
from vera.obligations import table as obligation_table
from vera.typed import build as build_typed

import pytest

from tests import pipeline
from tests.pipeline import checks
from vera.checker import typecheck_with_artifacts
from vera.codegen import compile
from vera.parser import parse_to_ast

_ADD = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}
"""

_SUB = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 - 1
}
"""


def _compiled(source: str = _ADD):
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source,
                                           collect_module_artifacts=True)
    assert not [d for d in diags if d.severity == "error"], diags
    typed = build_typed(program, [], arts)
    return compile(typed, source=source)


def _rows(source: str) -> list[obligation_table.Row]:
    return [row for row in obligation_table.build(pipeline.typed(source)).rows
            if row.kind == "int_overflow"]


def _unreadable(monkeypatch: pytest.MonkeyPatch) -> list[object]:
    """Patch the table's reading of every node to "no type", recording what
    the unpatched reading answered at each operand first."""
    answers: list[object] = []
    original = obligation_table._Builder.sem

    def unread(self: obligation_table._Builder, node: ast.Node) -> None:
        answers.append(original(self, node))
        return None

    monkeypatch.setattr(obligation_table._Builder, "sem", unread)
    return answers


def test_an_unreadable_width_is_guarded_as_int(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The property: the table cannot read the operands, the row is listed
    and the guard is emitted anyway, as the signed sequence."""
    assert [row.guard.check for row in _rows(_ADD)] == [True]
    answers = _unreadable(monkeypatch)
    rows = _rows(_ADD)
    assert answers, "the table never read a node"
    assert [row.guard.check for row in rows] == [True], rows
    result = _compiled()
    wat = result.wat
    assert checks(result, kind="overflow"), (
        "an arithmetic site whose width the table could not read "
        "emitted no overflow guard, so it wraps in silence while the "
        "obligation claims a runtime check:\n" + wat[:800]
    )
    assert "i64.xor" in wat, (
        "the guard emitted is not the signed sequence, so the site is "
        "checked against the unsigned range:\n" + wat[:800]
    )
    assert "i64.lt_u" not in wat, wat[:800]


def test_an_unreadable_subtraction_is_guarded_as_int(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The one place the fail-closed reading matters: a subtraction of two
    `@Nat` operands is the `nat_sub` underflow row and takes no overflow
    guard, so an unreadable width read as `Nat` would leave it unguarded.
    Read as `Int`, it is the overflow row and guarded."""
    _unreadable(monkeypatch)
    rows = _rows(_SUB)
    assert [row.guard.check for row in rows] == [True], rows
    result = _compiled(source=_SUB)
    assert checks(result, kind="overflow"), (
        "a subtraction whose width the table could not read took the "
        "`Nat` exclusion and no overflow guard:\n" + result.wat[:800]
    )


def test_the_module_still_loads_and_exports_its_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Fail-closed must not mean fail-differently: a guard bolted on at
    the cost of a malformed function would trade a silent wrap for a
    module that does not run."""
    _unreadable(monkeypatch)
    from vera.codegen.api import execute

    out = execute(_compiled(), fn_name="f", args=[3])
    assert out.value == 4, out


def test_the_verifier_fails_closed_on_the_same_answer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Both legs, not just the emitter (R-1412 F5).

    The verifier gated its OBLIGATION on the same `is not None`, so a site
    the emitter now guards would carry no record to count it — the desync
    one component over from the one #1417 describes.  Patched at the
    classifier's seam for the reason the emitter cell gives: no program
    reaches the `None` answer, so the only way to exercise the branch is to
    hand it that answer.
    """
    from vera.verifier import ContractVerifier

    monkeypatch.setattr(
        ContractVerifier, "_overflow_arith_type",
        lambda self, expr: None,
    )
    program = parse_to_ast(_ADD)
    diags, arts = typecheck_with_artifacts(program, _ADD,
                                           collect_module_artifacts=True)
    assert not [d for d in diags if d.severity == "error"], diags
    from vera.verifier import verify

    result = verify(build_typed(program, [], arts), _ADD)
    recorded = [o for o in result.obligations if o.kind == "int_overflow"]
    assert recorded, [dataclasses.asdict(o) for o in result.obligations]
    assert recorded[0].status in ("tier3", "verified"), recorded
