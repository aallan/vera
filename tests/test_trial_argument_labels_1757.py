"""A trial's arguments are labelled as the source names them (#1757).

`vera test` labelled a trial's arguments in parameter order, counting each
type from 0 left to right, so the first of two `@Nat` parameters was
reported as `@Nat.0`, the name the source gives the second.  `@T.0` is the
most recent binding of `T` (DE_BRUIJN.md), so a parameter's index counts
the parameters of its type after it, and the first of two `@Nat`
parameters is `@Nat.1`.  Three reports read the labels `_run_trials`
writes: the text report's failing trials, the `--json` report's `args`,
and the E703 description of a refuted proof.  A fourth reader,
`_assume_on_arguments`, reads the values by position, so the labels change
and the order of the arguments does not.

The matrix holds the labels over parameter shapes (two of one type, three
of one type, two types interleaved, a single parameter, a type once among
others, an alias among its base type, a `String` pair through the raw ABI)
by the three reports.  Each function's `requires` pins every
parameter to a value of its own by the name the source gives it, so the
tester's own generation puts that value at that parameter, and a report
must show each value under the name that pinned it, in the parameters'
order.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=["vera/tester.py"])

#: Each shape's parameters in order: the type, the name the source gives
#: the parameter (its index counts the later parameters of its type), and
#: the value its `requires` pins it to.
SHAPES: dict[str, tuple[tuple[str, str, int | bool | str], ...]] = {
    "two of one type": (
        ("Nat", "@Nat.1", 11), ("Nat", "@Nat.0", 12)),
    "three of one type": (
        ("Int", "@Int.2", -21), ("Int", "@Int.1", -22), ("Int", "@Int.0", -23)),
    "two types interleaved": (
        ("Int", "@Int.1", -31), ("Nat", "@Nat.1", 32),
        ("Int", "@Int.0", -33), ("Nat", "@Nat.0", 34)),
    "a single parameter": (
        ("Int", "@Int.0", -41),),
    "a type once among others": (
        ("Int", "@Int.1", -51), ("Bool", "@Bool.0", True), ("Int", "@Int.0", -53)),
    # A top-level alias is a slot type of its own (`naming.slot_name`): the
    # checker binds `@Cnt` under `Cnt`, not under the `Nat` it resolves to.
    "an alias among its base": (
        ("Cnt", "@Cnt.1", 61), ("Nat", "@Nat.0", 62), ("Cnt", "@Cnt.0", 63)),
    # `String` arguments reach the compiled function through the raw ABI
    # (`execute`'s `raw_args`), and the E703 description quotes them.
    "a `String` pair, through the raw ABI": (
        ("String", "@String.1", "ab"), ("Int", "@Int.0", -71),
        ("String", "@String.0", "cd")),
}

REPORTS = ("text", "json", "refutation")

#: Every trial fails this `ensures`, which the verifier leaves to Tier 3, so
#: every trial is reported with its arguments.  `Cnt` is the alias row's.
_FAILING = """\
type Cnt = Nat;

public fn f({params} -> @Int)
  requires({pins})
  ensures(string_length(int_to_string(@Int.result)) == 99)
  effects(pure)
{{
  0
}}
"""

#: #1695's composite coercion, which the verifier proves and every run
#: refutes (E703): an `Option<Int>` holding -7 bound into an `@Option<Nat>`
#: is obligated nowhere, so `mo`'s `@Nat` result is -7 and `mo(7) >= 0`,
#: proved from its type, runs false; `{premise}` is a statement at the head
#: of the body.  It replaced #1555's address comparison, which the typed
#: program fixed (#1525); when #1695 lands, the refutation cells and the
#: premise repro need another refuted proof.
_REFUTED = """\
type Cnt = Nat;

public fn f({params} -> @Int)
  requires({pins})
  ensures(@Int.result < 0)
  effects(pure)
{{
{premise}  if mo(7) >= 0 then {{ 0 - 1 }} else {{ 1 }}
}}

private fn mo(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @Option<Int> = Some(-7);
  let @Option<Nat> = @Option<Int>.0;
  match @Option<Nat>.0 {{
    Some(@Nat) -> @Nat.0,
    None -> 0
  }}
}}
"""


def _shown(value: int | bool | str) -> int | str:
    """A value as the text and `--json` reports show it: a `Bool` is the 1
    or 0 the compiled function receives (`_extract_values`)."""
    return value if isinstance(value, str) else int(value)


def _rendered(value: int | bool | str) -> str:
    """A value as the E703 description writes it (`_render_args`), a string
    quoted."""
    return json.dumps(value) if isinstance(value, str) else str(_shown(value))


def _pin(name: str, value: int | bool | str) -> str:
    if value is True:
        return name
    if value is False:
        return f"!{name}"
    if isinstance(value, str):
        return f"{name} == {json.dumps(value)}"
    return f"{name} == {value}"


def _source(template: str, shape: tuple[tuple[str, str, int | bool | str], ...],
            premise: str = "") -> str:
    return template.format(
        params=", ".join(f"@{ty}" for ty, _, _ in shape),
        pins=" && ".join(_pin(name, value) for _, name, value in shape),
        premise=premise)


def _write(tmp_path: Path, source: str) -> Path:
    path = tmp_path / "labels.vera"
    path.write_text(source, encoding="utf-8")
    return path


def _text_trials(stdout: str) -> list[list[tuple[str, str]]]:
    """Each failing trial's arguments as the text report prints them,
    `    @T.n = v, ... -> message`."""
    trials = []
    for line in stdout.splitlines():
        found = re.match(r"^    (@\S+ = .*?) -> ", line)
        if found:
            pairs = []
            for pair in found.group(1).split(", "):
                label, _, value = pair.partition(" = ")
                pairs.append((label, value))
            trials.append(pairs)
    return trials


def _refuted_trials(envelope: Any) -> list[str]:
    """The arguments each E703 description names, `the trial on ... failed`."""
    out = []
    for diag in envelope["diagnostics"]:
        if diag["error_code"] == "E703":
            found = re.search(r"the trial on (.*?) failed", diag["description"])
            assert found, diag["description"]
            out.append(found.group(1))
    return out


def _reported(tmp_path: Path, report: str,
              shape: tuple[tuple[str, str, int | bool | str], ...]) -> tuple[list[Any], Any]:
    """What *report* shows for each failing trial of *shape*'s function, and
    what it must show."""
    if report == "text":
        ran = pipeline.cli("test", "--trials", "3", _write(
            tmp_path, _source(_FAILING, shape)))
        assert ran.returncode != 0, ran.stdout
        return _text_trials(ran.stdout), [
            (name, str(_shown(value))) for _, name, value in shape]
    if report == "json":
        ran = pipeline.cli("test", "--json", "--trials", "3", _write(
            tmp_path, _source(_FAILING, shape)))
        [function] = ran.json()["functions"]
        return [json.dumps(list(t["args"].items())) for t in function["failures"]], (
            json.dumps([(name, _shown(value)) for _, name, value in shape]))
    ran = pipeline.cli("test", "--json", "--distrust", "--trials", "3", _write(
        tmp_path, _source(_REFUTED, shape)))
    return _refuted_trials(ran.json()), ", ".join(
        f"{name} = {_rendered(value)}" for _, name, value in shape)


@pytest.mark.parametrize("report", REPORTS)
@pytest.mark.parametrize("shape", SHAPES)
def test_each_report_names_each_argument_as_the_source_does(
        tmp_path: Path, shape: str, report: str) -> None:
    """Every failing trial shows each pinned value under the name that pins
    it, in the parameters' order."""
    trials, expected = _reported(tmp_path, report, SHAPES[shape])
    assert trials, f"{report} reported no failing trial"
    for trial in trials:
        assert trial == expected, (shape, report, trial)


def test_the_names_are_de_bruijn_indices() -> None:
    """The table states DE_BRUIJN.md's rule: a parameter of type `T` is
    `@T.n`, *n* the number of later parameters of type `T`."""
    for shape in SHAPES.values():
        types = [ty for ty, _, _ in shape]
        assert [name for _, name, _ in shape] == [
            f"@{ty}.{types[k + 1:].count(ty)}" for k, ty in enumerate(types)]


_REPRO = """\
public fn pair(@Nat, @Nat -> @Int)
  requires(@Nat.1 <= 0 && @Nat.0 >= 5 && @Nat.0 <= 9)
  ensures(string_length(int_to_string(@Int.result)) == 99)
  effects(pure)
{
  0
}
"""


def test_the_reported_program_repro(tmp_path: Path) -> None:
    """#1757's program, its `requires` as the issue states it, failing
    through a Tier 3 `ensures` rather than #1756's trap: the `requires`
    bounds `@Nat.1`, the first parameter, to 0 and `@Nat.0`, the second,
    to 5 to 9, and the report names them so."""
    ran = pipeline.cli("test", "--json", "--distrust", "--trials", "5",
                       _write(tmp_path, _REPRO))
    [function] = ran.json()["functions"]
    failures = function["failures"]
    assert failures, function
    for trial in failures:
        args = trial["args"]
        assert list(args) == ["@Nat.1", "@Nat.0"], args
        assert args["@Nat.1"] == 0 and 5 <= args["@Nat.0"] <= 9, args


def test_a_premise_reads_the_arguments_in_the_parameters_order_repro(
        tmp_path: Path) -> None:
    """`_assume_on_arguments` evaluates an `assume` at the head of a refuted
    function on the trial's values by position.  `@Nat.1 < @Nat.0` holds of
    the pinned 11 and 12 in the parameters' order and fails of them
    reversed, so the description says the arguments satisfy it."""
    shape = SHAPES["two of one type"]
    ran = pipeline.cli("test", "--json", "--distrust", "--trials", "3", _write(
        tmp_path, _source(_REFUTED, shape,
                          premise="  assume(@Nat.1 < @Nat.0);\n")))
    descriptions = [
        d["description"] for d in ran.json()["diagnostics"]
        if d["error_code"] == "E703"]
    assert descriptions, ran.stdout
    for description in descriptions:
        assert "the trial on @Nat.1 = 11, @Nat.0 = 12 failed" in description
        assert "which these arguments satisfy" in description, description
