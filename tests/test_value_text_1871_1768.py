"""A value a diagnostic quotes is written as the program would write it (#1871, #1768).

A refuted contract's counterexample listed every constant the solver context
had declared, its parameters' and its own alike (`_call_take_14_3`,
`_lit_7_16`), a `@Unit` parameter as `@Unit.0 = 0`, and printed its header
whether anything was left under it or not; each value was Z3's text of the
model's term (`True`, `1.6000000000000000888...*(2**-4)`, a raw newline, an
array's carrier constant).  `vera test` reported a `Bool` argument as the
`1` or `0` the compiled function receives, and printed a `String` argument
without its quotes on the trial line and with JSON's escapes in E703.

The rule: a counterexample lists the function's inputs, by the slot
references the source binds them to, and `@T.result` where the obligation is
an `ensures`; a value is the literal that denotes it, written by the
canonical formatter (`vera.literals`).  An input with no literal form is
named with a note, an array past the cap shows its first elements and how
many more there are, a zero-size input is not listed, and with nothing to
list there is no header.

The instrument: the ten emitters that print a counterexample, by the type of
the one input, each cell a contract refuted at exactly one input (the
`requires` pins it), asserting the whole block; and `vera test`'s three
renderers (the text trial line, `--json`'s `args`, E703) by each type it
generates.  No cell reads a value the solver was free to choose (#1785).
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import pytest
import z3

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/literals.py", "vera/smt.py", "vera/verifier.py",
    "vera/tester.py", "vera/cli.py"])

_PRELUDE = """\
type PosInt = { @Int | @Int.0 > 0 };
type IntToInt = fn(Int -> Int) effects(pure);

private fn need(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

private fn consume(@Option<PosInt> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""

#: Each emitter: its code, the function's return type, its `ensures`, its
#: body, and whether its counterexample names the result.
_EMITTERS: dict[str, tuple[str, str, str, str, bool]] = {
    "ensures": ("E500", "@Int", "@Int.result == 1", "0", True),
    "call_pre": ("E501", "@Int", "true", "need(0)", False),
    "underflow": ("E502", "@Nat", "true",
                  "let @Nat = 3;\n  let @Nat = 5;\n  @Nat.1 - @Nat.0", False),
    "nat_narrow": ("E503", "@Nat", "true",
                   "let @Int = 0 - 5;\n  @Int.0", False),
    "refined": ("E505", "@PosInt", "true", "let @Int = 0;\n  @Int.0", False),
    "nested": ("E505", "@Int", "true", "consume(@Option<Int>.0)", False),
    "assert": ("E507", "@Int", "true", "assert(1 == 2);\n  0", False),
    "div_zero": ("E526", "@Int", "true",
                 "let @Int = 0;\n  10 / @Int.0", False),
    "index": ("E527", "@Int", "true",
              "let @Array<Int> = [1, 2];\n  @Array<Int>.0[5]", False),
    "overflow": ("E528", "@Int", "true",
                 "let @Int = 9223372036854775807;\n  @Int.0 + 1", False),
}


def _array_pin(slot: str, values: list[int]) -> str:
    parts = [f"array_length({slot}) == {len(values)}"]
    parts += [f"{slot}[{i}] == {v}" for i, v in enumerate(values)]
    return " && ".join(parts)


#: Each input type: the parameter, the `requires` that pins it to one value,
#: and the line its counterexample shows (``None``: not listed).
_TYPES: dict[str, tuple[str, str, str | None]] = {
    "Bool": ("@Bool", "@Bool.0", "@Bool.0 = true"),
    "Bool_false": ("@Bool", "!@Bool.0", "@Bool.0 = false"),
    "Byte": ("@Byte", "byte_to_int(@Byte.0) == 7", "@Byte.0 = 7"),
    "Nat": ("@Nat", "@Nat.0 == 7", "@Nat.0 = 7"),
    "Int": ("@Int", "@Int.0 == -7", "@Int.0 = -7"),
    "Float64": ("@Float64", "@Float64.0 == 0.1", "@Float64.0 = 0.1"),
    "Float64_neg": ("@Float64", "@Float64.0 == -2.5", "@Float64.0 = -2.5"),
    "Float64_large": ("@Float64", "@Float64.0 == 100000000000000000000000.0",
                      "@Float64.0 = 100000000000000000000000.0"),
    "String": ("@String", '@String.0 == "q\\"x\\n"',
               '@String.0 = "q\\"x\\n"'),
    "String_invisible": ("@String", '@String.0 == "\\u{200B}"',
                         '@String.0 = "\\u{200B}"'),
    "Option": ("@Option<Int>", "@Option<Int>.0 == Some(7)",
               "@Option<Int>.0 = Some(7)"),
    "Option_none": ("@Option<Int>", "@Option<Int>.0 == None",
                    "@Option<Int>.0 = None"),
    "Tuple": ("@Tuple<Int, Bool>",
              "match @Tuple<Int, Bool>.0 { Tuple(@Int, @Bool) -> "
              "@Int.0 == 7 && @Bool.0 }",
              "@Tuple<Int, Bool>.0 = Tuple(7, true)"),
    "Array": ("@Array<Int>", _array_pin("@Array<Int>.0", [4, -5]),
              "@Array<Int>.0 = [4, -5]"),
    "Array_long": ("@Array<Int>", _array_pin("@Array<Int>.0", list(range(10))),
                   "@Array<Int>.0 = [0, 1, 2, 3, 4, 5, 6, 7, ... and 2 more]"),
    "Map": ("@Map<Int, Int>", "true",
            "@Map<Int, Int>.0: its value has no literal form"),
    "Function": ("@IntToInt", "true",
                 "@IntToInt.0: its value has no literal form"),
    "Unit": ("@Unit", "true", None),
}


#: The nested emitter's payload is a second input, pinned too: a value the
#: program does not construct, so the payload's refinement is the argument's
#: obligation (#1410).
_NESTED_INPUT = ("@Option<Int>", "@Option<Int>.0 == Some(0)",
                 "@Option<Int>.0 = Some(0)")


def _inputs(emitter: str, ty: str) -> tuple[str, str, list[str]]:
    """The parameters, the `requires` and the lines the inputs show."""
    param, pin, line = _TYPES[ty]
    lines = [] if line is None else [line]
    if emitter != "nested":
        return param, pin, lines
    if param == _NESTED_INPUT[0]:
        # Two `Option<Int>` parameters: the first is `@Option<Int>.1`.
        pin = pin.replace("@Option<Int>.0", "@Option<Int>.1")
        lines = [x.replace("@Option<Int>.0", "@Option<Int>.1") for x in lines]
    return (f"{param}, {_NESTED_INPUT[0]}", f"({pin}) && {_NESTED_INPUT[1]}",
            [*lines, _NESTED_INPUT[2]])


def _program(emitter: str, ty: str) -> str:
    _, ret, ensures, body, _ = _EMITTERS[emitter]
    param, pin, _ = _inputs(emitter, ty)
    return _PRELUDE + f"""
public fn f({param} -> {ret})
  requires({pin})
  ensures({ensures})
  effects(pure)
{{
  {body}
}}
"""


def _block(description: str) -> list[str] | None:
    """The lines under a description's `Counterexample:` header, or ``None``
    when it has none."""
    lines = description.split("\n")
    headers = [i for i, line in enumerate(lines)
               if line.strip() == "Counterexample:"]
    if not headers:
        return None
    assert len(headers) == 1, description
    out: list[str] = []
    for line in lines[headers[0] + 1:]:
        if not line.startswith("      "):
            break
        out.append(line.strip())
    return out


def _description(source: str, code: str) -> str:
    verified = pipeline.verify(source)
    found = [d for d in verified.diagnostics if d.error_code == code]
    assert len(found) == 1, verified.diagnostics
    return found[0].description


@pytest.mark.parametrize("ty", list(_TYPES))
@pytest.mark.parametrize("emitter", list(_EMITTERS))
def test_counterexample_by_emitter_and_type(emitter: str, ty: str) -> None:
    """Each emitter lists the inputs by name, each as its literal, and the
    result only for an `ensures`; with nothing to list it prints no header."""
    code, _, _, _, names_result = _EMITTERS[emitter]
    expected = sorted(_inputs(emitter, ty)[2])
    if names_result:
        expected.append("@Int.result = 0")
    block = _block(_description(_program(emitter, ty), code))
    assert block == (expected or None), block


def test_repro_one_counterexample_header_in_the_verifier() -> None:
    """Every emitter writes its counterexample through one helper: the
    header is written once in the verifier."""
    text = (Path(__file__).resolve().parent.parent / "vera" / "verifier.py"
            ).read_text(encoding="utf-8")
    assert text.count('"Counterexample:"') == 1


# -- The issues' programs ------------------------------------------------

_1871 = """\
type PosInt = { @Int | @Int.0 > 0 };

private fn take(@PosInt -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @PosInt.0
}

public fn a(@Int -> @Int)
  requires(@Int.0 == 0)
  ensures(true)
  effects(pure)
{
  take(@Int.0)
}

public fn b(-> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = 3;
  @Nat.0 - 5
}

public fn c(@Unit -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(-3)
}
"""


def _by_function(source: str) -> dict[str, str]:
    verified = pipeline.verify(source)
    out: dict[str, str] = {}
    for d in verified.diagnostics:
        for name in ("'a'", "'b'", "'c'"):
            if f"in {name}" in d.description:
                out[name.strip("'")] = d.description
    return out


def test_repro_1871_a_call_stand_in_is_not_listed() -> None:
    assert _block(_by_function(_1871)["a"]) == ["@Int.0 = 0"]


def test_repro_1871_no_parameters_no_header() -> None:
    description = _by_function(_1871)["b"]
    assert "Counterexample" not in description, description


def test_repro_1871_a_unit_parameter_is_not_listed() -> None:
    description = _by_function(_1871)["c"]
    assert "Counterexample" not in description, description
    assert "@Unit.0" not in description, description


def test_repro_1871_an_array_literal_constant_is_not_listed() -> None:
    source = """\
public fn f(@Int -> @Bool)
  requires(@Int.0 == 3)
  ensures(@Bool.result)
  effects(pure)
{
  array_length([@Int.0, 1]) != 2
}
"""
    block = _block(_description(source, "E500"))
    assert block == ["@Int.0 = 3", "@Bool.result = false"], block


# -- vera test -----------------------------------------------------------

#: The six types `vera test` generates: parameter, pin, the literal the
#: text and E703 show, and the JSON value `--json` gives.
_TRIAL_TYPES: dict[str, tuple[str, str, str, object]] = {
    "Bool": ("@Bool", "@Bool.0", "true", True),
    "Bool_false": ("@Bool", "!@Bool.0", "false", False),
    "Byte": ("@Byte", "byte_to_int(@Byte.0) == 7", "7", 7),
    "Nat": ("@Nat", "@Nat.0 == 7", "7", 7),
    "Int": ("@Int", "@Int.0 == -7", "-7", -7),
    "Float64": ("@Float64", "@Float64.0 == 0.1", "0.1", 0.1),
    "String": ("@String", '@String.0 == "q\\"x\\n"', '"q\\"x\\n"', 'q"x\n'),
}


def _trial_program(ty: str, *, proved: bool) -> str:
    param, pin, _, _ = _TRIAL_TYPES[ty]
    if not proved:
        # Tier 3 by an `ensures` the verifier cannot state.
        return f"""\
public fn f({param} -> @Int)
  requires({pin})
  ensures(string_length(int_to_string(@Int.result)) == 99)
  effects(pure)
{{
  0
}}
"""
    # Proved over an `assume` a trial's arguments violate, which `--distrust`
    # refutes by running it.  The `Int` it reads is the first parameter, so
    # the input under test stays `@T.0`; that `Int`'s value is the
    # generator's, and no cell reads it.
    helper = "@Int.1" if param == "@Int" else "@Int.0"
    return f"""\
public fn f(@Int, {param} -> @Int)
  requires({pin})
  ensures(@Int.result == 1)
  effects(pure)
{{
  assume({helper} == 1);
  {helper}
}}
"""


def _slot(ty: str) -> str:
    return f"{_TRIAL_TYPES[ty][0]}.0"


@pytest.mark.parametrize("ty", list(_TRIAL_TYPES))
def test_trial_text_line(ty: str, tmp_path: Path) -> None:
    path = tmp_path / "t.vera"
    path.write_text(_trial_program(ty, proved=False), encoding="utf-8")
    ran = pipeline.cli("test", "--trials", "3", path)
    expected = f"    {_slot(ty)} = {_TRIAL_TYPES[ty][2]} -> "
    assert expected in ran.stdout, ran.stdout


@pytest.mark.parametrize("ty", list(_TRIAL_TYPES))
def test_trial_json_args(ty: str, tmp_path: Path) -> None:
    path = tmp_path / "t.vera"
    path.write_text(_trial_program(ty, proved=False), encoding="utf-8")
    ran = pipeline.cli("test", "--json", "--trials", "3", path)
    failures = json.loads(ran.stdout)["functions"][0]["failures"]
    value = failures[0]["args"][_slot(ty)]
    expected = _TRIAL_TYPES[ty][3]
    assert value == expected and type(value) is type(expected), failures


@pytest.mark.parametrize("ty", list(_TRIAL_TYPES))
def test_trial_e703(ty: str) -> None:
    tested = pipeline.contract_test(
        _trial_program(ty, proved=True), trials=3, distrust=True)
    e703 = [d for d in tested.diagnostics if d.error_code == "E703"]
    assert e703, tested.diagnostics
    expected = f", {_slot(ty)} = {_TRIAL_TYPES[ty][2]} failed it at run time"
    assert expected in e703[0].description, e703[0].description


def _received(literal: str) -> str:
    """A function whose `requires` admits the one string *literal* names,
    and whose Tier 3 `ensures` holds exactly where the function received that
    string: it returns 1 then (`"1"`, one byte) and 10 otherwise."""
    return f"""\
public fn f(@String -> @Int)
  requires(@String.0 == {literal})
  ensures(string_length(int_to_string(@Int.result)) == 1)
  effects(pure)
{{
  if @String.0 == {literal} then {{ 1 }} else {{ 10 }}
}}
"""


def _trials_of(source: str) -> object:
    tested = pipeline.contract_test(source, trials=3)
    functions = [f for f in tested.result.functions if f.fn_name == "f"]
    assert len(functions) == 1, tested.result
    return functions[0]


def test_repro_1768_a_trial_is_called_with_the_string_generated() -> None:
    """A trial satisfies its own `requires`: the generated string is the one
    the model holds, U+200B, not Z3's text of it (`\\u{200b}`, six
    characters), which the function's own entry check refused."""
    fn = _trials_of(_received('"\\u{200B}"'))
    assert fn.trials_run >= 1 and fn.trials_failed == 0, fn.failures


#: The strings a trial is called with, each the model's: a character outside
#: ASCII, a quote, a newline, one outside the Basic Multilingual Plane (which
#: Z3's text spells as an escape), and the empty string.
_RECEIVED = {
    "non_ascii": '"café"',
    "quote": '"q\\"x"',
    "newline": '"a\\nb"',
    "astral": '"\\u{1F600}"',
    "empty": '""',
}


@pytest.mark.parametrize("name", list(_RECEIVED))
def test_trial_is_called_with_the_model_s_string(name: str) -> None:
    fn = _trials_of(_received(_RECEIVED[name]))
    assert fn.trials_run >= 1 and fn.trials_failed == 0, fn.failures


def test_repro_1768_reported_program(tmp_path: Path) -> None:
    path = tmp_path / "t.vera"
    path.write_text("""\
public fn f(@Int, @Bool, @Int -> @Int)
  requires(@Int.1 == -51 && @Bool.0 && @Int.0 == -53)
  ensures(string_length(int_to_string(@Int.result)) == 99)
  effects(pure)
{
  0
}
""", encoding="utf-8")
    ran = pipeline.cli("test", "--json", "--trials", "3", path)
    args = json.loads(ran.stdout)["functions"][0]["failures"][0]["args"]
    assert args == {"@Int.1": -51, "@Bool.0": True, "@Int.0": -53}, args
    text = pipeline.cli("test", "--trials", "3", path).stdout
    assert "@Int.1 = -51, @Bool.0 = true, @Int.0 = -53 -> " in text, text


# -- The renderer --------------------------------------------------------

_F64 = z3.Float64()


@pytest.mark.parametrize(("value", "text"), [
    (0.1, "0.1"), (-2.5, "-2.5"), (1e23, "100000000000000000000000.0"),
    (1e-7, "0.0000001"), (-0.0, "-0.0"), (2.0, "2.0"),
    (math.inf, "infinity()"), (-math.inf, "0.0 - infinity()"),
    (math.nan, "nan()"),
])
def test_float_literal(value: float, text: str) -> None:
    """A `Float64` is the shortest decimal that reads back as the same
    value; NaN and the infinities are the expressions that make them."""
    from vera import literals
    assert literals.text(literals.float_literal(value)) == text
    assert literals.z3_text(z3.FPVal(value, _F64)) == text
    if math.isfinite(value):
        assert float(text) == value


_FLOATS = [0.1, -2.5, 1e23, 1e-7, -0.0, 2.0, math.inf, -math.inf, math.nan]


@pytest.mark.parametrize("value", _FLOATS, ids=repr)
def test_float_text_reads_back_as_the_value(value: float) -> None:
    """The text a `Float64` is written as is a Vera expression, and a
    program returning it returns the same value, its sign of zero and NaN
    included."""
    from vera import literals
    text = literals.text(literals.float_literal(value))
    ran = pipeline.run(f"""\
public fn f(@Unit -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {text}
}}
""", "f", [])
    got = ran.value
    assert isinstance(got, float), got
    if math.isnan(value):
        assert math.isnan(got)
    else:
        assert got == value and math.copysign(1.0, got) == math.copysign(
            1.0, value), (text, got)


@pytest.mark.parametrize(("value", "text"), [
    ("a\nb", '"a\\nb"'), ('q"x', '"q\\"x"'), ("back\\slash", '"back\\\\slash"'),
    ("café", '"café"'), ("​", '"\\u{200B}"'),
    ("\U0001F600", '"\U0001F600"'),
])
def test_string_literal(value: str, text: str) -> None:
    """A `String` is its literal with the formatter's escapes, from a Python
    value and from the solver's value alike."""
    from vera import literals
    assert literals.text(literals.string_literal(value)) == text
    assert literals.z3_text(z3.StringVal(value)) == text
