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


#: The two headers `counterexample_text` writes: the plain one, and the one
#: at a line in a body that binds a listed input's name again.
_HEADER = "Counterexample:"
_RENAMED_HEADER = (
    "Counterexample (the function's inputs, as its signature names them):")


def _header(description: str) -> str | None:
    """The description's counterexample header, or ``None``."""
    found = [line.strip() for line in description.split("\n")
             if line.strip() in (_HEADER, _RENAMED_HEADER)]
    assert len(found) <= 1, description
    return found[0] if found else None


def _block(description: str) -> list[str] | None:
    """The lines under a description's counterexample header, either of
    the two, or ``None`` when it has none."""
    lines = description.split("\n")
    headers = [i for i, line in enumerate(lines)
               if line.strip() in (_HEADER, _RENAMED_HEADER)]
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
    term = literals.string_term(value)
    assert term is not None
    assert literals.z3_text(term) == text



# -- A string into the solver --------------------------------------------

#: A string of each class of character: the builder's term read back by the
#: reader is the same string.  The binding reads `\u{..}` and `\uXXXX` as
#: escapes; the other backslash spellings it keeps.
_ROUND_TRIP = {
    "printable_ascii": "Hello, world! 123",
    "backslash_u_brace": "\\u{41}",
    "backslash_u_brace_astral": "\\u{1F600}",
    "backslash_x": "\\x41",
    "backslash_u_four": "\\u0041",
    "backslash_alone": "\\",
    "backslash_doubled": "\\\\",
    "backslash_then_brace_escape": "\\\\u{41}",
    "quote": 'q"x',
    "control": "a\x01b\x7f",
    "zero_width": "​",
    "astral": "\U0001F600",
    "alphabet_end": "\U0002FFFF",
    "empty": "",
}


@pytest.mark.parametrize("name", list(_ROUND_TRIP))
def test_string_term_round_trip(name: str) -> None:
    from vera import literals
    value = _ROUND_TRIP[name]
    term = literals.string_term(value)
    assert term is not None
    assert literals.z3_string(term) == value


@pytest.mark.parametrize("value", ["\U00030000", "a\U0010FFFF", "\ud800"],
                         ids=["above_alphabet", "max_code_point", "surrogate"])
def test_string_term_defers_what_the_sort_cannot_hold(value: str) -> None:
    """#802: a code point above U+2FFFF, or a lone surrogate, has no term."""
    from vera import literals
    assert literals.string_term(value) is None


#: A literal holding escape text, beside the character the text spells.
_ESCAPE_TEXT = {
    "brace": ('"\\\\u{41}"', '"A"'),
    "four_digits": ('"\\\\u0041"', '"A"'),
    "astral": ('"\\\\u{1F600}"', '"\\u{1F600}"'),
}


def _escape_text_program(written: str, spelled: str) -> str:
    return f"""\
public fn same(@Unit -> @Bool)
  requires(true)
  ensures(@Bool.result)
  effects(pure)
{{
  {written} == {spelled}
}}
"""


def _ensures_statuses(source: str) -> list[str]:
    verified = pipeline.verify(source)
    return [o.status for o in verified.obligations if o.kind == "ensures"]


def test_repro_1871_a_literal_holding_escape_text_is_not_the_character() -> None:
    """`"\\u{41}"` is six characters, not `"A"`: the `ensures` is false at
    run time, so it is never proved (it was, Tier 1, with the run trapping
    on the postcondition)."""
    statuses = _ensures_statuses(_escape_text_program(*_ESCAPE_TEXT["brace"]))
    assert statuses and "verified" not in statuses, statuses


@pytest.mark.parametrize("name", list(_ESCAPE_TEXT))
def test_escape_text_is_not_the_character_it_spells(name: str) -> None:
    statuses = _ensures_statuses(_escape_text_program(*_ESCAPE_TEXT[name]))
    assert statuses and "verified" not in statuses, statuses


@pytest.mark.parametrize("name", list(_ESCAPE_TEXT))
def test_escape_text_equals_itself(name: str) -> None:
    """The control: the literal equals itself, proved."""
    written = _ESCAPE_TEXT[name][0]
    assert _ensures_statuses(_escape_text_program(written, written)) == [
        "verified"]


def test_repro_1871_no_solver_string_is_built_from_text_but_by_the_builder() -> None:
    """Every solver string built from a Vera or Python string goes through
    `vera.literals.string_term`: `z3.StringVal` is called in that function
    alone."""
    root = Path(__file__).resolve().parent.parent / "vera"
    sites = [
        f"{path.relative_to(root).as_posix()}:{n}"
        for path in sorted(root.rglob("*.py"))
        for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1)
        if "StringVal(" in line and not line.lstrip().startswith("#")
    ]
    assert len(sites) == 1 and sites[0].startswith("literals.py:"), sites


# -- Whose names a counterexample lists ----------------------------------

def _named(body: str, *, ensures: str = "true", ret: str = "@Nat") -> str:
    return f"""\
public fn f(@Int -> {ret})
  requires(@Int.0 == -1)
  ensures({ensures})
  effects(pure)
{{
  {body}
}}
"""


def test_repro_1871_a_let_that_rebinds_an_input_s_name_says_whose_names() -> None:
    """At `@Int.0` after `let @Int = @Int.0 * 2`, the line reads -2; the
    block lists the parameter, -1, under the signature's name, and its
    header says so."""
    description = _description(_named("let @Int = @Int.0 * 2;\n  @Int.0"), "E503")
    assert _header(description) == _RENAMED_HEADER, description
    assert _block(description) == ["@Int.0 = -1"], description


def test_repro_1871_no_rebinding_keeps_the_plain_header() -> None:
    description = _description(_named("@Int.0"), "E503")
    assert _header(description) == _HEADER, description
    assert _block(description) == ["@Int.0 = -1"], description


def test_a_match_binder_rebinds_an_input_s_name() -> None:
    description = _description(_named(
        "match Some(@Int.0 * 2) {\n    Some(@Int) -> @Int.0,\n    None -> 0\n  }"),
        "E503")
    assert _header(description) == _RENAMED_HEADER, description
    assert _block(description) == ["@Int.0 = -1"], description


def test_an_obligation_in_a_contract_clause_keeps_the_plain_header() -> None:
    """A clause is read in the signature's scope, whatever the body binds:
    the division in the `ensures` is `E526` at `@Int.0 = -1`, the parameter,
    though the body binds `@Int` again."""
    source = _named("let @Int = 1;\n  @Int.0",
                    ensures="10 / (@Int.0 + 1) > 0", ret="@Int")
    description = _description(source, "E526")
    assert _header(description) == _HEADER, description
    assert _block(description) == ["@Int.0 = -1"], description


def test_a_binder_of_another_type_keeps_the_plain_header() -> None:
    """A `let` that binds no listed input's name renames nothing."""
    description = _description(_named("let @Bool = true;\n  @Int.0"), "E503")
    assert _header(description) == _HEADER, description
    assert _block(description) == ["@Int.0 = -1"], description


# -- One value's literal is bounded --------------------------------------

def _chain(links: int) -> z3.ExprRef:
    """`Link(Link(... End))`, *links* deep: ``links + 1`` parts."""
    chain = z3.Datatype("ValueTextChain")
    chain.declare("End")
    chain.declare("Link", ("Link_0", chain))
    sort = chain.create()
    value = sort.End
    for _ in range(links):
        value = sort.Link(value)
    return value


def _tree(depth: int, *, shared: bool) -> z3.ExprRef:
    """A complete binary tree of *depth* levels of `Node`, ``2^(depth+1) - 1``
    parts.  Shared: each `Node` holds the one subtree below it twice (one
    term).  Unshared: each leaf holds its own `Int`, so no two subtrees are
    one term."""
    tree = z3.Datatype("ValueTextTree")
    tree.declare("Leaf", ("Leaf_0", z3.IntSort()))
    tree.declare("Node", ("Node_0", tree), ("Node_1", tree))
    sort = tree.create()
    if shared:
        value = sort.Leaf(z3.IntVal(0))
        for _ in range(depth):
            value = sort.Node(value, value)
        return value
    level = [sort.Leaf(z3.IntVal(i)) for i in range(2 ** depth)]
    while len(level) > 1:
        level = [sort.Node(level[i], level[i + 1]) for i in range(0, len(level), 2)]
    return level[0]


@pytest.mark.parametrize("links", [62, 63, 64], ids=["under", "at", "over"])
def test_one_value_is_written_whole_up_to_the_budget(links: int) -> None:
    """A value of `VALUE_BUDGET` parts is written whole; one part more is
    written in part, with `...` and the note, so no reader takes it for
    the value."""
    from vera import literals
    written = literals.z3_text(_chain(links))
    assert written is not None
    whole = links + 1 <= literals.VALUE_BUDGET
    assert ("..." in written) is not whole, written
    assert written.endswith(
        f" (elided past {literals.VALUE_BUDGET} parts)") is not whole, written
    if whole:
        assert written == "Link(" * links + "End" + ")" * links


@pytest.mark.parametrize("shared", [True, False], ids=["shared", "unshared"])
def test_a_large_value_costs_the_budget_not_its_size(shared: bool) -> None:
    """2^15 - 1 parts, shared or not, write the same bounded text: the budget
    counts each place a shared subterm stands, and stops there."""
    from vera import literals
    written = literals.z3_text(_tree(14, shared=shared))
    assert written is not None and written.endswith(
        f" (elided past {literals.VALUE_BUDGET} parts)"), written
    assert len(written) < 2000, len(written)


def test_repro_1871_a_value_shared_26_deep_is_written_at_once() -> None:
    """2^27 - 1 parts by sharing, the review's example, written in bounded
    time and text (it took 39 s and 12 MB of text at 20 levels)."""
    import time

    from vera import literals
    value = _tree(26, shared=True)
    start = time.perf_counter()
    written = literals.z3_text(value)
    assert time.perf_counter() - start < 5.0
    assert written is not None and len(written) < 2000, written


def test_a_value_under_the_budget_reads_back_as_itself() -> None:
    """Below the budget the literal is the value: pinned by it, a refuted
    contract's counterexample writes the same text."""
    from vera import literals
    value = literals.z3_text(_tree(2, shared=False))
    assert value is not None and "..." not in value
    vera_value = value.replace("Leaf(", "VLeaf(").replace("Node(", "VNode(")
    source = f"""\
private data VTree {{
  VLeaf(Int),
  VNode(VTree, VTree)
}}

public fn f(@VTree -> @Int)
  requires(@VTree.0 == {vera_value})
  ensures(@Int.result == 1)
  effects(pure)
{{
  0
}}
"""
    assert _block(_description(source, "E500")) == [
        f"@VTree.0 = {vera_value}", "@Int.result = 0"]


# -- Always run: the properties every pull request's sample must hold ------
#
# The matrices above are sampled on a pull request; the tests below are not
# parametrised, so each runs every time, and each pins a property a mutant
# of this module's code breaks (the Mutation (diff) lane's survivors).

def _fake_array_reader(arrays: dict[int, tuple[int, list[z3.ExprRef]]]):
    """A reader over z3 constants stood in for arrays: id -> (length,
    first elements)."""
    def read(value: z3.ExprRef):
        return arrays.get(value.get_id())
    return read


def test_repro_literals_write_each_kind_whole() -> None:
    from vera import literals
    assert literals.text(literals.int_literal(-7)) == "-7"
    assert literals.text(literals.bool_literal(False)) == "false"
    assert literals.text(literals.float_literal(-math.inf)) == "0.0 - infinity()"
    assert literals.text(literals.float_literal(math.inf)) == "infinity()"
    assert literals.text(literals.float_literal(0.5)) == "0.5"
    # A floating-point term that is not yet a numeral is simplified first.
    three = z3.fpAdd(z3.RNE(), z3.FPVal(1.0, _F64), z3.FPVal(2.0, _F64))
    assert literals.z3_float(three) == 3.0
    assert literals.z3_text(three) == "3.0"
    # The sort's alphabet and the surrogates, at each boundary.
    assert literals.holds_string("\U0002FFFF") and not literals.holds_string("\U00030000")
    assert not literals.holds_string("\ud800") and not literals.holds_string("\udfff")
    assert literals.holds_string("퟿") and literals.holds_string("")
    term = literals.string_term("\\u{41}")
    assert term is not None and literals.z3_string(term) == "\\u{41}"
    assert literals.z3_text(z3.IntVal(5)) == "5"
    assert literals.z3_text(z3.BoolVal(True)) == "true"
    # A term no literal writes (an uninterpreted constant) has none.
    assert literals.z3_text(z3.Int("free")) is None
    assert literals.z3_text(z3.Bool("free")) is None


def test_repro_literals_write_an_array_whole_and_in_part() -> None:
    from vera import literals
    sort = z3.DeclareSort("ValueTextArr")
    two, nine, empty, outer = (z3.Const(n, sort) for n in ("two", "nine", "empty", "outer"))
    ints = [z3.IntVal(i) for i in range(9)]
    reader = _fake_array_reader({
        two.get_id(): (2, ints[:2]),
        nine.get_id(): (9, ints[:8]),
        empty.get_id(): (0, []),
    })
    assert literals.z3_text(two, reader) == "[0, 1]"
    assert literals.z3_text(empty, reader) == "[]"
    assert literals.z3_text(nine, reader) == "[0, 1, 2, 3, 4, 5, 6, 7, ... and 1 more]"
    # An array of arrays reads its elements through the same reader.
    nested = z3.DeclareSort("ValueTextArrArr")
    outer = z3.Const("outer", nested)
    reader2 = _fake_array_reader({outer.get_id(): (1, [two]), two.get_id(): (2, ints[:2])})
    assert literals.z3_text(outer, reader2) == "[[0, 1]]"
    # An element with no literal leaves the array with none.
    odd = z3.Const("odd", sort)
    assert literals.z3_text(odd, _fake_array_reader({odd.get_id(): (1, [z3.Int("x")])})) is None
    # No reader: a carrier has no literal.
    assert literals.z3_text(two) is None


def test_repro_literals_bound_one_value_at_the_budget() -> None:
    from vera import literals
    assert literals.VALUE_BUDGET == 64
    at = literals.z3_text(_chain(63))
    over = literals.z3_text(_chain(64))
    assert at == "Link(" * 63 + "End" + ")" * 63
    assert over == "Link(" * 64 + "..." + ")" * 64 + " (elided past 64 parts)"
    # The budget is per value: a second value starts afresh.
    assert literals.z3_text(_chain(63)) == at


def test_repro_render_args_writes_each_argument_and_none() -> None:
    from vera.tester import render_args
    assert render_args({}) == "no arguments"
    assert render_args({"@Bool.0": True, "@String.0": 'q"\n', "@Float64.0": 0.1,
                        "@Int.0": -7}) == (
        '@Bool.0 = true, @String.0 = "q\\"\\n", @Float64.0 = 0.1, @Int.0 = -7')


def _assumption(source: str, args: dict[str, object]) -> object:
    from vera.tester import TrialResult, _assume_on_arguments
    checked = pipeline.check(source)
    assert checked.ok, checked.diagnostics
    [decl] = [d.decl for d in checked.program.declarations
              if getattr(d.decl, "name", None) == "f"]
    assume = decl.body.statements[0].expr
    trial = TrialResult(fn_name="f", args=args, status="fail", message="")  # type: ignore[arg-type]
    return _assume_on_arguments(
        decl, assume, trial, checked.artifacts.alias_env, typed=checked.typed)


def _assume_program(params: str, predicate: str) -> str:
    return f"""\
public fn f({params} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  assume({predicate});
  0
}}
"""


def test_repro_an_assume_is_read_on_the_trial_s_vera_values() -> None:
    """E703 says whether a trial's arguments satisfy the `assume` a refuted
    proof rests on, from the arguments as Vera values (#1768)."""
    boolean = _assume_program("@Bool", "@Bool.0")
    assert _assumption(boolean, {"@Bool.0": True}) is True
    assert _assumption(boolean, {"@Bool.0": False}) is False
    text = _assume_program("@String", '@String.0 == "\\\\u{41}"')
    assert _assumption(text, {"@String.0": "\\u{41}"}) is True
    assert _assumption(text, {"@String.0": "A"}) is False
    # A string the solver's sort cannot hold: not told.
    assert _assumption(text, {"@String.0": "\U00030000"}) is None
    real = _assume_program("@Float64", "@Float64.0 > 1.5")
    assert _assumption(real, {"@Float64.0": 2.0}) is True
    assert _assumption(real, {"@Float64.0": 1.0}) is False


def test_repro_the_e703_description_counts_its_proofs() -> None:
    from vera.obligations.core import ProofObligation
    from vera.tester import TrialResult, _refutation_description
    first = ProofObligation(fn_name="f", kind="ensures", expr_text="@Int.result == 1",
                            status="verified", line=3, column=3)
    second = ProofObligation(fn_name="f", kind="ensures", expr_text="@Int.result > 0",
                             status="verified", line=4, column=3)
    one = TrialResult(fn_name="f", args={"@Bool.0": False}, status="refuted",
                      message="Postcondition violation in f", refutes=[first])
    two = TrialResult(fn_name="f", args={"@Bool.0": False}, status="refuted",
                      message="Postcondition violation in f", refutes=[first, second])
    assert _refutation_description("f", one, None) == (
        "Tier 1 proof refuted in 'f': ensures(@Int.result == 1) was proved, "
        "but the trial on @Bool.0 = false failed it at run time: "
        "Postcondition violation in f")
    assert _refutation_description("f", two, None) == (
        "Tier 1 proof refuted in 'f': ensures(@Int.result == 1) and "
        "ensures(@Int.result > 0) were each proved, but the trial on "
        "@Bool.0 = false failed one of them at run time: "
        "Postcondition violation in f")


def test_repro_the_string_seeds_are_each_tried() -> None:
    """With nothing to constrain it, a `String` parameter's inputs include
    every boundary seed, each the seed itself."""
    from vera.tester import _BOUNDARY_STRING, _generate_inputs, _get_param_types
    checked = pipeline.check("""\
public fn f(@String -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
""")
    [decl] = [d.decl for d in checked.program.declarations
              if getattr(d.decl, "name", None) == "f"]
    env = checked.artifacts.alias_env
    inputs = _generate_inputs(decl, _get_param_types(decl, env), 20, env,
                              typed=checked.typed)
    assert inputs is not None
    generated = {args[0] for args in inputs}
    assert set(_BOUNDARY_STRING) <= generated, generated


def test_repro_a_bool_argument_reaches_the_function_as_its_value() -> None:
    """The compiled function is called with 1 for `true`: `@Bool.0 == true`
    holds in it, and every trial passes."""
    fn = _trials_of("""\
public fn f(@Bool -> @Int)
  requires(@Bool.0)
  ensures(string_length(int_to_string(@Int.result)) == 1)
  effects(pure)
{
  if @Bool.0 == true then { 1 } else { 10 }
}
""")
    assert fn.trials_run >= 1 and fn.trials_failed == 0, fn.failures


def test_repro_each_emitter_writes_its_block_and_header() -> None:
    """Every emitter, for a `Bool`, an `Int` and a `Nat` input: the whole
    block, and the long header exactly where its body binds the input's
    name again (`let @Int` before an `Int` input's line)."""
    for emitter, (code, _, _, body, names_result) in _EMITTERS.items():
        for ty in ("Bool", "Int", "Nat"):
            param, _, line = _TYPES[ty]
            expected = sorted(_inputs(emitter, ty)[2])
            if names_result:
                expected.append("@Int.result = 0")
            description = _description(_program(emitter, ty), code)
            assert _block(description) == expected, (emitter, ty, description)
            renamed = f"let {param} =" in body
            assert _header(description) == (
                _RENAMED_HEADER if renamed else _HEADER), (emitter, ty, description)


def _rebound(body: str, params: str, pin: str, ret: str = "@Int") -> str:
    return _PRELUDE + f"""
public fn f({params} -> {ret})
  requires({pin})
  ensures(true)
  effects(pure)
{{
  {body}
}}
"""


def test_repro_the_emitters_no_template_rebinds_for_say_whose_names() -> None:
    """The emitters no template above rebinds an input for: a call's
    precondition (E501), a payload's refinement (E505), an `assert` (E507)
    and an index (E527), each after a `let` of the input's type, each the
    long header and the parameter's value."""
    call = _description(_rebound("let @Int = 0;\n  need(@Int.0)",
                                 "@Int", "@Int.0 == 3"), "E501")
    assert _header(call) == _RENAMED_HEADER and _block(call) == ["@Int.0 = 3"], call
    payload = _description(_rebound(
        "let @Option<Int> = @Option<Int>.0;\n  consume(@Option<Int>.0)",
        "@Option<Int>", "@Option<Int>.0 == Some(0)"), "E505")
    assert _header(payload) == _RENAMED_HEADER, payload
    assert _block(payload) == ["@Option<Int>.0 = Some(0)"], payload
    assert "the refinement `Option<{@Int | ...}>` writes on a component" in payload, payload
    for code, body in (
            ("E507", "let @Int = 0;\n  assert(@Int.0 == 1);\n  0"),
            ("E527", "let @Int = 5;\n  [1, 2][@Int.0]")):
        rebound = _description(_rebound(body, "@Int", "@Int.0 == 3"), code)
        assert _header(rebound) == _RENAMED_HEADER, (code, rebound)
        assert _block(rebound) == ["@Int.0 = 3"], (code, rebound)


def test_repro_a_refinement_predicate_lists_its_binder() -> None:
    """A predicate's own obligation lists its binder, by the base's slot
    name, and the base's facts hold of it: `10 / (@Nat.0 + 1)` divides by
    no zero."""
    divides = _PRELUDE + """
type Tenth = { @Int | 10 / @Int.0 > 0 };
type NatTenth = { @Nat | 10 / (@Nat.0 + 1) > 0 };

public fn f(@Tenth, @NatTenth -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""
    verified = pipeline.verify(divides)
    found = [d for d in verified.diagnostics if d.error_code == "E526"]
    assert len(found) == 1, verified.diagnostics
    assert _header(found[0].description) == _HEADER, found[0].description
    assert _block(found[0].description) == ["@Int.0 = 0"], found[0].description


def test_repro_a_generic_refined_return_lists_its_inputs() -> None:
    """A generic function's refined return, decided before its clones: the
    `Int` input as its literal, the type variable's with the note."""
    source = _PRELUDE + """
private forall<T> fn bad(@T, @Int -> @PosInt)
  requires(@Int.0 == -1)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""
    verified = pipeline.verify(source)
    found = [d for d in verified.diagnostics if d.error_code == "E505"]
    assert len(found) == 1, verified.diagnostics
    assert _block(found[0].description) == [
        "@Int.0 = -1", "@T.0: its value has no literal form"], found[0].description


def test_repro_an_ensures_lists_each_type_s_input_and_the_body_s_result() -> None:
    """One emitter over every input type of the matrix, and the result the
    body gives (1, not the declared constant's 0)."""
    for ty, (param, pin, line) in _TYPES.items():
        source = _PRELUDE + f"""
public fn f({param} -> @Int)
  requires({pin})
  ensures(@Int.result == 0)
  effects(pure)
{{
  1
}}
"""
        expected = ([] if line is None else [line]) + ["@Int.result = 1"]
        assert _block(_description(source, "E500")) == expected, ty


def test_repro_an_array_no_query_reads_is_empty() -> None:
    """An `Array` input whose length no query reads is unconstrained: the
    model holds it at length 0, `[]`."""
    source = _PRELUDE + """
public fn f(@Array<Int> -> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{
  1
}
"""
    assert _block(_description(source, "E500")) == [
        "@Array<Int>.0 = []", "@Int.result = 1"]


def test_repro_a_predicate_binds_its_binder_under_its_own_key() -> None:
    """A predicate's binder is listed by its base's slot name, the one a
    parameter of that type is named by (`@Option<Int>.0` for `@Option<Cnt>`),
    not by the first reference the traversal meets (the arm's `@Int`, which
    listed it as `@Int.0 = Some(0)`), and it is read
    under its references' key; the facts of a refined base hold of the
    binder (`PosTenth` divides by no zero)."""
    source = _PRELUDE + """
type Cnt = Int;
type Payload = { @Option<Cnt> | match @Option<Cnt>.0 { Some(@Int) -> 10 / @Int.0 > 0, None -> true } };
type PosTenth = { @PosInt | 10 / @PosInt.0 > 0 };

public fn f(@Payload, @PosTenth -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""
    verified = pipeline.verify(source)
    found = [d for d in verified.diagnostics if d.error_code == "E526"]
    assert len(found) == 1, verified.diagnostics
    assert _block(found[0].description) == ["@Option<Int>.0 = Some(0)"], found[0].description


def test_repro_a_generic_function_s_inputs_are_one_constant_each() -> None:
    """The generic fast path declares each input under its own name: two
    `Int` inputs pinned to different values are two values, and the refined
    return is refuted at them."""
    source = _PRELUDE + """
private forall<T> fn bad(@T, @Int, @Int -> @PosInt)
  requires(@Int.1 == 1 && @Int.0 == -1)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""
    verified = pipeline.verify(source)
    found = [d for d in verified.diagnostics if d.error_code == "E505"]
    assert len(found) == 1, verified.diagnostics
    assert _block(found[0].description) == [
        "@Int.0 = -1", "@Int.1 = 1", "@T.0: its value has no literal form"]


def test_repro_a_reset_context_lists_no_earlier_input() -> None:
    """A warm context reused for the next function forgets the last one's
    inputs."""
    from vera.smt import SmtContext
    from vera.types import INT
    ctx = SmtContext()
    ctx.declare_input("@Int.0", ctx.declare_int("@Int.0"), INT)
    assert ctx.check_valid(z3.BoolVal(False), []).counterexample.shown == (
        ("@Int.0", "0"),)
    ctx.reset()
    assert ctx.check_valid(z3.BoolVal(False), []).counterexample.shown == ()


def test_repro_the_trial_report_shows_three_failures(tmp_path: Path) -> None:
    """The text report shows a function's first three failing trials."""
    path = tmp_path / "t.vera"
    path.write_text("""\
public fn f(@Int -> @Int)
  requires(true)
  ensures(string_length(int_to_string(@Int.result)) == 99)
  effects(pure)
{
  @Int.0
}
""", encoding="utf-8")
    ran = pipeline.cli("test", "--trials", "10", path)
    lines = [line for line in ran.stdout.splitlines() if line.startswith("    @Int.0 = ")]
    assert len(lines) == 3, ran.stdout


def test_repro_a_refutation_decided_on_a_literal_lists_nothing() -> None:
    """A narrowing decided on a literal (#1251) has no model and no
    counterexample: the description says what the value is, and no header
    stands over nothing."""
    source = """\
type Small = { @Byte | byte_to_int(@Byte.0) < 10 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Small = 200;
  @Int.0
}
"""
    description = _description(source, "E505")
    assert _header(description) is None and "200" in description, description
