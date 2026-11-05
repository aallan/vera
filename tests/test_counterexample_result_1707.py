"""A refuted postcondition's counterexample prints the result the body gives
at the printed input (#1707).

The goal of an `ensures` is translated with `@T.result` replaced by the
body's term (`SmtContext.set_result_var(body_expr)`), so the `@result`
constant the function declares is in no query: the counterexample printed
it as the model left it, `0` (or `False`, or a sort's first constructor)
whatever the body returned.  The class is every refuted `ensures`, whatever
the body's shape, so the matrix spans the body shapes the reports and the
lane named: a `match` of two and of three arms, a literal arm, a `_` arm, an
`if` nested in an arm, a body with no `match`, a non-commutative operation
over two parameters, and a call.

The oracle is the run: each program's refuted `ensures` is replaced by
`ensures(true)`, the function is called at the counterexample's printed
input, and the printed `@T.result` must equal the value the call returns.
"""

from __future__ import annotations

import re

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=["vera/smt.py"])


def _fn(name: str, sig: str, ensures: str, body: str) -> str:
    return (f"public fn {name}({sig})\n  requires(true)\n  ensures({ensures})\n"
            f"  effects(pure)\n{{\n  {body}\n}}\n")


#: name -> (declarations before the function, function name, signature,
#: refuted ensures, body, the printed input's slot names in argument order).
_SHAPES: dict[str, tuple[str, str, str, str, str, tuple[str, ...]]] = {
    "issue_match": (
        "", "g", "@Option<Int> -> @Int", "@Int.result == 0",
        "match @Option<Int>.0 {\n    Some(@Int) -> @Int.0,\n    None -> 0\n  }",
        ("@Option<Int>.0",)),
    "two_arms": (
        "", "t", "@Bool -> @Int", "@Int.result > 5",
        "match @Bool.0 {\n    true -> 7,\n    false -> 3\n  }",
        ("@Bool.0",)),
    "three_arms": (
        "private data Tri {\n  A(Int),\n  B,\n  C(Int)\n}\n\n",
        "t3", "@Tri -> @Int", "@Int.result < 100",
        "match @Tri.0 {\n    A(@Int) -> @Int.0 + 1,\n    B -> 0,\n"
        "    C(@Int) -> @Int.0 * 2\n  }",
        ("@Tri.0",)),
    "literal_arm": (
        "", "lit", "@Int -> @Int", "@Int.result != 42",
        "match @Int.0 {\n    7 -> 42,\n    _ -> @Int.0 + 1\n  }",
        ("@Int.0",)),
    "wildcard_arm": (
        "", "w", "@Option<Int> -> @Int", "@Int.result >= 0",
        "match @Option<Int>.0 {\n    Some(@Int) -> @Int.0 - 3,\n    _ -> 1\n  }",
        ("@Option<Int>.0",)),
    "nested_if": (
        "", "ni", "@Option<Int> -> @Int", "@Int.result < 10",
        "match @Option<Int>.0 {\n    Some(@Int) -> if @Int.0 > 5 then {\n"
        "      @Int.0 * 3\n    } else {\n      0\n    },\n    None -> 2\n  }",
        ("@Option<Int>.0",)),
    "no_match": (
        "", "bar", "@Int -> @Int", "@Int.result < 0", "@Int.0 + 10",
        ("@Int.0",)),
    "subtraction": (
        "", "s", "@Int, @Int -> @Int", "@Int.result != 5 || @Int.0 != 2",
        "@Int.1 - @Int.0",
        ("@Int.1", "@Int.0")),
    "call": (
        "private fn one(@Int -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result == 1)\n  effects(pure)\n{\n  1\n}\n\n",
        "c", "@Int -> @Int", "@Int.result == 0", "one(@Int.0)",
        ("@Int.0",)),
    "bool_result": (
        "", "b", "@Int -> @Bool", "@Bool.result == false",
        "@Int.0 > 3",
        ("@Int.0",)),
}

_LINE = re.compile(r"^\s+(@[^=]+?) = (.+)$")


def _counterexample(source: str) -> dict[str, str]:
    verified = pipeline.verify(source)
    e500 = [d for d in verified.errors if d.error_code == "E500"]
    assert len(e500) == 1, [d.error_code for d in verified.errors]
    out: dict[str, str] = {}
    for line in e500[0].description.splitlines():
        m = _LINE.match(line)
        if m:
            out[m.group(1).strip()] = m.group(2).strip()
    return out


def _literal(value: str) -> str:
    """A printed model value as Vera source: `False` -> `false`, a negative
    literal parenthesised as a subtraction."""
    value = {"False": "false", "True": "true"}.get(value, value)
    return re.sub(r"(?<![\w.])-(\d+)", r"(0 - \1)", value)


def _run(source: str) -> str:
    """What `vera run --fn probe` prints for *source*'s `probe`."""
    ran = pipeline.run(source, "probe", [], file="twin.vera")
    assert ran.ok, ran.trap
    return str(ran.execution.value)


@pytest.mark.parametrize("shape", sorted(_SHAPES))
def test_the_printed_result_is_the_bodys_value_at_the_printed_input(
        shape: str) -> None:
    decls, name, sig, ensures, body, inputs = _SHAPES[shape]
    ce = _counterexample(decls + _fn(name, sig, ensures, body))
    ret = sig.rsplit("-> @", 1)[1]
    result_key = f"@{ret}.result"
    assert result_key in ce, ce
    args = ", ".join(_literal(ce[slot]) for slot in inputs)
    twin = (decls + _fn(name, sig, "true", body)
            + f"\npublic fn probe(@Unit -> @{ret})\n  requires(true)\n"
              f"  ensures(true)\n  effects(pure)\n{{\n  {name}({args})\n}}\n")
    ran = _run(twin)
    if ret == "Bool":
        # A returned `Bool` is its WASM `i32`.
        ran = {"1": "true", "0": "false"}.get(ran, ran)
    printed = {"False": "false", "True": "true"}.get(
        ce[result_key], ce[result_key])
    assert printed == ran, (ce, ran)


def test_repro_1707_a_match_prints_the_arm_it_took() -> None:
    """The issue's program: `Some(2)` printed beside `@Int.result = 0`, where
    the body returns 2; whatever `Some(n)` the model picks, the printed
    result is `n`."""
    decls, name, sig, ensures, body, _ = _SHAPES["issue_match"]
    ce = _counterexample(decls + _fn(name, sig, ensures, body))
    # The relation, not the model's choice: the arm taken returns the
    # payload, so the printed result is the printed `Some`'s payload (and
    # not 0, which the refutation rules out).
    payload = re.fullmatch(r"Some\((-?\d+)\)", ce["@Option<Int>.0"])
    assert payload is not None, ce
    assert ce["@Int.result"] == payload.group(1) != "0", ce


def test_repro_1707_a_body_with_no_match_prints_its_value() -> None:
    """The line found writing #1757's instrument: `@Int.0 = 3` beside
    `@Int.result = 0`, where the body's value at 3 is 13."""
    source = """\
private fn bar(@Int -> @Int)
  requires(@Int.0 == 3)
  ensures(@Int.result < 0)
  effects(pure)
{
  @Int.0 + 10
}
"""
    ce = _counterexample(source)
    assert ce == {"@Int.0": "3", "@Int.result": "13"}
