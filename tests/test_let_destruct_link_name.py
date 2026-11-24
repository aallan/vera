"""A destructuring `let` names its constructor by its link name (#F1).

The linker spells every constructor by its type's link name (`Box$MkBox`,
#1694) in the nodes that name one through a `name` field.  A destructuring
`let` names its shape through a field of its own (`constructor`), so it kept
the written spelling, and the verifier's lookup of the destructured
constructor in the value's sort, which holds `Box$MkBox`, found nothing: the
block had no term and every obligation over it was a runtime check (`E522`)
where the `match` spelling of the same read is proved.

The matrix: how the destructure names its shape (the constructor, the type,
an alias of the type) x the data type (generic, non-generic, two fields) x
where the value comes from (a construction, a parameter, a `let`).  Every
cell's `ensures` is proved, as its `match` twin's is.
"""

from __future__ import annotations

import itertools

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=["vera/binding.py", "vera/smt.py"])

FILE = "destructure.vera"

#: name: (declaration, the value's type, constructor, the type's name,
#:        the binders, the slot the result reads, a construction)
_TYPES = {
    "generic": ("private data Box<T> { MkBox(T) }", "Box<Int>", "MkBox", "Box",
                "<@Int>", "@Int.0", "MkBox(5)"),
    "plain": ("private data One { MkOne(Int) }", "One", "MkOne", "One",
              "<@Int>", "@Int.0", "MkOne(5)"),
    "pair": ("private data Two { MkTwo(Int, Bool) }", "Two", "MkTwo", "Two",
             "<@Int, @Bool>", "@Int.0", "MkTwo(5, true)"),
}
_NAMES = ("constructor", "type", "alias")
_SOURCES = ("construction", "parameter", "let")


def _program(tname: str, naming: str, source: str) -> str:
    decl, te, ctor, tyname, binders, read, built = _TYPES[tname]
    alias = f"type Alias = {te};"
    shape = {"constructor": ctor, "type": tyname, "alias": "Alias"}[naming]
    if source == "construction":
        param, value, pre = "Int", built, "true"
    elif source == "parameter":
        param, value = te, f"@{te}.0"
        pre = f"match @{te}.0 {{ {ctor}({', '.join(['@Int'] + (['_'] if tname == 'pair' else []))}) -> @Int.0 == 5 }}"
    else:
        param, value, pre = "Int", f"{{ let @{te} = {built}; @{te}.0 }}", "true"
    return (
        f"{decl}\n\n{alias}\n\n"
        f"public fn f(@{param} -> @Int)\n  requires({pre})\n"
        f"  ensures(@Int.result == 5)\n  effects(pure)\n{{\n"
        f"  let {shape}{binders} = {value};\n  {read}\n}}\n")


_CELLS = list(itertools.product(_TYPES, _NAMES, _SOURCES))


@pytest.mark.parametrize("cell", [pytest.param(c, id=".".join(c)) for c in _CELLS])
def test_a_destructure_of_a_data_type_translates(cell: tuple[str, str, str]) -> None:
    verified = pipeline.verify(_program(*cell), file=FILE)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    (status,) = [o.status for o in verified.obligations
                 if o.fn_name == "f" and o.kind == "ensures"]
    assert status == "verified"


_REPRO = """\
private data Box { MkBox(Int) }

public fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 5)
  effects(pure)
{
  let MkBox<@Int> = MkBox(5);
  @Int.0
}
"""


def test_repro_a_destructure_of_a_user_data_type_is_proved() -> None:
    """`E522` at d202df53: the destructure had no term."""
    verified = pipeline.verify(_REPRO, file=FILE)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    assert [(o.kind, o.status) for o in verified.obligations
            if o.fn_name == "f" and o.kind == "ensures"] == [("ensures", "verified")]
    ran = pipeline.run(_REPRO, "f", [0], file=FILE)
    assert ran.ok and ran.value == 5, ran.trap
