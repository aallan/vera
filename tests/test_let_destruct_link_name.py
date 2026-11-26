"""A destructuring `let` names its constructor by its link name (#1924).

The linker spells every constructor by its type's link name (`Box$MkBox`,
#1694) in the nodes that name one through a `name` field.  A destructuring
`let` names its shape through a field of its own (`constructor`), so it kept
the written spelling, and the verifier's lookup of the destructured
constructor in the value's sort, which holds `Box$MkBox`, found nothing: the
block had no term and every obligation over it was a runtime check (`E522`)
where the `match` spelling of the same read is proved.

The matrix: how the destructure names its shape (the constructor, the type,
an alias of the type) x the data type (generic, non-generic, two fields,
two fields of one type) x where the value comes from (a construction, a
parameter, a `let`).  Every cell's `ensures` is proved, as its `match`
twin's is.  The two `Int` fields are unequal and read by a subtraction, so a
destructure that swapped them proves nothing, and the built cells are run.
"""

from __future__ import annotations

import itertools
from pathlib import Path

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=["vera/binding.py", "vera/smt.py"])

FILE = "destructure.vera"

#: name: (declaration, the value's type, constructor, the type's name,
#:        the binders, the slot the result reads, a construction, the
#:        parameter's precondition)
_TYPES = {
    "generic": ("private data Box<T> { MkBox(T) }", "Box<Int>", "MkBox", "Box",
                "<@Int>", "@Int.0", "MkBox(5)",
                "match @Box<Int>.0 { MkBox(@Int) -> @Int.0 == 5 }"),
    "plain": ("private data One { MkOne(Int) }", "One", "MkOne", "One",
              "<@Int>", "@Int.0", "MkOne(5)",
              "match @One.0 { MkOne(@Int) -> @Int.0 == 5 }"),
    "pair": ("private data Two { MkTwo(Int, Bool) }", "Two", "MkTwo", "Two",
             "<@Int, @Bool>", "@Int.0", "MkTwo(5, true)",
             "match @Two.0 { MkTwo(@Int, _) -> @Int.0 == 5 }"),
    # The first field minus the second: 7 - 2.  Swapped, it reads -5.
    "ints": ("private data Ints { MkInts(Int, Int) }", "Ints", "MkInts", "Ints",
             "<@Int, @Int>", "@Int.1 - @Int.0", "MkInts(7, 2)",
             "match @Ints.0 { MkInts(@Int, @Int) -> @Int.1 - @Int.0 == 5 }"),
}
_NAMES = ("constructor", "type", "alias")
_SOURCES = ("construction", "parameter", "let")


def _program(tname: str, naming: str, source: str) -> str:
    decl, te, ctor, tyname, binders, read, built, pre_param = _TYPES[tname]
    alias = f"type Alias = {te};"
    shape = {"constructor": ctor, "type": tyname, "alias": "Alias"}[naming]
    if source == "construction":
        param, value, pre = "Int", built, "true"
    elif source == "parameter":
        param, value, pre = te, f"@{te}.0", pre_param
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
    if cell[2] != "parameter":
        ran = pipeline.run(_program(*cell), "f", [0], file=FILE)
        assert ran.ok and ran.value == 5, ran.trap


def _guarded_program(tname: str, naming: str) -> str:
    """A refined binder of an opaque value, passed to a precondition that
    only the bind's guard establishes."""
    decl, te, ctor, tyname = _TYPES[tname][:4]
    shape = {"constructor": ctor, "type": tyname, "alias": "Alias"}[naming]
    return (
        f"{decl}\n\ntype Alias = {te};\n\ntype Pos = {{ @Int | @Int.0 > 0 }};\n\n"
        "private fn need(@Int -> @Int)\n  requires(@Int.0 > 0)\n  ensures(true)\n"
        "  effects(pure)\n{\n  @Int.0\n}\n\n"
        f"private fn mk(@Int -> @{te})\n  requires(true)\n  ensures(true)\n"
        f"  effects(pure)\n{{\n  {ctor}(@Int.0)\n}}\n\n"
        "public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
        f"  effects(pure)\n{{\n  let {shape}<@Pos> = mk(@Int.0);\n  need(@Pos.0)\n}}\n")


@pytest.mark.parametrize("cell", [
    pytest.param((t, n), id=f"{t}.{n}")
    for t in ("generic", "plain") for n in _NAMES])
def test_a_destructure_named_by_its_type_keeps_the_guard_fact(
        cell: tuple[str, str]) -> None:
    """The bind's guard establishes `@Pos` whichever name the shape is
    written with, so the call's precondition is proved: read under the
    type's or the alias's name, the guard fact was dropped and the call
    refused (`E501`) at 71b3d463."""
    verified = pipeline.verify(_guarded_program(*cell), file=FILE)
    assert [o.status for o in verified.obligations
            if o.fn_name == "f" and o.kind == "call_pre"] == ["verified"]
    assert "E501" not in [d.error_code for d in verified.diagnostics]
    ran = pipeline.run(_guarded_program(*cell), "f", [3], file=FILE)
    assert ran.ok and ran.value == 3, ran.trap


def test_repro_a_type_named_destructure_proves_the_call_its_guard_admits() -> None:
    """`let One<@Pos> = mk(@Int.0); need(@Pos.0)`: `E501` at 71b3d463."""
    verified = pipeline.verify(_guarded_program("plain", "type"), file=FILE)
    assert [o.status for o in verified.obligations
            if o.fn_name == "f" and o.kind == "call_pre"] == ["verified"]


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


_LINKED = """\
private data Box {{ MkBox(Int) }}

type Alias = Box;

public fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 5)
  effects(pure)
{{
  let {shape}<@Int> = MkBox(5);
  @Int.0
}}
"""


@pytest.mark.parametrize("shape, linked", [
    ("MkBox", "Box$MkBox"), ("Box", "Box"), ("Alias", "Alias")])
def test_the_linker_names_a_destructures_constructor(shape: str, linked: str) -> None:
    """The root of #1924, at the linker: a destructure that names its shape
    by a constructor carries the constructor's link name, as every other
    constructor spelling does; one that names it by the type or an alias
    keeps the type's name.  `MkBox` stayed `MkBox` at 252ddf61."""
    from vera import ast as vast
    from vera.binding import bind_program, link
    from vera.prelude import prelude_declarations

    checked = pipeline.check(_LINKED.format(shape=shape), file=FILE)
    assert checked.ok, [d.error_code for d in checked.errors]
    modules = checked.resolved or []
    prelude, _source = prelude_declarations(
        checked.program, {m.path: m.program for m in modules})
    program, _linked_modules = link(
        checked.program, modules, bind_program(checked.program, modules, prelude))
    found: list[str] = []
    stack: list[object] = [program]
    while stack:
        node = stack.pop()
        if isinstance(node, vast.LetDestruct):
            found.append(node.constructor)
        if isinstance(node, vast.Node):
            stack.extend(getattr(node, name) for name in node.__dataclass_fields__)
        elif isinstance(node, (list, tuple)):
            stack.extend(node)
    assert found == [linked], found


_IMPORTED_LIB = """\
module boxlib;

public data Box {
  MkBox(Int)
}
"""

_IMPORTED = """\
import boxlib;

type Alias = Box;

public fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 5)
  effects(pure)
{{
  let {shape}<@Int> = MkBox(5);
  @Int.0
}}
"""


@pytest.mark.parametrize("shape", ["MkBox", "Box", "Alias"])
def test_repro_a_destructure_of_an_imported_data_type_is_proved(
    tmp_path: Path, shape: str,
) -> None:
    """An imported type's link name (`mod$boxlib$Box`) is not the name it is
    written by, so the destructure reads it only under that link name.  `Box`
    was `E522` (no term) at 58084ab0: the SMT layer took a shape for a type
    only when its name was among the local data types and aliases."""
    (tmp_path / "boxlib.vera").write_text(_IMPORTED_LIB, encoding="utf-8")
    main = tmp_path / "main.vera"
    main.write_text(_IMPORTED.format(shape=shape), encoding="utf-8")
    verified = pipeline.verify(main)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    assert [(o.kind, o.status) for o in verified.obligations
            if o.fn_name == "f" and o.kind == "ensures"] == [("ensures", "verified")]
    ran = pipeline.run(main, "f", [0])
    assert ran.ok and ran.value == 5, ran.trap
