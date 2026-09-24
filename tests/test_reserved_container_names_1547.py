"""#1547 — the built-in container names are reserved (E158).

The checker gives a built-in type and a ``data`` declaration of its name one
type, ``AdtType(name, args)``, whenever the two take the same number of type
arguments.  Nothing downstream can then tell a value of the built-in from a
value of the declaration, and the program runs to a wrong result:

* ``show(decimal_from_int(5))`` beside ``data Decimal { MkShadow(Int) }``
  printed ``5`` on ``main`` and ``MkShadow(0)`` on the release branch;
* ``show([1, 2])`` beside ``data Array<T> { MkArr(T) }`` printed ``[1, 2]``
  on ``main`` and built a module that fails to load on the release branch;
* ``unwrap(decimal_from_int(5))``, matching ``MkShadow(@Int)``, returned
  ``0`` on both: the host handle read as a heap object.

So ``Array``, ``Map``, ``Set`` and ``Decimal`` join ``Future``, ``Tuple`` and
the primitive type names: a ``data`` declaration of one is refused at check
(E158), at any number of type parameters, in the entry file and in a module
alike.  Only the data namespace is reserved.  No built-in constructor has a
container's name, so a constructor may still take one, and a ``type`` alias
of one is still legal (``tests/test_name_resolution_spine_1316.py``).

* :class:`TestTheClassMatrix` — every name, at no type parameters, at the
  built-in's own count and at another count, declared in the entry file and
  in an imported module, alone and beside a built-in value of that type.
  Every cell is refused with exactly one E158, at the declaration.
* :class:`TestTheReportedPrograms` — the #1547 programs, refused.
* :class:`TestTheControls` — the same programs without the declaration run,
  so no refusal cell passes by refusing the built-in value itself.
* :class:`TestAConstructorOfTheNameStaysLegal` — the boundary: a constructor
  named like a container is accepted and leaves the built-in untouched.
"""
from __future__ import annotations

import re
from pathlib import Path

import pytest

from tests.test_check_implies_compile import Outcome, pipeline, run_main
from vera.codegen.core import _CONTAINER_NAMES

_CONTRACT = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

#: Each container: the built-in type's number of type arguments, and a
#: built-in value of it with the type ``main`` returns it at and the value
#: the control (no declaration) returns.
_CONTAINERS: dict[str, tuple[int, str, str, object]] = {
    "Array": (1, "String", "show([1, 2])", "[1, 2]"),
    "Map": (2, "Int", "map_size(map_insert(map_new(), 1, 2))", 1),
    "Set": (1, "Int", "set_size(set_add(set_new(), 1))", 1),
    "Decimal": (0, "String", "show(decimal_from_int(5))", "5"),
}

_PARAMS = ("A", "B", "C")


def _arities(name: str) -> list[int]:
    """None, the built-in's own count, and one other count."""
    own = _CONTAINERS[name][0]
    return sorted({0, own, 2 if own == 1 else 1})


def _fn(name: str, ret: str, body: str) -> str:
    return f"public fn {name}(@Unit -> @{ret})\n{_CONTRACT}{{\n  {body}\n}}\n"


def _decl(name: str, arity: int, visibility: str) -> str:
    """``data <name>`` at *arity* type parameters, each carried by a field."""
    params = _PARAMS[:arity]
    head = f"{name}<{', '.join(params)}>" if params else name
    fields = ", ".join(params) if params else "Int"
    return f"{visibility} data {head} {{\n  MkZz({fields})\n}}\n\n"


def _program(
    name: str, arity: int | None, placement: str, use: str,
) -> tuple[dict[str, str], str]:
    """The files, and the one that holds the declaration.

    *arity* ``None`` leaves the declaration out: the control.  *use*
    ``"alone"`` returns a literal; ``"value"`` returns the built-in value of
    the container, in the namespace that declares the name.
    """
    _own, ret, value, _expected = _CONTAINERS[name]
    ret, body = (ret, value) if use == "value" else ("Int", "0")
    if placement == "entry":
        decl = "" if arity is None else _decl(name, arity, "private")
        return {"main.vera": decl + _fn("main", ret, body)}, "main.vera"
    decl = "" if arity is None else _decl(name, arity, "public")
    return {
        "zlib.vera": "module zlib;\n\n" + decl + _fn("probe", ret, body),
        "main.vera": "import zlib;\n\n" + _fn("main", ret, "zlib::probe(())"),
    }, "zlib.vera"


def _assert_refused_once_at_the_declaration(
    out: Outcome, files: dict[str, str], declaring: str, name: str,
) -> None:
    """One E158, located on the declaration's ``data`` line in its file."""
    assert not out.accepted, f"{name}: accepted — {out.describe()}"
    assert [d.error_code for d in out.check_errors] == ["E158"], out.describe()
    diag = out.check_errors[0]
    line = next(
        number for number, text in enumerate(
            files[declaring].splitlines(), start=1)
        if re.match(rf"(public |private )data {name}\b", text))
    assert diag.location.line == line, (diag.location, line)
    assert Path(diag.location.file or "").name == declaring, diag.location
    # The message names the rule, the rationale says why for these four
    # built-in types (§2 calls each a built-in type, `Decimal` included),
    # and the fix tells the writer to rename the type.
    assert f"'{name}' is a reserved built-in type name" in diag.description, (
        diag.description)
    assert (f"'{name}' is a built-in type. Declared with the built-in's "
            "number of type arguments") in diag.rationale, diag.rationale
    assert diag.fix.startswith("Rename the data type"), diag.fix


def _matrix() -> list[object]:
    return [
        pytest.param(name, arity, placement, use,
                     id=f"{name}<{arity}>-{placement}-{use}")
        for name in sorted(_CONTAINERS) for arity in _arities(name)
        for placement in ("entry", "module") for use in ("alone", "value")
    ]


class TestTheClassMatrix:
    """Every cell of the class is refused, the same way."""

    def test_the_matrix_covers_every_container(self) -> None:
        """Keyed by the names code generation branches on as containers, so
        a container added there without a reservation fails here."""
        assert set(_CONTAINERS) == set(_CONTAINER_NAMES)

    @pytest.mark.parametrize("name,arity,placement,use", _matrix())
    def test_refused_with_E158(
        self, tmp_path: Path, name: str, arity: int, placement: str, use: str,
    ) -> None:
        files, declaring = _program(name, arity, placement, use)
        _assert_refused_once_at_the_declaration(
            pipeline(tmp_path, files), files, declaring, name)


class TestTheControls:
    """The matrix's programs without the declaration run, in both
    placements, to the value the built-in gives."""

    @pytest.mark.parametrize("placement", ["entry", "module"])
    @pytest.mark.parametrize("name", sorted(_CONTAINERS))
    def test_runs_without_the_declaration(
        self, tmp_path: Path, name: str, placement: str,
    ) -> None:
        files, _declaring = _program(name, None, placement, "value")
        out = pipeline(tmp_path, files)
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", _CONTAINERS[name][3])


#: The #1547 reports.  ``main`` (6dc41d40) and the release branch
#: (cc61fb9c) both accepted every one at check.
_REPORTED = {
    # main printed 5; the release branch printed MkShadow(0).
    "decimal-show": (
        "private data Decimal {\n  MkShadow(Int)\n}\n\n",
        "String", "show(decimal_from_int(5))"),
    # main printed [1, 2]; the release branch built an unloadable module.
    "generic-array-show": (
        "private data Array<T> {\n  MkArr(T)\n}\n\n",
        "String", "show([1, 2])"),
    # main and the release branch returned 0: the handle read as MkShadow.
    "decimal-as-the-declaration": (
        "private data Decimal {\n  MkShadow(Int)\n}\n\n"
        "private fn unwrap(@Decimal -> @Int)\n" + _CONTRACT
        + "{\n  match @Decimal.0 {\n    MkShadow(@Int) -> @Int.0\n  }\n}\n\n",
        "Int", "unwrap(decimal_from_int(5))"),
    # main dropped main (E602, E620); the release branch returned 0.
    "array-as-the-declaration": (
        "private data Array<T> {\n  MkArr(T)\n}\n\n"
        "private fn first(@Array<Int> -> @Int)\n" + _CONTRACT
        + "{\n  match @Array<Int>.0 {\n    MkArr(@Int) -> @Int.0\n  }\n}\n\n",
        "Int", "first([1, 2])"),
}


class TestTheReportedPrograms:
    @pytest.mark.parametrize("case", sorted(_REPORTED))
    def test_refused_with_E158(self, tmp_path: Path, case: str) -> None:
        decl, ret, body = _REPORTED[case]
        files = {"main.vera": decl + _fn("main", ret, body)}
        name = "Decimal" if "decimal" in case else "Array"
        _assert_refused_once_at_the_declaration(
            pipeline(tmp_path, files), files, "main.vera", name)


class TestAConstructorOfTheNameStaysLegal:
    """The reservation is the DATA namespace only.

    ``Tuple`` and ``Future`` are reserved as constructor names as well,
    because the built-in has a constructor of that name whose layout slot a
    user's would take.  No built-in constructor is called ``Array``,
    ``Map``, ``Set`` or ``Decimal``, so a constructor of one of those names
    collides with nothing: it is accepted, renders as itself, and the
    built-in value beside it renders as in the control.
    """

    @pytest.mark.parametrize("name", sorted(_CONTAINERS))
    def test_accepted_and_both_render(self, tmp_path: Path, name: str) -> None:
        _own, _ret, value, expected = _CONTAINERS[name]
        shown = value if value.startswith("show(") else f"show({value})"
        files = {"main.vera": (
            f"private data ZzBox {{\n  {name}(Int)\n}}\n\n"
            + _fn("main", "String",
                  f"string_concat(show({name}(3)), {shown})"))}
        out = pipeline(tmp_path, files)
        assert out.accepted and out.compiles_clean, out.describe()
        assert run_main(out) == ("ok", f"{name}(3){expected}")
