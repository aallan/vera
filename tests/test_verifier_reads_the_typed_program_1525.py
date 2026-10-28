"""The verifier reads every type from the typed program (#1525).

The verifier derived two facts the checker already held, and the derivations
disagreed with the checker's.

A data type's SMT sort.  The verifier built a data type's sort from the types
a function's signature and its `let`s name, and recovered a constructor's
instantiation from the sorts of its arguments, never from the type the
checker gave the construction.  A construction of a type the function names
nowhere (a call's argument, an `if`'s arm, a `match` in place) found no sort:
it did not translate, the call taking it lost its callee's `ensures`, and a
later `requires` resting on that fact was refused (E501), while the same call
after an unused `let` of the type proved.  A type a module declares had no
sort in the entry's functions at all.  A value built from `@Nat` components
was a different sort from the same value at `Int` (`Option<Nat>` against
`Option<Int>`), so a `match` joining the two crashed Z3 (E699, #1594).  The
sort of a value is now the sort of the type the checker gave it, whatever
file declares the type, and `Nat` and `Int` are one sort, as a refinement
and its base are.

A parameter's slot name.  The verifier named each parameter's solver
constant by its own left-to-right count, so the first of two `@Int`
parameters was `@Int.0` in every counterexample, where the source calls it
`@Int.1` (#1767).  Each parameter is now named by the slot reference the
source binds it to, a generic's instance by its template's.

The SORT matrix is every place a data type is declared (the entry file, an
imported module, the prelude, a generic of the entry, the built-in `Tuple`)
x every way its value is built (a payload of an `@Int`, of a `@Nat`, a
nullary constructor) x every use that needs the value's sort (a call's
argument whose callee's `ensures` the function's rests on, the same call's
result feeding a `requires`, nested in an `Option`, an `if`'s arm, a `match`
in place, `==`), each in a function that names the type nowhere: every
obligation proves.  The MODULAR cells hold the other side of the same rule:
a construction is modelled as any other argument is, so a postcondition its
callee's contract does not establish is refused, as the same call over an
`@Int` is.  The SLOT matrix is every parameter list a name can be counted
wrong over.  Each cell is its own test, unparametrised.
"""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/verifier.py",
    "vera/smt.py",
    "vera/typed.py",
    "vera/registration.py",
])

_C = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


# =====================================================================
# The sort matrix
# =====================================================================

@dataclass(frozen=True)
class Decl:
    """Where a data type is declared, and how a program builds one."""

    name: str
    type: str
    """The type as a signature spells it."""

    payload: str
    """A construction with an `Int` payload, ``{x}`` for the payload."""

    nullary: str | None
    """A nullary construction, if the type has one."""

    other: str
    """A second construction, for an `if`'s other arm."""

    pattern: str
    """A pattern that matches the payload construction, binding nothing."""

    entry: str = ""
    """What the entry file declares or imports for it."""

    module: str | None = None
    """The module the entry imports it from, if any."""


_MODULE = ("module gen_lib;\n\n"
           "public data Tally {\n  Amber(Int),\n  Basalt\n}\n")

DECLS = (
    Decl("entry", "Gauge", "Bravo({x})", "Charlie", "Charlie", "Bravo(_)",
         entry="private data Gauge {\n  Bravo(Int),\n  Charlie\n}\n"),
    Decl("imported", "Tally", "Amber({x})", "Basalt", "Basalt", "Amber(_)",
         entry="import gen_lib(Tally);\n", module=_MODULE),
    Decl("prelude", "Option<Int>", "Some({x})", "None", "None", "Some(_)"),
    Decl("generic", "Box<Int>", "MkBox({x})", "Empty", "Empty", "MkBox(_)",
         entry="private data Box<T> {\n  MkBox(T),\n  Empty\n}\n"),
    Decl("tuple", "Tuple<Int, Int>", "Tuple({x}, 1)", None, "Tuple(2, 3)",
         "Tuple(_, _)"),
)

BUILDS = ("int", "nat", "nullary")

USES = ("argument", "precondition", "nested", "if_arm", "scrutinee",
        "equality")


def _value(decl: Decl, build: str) -> str:
    if build == "nullary":
        assert decl.nullary is not None
        return decl.nullary
    return decl.payload.format(x="@Int.0" if build == "int" else "@Nat.0")


def _program(decl: Decl, build: str, use: str) -> dict[str, str]:
    """The program of one cell: `probe` builds a value of *decl*'s type the
    way *build* says and uses it as *use* says, naming the type nowhere."""
    value = _value(decl, build)
    param = "@Nat" if build == "nat" else "@Int"
    helpers = (
        f"private fn take(@{decl.type} -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result == 4)\n  effects(pure)\n{\n  4\n}\n\n"
        f"private fn take_opt(@Option<{decl.type}> -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result == 4)\n  effects(pure)\n{\n  4\n}\n\n"
        "private fn pos(@Int -> @Int)\n  requires(@Int.0 > 0)\n"
        "  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n\n"
    )
    if use == "argument":
        probe = (f"public fn probe({param} -> @Int)\n  requires(true)\n"
                 f"  ensures(@Int.result == 4)\n  effects(pure)\n"
                 f"{{\n  take({value})\n}}\n")
    elif use == "precondition":
        probe = (f"public fn probe({param} -> @Int)\n" + _C
                 + f"{{\n  let @Int = take({value});\n  pos(@Int.0)\n}}\n")
    elif use == "nested":
        probe = (f"public fn probe({param} -> @Int)\n  requires(true)\n"
                 f"  ensures(@Int.result == 4)\n  effects(pure)\n"
                 f"{{\n  take_opt(Some({value}))\n}}\n")
    elif use == "if_arm":
        probe = (f"public fn probe({param}, @Bool -> @Int)\n  requires(true)\n"
                 f"  ensures(@Int.result == 4)\n  effects(pure)\n"
                 f"{{\n  take(if @Bool.0 then {{ {value} }} else "
                 f"{{ {decl.other} }})\n}}\n")
    elif use == "scrutinee":
        pattern = decl.nullary if build == "nullary" else decl.pattern
        probe = (f"public fn probe({param} -> @Int)\n  requires(true)\n"
                 f"  ensures(@Int.result == 4)\n  effects(pure)\n"
                 f"{{\n  match {value} {{\n    {pattern} -> 4,\n"
                 f"    _ -> 5\n  }}\n}}\n")
    else:
        probe = (f"public fn probe({param} -> @Bool)\n  requires(true)\n"
                 f"  ensures(@Bool.result)\n  effects(pure)\n"
                 f"{{\n  {value} == {value}\n}}\n")
    files = {"main.vera": decl.entry + ("\n" if decl.entry else "")
             + helpers + probe}
    if decl.module is not None:
        files["gen_lib.vera"] = decl.module
    return files


def _every_probe_obligation_proves(path: Path) -> None:
    verified = pipeline.verify(path)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    statuses = sorted(
        (o.kind.value if hasattr(o.kind, "value") else o.kind,
         o.status.value if hasattr(o.status, "value") else o.status, o.line)
        for o in verified.obligations if o.fn_name == "probe")
    assert statuses, "probe has no obligation"
    assert all(s == "verified" for _k, s, _l in statuses), statuses


@dataclass(frozen=True)
class SortCell:
    decl: Decl
    build: str
    use: str

    @property
    def name(self) -> str:
        return f"{self.decl.name}_{self.build}_{self.use}"


def _valid(decl: Decl, build: str, use: str) -> bool:
    """Whether the cell's program checks: `Tuple` has no nullary
    constructor and no `==` (E243), and a nullary constructor of a generic
    type has no type for `==` to compare at (E142)."""
    if build == "nullary" and decl.nullary is None:
        return False
    if use == "equality" and decl.name == "tuple":
        return False
    return not (use == "equality" and build == "nullary"
                and decl.name in ("prelude", "generic"))


_SORT_CELLS = tuple(
    SortCell(decl, build, use)
    for decl in DECLS for build in BUILDS for use in USES
    if _valid(decl, build, use)
)


#: The cells red at e807be43: a construction whose type the function names
#: nowhere had no sort, so it did not translate and the obligation resting
#: on it fell to a runtime check (the `ensures`) or was refused (E501).  A
#: `Tuple`'s sort was built from its components' sorts, so a `Tuple` alone
#: translated; inside an `Option` it did not.
_RED_AT_BASE: frozenset[str] = frozenset(
    c.name for c in _SORT_CELLS
    if c.decl.name != "tuple" or c.use == "nested")


def _sort_test(cell: SortCell) -> Callable[[Path], None]:
    def test(tmp_path: Path) -> None:
        path = pipeline.write_tree(tmp_path, _program(
            cell.decl, cell.build, cell.use))
        _every_probe_obligation_proves(path)
    test.__name__ = f"test_sort_{cell.name}"
    test.__doc__ = (f"A {cell.decl.name} type's value built by {cell.build}, "
                    f"used as {cell.use}, in a function naming it nowhere.")
    return test


for _cell in _SORT_CELLS:
    _test = _sort_test(_cell)
    if _cell.name in _RED_AT_BASE:
        _test = pytest.mark.xfail(strict=True, reason=(
            "red at e807be43: the construction's type has no sort"))(_test)
    globals()[f"test_sort_{_cell.name}"] = _test
del _cell, _test


def test_the_sort_matrix_spans_every_combination() -> None:
    """80 cells: 5 declaring places, 3 builds and 6 uses, less the four
    programs the checker refuses (`_valid`)."""
    assert len(_SORT_CELLS) == len({c.name for c in _SORT_CELLS}) == 80


# =====================================================================
# The modular cells: a construction is modelled as any argument is
# =====================================================================

def _ensures_status(files: dict[str, str], tmp_path: Path) -> str:
    """The status of `probe`'s `ensures`."""
    path = pipeline.write_tree(tmp_path, files)
    verified = pipeline.verify(path)
    found = [o.status.value if hasattr(o.status, "value") else o.status
             for o in verified.obligations
             if o.fn_name == "probe" and (o.kind.value if hasattr(o.kind, "value")
                                          else o.kind) == "ensures"]
    assert len(found) == 1, found
    return found[0]


def _modular_program(decl: Decl, scalar: bool) -> dict[str, str]:
    """`probe` calls a callee whose `ensures` says nothing of its result
    and claims the result is 4: over *decl*'s construction, or over the
    `@Int` itself (*scalar*)."""
    formal, argument = (("@Int", "@Int.0") if scalar else
                        (f"@{decl.type}", _value(decl, "int")))
    files = {"main.vera": (decl.entry + ("\n" if decl.entry else "")
             + f"private fn some({formal} -> @Int)\n" + _C + "{\n  4\n}\n\n"
             + "public fn probe(@Int -> @Int)\n  requires(true)\n"
             + "  ensures(@Int.result == 4)\n  effects(pure)\n"
             + f"{{\n  some({argument})\n}}\n")}
    if decl.module is not None:
        files["gen_lib.vera"] = decl.module
    return files


def _modular_test(decl: Decl) -> Callable[[Path], None]:
    def test(tmp_path: Path) -> None:
        scalar = _ensures_status(_modular_program(decl, True), tmp_path / "s")
        built = _ensures_status(_modular_program(decl, False), tmp_path / "d")
        assert scalar == "violated", scalar
        assert built == scalar, (built, scalar)
    test.__name__ = f"test_modular_{decl.name}"
    test.__doc__ = (f"A {decl.name} type's construction as an argument: its "
                    f"callee's contract is all the caller knows, as of an "
                    f"`@Int`'s.")
    return test


#: The modular cells red at e807be43: the construction did not translate,
#: so the claim fell to a runtime check where the scalar's is refused.  A
#: `Tuple` translated, and was refused as the scalar is.
_MODULAR_RED_AT_BASE: frozenset[str] = frozenset(
    d.name for d in DECLS if d.name != "tuple")

for _decl in DECLS:
    _test = _modular_test(_decl)
    if _decl.name in _MODULAR_RED_AT_BASE:
        _test = pytest.mark.xfail(strict=True, reason=(
            "red at e807be43: the construction's type has no sort"))(_test)
    globals()[f"test_modular_{_decl.name}"] = _test
del _decl, _test


# =====================================================================
# The slot matrix: a parameter is named as the source binds it
# =====================================================================

@dataclass(frozen=True)
class Slots:
    """A parameter list, the values its `requires` pins, and the names the
    counterexample must give them."""

    name: str
    files: dict[str, str]
    expect: dict[str, str | None]
    """Each parameter's slot reference, and the value it must be shown at
    (``None``: any value, the contract pins none)."""


def _fn(params: str, pins: str, ret: str = "@Int.result < 0",
        body: str = "0", head: str = "private fn foo") -> str:
    return (f"{head}({params} -> @Int)\n  requires({pins})\n"
            f"  ensures({ret})\n  effects(pure)\n{{\n  {body}\n}}\n")


SLOTS = (
    Slots("two_of_one_type", {"main.vera": _fn(
        "@Int, @Int", "@Int.1 == 3 && @Int.0 == 4")},
        {"@Int.1": "3", "@Int.0": "4"}),
    Slots("three_of_one_type", {"main.vera": _fn(
        "@Int, @Int, @Int", "@Int.2 == 3 && @Int.1 == 4 && @Int.0 == 5")},
        {"@Int.2": "3", "@Int.1": "4", "@Int.0": "5"}),
    Slots("interleaved", {"main.vera": _fn(
        "@Int, @Bool, @Int", "@Int.1 == 3 && @Int.0 == 4 && @Bool.0")},
        {"@Int.1": "3", "@Int.0": "4", "@Bool.0": "True"}),
    Slots("two_types_twice", {"main.vera": _fn(
        "@Nat, @Int, @Nat, @Int",
        "@Nat.1 == 3 && @Int.1 == 4 && @Nat.0 == 5 && @Int.0 == 6")},
        {"@Nat.1": "3", "@Int.1": "4", "@Nat.0": "5", "@Int.0": "6"}),
    Slots("alias", {"main.vera": "type Age = Int;\n\n" + _fn(
        "@Age, @Age", "@Age.1 == 3 && @Age.0 == 4")},
        {"@Age.1": "3", "@Age.0": "4"}),
    Slots("helper", {"main.vera": _fn(
        "@Int", "true", ret="true", body="bar(@Int.0, 4)",
        head="public fn foo") + "where {\n" + "\n".join(
        "  " + line if line else line for line in _fn(
            "@Int, @Int", "@Int.1 == 3 && @Int.0 == 4",
            head="fn bar").splitlines()) + "\n}\n"},
        {"@Int.1": "3", "@Int.0": "4"}),
    Slots("generic_instance", {"main.vera": _fn(
        "@T, @Int", "@Int.0 == 4", head="private forall<T> fn foo")
        + "\npublic fn main(@Int -> @Int)\n  requires(@Int.0 == 3)\n"
        "  ensures(true)\n  effects(pure)\n{\n  foo(@Int.0, 4)\n}\n"},
        {"@T.0": None, "@Int.0": "4"}),
)


def _counterexample(text: str) -> dict[str, str]:
    """The `name = value` lines of a counterexample."""
    block = text.split("Counterexample:", 1)[1]
    return dict(re.findall(r"^\s*(@[^\s=]+)\s*=\s*(\S+)\s*$", block,
                           flags=re.MULTILINE))


def _slots_test(case: Slots) -> Callable[[Path], None]:
    def test(tmp_path: Path) -> None:
        path = pipeline.write_tree(tmp_path, case.files)
        verified = pipeline.verify(path)
        refused = [d for d in verified.errors if d.error_code == "E500"]
        assert len(refused) == 1, [d.format() for d in verified.diagnostics]
        shown = _counterexample(refused[0].description)
        for slot, value in case.expect.items():
            assert slot in shown, shown
            assert value is None or shown[slot] == value, shown
    test.__name__ = f"test_slots_{case.name}"
    test.__doc__ = (f"A counterexample over {case.name.replace('_', ' ')} "
                    f"names each parameter as the source does.")
    return test


#: The slot cells red at e807be43: the verifier named the parameters by its
#: own left-to-right count.
_SLOTS_RED_AT_BASE: frozenset[str] = frozenset(c.name for c in SLOTS)

for _case in SLOTS:
    _test = _slots_test(_case)
    if _case.name in _SLOTS_RED_AT_BASE:
        _test = pytest.mark.xfail(strict=True, reason=(
            "red at e807be43: a parameter named by the verifier's own "
            "count"))(_test)
    globals()[f"test_slots_{_case.name}"] = _test
del _case, _test
