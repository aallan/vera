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
wrong over.  The NESTED-PATH cells hold the source walk's reading of an
opaque source's declarations down a nested pattern's path, which the
verifier's records and code generation's guards share.  The last cells pin
an `==` of a data type at `Nat` with the same at `Int` at Tier 3 (#1814), a
clone with no template as the table's defect, and a clone's result named by
its template's, as its parameters are.  Each cell is its own test,
unparametrised.
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
    "vera/narrowing.py",
    "vera/wasm/data.py",
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
    globals()[f"test_sort_{_cell.name}"] = _sort_test(_cell)
del _cell


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


for _decl in DECLS:
    globals()[f"test_modular_{_decl.name}"] = _modular_test(_decl)
del _decl


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


for _case in SLOTS:
    globals()[f"test_slots_{_case.name}"] = _slots_test(_case)
del _case


# =====================================================================
# A type variable a construction leaves open takes its position's type
# =====================================================================

_OPEN_NULLARY = """\
private fn take(@Option<Bool> -> @Int)
  requires(match @Option<Bool>.0 { Some(@Bool) -> @Bool.0, None -> true })
  ensures(@Int.result == 4)
  effects(pure)
{
  4
}

public fn probe(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 4)
  effects(pure)
{
  take(None)
}
"""


def test_a_nullary_constructor_takes_the_type_its_position_fixes(
        tmp_path: Path) -> None:
    """`None` fixes no type argument of its own; the formal it is passed
    at does, so it is a term of `Option<Bool>`'s sort, the one `take`'s
    parameter and its precondition read it at, and the call is modelled
    (#1525)."""
    path = pipeline.write_tree(tmp_path, {"main.vera": _OPEN_NULLARY})
    _every_probe_obligation_proves(path)


# =====================================================================
# A component's declared type down a nested pattern's path
# =====================================================================
#
# Over an opaque source the source walk reads the declaration, down every
# step of the pattern's path to the component (`declared_component_is_nat`),
# for the verifier's narrowing record and code generation's guard alike, so
# a `@Nat` component the declarations type `Nat` is neither obligated nor
# guarded: at 37318876 code generation guarded the last two with no record
# (W004).

_NESTED_PATHS = {
    "binder": (
        "  match @Wrap.0 {\n    W(MkBox(@Nat)) -> @Nat.0\n  }", "@Wrap"),
    "destructure": (
        "  let W<@Box<Nat>> = @Wrap.0;\n  let MkBox<@Nat> = @Box<Nat>.0;\n"
        "  @Nat.0", "@Wrap"),
    "tuple": (
        "  match @Tuple<Box<Nat>, Int>.0 {\n"
        "    Tuple(MkBox(@Nat), @Int) -> @Nat.0\n  }", "@Tuple<Box<Nat>, Int>"),
}


def _nested_path_program(body: str, param: str) -> str:
    return ("private data Box<T> {\n  MkBox(T)\n}\n\n"
            "private data Wrap {\n  W(Box<Nat>)\n}\n\n"
            f"public fn probe({param} -> @Nat)\n" + _C + "{\n" + body + "\n}\n")


def _nested_path_test(name: str) -> Callable[[Path], None]:
    def test(tmp_path: Path) -> None:
        body, param = _NESTED_PATHS[name]
        path = pipeline.write_tree(
            tmp_path, {"main.vera": _nested_path_program(body, param)})
        verified = pipeline.verify(path, reconcile=True)
        assert verified.ok, [d.format() for d in verified.diagnostics]
        assert [o for o in verified.obligations if o.kind == "nat_bind"] == []
        joined = verified.reconciled
        assert joined is not None and joined.reconciliation is not None
        assert joined.report()["mismatches"] == [], joined.report()
        assert "nat_guard" not in [c.kind for c in pipeline.compile(path).checks()]
    test.__name__ = f"test_nested_path_{name}"
    test.__doc__ = (f"A `@Nat` {name} component two steps down an opaque "
                    f"source's declarations, which type it `Nat`: no record "
                    f"and no guard.")
    return test


for _name in _NESTED_PATHS:
    globals()[f"test_nested_path_{_name}"] = _nested_path_test(_name)
del _name


# =====================================================================
# An equality of a data type at `Nat` with the same at `Int`
# =====================================================================

_CROSS_EQUALITY = """\
private data Box<T> {
  MkBox(T)
}

private fn cross(@Option<Nat>, @Option<Int> -> @Bool)
  requires(match @Option<Int>.0 { Some(@Int) -> @Int.0 < 0, None -> false })
  ensures(!@Bool.result)
  effects(pure)
{
  @Option<Nat>.0 == @Option<Int>.0
}

private fn box_cross(@Box<Nat>, @Int -> @Bool)
  requires(@Int.0 < 0)
  ensures(!@Bool.result)
  effects(pure)
{
  @Box<Nat>.0 == MkBox(@Int.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Bool = cross(Some(3), Some(0 - 1));
  let @Bool = cross(None, Some(0 - 7));
  let @Bool = box_cross(MkBox(2), 0 - 1);
  if @Bool.0 || @Bool.1 || @Bool.2 then { 1 } else { 0 }
}
"""


def test_repro_an_equality_of_two_instantiations_stays_a_runtime_check(
        tmp_path: Path) -> None:
    """`Option<Nat>` and `Option<Int>` are one sort, and a term of the
    `Nat` one states no `>= 0` of its components (#1814), so the solver
    met `Some(-1)` with an `Option<Nat>` holding it and refused `cross`'s
    true `ensures` (`E500`), as 37318876 refused `box_cross`'s with
    `MkBox(-1)`.  An `==` of two checked types has no term: each `ensures`
    is a runtime check (`E522`), and the calls run with no trap."""
    path = pipeline.write_tree(tmp_path, {"main.vera": _CROSS_EQUALITY})
    verified = pipeline.verify(path)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    ensures = sorted((o.fn_name, o.status, o.error_code)
                     for o in verified.obligations
                     if o.fn_name in ("cross", "box_cross")
                     and o.kind == "ensures")
    assert ensures == [("box_cross", "tier3", "E522"),
                       ("cross", "tier3", "E522")], ensures
    ran = pipeline.run(path, "main", [])
    assert ran.ok, ran.stderr or ran.trap
    assert ran.value == 0, ran.value


# =====================================================================
# A clone with no template in the table
# =====================================================================

_PICK = """\
private forall<T> fn pick(@T, @T, @Int -> @T)
  requires(true)
  ensures(@T.result == @T.1)
  effects(pure)
{
  if @Int.0 > 0 then { @T.1 } else { @T.0 }
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(1, 2, @Int.0)
}
"""


def test_a_clone_with_no_template_is_a_defect_of_the_table() -> None:
    """A clone's parameters are named by its template's, read through the
    typed program's `origin`; a clone with no entry there is the table's
    defect, raised as `_written_type` raises one, where the clone was
    named by its own parameters (`@Int.2`) with no error."""
    from vera.verifier import verify

    typed = pipeline.typed(_PICK, file="main.vera")
    clones = [inst.clone for inst in typed.instances
              if inst.clone is not None and inst.clone.name.startswith("pick")]
    assert clones, [inst.name for inst in typed.instances]
    for clone in clones:
        assert clone.node_id is not None
        del typed.origin[clone.node_id]
    with pytest.raises(ValueError, match="has no template in the typed program"):
        verify(typed, source=_PICK, file="main.vera")


# =====================================================================
# A clone's result is named by its template's, as its parameters are
# =====================================================================

_WRAP_BAD = """\
private forall<T> fn wrap_bad(@T -> @Option<T>)
  requires(true)
  ensures(match @Option<T>.result { Some(@T) -> false, None -> true })
  effects(pure)
{
  Some(@T.0)
}

public fn use_wrap(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match wrap_bad(@Bool.0) {
    Some(@Bool) -> 1,
    None -> 0
  }
}
"""


def _counterexample_names(source: str, fn: str) -> list[str]:
    verified = pipeline.verify(source, file="main.vera")
    (found,) = [d for d in verified.diagnostics
                if d.error_code == "E500" and f"'{fn}'" in d.description]
    return re.findall(r"^\s+(@\S+) = ", found.description, re.M)


def test_a_clones_result_is_named_by_its_template() -> None:
    """`pick$Int`'s counterexample names its parameters `@T.1`, `@T.0` and
    `@Int.0`, its template's, and its result `@T.result`, where it read
    the clone's `@Int.result`."""
    assert sorted(_counterexample_names(_PICK, "pick")) == [
        "@Int.0", "@T.0", "@T.1", "@T.result"]


def test_a_clones_composite_result_is_named_by_its_template() -> None:
    """`wrap_bad`'s instance at `Bool` names its result `@Option<T>.result`,
    as the template writes it, beside its parameter `@T.0`."""
    assert sorted(_counterexample_names(_WRAP_BAD, "wrap_bad")) == [
        "@Option<T>.result", "@T.0"]


# =====================================================================
# An imported type's refinement calls its own module's function
# =====================================================================
#
# The module's declarations are registered by a second verifier, which
# reads each declared type off the typed program; a refinement's predicate
# there is the checker's node as the module writes it, and only the linked
# twin names the module's own `small` rather than the importer's.

_SMALL_LIB = """\
module gen_lib;

public fn small(@Int -> @Bool)
  requires(true)
  ensures(@Bool.result == (@Int.0 < 10))
  effects(pure)
{
  @Int.0 < 10
}

type Small = { @Int | small(@Int.0) };

public fn take(@Small -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Small.0
}

public fn mk(@Int -> @Small)
  requires(@Int.0 < 10)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""

#: The importer's own `small`, true of every value: read in place of
#: `gen_lib.small`, it proves any narrowing into `Small`.
_IMPORTER_SMALL_TRUE = """\
private fn small(@Int -> @Bool)
  requires(true)
  ensures(@Bool.result)
  effects(pure)
{
  true
}
"""

#: The importer's own `small`, true of the negative values: assumed in
#: place of `gen_lib.small`, it makes a `Small` negative.
_IMPORTER_SMALL_NEGATIVE = """\
private fn small(@Int -> @Bool)
  requires(true)
  ensures(@Bool.result == (@Int.0 < 0))
  effects(pure)
{
  @Int.0 < 0
}
"""


def _imported_refinement(entry: str, tmp_path: Path) -> list[tuple[str, str]]:
    path = pipeline.write_tree(tmp_path, {
        "main.vera": entry, "gen_lib.vera": _SMALL_LIB})
    verified = pipeline.verify(path)
    return sorted((o.kind, o.status) for o in verified.obligations
                  if o.fn_name == "main"
                  and o.kind in ("refine_bind", "ensures"))


def test_repro_an_imported_parameters_refinement_calls_its_modules_function(
        tmp_path: Path) -> None:
    """`take(50)` narrows 50 into `gen_lib`'s `Small`, whose predicate is
    `gen_lib.small`, false at 50: the narrowing is refuted, where the
    importer's own `small`, true of every value, was read in its place and
    the call proved, to trap at run time."""
    entry = ("import gen_lib(take);\n\n" + _IMPORTER_SMALL_TRUE
             + "\npublic fn main(@Unit -> @Int)\n" + _C + "{\n  take(50)\n}\n")
    assert _imported_refinement(entry, tmp_path) == [
        ("ensures", "verified"), ("refine_bind", "violated")]


def test_repro_an_imported_results_refinement_calls_its_modules_function(
        tmp_path: Path) -> None:
    """`mk(5)` returns a `Small`, which assumes `gen_lib.small` of the
    result, so `main`'s `ensures(@Int.result < 0)` is refuted, where the
    importer's own `small` was assumed in its place and proved it."""
    entry = ("import gen_lib(mk);\n\n" + _IMPORTER_SMALL_NEGATIVE
             + "\npublic fn main(@Unit -> @Int)\n  requires(true)\n"
             + "  ensures(@Int.result < 0)\n  effects(pure)\n{\n  mk(5)\n}\n")
    assert _imported_refinement(entry, tmp_path) == [("ensures", "violated")]
