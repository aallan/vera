"""One typed program: a judgment that depends on a generic's instantiation is
made at check (#1679; ROADMAP Stage 26).

A rule whose answer depends on what a generic is instantiated at was applied
only by code generation's monomorphizer, after the checker and the verifier
had accepted the program: an ability constraint the instantiation does not
satisfy, a ``State<T>`` cell at a type no cell holds, a ``Map`` or ``Set``
key, value or element that is an ``Array``.  And the checker read a generic
callee's effect row as declared, so a row the instantiation satisfies was
refused.  The typed program derives every instantiation once, after the
checker, and each judgment is made there, at the call that fixes the type
argument, with its location and a fix.

The ``repro`` cells are the issue's instances.  The class matrix crosses the
four judgments with the five positions a type argument can be fixed from and
the two verdicts: every unsatisfied pair is refused at check with its code at
the call; every satisfied pair checks, verifies and runs as at the base.
"""

from __future__ import annotations

import json
import re
from collections.abc import Callable
from dataclasses import dataclass, replace
from pathlib import Path

import pytest

from tests import pipeline
from vera import ast

pytestmark = pytest.mark.matrix(decides=[
    "vera/typed.py",
    "vera/monomorphize.py",
    "vera/codegen/monomorphize.py",
    "vera/checker/calls.py",
    "vera/checker/control.py",
    "vera/checker/core.py",
    "vera/checker/resolution.py",
    "vera/lowering.py",
    "vera/smt.py",
])


_C = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _fn(head: str, body: str, effects: str = "pure") -> str:
    return (f"{head}\n  requires(true)\n  ensures(true)\n  effects({effects})\n"
            f"{{\n  {body}\n}}\n")


def _codes(diagnostics: object) -> list[str | None]:
    return [d.error_code for d in diagnostics]  # type: ignore[attr-defined]


def _position(text: str, needle: str, occurrence: int = -1) -> tuple[int, int]:
    """The 1-based (line, column) of *needle* in *text*: its last occurrence
    by default, which is the call written in the entry's last function."""
    starts = [i for i in range(len(text)) if text.startswith(needle, i)]
    assert starts, needle
    at = starts[occurrence]
    line = text.count("\n", 0, at) + 1
    column = at - (text.rfind("\n", 0, at) + 1) + 1
    return line, column


def _refused_at_call(code: str, needle: str, occurrence: int = -1
                     ) -> Callable[[Path], None]:
    """Refused at check with *code* at *needle* in main.vera."""
    def expect(path: Path) -> None:
        line, column = _position(path.read_text(encoding="utf-8"), needle,
                                 occurrence)
        _refused_at(path, code, line, column)
    return expect


def _refused_at(path: Path, code: str, line: int, column: int) -> None:
    """*path* is refused at check with *code* at (*line*, *column*)."""
    checked = pipeline.check(path)
    found = [d for d in checked.errors if d.error_code == code]
    assert found, [d.format() for d in checked.diagnostics]
    where = [(d.location.line, d.location.column) for d in found]
    assert (line, column) in where, where


# =====================================================================
# The instances
# =====================================================================

_LT = _fn("public forall<T where Ord<T>> fn lt(@T, @T -> @Bool)",
          "match compare(@T.1, @T.0) {\n    Less -> true,\n    _ -> false\n  }")
_REPRO_ORD = _LT + "\n" + _fn(
    "public fn main(@Unit -> @Int)",
    "if lt(true, false) then {\n    1\n  } else {\n    0\n  }")
_SAME = _fn("public forall<T where Eq<T>> fn same(@T, @T -> @Bool)",
            "@T.1 == @T.0")
_REPRO_EQ = _SAME + "\n" + _fn("public fn main(@Unit -> @Bool)",
                               "same([1], [1])")
_REPRO_CELL = _fn(
    "private forall<T> fn f(@T -> @Int)",
    "handle[State<T>](@T = @T.0) {\n    get(@Unit) -> { resume(@T.0) },\n"
    "    put(@T) -> { resume(()) }\n  } in {\n    1\n  }") + "\n" + _fn(
    "public fn main(@Unit -> @Int)", 'f("abc")')
_REPRO_E533 = _fn(
    "private forall<T> fn sneak(@T -> @T)",
    "handle[State<T>](@Nat = 3) {\n    put(@T) -> { resume(()) }\n  } in {\n"
    "    put(@T.0);\n    get(())\n  }") + "\n" + _fn(
    "public fn go(@Int, @Float64 -> @Int)",
    "let @Float64 = sneak(@Float64.0);\n  sneak(@Int.0)")
_REPRO_MAP_ARRAY_KEY = _fn(
    "public fn main(@Unit -> @Int)",
    "let @Map<Array<Int>, Int> = map_insert(map_new(), [1, 2], 5);\n"
    "  nat_to_int(map_size(@Map<Array<Int>, Int>.0))")
_REPRO_ROW = _fn(
    "private forall<T> fn peek(@T -> @T)", "get(())",
    effects="<State<T>>") + "\n" + _fn(
    "public fn f(@Int -> @Int)",
    "handle[State<Int>](@Int = 0) { get(@Unit) -> { resume(@Int.0) }, "
    "put(@Int) -> { resume(()) } } in { peek(1) }")
_M_IMPOSSIBLE = (
    "module m;\n\npublic forall<T> fn impossible(@T -> @T)\n"
    "  requires(false)\n  ensures(true)\n  effects(pure)\n{\n  @T.0\n}\n")
_REPRO_FALSE_REQUIRES = "import m(impossible);\n\n" + _fn(
    "public fn calls_generic(@Int -> @Int)", "impossible(@Int.0)")


@dataclass(frozen=True)
class Repro:
    files: dict[str, str]
    expect: Callable[[Path], None]


def _runs(fn: str, args: list[int] | None = None, *,
          value: object = None, stdout: str | None = None
          ) -> Callable[[Path], None]:
    def expect(path: Path) -> None:
        verified = pipeline.verify(path)
        assert verified.ok, [d.format() for d in verified.diagnostics]
        ran = pipeline.run(path, fn, args or [])
        assert ran.ok, (ran.stderr, ran.trap)
        if stdout is not None:
            assert ran.stdout == stdout, ran.stdout
        if value is not None:
            assert ran.value == value, ran.value
    return expect


def _verify_refuses_at(code: str, needle: str) -> Callable[[Path], None]:
    def expect(path: Path) -> None:
        line, column = _position(path.read_text(encoding="utf-8"), needle)
        verified = pipeline.verify(path)
        found = [d for d in verified.errors if d.error_code == code]
        assert found, [d.format() for d in verified.diagnostics]
        where = [(d.location.line, d.location.column) for d in found]
        assert (line, column) in where, where
    return expect


REPROS: dict[str, Repro] = {
    # The issue's two programs.
    "ord_constraint_at_bool": Repro(
        {"main.vera": _REPRO_ORD},
        _refused_at_call("E613", "lt(true, false)")),
    "eq_constraint_at_array": Repro(
        {"main.vera": _REPRO_EQ},
        _refused_at_call("E613", "same([1], [1])")),
    "state_cell_at_string": Repro(
        {"main.vera": _REPRO_CELL},
        _refused_at_call("E607", 'f("abc")')),
    # The handler state declaration a cell diverges from at an
    # instantiation (the check-implies-compile sweep's line).
    "handler_state_declaration_at_instantiation": Repro(
        {"main.vera": _REPRO_E533},
        _refused_at_call("E533", "sneak(@Float64.0)")),
    # #1680: a `Map` with an `Array` key.
    "1680_map_with_array_key": Repro(
        {"main.vera": _REPRO_MAP_ARRAY_KEY},
        _refused_at_call("E135", "Map<Array<Int>, Int>", 0)),
    # #1769: a generic callee's row, instantiated, fits the handler.
    "1769_instantiated_row_fits": Repro(
        {"main.vera": _REPRO_ROW}, _runs("f", [3], value=0)),
    # #1468: a false `requires` on a generic callee behind a module
    # boundary is refuted at the call, as on a monomorphic one.
    "1468_false_requires_on_generic_callee": Repro(
        {"m.vera": _M_IMPOSSIBLE, "main.vera": _REPRO_FALSE_REQUIRES},
        _verify_refuses_at("E501", "impossible(@Int.0)")),
}


@pytest.mark.parametrize("name", sorted(REPROS))
def test_repro_instance(name: str, tmp_path: Path) -> None:
    repro = REPROS[name]
    repro.expect(pipeline.write_tree(tmp_path, repro.files))


# =====================================================================
# The class matrix: judgment x position x verdict
# =====================================================================
#
# A judgment's generic is declared in the entry file (in module `m` for the
# module position), and the type argument is fixed by the call the position
# names.  The ROOT call -- the one written in a non-generic body, whose
# arguments fix the type -- is where an unsatisfied pair is refused.


@dataclass(frozen=True)
class Judgment:
    code: str
    generic: str            # the generic, named `g`, over its variable `T`
    nested: str             # the same over `@Option<T>`, named `g`
    ret: str                # the type a call of `g` returns
    sat: str                # an argument the judgment accepts
    unsat: str              # an argument it refuses
    effects: str = "pure"   # the row the caller declares
    handler: str = ""       # a handler the call is written inside
    #: A position whose root call an earlier rule refuses, with its code.
    refused_first: tuple[tuple[str, str], ...] = ()


_STATE_INT = ("handle[State<Int>](@Int = 0) { get(@Unit) -> { resume(@Int.0) }, "
              "put(@Int) -> { resume(()) } } in { ")

JUDGMENTS: dict[str, Judgment] = {
    "ability": Judgment(
        "E613",
        _fn("public forall<T where Eq<T>> fn g(@T -> @Bool)", "@T.0 == @T.0"),
        _fn("public forall<T where Eq<T>> fn g(@Option<T> -> @Bool)",
            "@Option<T>.0 == @Option<T>.0"),
        "Bool", "1", "[1]"),
    "cell": Judgment(
        "E607",
        _fn("public forall<T> fn g(@T -> @Int)",
            "handle[State<T>](@T = @T.0) {\n    get(@Unit) -> { resume(@T.0) },\n"
            "    put(@T) -> { resume(()) }\n  } in {\n    1\n  }"),
        _fn("public forall<T> fn g(@Option<T> -> @Int)",
            "match @Option<T>.0 {\n    Some(@T) -> handle[State<T>](@T = @T.0) {\n"
            "      get(@Unit) -> { resume(@T.0) },\n"
            "      put(@T) -> { resume(()) }\n    } in {\n      1\n    },\n"
            "    None -> 0\n  }"),
        "Int", "5", '"abc"'),
    "collection_key": Judgment(
        "E135",
        _fn("public forall<T> fn g(@T -> @Int)",
            "nat_to_int(map_size(map_insert(map_new(), @T.0, 1)))"),
        _fn("public forall<T> fn g(@Option<T> -> @Int)",
            "match @Option<T>.0 {\n    Some(@T) -> nat_to_int(map_size(map_insert("
            "map_new(), @T.0, 1))),\n    None -> 0\n  }"),
        "Int", "5", "[1]"),
    "effect_row": Judgment(
        "E125",
        _fn("public forall<T> fn g(@T -> @T)", "get(())", effects="<State<T>>"),
        _fn("public forall<T> fn g(@Option<T> -> @T)", "get(())",
            effects="<State<T>>"),
        "Int", "1", "true", handler=_STATE_INT),
    # The cell's twin: an `Exn<T>` payload at a type no tag throws.  Through
    # another generic, the one between reads its `Unit` argument, which E206
    # refuses at the root call first.
    "payload": Judgment(
        "E612",
        _fn("public forall<T> fn g(@T -> @Int)",
            "handle[Exn<T>] {\n    throw(@T) -> { 0 }\n  } in {\n    1\n  }"),
        _fn("public forall<T> fn g(@Option<T> -> @Int)",
            "handle[Exn<T>] {\n    throw(@T) -> { 0 }\n  } in {\n    1\n  }"),
        "Int", "5", "()", refused_first=(("through_generic", "E206"),)),
}

POSITIONS = ("direct", "through_generic", "through_closure", "through_module",
             "nested_in_data")


def _matrix_program(judgment: Judgment, position: str, arg: str
                    ) -> tuple[dict[str, str], int, int]:
    """The program, and the (line, column) of the root call."""
    generic = judgment.nested if position == "nested_in_data" else judgment.generic
    call_arg = f"Some({arg})" if position == "nested_in_data" else arg
    ret = judgment.ret if judgment.code != "E125" or arg == judgment.sat else "Bool"
    open_h, close_h = (judgment.handler, " }") if judgment.handler else ("", "")
    caller_effects = "pure"
    decls = ""
    call = f"g({call_arg})"
    if position == "through_generic":
        row = "<State<U>>" if judgment.code == "E125" else "pure"
        ret_u = "U" if judgment.code == "E125" else judgment.ret
        decls = _fn(f"private forall<U> fn outer(@U -> @{ret_u})", "g(@U.0)",
                    effects=row) + "\n"
        call = f"outer({call_arg})"
    if position == "through_closure":
        # The closure declares the handler's row, so what an unsatisfied
        # pair is refused for is the generic's row at its instantiation.
        inner_row = "<State<Int>>" if judgment.code == "E125" else "pure"
        body = (f"{open_h}apply_fn(fn(@Unit -> @{ret}) effects({inner_row}) "
                f"{{ {call} }}, ()){close_h}")
    else:
        body = f"{open_h}{call}{close_h}"
    entry = ""
    files: dict[str, str] = {}
    if position == "through_module":
        files["m.vera"] = "module m;\n\n" + generic
        entry = "import m(g);\n\n"
    else:
        decls = generic + "\n" + decls
    main = _fn(f"public fn main(@Unit -> @{ret})", body, effects=caller_effects)
    text = entry + decls + main
    files["main.vera"] = text
    line, column = _position(text, call)
    return files, line, column


MATRIX = [
    (j, p, v) for j in JUDGMENTS for p in POSITIONS for v in ("sat", "unsat")
]


#: At 94cef528 every unsatisfied ability, cell, key and payload pair passed
#: check (code generation refused it, or compiled an invalid module), and
#: every satisfied effect-row pair was refused (E125, #1769).
#:
#: Each satisfied pair's obligations, (kind/status, count), as `vera verify`
#: recorded them at 94cef528: the negative space, which the judgments leave
#: as it was.  The effect-row pairs, refused there, record what the other
#: judgments' pairs do.
_SAT_OBLIGATIONS: dict[str, tuple[tuple[str, int], ...]] = {
    "ability-direct": (("ensures/verified", 2), ("requires/verified", 2)),
    "ability-nested_in_data": (("ensures/verified", 2), ("requires/verified", 2)),
    "ability-through_closure": (("ensures/verified", 2), ("requires/verified", 2)),
    "ability-through_generic": (("ensures/verified", 3), ("requires/verified", 3)),
    "ability-through_module": (("ensures/verified", 2), ("requires/verified", 2)),
    "cell-direct": (("ensures/verified", 2), ("requires/verified", 2)),
    "cell-nested_in_data": (("ensures/verified", 2), ("requires/verified", 2)),
    "cell-through_closure": (("ensures/verified", 2), ("requires/verified", 2)),
    "cell-through_generic": (("ensures/verified", 3), ("requires/verified", 3)),
    "cell-through_module": (("ensures/verified", 2), ("requires/verified", 2)),
    "collection_key-direct": (("ensures/verified", 2), ("nat_bind/tier3", 1), ("requires/verified", 2)),
    "collection_key-nested_in_data": (("ensures/verified", 2), ("nat_bind/tier3", 1), ("requires/verified", 2)),
    "collection_key-through_closure": (("ensures/verified", 2), ("nat_bind/tier3", 1), ("requires/verified", 2)),
    "collection_key-through_generic": (("ensures/verified", 3), ("nat_bind/tier3", 1), ("requires/verified", 3)),
    "collection_key-through_module": (("ensures/verified", 2), ("nat_bind/tier3", 1), ("requires/verified", 2)),
    "effect_row-direct": (("ensures/verified", 2), ("requires/verified", 2)),
    "effect_row-nested_in_data": (("ensures/verified", 2), ("requires/verified", 2)),
    "effect_row-through_closure": (("ensures/verified", 2), ("requires/verified", 2)),
    "effect_row-through_generic": (("ensures/verified", 3), ("requires/verified", 3)),
    "effect_row-through_module": (("ensures/verified", 2), ("requires/verified", 2)),
    "payload-direct": (("ensures/verified", 2), ("requires/verified", 2)),
    "payload-nested_in_data": (("ensures/verified", 2), ("requires/verified", 2)),
    "payload-through_closure": (("ensures/verified", 2), ("requires/verified", 2)),
    "payload-through_generic": (("ensures/verified", 3), ("requires/verified", 3)),
    "payload-through_module": (("ensures/verified", 2), ("requires/verified", 2)),
}


@pytest.mark.parametrize(("judgment", "position", "verdict"), [
    pytest.param(j, p, v, id=f"{j}-{p}-{v}") for j, p, v in MATRIX
])
def test_instantiation_judgment(judgment: str, position: str, verdict: str,
                                tmp_path: Path) -> None:
    j = JUDGMENTS[judgment]
    arg = j.sat if verdict == "sat" else j.unsat
    files, line, column = _matrix_program(j, position, arg)
    path = pipeline.write_tree(tmp_path, files)
    if verdict == "unsat":
        _refused_at(path, dict(j.refused_first).get(position, j.code),
                    line, column)
        return
    checked = pipeline.check(path)
    assert checked.ok, [d.format() for d in checked.diagnostics]
    verified = pipeline.verify(path)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    counts: dict[str, int] = {}
    for obligation in verified.obligations:
        key = f"{obligation.kind}/{obligation.status}"
        counts[key] = counts.get(key, 0) + 1
    assert tuple(sorted(counts.items())) == _SAT_OBLIGATIONS[
        f"{judgment}-{position}"]
    ran = pipeline.run(path, "main")
    assert ran.ok, (ran.stderr, ran.trap)


# =====================================================================
# A call site's precondition, for every callee (#1468)
# =====================================================================
#
# A generic callee's contract is its clone's at the call's instantiation
# (the typed program's instance of the call), so the call site judges it as
# it judges a monomorphic callee's: each precondition shape records the
# same status and code whatever the callee.  At 94cef528 the generic and
# the imported generic demoted every shape (E532), the provable and the
# false alike; the satisfiable-but-unprovable row is the control that keeps
# a fix from turning every unproven precondition into a refusal.

_CALLEE_SHAPES = ("mono", "forall", "where", "imported")

#: Each precondition, the argument the call passes, and the call site's
#: records: (status, code).
_PRECONDITIONS: dict[str, tuple[str, str, list[tuple[str, str]]]] = {
    "false": ("false", "5", [("violated", "E501")]),
    "refutable": ("@Int.0 > 10", "3", [("violated", "E501")]),
    "satisfiable_unprovable": (
        "array_length(array_range(0, @Int.0)) > 3", "5",
        [("tier3", "E532")]),
    "provable": ("@Int.0 > 0", "5", []),
}


#: A generic callee whose precondition the verifier cannot state: the call
#: demotes (`E532`), and its record names the precondition as the generic
#: writes it, the clause the clone's prologue check is emitted for, so the
#: record and the check pair (`vera verify` reconciles them).
_UNDECIDED_GENERIC_PRE = (
    _fn("private forall<T> fn first_len(@Array<T> -> @Nat)",
        "array_length(@Array<T>.0)").replace(
        "requires(true)",
        "requires(array_length(array_range(0, array_length(@Array<T>.0))) > 0)",
        1)
    + "\n" + _fn("public fn main(@Unit -> @Nat)", "first_len([1, 2])"))


def test_a_generic_calls_demoted_precondition_pairs_with_its_check(
        tmp_path: Path) -> None:
    path = pipeline.write_tree(tmp_path, {"main.vera": _UNDECIDED_GENERIC_PRE})
    verified = pipeline.verify(path, reconcile=True)
    assert [(o.status, o.error_code) for o in verified.obligations
            if o.kind == "call_pre"] == [("tier3", "E532")]
    assert verified.ok, [d.format() for d in verified.diagnostics]


def _callee_program(shape: str, pre: str, arg: str) -> dict[str, str]:
    callee = _fn(
        "private fn c(@Int -> @Int)" if shape in ("mono", "where")
        else "private forall<T> fn c(@T, @Int -> @Int)", "@Int.0"
    ).replace("requires(true)", f"requires({pre})", 1)
    call = f"c({arg})" if shape in ("mono", "where") else f"c(true, {arg})"
    main = _fn("public fn main(@Unit -> @Int)", call)
    if shape == "where":
        helper = callee.replace("private fn c", "fn c").replace("\n", "\n  ")
        return {"main.vera": main.rstrip("\n") + "\nwhere {\n  "
                + helper.rstrip() + "\n}\n"}
    if shape == "imported":
        return {"m.vera": "module m;\n\n" + callee.replace("private", "public"),
                "main.vera": "import m(c);\n\n" + main}
    return {"main.vera": callee + "\n" + main}


@pytest.mark.parametrize("shape", _CALLEE_SHAPES)
@pytest.mark.parametrize("precondition", list(_PRECONDITIONS))
def test_a_call_sites_precondition_is_judged_alike_for_every_callee(
        shape: str, precondition: str, tmp_path: Path) -> None:
    pre, arg, records = _PRECONDITIONS[precondition]
    path = pipeline.write_tree(tmp_path, _callee_program(shape, pre, arg))
    verified = pipeline.verify(path)
    assert [(o.status, o.error_code) for o in verified.obligations
            if o.kind == "call_pre"] == records, [
        d.format() for d in verified.diagnostics]


# =====================================================================
# A Map or Set with an Array or zero-size component, as written (#1680)
# =====================================================================
#
# A component that holds no type parameter is judged where it is written:
# a written type at the type (E135, the zero-size rule's Array sibling), an
# operation whose component only inference gives at the call.  Each refused
# shape has its nearest neighbour the check accepts beside it, which checks,
# verifies and records what it did at 94cef528.

_MAP_SIZE = "nat_to_int(map_size(@{T}.0))"
_SET_SIZE = "nat_to_int(set_size(@{T}.0))"


def _written(ty: str, size: str) -> str:
    return _fn("public fn main(@Unit -> @Int)",
               f"let @{ty} = {ty.split('<')[0].lower()}_new();\n  "
               + size.replace("{T}", ty))


#: (refused program, the needle E135 is reported at, the neighbour).
COMPONENTS: dict[str, tuple[str, str, str]] = {
    "written_map_key": (
        _written("Map<Array<Int>, Int>", _MAP_SIZE), "Map<Array<Int>, Int>",
        _written("Map<String, Int>", _MAP_SIZE)),
    "written_map_value": (
        _written("Map<String, Array<Int>>", _MAP_SIZE),
        "Map<String, Array<Int>>",
        _written("Map<String, Option<Array<Int>>>", _MAP_SIZE)),
    "written_set_element": (
        _written("Set<Array<Int>>", _SET_SIZE), "Set<Array<Int>>",
        _written("Set<String>", _SET_SIZE)),
    "inferred_map_key": (
        _fn("public fn main(@Unit -> @Int)",
            "nat_to_int(map_size(map_insert(map_new(), [1, 2], 5)))"),
        "map_insert(",
        _fn("public fn main(@Unit -> @Int)",
            "nat_to_int(map_size(map_insert(map_new(), show([1, 2]), 5)))")),
    "inferred_map_value": (
        _fn("public fn main(@Unit -> @Int)",
            'nat_to_int(map_size(map_insert(map_new(), "k", [1, 2])))'),
        "map_insert(",
        _fn("public fn main(@Unit -> @Int)",
            'nat_to_int(map_size(map_insert(map_new(), "k", Some([1, 2]))))')),
    "inferred_set_element": (
        _fn("public fn main(@Unit -> @Int)",
            "nat_to_int(set_size(set_add(set_new(), [1, 2])))"),
        "set_add(",
        _fn("public fn main(@Unit -> @Int)",
            "nat_to_int(set_size(set_add(set_new(), show([1, 2]))))")),
    "inferred_zero_size_value": (
        _fn("public fn main(@Unit -> @Int)",
            'nat_to_int(map_size(map_insert(map_new(), "k", ())))'),
        "map_insert(",
        _fn("public fn main(@Unit -> @Int)",
            'nat_to_int(map_size(map_insert(map_new(), "k", Some(()))))')),
}

#: Each neighbour's obligations at 94cef528, (kind/status, count).
_NEIGHBOUR_OBLIGATIONS: dict[str, tuple[tuple[str, int], ...]] = {
    "inferred_map_key": (("ensures/verified", 1), ("nat_bind/tier3", 1), ("requires/verified", 1)),
    "inferred_map_value": (("ensures/verified", 1), ("nat_bind/tier3", 1), ("requires/verified", 1)),
    "inferred_set_element": (("ensures/verified", 1), ("nat_bind/tier3", 1), ("requires/verified", 1)),
    "inferred_zero_size_value": (("ensures/verified", 1), ("nat_bind/tier3", 1), ("requires/verified", 1)),
    "written_map_key": (("ensures/verified", 1), ("nat_bind/tier3", 1), ("requires/verified", 1)),
    "written_map_value": (("ensures/verified", 1), ("nat_bind/tier3", 1), ("requires/verified", 1)),
    "written_set_element": (("ensures/verified", 1), ("nat_bind/tier3", 1), ("requires/verified", 1)),
}


@pytest.mark.parametrize("name", sorted(COMPONENTS))
def test_a_component_no_operation_lowers_is_refused_as_written(
        name: str, tmp_path: Path) -> None:
    source, needle, _ = COMPONENTS[name]
    path = pipeline.write_tree(tmp_path, {"main.vera": source})
    _refused_at_call("E135", needle, 0)(path)


@pytest.mark.parametrize("name", sorted(COMPONENTS))
def test_the_nearest_component_neighbour_is_accepted(
        name: str, tmp_path: Path) -> None:
    neighbour = COMPONENTS[name][2]
    path = pipeline.write_tree(tmp_path, {"main.vera": neighbour})
    checked = pipeline.check(path)
    assert checked.ok, [d.format() for d in checked.diagnostics]
    verified = pipeline.verify(path)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    counts: dict[str, int] = {}
    for obligation in verified.obligations:
        key = f"{obligation.kind}/{obligation.status}"
        counts[key] = counts.get(key, 0) + 1
    assert tuple(sorted(counts.items())) == _NEIGHBOUR_OBLIGATIONS[name]
    ran = pipeline.run(path, "main")
    assert ran.ok, (ran.stderr, ran.trap)


# =====================================================================
# Each judgment's fix, applied as written, clears it
# =====================================================================

_REPLACE = re.compile(r"replace '(.+?)' with '(.+?)'")


def _fix_cases() -> dict[str, tuple[dict[str, str], str]]:
    """Every refused program here whose refusal is a judgment this change
    makes, with its code."""
    cases: dict[str, tuple[dict[str, str], str]] = {}
    for j, p, v in MATRIX:
        judgment = JUDGMENTS[j]
        if (v == "unsat" and j != "effect_row"
                and p not in dict(judgment.refused_first)):
            cases[f"{j}-{p}"] = (
                _matrix_program(judgment, p, judgment.unsat)[0],
                judgment.code)
    for name, code in (("ord_constraint_at_bool", "E613"),
                       ("eq_constraint_at_array", "E613"),
                       ("state_cell_at_string", "E607"),
                       ("handler_state_declaration_at_instantiation",
                        "E533")):
        cases[name] = (REPROS[name].files, code)
    for name, (source, _, _) in COMPONENTS.items():
        cases[name] = ({"main.vera": source}, "E135")
    return cases


FIX_CASES = _fix_cases()


@pytest.mark.parametrize("name", sorted(FIX_CASES))
def test_the_fix_applied_as_written_checks_clean(
        name: str, tmp_path: Path) -> None:
    """The diagnostic's fix is a replacement in the reported program, and
    the program it makes checks with no diagnostic of the code."""
    files, code = FIX_CASES[name]
    checked = pipeline.check(pipeline.write_tree(tmp_path / "before", files))
    found = [d for d in checked.errors if d.error_code == code]
    assert found, [d.format() for d in checked.diagnostics]
    match = _REPLACE.search(found[0].fix)
    assert match is not None, found[0].fix
    old, new = match.groups()
    fixed = {path: text.replace(old, new) for path, text in files.items()}
    assert fixed != files, (old, new)
    after = pipeline.check(pipeline.write_tree(tmp_path / "after", fixed))
    assert after.ok and code not in _codes(after.diagnostics), [
        d.format() for d in after.diagnostics]


# =====================================================================
# Node identity: the key the typed program's tables are keyed by
# =====================================================================
#
# A span cannot tell a clone's node from its template's (a clone keeps the
# template's spans), so the tables are keyed by a node's identity, which
# the parser's transform gives every node once and the link step keeps.

_ROOT = Path(__file__).resolve().parents[1]
_CORPUS = sorted((_ROOT / "examples").glob("*.vera")) + sorted(
    (_ROOT / "tests" / "conformance").glob("*.vera"))


def _nodes(root: object) -> list[ast.Node]:
    """Every node object under *root*, each once."""
    from dataclasses import fields as dc_fields

    seen: set[int] = set()
    found: list[ast.Node] = []
    stack: list[object] = [root]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Node):
            if id(node) in seen:
                continue
            seen.add(id(node))
            found.append(node)
            stack.extend(getattr(node, f.name) for f in dc_fields(node)
                         if f.name != "span")
        elif isinstance(node, tuple):
            stack.extend(node)
    return found


@pytest.mark.parametrize("path", _CORPUS, ids=lambda p: p.name)
def test_every_node_has_one_identity(path: Path) -> None:
    """Every node a corpus program parses to has an identity, and no two
    node objects share one."""
    nodes = _nodes(pipeline.parse(path).program)
    assert nodes
    assert all(node.node_id is not None for node in nodes), [
        type(n).__name__ for n in nodes if n.node_id is None][:5]
    ids = [node.node_id for node in nodes]
    assert len(ids) == len(set(ids))


@pytest.mark.parametrize("path", _CORPUS, ids=lambda p: p.name)
def test_the_link_keeps_every_identity(path: Path) -> None:
    """The linked program, its modules and its prelude hold only numbered
    nodes, and a node the link step rebuilt keeps the identity of the node
    it was rebuilt from, so the checker's table answers for it."""
    from vera.binding import link_program, source_twins

    checked = pipeline.check(path)
    if not checked.ok:
        pytest.skip("a library module or a negative fixture: no link")
    resolved = list(checked.resolved or ())
    linked = link_program(checked.program, resolved)
    twins = source_twins(checked.program, linked.program)
    for mod, lmod in zip(resolved, linked.modules, strict=True):
        source_twins(mod.program, lmod.program, twins)
    for root in (linked.program, *(m.program for m in linked.modules),
                 linked.prelude):
        for node in _nodes(root):
            assert node.node_id is not None, type(node).__name__
            twin = twins.get(id(node))
            if twin is not None:
                assert node.node_id == twin.node_id, type(node).__name__


def test_identity_is_not_serialised() -> None:
    """`vera ast --json` and `vera parse`'s tree carry no identity: it is a
    position, as a span is, not part of what the program says."""
    program = pipeline.parse(_CORPUS[0]).program
    assert "node_id" not in json.dumps(program.to_dict())
    assert "node_id" not in program.pretty()
    rebuilt = replace(program)
    assert rebuilt == program and rebuilt.node_id == program.node_id


# =====================================================================
# The checker's tables by identity
# =====================================================================
#
# The check types every node of the entry file, of each module it reaches
# and of the prelude (whose bodies it now checks, in the prelude's own
# namespace), and records each generic call's instantiation, all keyed by
# node identity.


def _checked_corpus_program(path: Path) -> pipeline.Checked:
    checked = pipeline.check(path)
    if not checked.ok:
        pytest.skip("a library module or a negative fixture: refused at check")
    return checked


def _roots(checked: pipeline.Checked) -> list[object]:
    return [checked.program, *(m.program for m in checked.resolved or ()),
            checked.artifacts.prelude]


@pytest.mark.parametrize("path", _CORPUS, ids=lambda p: p.name)
def test_the_prelude_a_program_binds_checks_clean(path: Path) -> None:
    """The prelude bodies a program is compiled with check in their own
    namespace with no diagnostic of any severity: one there would be a
    defect of the compiler's own source."""
    from vera.checker.core import TypeChecker, check_prelude_bodies

    arts = _checked_corpus_program(path).artifacts
    assert arts.prelude
    checker = TypeChecker()
    checker._bound_prelude = (arts.prelude, arts.prelude_source)
    checker.node_semantic_types, checker.node_target_types = {}, {}
    checker.instantiations = {}
    assert [d.format() for d in check_prelude_bodies(checker)] == []
    assert checker.node_semantic_types


@pytest.mark.parametrize("path", _CORPUS, ids=lambda p: p.name)
def test_every_expression_is_typed_by_its_identity(path: Path) -> None:
    """Every expression of a checked program, its modules and its prelude
    has the checker's type in the table keyed by node identity."""
    checked = _checked_corpus_program(path)
    table = checked.artifacts.node_semantic_types
    untyped = [type(node).__name__ for root in _roots(checked)
               for node in _nodes(root)
               if isinstance(node, ast.Expr) and node.node_id not in table]
    assert untyped == []


@pytest.mark.parametrize("path", _CORPUS, ids=lambda p: p.name)
def test_the_identity_tables_hold_what_the_span_tables_hold(path: Path) -> None:
    """Every type and target the check records by span it records by node
    identity too: for each expression of the entry file whose span no other
    node shares, the two tables give the same answer.  A recording site that
    writes only the span table (the constructor-field gap fill of #1503 did)
    leaves its node unanswered for the verifier and code generation, which
    read only the identity tables."""
    checked = _checked_corpus_program(path)
    arts = checked.artifacts
    by_span: dict[object, list[ast.Node]] = {}
    for node in _nodes(checked.program):
        if isinstance(node, ast.Expr) and node.span is not None:
            by_span.setdefault(ast.span_key(node), []).append(node)
    for key, nodes in by_span.items():
        if len(nodes) != 1:
            continue
        (node,) = nodes
        for spans, ids in ((arts.expr_semantic_types, arts.node_semantic_types),
                           (arts.expr_target_types, arts.node_target_types)):
            if key in spans:
                assert ids.get(node.node_id) == spans[key], (
                    ast.format_expr(node), key)


@pytest.mark.parametrize("path", _CORPUS, ids=lambda p: p.name)
def test_every_generic_call_records_its_instantiation(path: Path) -> None:
    """Every call the binding binds to a generic declaration has the
    instantiation the check inferred there, naming that declaration by its
    link name; a built-in's call records none."""
    from vera.binding import BUILTIN

    checked = _checked_corpus_program(path)
    arts = checked.artifacts
    assert arts.binding is not None
    for root in _roots(checked):
        for node in _nodes(root):
            if not isinstance(node, (ast.FnCall, ast.ModuleCall)):
                continue
            ident = arts.binding.of(node)
            record = arts.instantiations.get(node.node_id)
            if ident is None or ident.owner == BUILTIN:
                assert record is None, node
                continue
            decl = arts.binding.decls.get(ident)
            if decl is not None and decl.forall_vars:
                assert record is not None, ast.format_expr(node)
                assert record.callee == ident.link_name


# =====================================================================
# The typed program: every instance built once, every clone node typed
# =====================================================================


@pytest.mark.parametrize("path", _CORPUS, ids=lambda p: p.name)
def test_every_expression_of_every_clone_is_typed(path: Path) -> None:
    """Every expression of every clone the typed program builds has a type
    of its own, under its own identity, its template's under the instance's
    substitution (no type variable the instance binds is left in it), and
    every generic call a clone compiles names the instance it calls, which
    is built."""
    from vera.typed import build
    from vera.types import AdtType, FunctionType, RefinedType, TypeVar

    def variables(ty: object) -> set[str]:
        if isinstance(ty, TypeVar):
            return {ty.name}
        if isinstance(ty, RefinedType):
            return variables(ty.base)
        if isinstance(ty, AdtType):
            return set().union(*(variables(a) for a in ty.type_args))
        if isinstance(ty, FunctionType):
            return set().union(variables(ty.return_type),
                               *(variables(p) for p in ty.params))
        return set()

    checked = _checked_corpus_program(path)
    typed = build(checked.program, list(checked.resolved or ()),
                  checked.artifacts)
    recorded = checked.artifacts.instantiations
    template_ids = {node.node_id for root in _roots(checked)
                    for node in _nodes(root)}
    for inst in typed.instances:
        assert inst.clone is not None and inst.clone.name == inst.name
        for node in inst.compiled_nodes():
            assert node.node_id not in template_ids, inst.name
            if isinstance(node, ast.Expr):
                ty = typed.semantic_type(node)
                assert ty is not None, (inst.name, ast.format_expr(node))
                assert not variables(ty) & set(inst.sigma), (
                    inst.name, ast.format_expr(node), ty)
            if (isinstance(node, (ast.FnCall, ast.ModuleCall))
                    and typed.origin.get(node.node_id) in recorded):
                callee = typed.call_target(node)
                assert callee is not None and callee.clone is not None, (
                    inst.name, ast.format_expr(node))
