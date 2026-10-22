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

from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/monomorphize.py",
    "vera/codegen/monomorphize.py",
    "vera/checker/calls.py",
    "vera/checker/core.py",
    "vera/lowering.py",
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


@pytest.mark.parametrize("name", [
    pytest.param(name, marks=pytest.mark.xfail(strict=True, reason="red at 94cef528: the typed program (#1679) flips it")) for name in sorted(REPROS)
])
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
        inner_row = "<State<Int>>" if judgment.code == "E125" and arg == judgment.sat else (
            "<State<Bool>>" if judgment.code == "E125" else "pure")
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


def _red_at_base(judgment: str, verdict: str) -> bool:
    """At 94cef528 every unsatisfied ability, cell and key pair passes check,
    and every satisfied effect-row pair is refused (E125)."""
    return (verdict == "sat") == (judgment == "effect_row")


@pytest.mark.parametrize(("judgment", "position", "verdict"), [
    pytest.param(j, p, v, id=f"{j}-{p}-{v}",
                 marks=[pytest.mark.xfail(strict=True, reason="red at 94cef528: the typed program (#1679) flips it")] if _red_at_base(j, v) else [])
    for j, p, v in MATRIX
])
def test_instantiation_judgment(judgment: str, position: str, verdict: str,
                                tmp_path: Path) -> None:
    j = JUDGMENTS[judgment]
    arg = j.sat if verdict == "sat" else j.unsat
    files, line, column = _matrix_program(j, position, arg)
    path = pipeline.write_tree(tmp_path, files)
    if verdict == "unsat":
        _refused_at(path, j.code, line, column)
        return
    checked = pipeline.check(path)
    assert checked.ok, [d.format() for d in checked.diagnostics]
    verified = pipeline.verify(path)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    ran = pipeline.run(path, "main")
    assert ran.ok, (ran.stderr, ran.trap)
