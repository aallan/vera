"""Every recursive function proves it terminates or says it may not (#1492).

Spec §5.6 requires a ``decreases`` clause on every recursive function, and
§7.7.3 states the rule by effect row: a function without ``Diverge`` must be
proved to terminate.  Recursion is decided over the program's call graph
(:mod:`vera.callgraph`), so the instrument here enumerates the SHAPES a cycle
can take and crosses them with the effect rows, the three ways a function
can answer the rule, and where the cycle is written:

* shapes — a direct self-call; mutual 2- and 3-cycles of top-level
  functions; a ``where`` helper calling itself; a mutual pair of helpers; a
  cycle between a parent and its helper; a cycle across groups (a parent,
  its helper and a top-level function, #1520); a call through a closure; a
  call in a handler clause;
* rows — ``pure``, ``<IO>``, ``<State<Int>>`` and ``<Exn<Int>>``;
* answers — every cycle member declares ``decreases``; none does; every
  function declares ``Diverge``, which is guarded only where it also
  declares ``decreases``;
* flavours — plain functions, and generic ones (``forall<T>``, whose
  ``where`` helpers are written over the parent's ``T``);
* placements — the program itself, and a module the program imports.

Each cell asserts the check-time outcome: accepted, or ``E137`` on exactly
the functions on the cycle.  Each accepted ``Diverge`` cell is also compiled
(no ``E603``) and run, and must return the value its body computes.

Further groups hold the rest of the class:

* contract cycles (#1521) — a contract or refinement predicate that calls
  back into its own function is refused with ``E138``, with and without a
  measure;
* the measure obligation over the whole cycle (#1520) — a cycle through a
  function outside the ``where`` group, for a plain and for a generic
  function, is never reported ``verified`` unless every call on it
  decreases;
* call positions (#1524 review) — one cell per place a call can be
  written, DERIVED from the ``vera.ast`` expression classes, for a plain and
  a generic function: a call there that does not decrease is never proved,
  and one that does is proved wherever the walk reads its arguments in the
  activation that makes it;
* a call the measure walk misses withholds the proof, pinned with the walk
  made to miss one;
* an untranslatable ``let`` of every sort family takes its slot with a fresh
  value, so a later reference never reads the binding it shadows.

The census cell holds ``examples/``, the conformance suite and every gated
documentation block at zero violations.
"""

from __future__ import annotations

import dataclasses
import importlib.util
import json
import re
import sys
import tempfile
import typing
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

from tests.codegen_helpers import _assert_no_orphan_call_indirect
from tests.module_fixture_helpers import fake_resolved_module
from vera import ast
from vera.checker import typecheck
from vera.codegen import CompileResult, compile, execute
from vera.errors import Diagnostic
from vera.parser import parse_file, parse_to_ast
from vera.resolver import ResolvedModule
from vera.runtime.traps import WasmTrapError
from vera.transform import transform
from vera.verifier import ContractVerifier, verify

ROOT = Path(__file__).resolve().parent.parent


def _modules(module_text: str | None) -> list[ResolvedModule]:
    return ([fake_resolved_module(("m",), module_text)]
            if module_text is not None else [])


def _check(source: str, module_text: str | None = None) -> list[Diagnostic]:
    """Parse and type-check *source*, with module ``m`` when given."""
    return typecheck(parse_to_ast(source), source,
                     resolved_modules=_modules(module_text))


def _compile(source: str, module_text: str | None = None) -> CompileResult:
    """Compile *source* through a real temp file, with module ``m``.

    ``delete=False`` plus an unlink after the handle is closed: the
    Windows-portable pattern (TESTING.md, Test Fixture Conventions).
    """
    tmp = tempfile.NamedTemporaryFile(  # noqa: SIM115 — closed by the `with`
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    )
    name = tmp.name
    try:
        with tmp:
            tmp.write(source)
        result = compile(transform(parse_file(name)), source=source,
                         file=name, resolved_modules=_modules(module_text))
        _assert_no_orphan_call_indirect(result.wat)
        return result
    finally:
        Path(name).unlink(missing_ok=True)


# =====================================================================
# The shape matrix
# =====================================================================


@dataclass(frozen=True)
class Fn:
    """One function of a shape: it calls *calls* (or nothing).

    *closure* makes the call through a closure the body builds, and
    *clause* makes it in a handler clause, on the value the body throws.
    """

    name: str
    calls: str | None
    helpers: tuple[Fn, ...] = ()
    closure: bool = False
    clause: bool = False


#: shape name -> (top-level functions, the names on the cycle).  The entry
#: point is always `f`.
SHAPES: dict[str, tuple[tuple[Fn, ...], frozenset[str]]] = {
    "direct": ((Fn("f", "f"),), frozenset({"f"})),
    "mutual2": ((Fn("f", "g"), Fn("g", "f")), frozenset({"f", "g"})),
    "mutual3": (
        (Fn("f", "g"), Fn("g", "h"), Fn("h", "f")),
        frozenset({"f", "g", "h"}),
    ),
    "where_self": (
        (Fn("f", "w", helpers=(Fn("w", "w"),)),), frozenset({"w"}),
    ),
    "where_mutual": (
        (Fn("f", "a", helpers=(Fn("a", "b"), Fn("b", "a"))),),
        frozenset({"a", "b"}),
    ),
    "parent_where": (
        (Fn("f", "w", helpers=(Fn("w", "f"),)),), frozenset({"f", "w"}),
    ),
    "across_groups": (
        (Fn("f", "w", helpers=(Fn("w", "h"),)), Fn("h", "f")),
        frozenset({"f", "w", "h"}),
    ),
    "closure": ((Fn("f", "f", closure=True),), frozenset({"f"})),
    "clause": ((Fn("f", "f", clause=True),), frozenset({"f"})),
}

ROWS: dict[str, str | None] = {
    "pure": None, "io": "IO", "state": "State<Int>", "exn": "Exn<Int>",
}

ANSWERS = ("decreases", "none", "diverge")

FLAVOURS = ("plain", "generic")

PLACEMENTS = ("local", "module")


def _effects(row: str | None, diverge: bool) -> str:
    parts = (["Diverge"] if diverge else []) + ([row] if row else [])
    return f"effects(<{', '.join(parts)}>)" if parts else "effects(pure)"


def _render(fn: Fn, cycle: frozenset[str], row: str | None, answer: str,
            generic: bool, indent: str = "") -> str:
    effects = _effects(row, answer == "diverge")
    measure = (f"{indent}  decreases(@Nat.0)\n"
               if answer == "decreases" and fn.name in cycle else "")
    targ = ", @T.0" if generic else ""
    if fn.calls is None:
        step = "@Nat.0"
    elif fn.closure:
        step = (f"apply_fn(fn(@Nat -> @Nat) {effects} {{ {fn.calls}(@Nat.0"
                f"{targ}) }}, @Nat.0 - 1) + 2")
    elif fn.clause:
        step = (f"handle[Exn<Nat>] {{ throw(@Nat) -> {{ {fn.calls}(@Nat.0"
                f"{targ}) + 2 }} }} in {{ throw(@Nat.0 - 1) }}")
    else:
        step = f"{fn.calls}(@Nat.0 - 1{targ}) + 2"
    top = not indent
    # A helper of a generic parent is written over the parent's `T`.
    head = ("public " if top else "") + ("forall<T> " if generic and top else "")
    params = "@Nat, @T -> @Nat" if generic else "@Nat -> @Nat"
    text = (
        f"{indent}{head}fn {fn.name}({params})\n"
        f"{indent}  requires(true)\n"
        f"{indent}  ensures(true)\n"
        f"{measure}"
        f"{indent}  {effects}\n"
        f"{indent}{{\n"
        f"{indent}  if @Nat.0 == 0 then {{ 0 }} else {{ {step} }}\n"
        f"{indent}}}\n"
    )
    if fn.helpers:
        inner = "".join(
            _render(h, cycle, row, answer, generic, indent + "  ")
            for h in fn.helpers
        )
        text += f"{indent}where {{\n{inner}{indent}}}\n"
    return text


def _program(shape: str, row: str, answer: str, flavour: str = "plain",
             placement: str = "local") -> tuple[str, str | None]:
    """The program, and module ``m``'s text when the cycle lives there.

    Every program has a non-generic `entry` that calls `f`, so a generic
    cycle is instantiated and a module's is reached.
    """
    fns, cycle = SHAPES[shape]
    generic = flavour == "generic"
    text = "\n".join(
        _render(fn, cycle, ROWS[row], answer, generic) for fn in fns)
    entry = (
        "public fn entry(@Nat -> @Nat)\n  requires(true)\n  ensures(true)\n"
        f"  {_effects(ROWS[row], answer == 'diverge')}\n"
        f"{{\n  f(@Nat.0{', true' if generic else ''})\n}}\n"
    )
    if placement == "local":
        return text + "\n" + entry, None
    return "import m;\n\n" + entry, "module m;\n\n" + text


def _e137_names(diags: list[Diagnostic]) -> set[str]:
    # "Function 'x' is recursive ..."
    return {d.description.split("'")[1] for d in diags
            if d.error_code == "E137"}


CELLS = [
    (shape, row, answer, flavour, placement)
    for shape in SHAPES for row in ROWS for answer in ANSWERS
    for flavour in FLAVOURS for placement in PLACEMENTS
]


@pytest.mark.parametrize(
    ("shape", "row", "answer", "flavour", "placement"), CELLS)
def test_rule_at_check(shape: str, row: str, answer: str, flavour: str,
                       placement: str) -> None:
    """Accepted with a measure or with Diverge; E137 on the cycle without."""
    source, module_text = _program(shape, row, answer, flavour, placement)
    diags = _check(source, module_text)
    errors = [d for d in diags if d.severity == "error"]
    if answer == "none":
        assert {d.error_code for d in errors} == {"E137"}, (source, errors)
        assert _e137_names(errors) == set(SHAPES[shape][1]), (
            source, module_text)
        for d in errors:
            assert "decreases(@Nat.1 - @Nat.0)" in d.fix
            assert "Diverge" in d.fix
    else:
        assert errors == [], (source, module_text, errors)


DIVERGE_CELLS = [
    (shape, row, flavour, placement)
    for shape in SHAPES for row in ROWS
    for flavour in FLAVOURS for placement in PLACEMENTS
]


@pytest.mark.parametrize(("shape", "row", "flavour", "placement"),
                         DIVERGE_CELLS)
def test_diverge_cell_compiles_and_runs(shape: str, row: str, flavour: str,
                                        placement: str) -> None:
    """A Diverge cell compiles with nothing skipped, and runs its cycle."""
    source, module_text = _program(shape, row, "diverge", flavour, placement)
    result = _compile(source, module_text)
    codes = [d.error_code for d in result.diagnostics]
    assert "E603" not in codes, (source, result.diagnostics)
    assert not [d for d in result.diagnostics if d.severity == "error"]
    # Three hops of `callee(@Nat.0 - 1) + 2` from 3 down to 0: 6, a value
    # no skipped or stubbed function could return by accident.
    assert execute(result, fn_name="entry", args=[3]).value == 6


def test_diverge_chain_to_main_runs() -> None:
    """E125 carries Diverge up to main, and the whole chain still builds."""
    source = (
        _program("mutual2", "io", "diverge")[0]
        + "\npublic fn main(@Unit -> @Unit)\n  requires(true)\n"
        "  ensures(true)\n  effects(<Diverge, IO>)\n{\n"
        "  let @Nat = f(3);\n  IO.print(\"\\(@Nat.0)\")\n}\n"
    )
    assert [d for d in _check(source) if d.severity == "error"] == []
    result = _compile(source)
    assert "E603" not in [d.error_code for d in result.diagnostics]
    assert execute(result).stdout == "6"


def test_caller_of_diverge_must_declare_it() -> None:
    """The opt-out is not silent: a caller without Diverge is E125."""
    source = (
        _program("direct", "pure", "diverge")[0]
        + "\npublic fn main(@Unit -> @Nat)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n  f(3)\n}\n"
    )
    assert "E125" in {d.error_code for d in _check(source)}


_DIVERGE_GROWING = """
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  {measure}effects(<Diverge>)
{
  if @Nat.0 > 5 then { 0 } else { f(@Nat.0 + 1) }
}
"""


@pytest.mark.parametrize("measure", [False, True])
def test_diverge_function_is_guarded_only_with_a_measure(
        measure: bool) -> None:
    """Spec §7.7.3: a `Diverge` function compiles like any other, and has a
    termination guard only if it also declares `decreases`.

    The recursion grows towards its base case.  Without a measure nothing
    checks it and it returns; with one, the guard follows the clause and
    traps on the first growing call.
    """
    source = _DIVERGE_GROWING.replace(
        "{measure}", "decreases(@Nat.0)\n  " if measure else "")
    result = _compile(source)
    assert not [d for d in result.diagnostics if d.severity == "error"]
    guarded = re.search(r"\$dec_active_f(?![A-Za-z0-9_])", result.wat)
    assert (guarded is not None) == measure, result.wat[:400]
    if measure:
        with pytest.raises(WasmTrapError, match="failed to decrease"):
            execute(result, fn_name="f", args=[1])
    else:
        assert execute(result, fn_name="f", args=[1]).value == 0


# =====================================================================
# Contract cycles (#1521)
# =====================================================================

_SPEC_CYCLES = {
    # A function whose postcondition calls itself.
    "ensures_self": """
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == 0 || f(@Nat.result - 1) >= 0)
  {measure}effects(pure)
{
  @Nat.0
}
""",
    # A function whose precondition calls itself.
    "requires_self": """
public fn f(@Nat -> @Nat)
  requires(@Nat.0 == 0 || f(@Nat.0 - 1) >= 0)
  ensures(true)
  {measure}effects(pure)
{
  @Nat.0
}
""",
    # A postcondition that calls a function whose body calls back.
    "ensures_mutual": """
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(g(@Nat.0) >= 0)
  {measure}effects(pure)
{
  @Nat.0
}

public fn g(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(@Nat.0) + 1
}
""",
    # A refinement predicate in a parameter's type, reached through an alias.
    "alias_predicate": """
type Small = { @Nat | f(@Nat.0) < 10 };

public fn f(@Small -> @Nat)
  requires(true)
  ensures(true)
  {measure}effects(pure)
{
  @Small.0
}
""",
    # A constructor's field predicate, evaluated where the body builds one.
    "constructor_field": """
type Small = { @Nat | f(@Nat.0) < 10 };

private data Box {
  B(Small)
}

public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  {measure}effects(pure)
{
  let @Box = B(1);
  @Nat.0
}
""",
    # A refinement written in the body itself.
    "body_refinement": """
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  {measure}effects(pure)
{
  let @{ @Nat | f(@Nat.0) < 10 } = 1;
  @Nat.0
}
""",
}


#: The measure a shape's `f` declares, where its parameter is not a `@Nat`.
_SPEC_MEASURES = {"alias_predicate": "decreases(@Small.0)"}


@pytest.mark.parametrize("measure", [True, False])
@pytest.mark.parametrize("shape", sorted(_SPEC_CYCLES))
def test_contract_cycle_is_refused(shape: str, measure: bool) -> None:
    """E138 at the call, whether or not the function declares a measure."""
    clause = _SPEC_MEASURES.get(shape, "decreases(@Nat.0)")
    source = _SPEC_CYCLES[shape].replace(
        "{measure}", f"{clause}\n  " if measure else "")
    errors = [d for d in _check(source) if d.severity == "error"]
    assert [d.error_code for d in errors] == ["E138"], (source, errors)


def test_contract_call_off_the_cycle_is_accepted() -> None:
    """A contract may call a function that does not lead back."""
    source = """
public fn g(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0 + 1
}

public fn f(@Nat -> @Nat)
  requires(g(@Nat.0) > 0)
  ensures(true)
  effects(pure)
{
  @Nat.0
}
"""
    assert [d for d in _check(source) if d.severity == "error"] == []


def test_contract_edge_does_not_make_a_function_recursive() -> None:
    """Spec §5.6: recursion is a cycle of COMPUTATION edges.

    `f`'s precondition calls `g`, and `g`'s body calls `f`: a cycle through
    a specification edge.  It is refused with E138 at the call, and `f` is
    not thereby recursive, so no E137 joins it.
    """
    source = """
public fn f(@Nat -> @Nat)
  requires(g(@Nat.0) >= 0)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn g(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { f(@Nat.0 - 1) }
}
"""
    errors = [d for d in _check(source) if d.severity == "error"]
    assert [d.error_code for d in errors] == ["E138"], errors


# =====================================================================
# The measure is checked over the whole cycle (#1520)
# =====================================================================


def _decreases_status(source: str, module_text: str | None = None,
                      kind: str = "decreases") -> list[str]:
    program = parse_to_ast(source)
    result = verify(program, source, resolved_modules=_modules(module_text))
    return [o.status for o in result.obligations if o.kind == kind]


_ACROSS_GROUPS_NOT_DECREASING = """
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { h(@Nat.0) + f(@Nat.0 - 1) }
}

public fn h(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 > 5 then { 0 } else { f(@Nat.0 + 1) }
}
"""


def test_cycle_through_top_level_function_is_not_proved() -> None:
    """#1520: `f` reaches itself through `h` with a larger argument.

    The measure was proved over `f`'s self-call alone, so the obligation
    read `verified` while the runtime guard, following the real chain,
    trapped.
    """
    assert "verified" not in _decreases_status(_ACROSS_GROUPS_NOT_DECREASING)


#: The #1520 shape with `f` generic.  A generic is verified only through its
#: monomorphized clones, and a clone is a copy the call graph never saw, so
#: its measure is compared on its `where` group by name.  That is sound only
#: while the original's cycle lies inside the group; here it runs through the
#: top-level `g`, whose call grows, and the run traps in `f$Int`.
_GENERIC_ACROSS_TOP_LEVEL = """
public forall<T> fn f(@Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { g(@Nat.0) + f(@Nat.0 - 1, @T.0) }
}

public fn g(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 > 5 then { 0 } else { f(@Nat.0 + 1, true) }
}
"""

#: Instantiates `f` at `T = Bool`, so no slot namespace merges with `@Nat`.
_ENTRY = """
public fn entry(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(3, true)
}
"""


@pytest.mark.parametrize("placement", PLACEMENTS)
def test_generic_cycle_through_top_level_function_is_not_proved(
        placement: str) -> None:
    """#1524 review: the clone path proves nothing across the group's edge."""
    if placement == "local":
        source, module_text = _GENERIC_ACROSS_TOP_LEVEL + _ENTRY, None
    else:
        source = "import m;\n" + _ENTRY
        module_text = "module m;\n" + _GENERIC_ACROSS_TOP_LEVEL
    statuses = _decreases_status(source, module_text)
    assert statuses and "verified" not in statuses, statuses


def test_decreasing_top_level_cycle_is_proved() -> None:
    """The positive twin: every edge of a top-level pair decreases."""
    source = _program("mutual2", "pure", "decreases")[0]
    assert _decreases_status(source) == ["verified", "verified"]


@pytest.mark.parametrize("position", ["if_condition", "destructure"])
def test_call_in_a_skipped_position_is_compared(position: str) -> None:
    """A recursive call the verifier's walk used to skip.

    Each program calls `f` again with the SAME argument, so no measure
    decreases on that call.  The walk read neither an `if` condition nor a
    destructure's right-hand side, so the obligation was proved from the
    other call alone.
    """
    if position == "if_condition":
        body = ("if @Nat.0 == 0 then { 0 } else {\n"
                "    if f(@Nat.0) == 7 then { 1 } else { f(@Nat.0 - 1) }\n"
                "  }")
    else:
        body = ("if @Nat.0 == 0 then { 0 } else {\n"
                "    let Tuple<@Nat, @Nat> = Tuple(f(@Nat.0), 1);\n"
                "    f(@Nat.0 - 1)\n  }")
    source = (
        "public fn f(@Nat -> @Nat)\n  requires(true)\n  ensures(true)\n"
        "  decreases(@Nat.0)\n  effects(pure)\n{\n  " + body + "\n}\n"
    )
    assert [d for d in _check(source) if d.severity == "error"] == []
    assert "verified" not in _decreases_status(source), source


_MUTUAL_ADT_WRAPPING = """
private data Tree {
  Leaf,
  Node(Forest)
}

private data Forest {
  Empty,
  More(Tree, Forest)
}

private fn tree_size(@Tree -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@Tree.0)
  effects(pure)
{
  match @Tree.0 {
    Leaf -> 1,
    Node(@Forest) -> forest_size(@Forest.0)
  }
}

private fn forest_size(@Forest -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@Forest.0)
  effects(pure)
{
  match @Forest.0 {
    Empty -> 0,
    More(@Tree, @Forest) -> tree_size(Node(More(@Tree.0, @Forest.0))) + forest_size(@Forest.0)
  }
}
"""


def test_top_level_pair_over_two_data_types_is_not_proved() -> None:
    """#1520: `forest_size` re-wraps its own forest and hands it to `tree_size`.

    The pair never terminates, and the measure was proved over
    `forest_size`'s self-call alone because `tree_size` sat outside its
    `where` group.  The two measures have different types, so no common
    order decides the cross call and neither is proved.
    """
    assert "verified" not in _decreases_status(_MUTUAL_ADT_WRAPPING)


@pytest.mark.parametrize("binder", ["closure", "clause"])
def test_call_under_a_closure_or_clause_binder_is_not_proved(
        binder: str) -> None:
    """A closure parameter or a clause binder shadows the parameter.

    Inside the body `@Nat.0` is the closure's argument, `n + 10`, or the
    thrown value, `n + 5`, so the call grows.  The walk read it against the
    enclosing env as `f(n - 1)` and proved it; the runtime guard trapped.
    """
    if binder == "closure":
        step = ("apply_fn(fn(@Nat -> @Nat) effects(pure) "
                "{ f(@Nat.0 - 1) }, @Nat.0 + 10)")
    else:
        step = ("handle[Exn<Nat>] {\n      throw(@Nat) -> { f(@Nat.0 - 1) }\n"
                "    } in {\n      throw(@Nat.0 + 5)\n    }")
    source = (
        "public fn f(@Nat -> @Nat)\n  requires(true)\n  ensures(true)\n"
        "  decreases(@Nat.0)\n  effects(pure)\n{\n"
        "  if @Nat.0 == 0 then { 0 } else {\n    " + step + "\n  }\n}\n"
    )
    assert [d for d in _check(source) if d.severity == "error"] == []
    assert "verified" not in _decreases_status(source), source


def test_call_after_an_untranslatable_let_is_not_proved() -> None:
    """A `let` the verifier cannot translate still binds a slot.

    `@Nat.0` in the recursive call names the `let`'s value, `n + 2`, so the
    call is `f(n + 1)` and no measure decreases on it.  The walk left an
    untranslatable binding out of its env, read `@Nat.0` as the parameter,
    and proved `f(n - 1)` instead, while the runtime guard trapped.
    """
    source = (
        "public fn f(@Nat -> @Nat)\n  requires(true)\n  ensures(true)\n"
        "  decreases(@Nat.0)\n  effects(pure)\n{\n"
        "  if @Nat.0 == 0 then { 0 } else {\n"
        "    let @Nat = array_length(array_map([@Nat.0, 1], "
        "fn(@Nat -> @Nat) effects(pure) { @Nat.0 + 1 })) + @Nat.0;\n"
        "    f(@Nat.0 - 1)\n  }\n}\n"
    )
    assert [d for d in _check(source) if d.severity == "error"] == []
    assert "verified" not in _decreases_status(source), source


# =====================================================================
# Every position a call can be written in (#1524 review)
# =====================================================================
#
# The positions are DERIVED from `vera.ast`: every field of an expression
# class that can hold an expression, followed through the non-expression
# nodes that carry them (a match arm, a handler clause or state, a block's
# statements), and never through a type or a pattern, whose calls are
# specification calls (E138's, not the measure's).  The table below must
# name exactly that set, so a new expression kind or field fails
# `test_positions_are_derived_from_the_ast` until it has a cell.


def _node_types(tp: object) -> set[type]:
    if typing.get_origin(tp) is None:
        return ({tp} if isinstance(tp, type) and issubclass(tp, ast.Node)
                else set())
    out: set[type] = set()
    for arg in typing.get_args(tp):
        out |= _node_types(arg)
    return out


def _concrete(cls: type) -> list[type]:
    subs = [c for c in vars(ast).values()
            if isinstance(c, type) and issubclass(c, cls) and c is not cls]
    return subs or [cls]


def _expression_classes() -> list[type]:
    return [c for c in vars(ast).values()
            if isinstance(c, type) and issubclass(c, ast.Expr)
            and c is not ast.Expr]


def _derived_positions() -> set[str]:
    """``Class.field`` for every place an expression can hold a call."""
    out: set[str] = set()

    def visit(cls: type, prefix: str, path: tuple[type, ...]) -> None:
        hints = typing.get_type_hints(cls, vars(ast))
        for f in dataclasses.fields(cls):
            if f.name == "span":
                continue
            for nt in _node_types(hints[f.name]):
                if issubclass(nt, ast.Expr):
                    out.add(f"{prefix}.{f.name}")
                elif not issubclass(nt, (ast.TypeExpr, ast.Pattern)):
                    # A carrier that contains itself would recurse forever;
                    # the positions it adds are the ones already on the path.
                    for sub in _concrete(nt):
                        if sub not in path:
                            visit(sub, f"{prefix}.{f.name}.{sub.__name__}",
                                  (*path, sub))

    for cls in _expression_classes():
        visit(cls, cls.__name__, (cls,))
    return out


@dataclass(frozen=True)
class Position:
    """How to write one recursive call in one position.

    *snippet* holds ``{call}``.  It is bound by a ``let`` of *let_type*
    (never ``Nat``, so ``@Nat.0`` stays the parameter), written as a
    statement when *let_type* is None, or is the whole branch when *raw*:
    then it binds ``@Nat`` slots itself and holds its own decreasing call,
    ``{anchor}``, below *anchor_binders* of them.  *binders* is how many
    ``@Nat`` binders sit between the call and the parameter.

    *proved* is False where the walk finds the call but proves nothing
    from it, because the call may run in another activation than the one
    that makes it (a closure, a quantifier's predicate, a handler clause):
    there a decreasing call leaves the obligation ``tier3`` as well.
    """

    snippet: str
    let_type: str | None = "Bool"
    binders: int = 0
    row: str | None = None
    proved: bool = True
    raw: bool = False
    anchor_binders: int = 0


POSITIONS: dict[str, Position] = {
    "AnonFn.body": Position(
        "apply_fn(fn(@Unit -> @Nat) effects(pure) {{ {call} }}, ()) > 0",
        proved=False),
    "ArrayLit.elements": Position("[{call}, 1]", "Array<Nat>"),
    "AssertExpr.expr": Position("assert({call} >= 0)", None),
    "AssumeExpr.expr": Position("assume({call} >= 0)", None),
    "BinaryExpr.left": Position("{call} + 1 > 0"),
    "BinaryExpr.right": Position("1 + {call} > 0"),
    "Block.expr": Position("if true then {{ {call} > 0 }} else {{ false }}"),
    "Block.statements.ExprStmt.expr": Position("{call}", None),
    "Block.statements.LetDestruct.value": Position(
        "let Tuple<@Nat, @Nat> = Tuple({call}, 1);\n    {anchor}",
        raw=True, anchor_binders=2),
    "Block.statements.LetStmt.value": Position(
        "let @Nat = {call};\n    {anchor}", raw=True, anchor_binders=1),
    "ConstructorCall.args": Position("Some({call})", "Option<Nat>"),
    "ExistsExpr.domain": Position(
        "exists(@Nat, {call}, fn(@Nat -> @Bool) effects(pure) {{ true }})"),
    "ExistsExpr.predicate": Position(
        "exists(@Nat, 2, fn(@Nat -> @Bool) effects(pure) {{ {call} > 0 }})",
        binders=1, proved=False),
    "FnCall.args": Position("nat_to_string({call})", "String"),
    "ForallExpr.domain": Position(
        "forall(@Nat, {call}, fn(@Nat -> @Bool) effects(pure) {{ true }})"),
    "ForallExpr.predicate": Position(
        "forall(@Nat, 2, fn(@Nat -> @Bool) effects(pure) {{ {call} > 0 }})",
        binders=1, proved=False),
    "HandleExpr.body": Position(
        "handle[Exn<Nat>] {{ throw(@Nat) -> {{ false }} }} "
        "in {{ {call} > 0 }}"),
    "HandleExpr.clauses.HandlerClause.body": Position(
        "handle[Exn<Nat>] {{ throw(@Nat) -> {{ {call} > 0 }} }} "
        "in {{ throw(0) }}", binders=1, proved=False),
    "HandleExpr.clauses.HandlerClause.state_update": Position(
        "handle[State<Nat>](@Nat = 0) {{ get(@Unit) -> {{ resume(@Nat.0) }}, "
        "put(@Nat) -> {{ resume(()) }} with @Nat = {call} }} "
        "in {{ put(1); get(()) > 0 }}", binders=2, proved=False),
    "HandleExpr.state.HandlerState.init_expr": Position(
        "handle[State<Nat>](@Nat = {call}) {{ get(@Unit) -> "
        "{{ resume(@Nat.0) }}, put(@Nat) -> {{ resume(()) }} }} "
        "in {{ get(()) > 0 }}"),
    "IfExpr.condition": Position(
        "if {call} > 0 then {{ true }} else {{ false }}"),
    "IfExpr.else_branch": Position(
        "if @Nat.0 > 3 then {{ true }} else {{ {call} > 0 }}"),
    "IfExpr.then_branch": Position(
        "if @Nat.0 > 3 then {{ {call} > 0 }} else {{ true }}"),
    "IndexExpr.collection": Position("[{call} > 0, true][0]"),
    "IndexExpr.index": Position("[true, false][{call} % 2]"),
    "InterpolatedString.parts": Position('"\\({call})"', "String"),
    "MatchExpr.arms.MatchArm.body": Position(
        "match Some(1) {{ Some(@Nat) -> {call} > 0, None -> false }}",
        binders=1),
    "MatchExpr.scrutinee": Position(
        "match Some({call}) {{ Some(@Nat) -> true, None -> false }}"),
    "ModuleCall.args": Position("m::ident({call}) > 0"),
    "QualifiedCall.args": Position(
        "IO.print(nat_to_string({call}))", None, row="IO"),
    "UnaryExpr.operand": Position("!({call} > 0)"),
}

#: Module `m` for the `ModuleCall` position: a plain function to call into.
_IDENT_MODULE = """public fn ident(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.0)
  effects(pure)
{
  @Nat.0
}
"""


def test_positions_are_derived_from_the_ast() -> None:
    """The cells cover exactly the positions `vera.ast` defines."""
    assert set(POSITIONS) == _derived_positions()


def _position_program(position: str, generic: bool, decreasing: bool) -> str:
    """`f` with one recursive call in *position* and one that decreases.

    The decreasing call is always there, so a walk that missed the call in
    the position would still have a call to prove the measure from.
    """
    pos = POSITIONS[position]
    targ = ", @T.0" if generic else ""
    arg = (f"@Nat.{pos.binders} - 1" if decreasing
           else f"@Nat.{pos.binders} + 1")
    anchor = f"f(@Nat.0 - 1{targ})"
    if pos.raw:
        body = pos.snippet.format(
            call=f"f({arg}{targ})",
            anchor=f"f(@Nat.{pos.anchor_binders} - 1{targ})")
    else:
        text = pos.snippet.format(call=f"f({arg}{targ})")
        bound = f"let @{pos.let_type} = {text};" if pos.let_type else f"{text};"
        body = f"{bound}\n    {anchor}"
    effects = f"effects(<{pos.row}>)" if pos.row else "effects(pure)"
    head = ("public forall<T> fn f(@Nat, @T -> @Nat)" if generic
            else "public fn f(@Nat -> @Nat)")
    source = (
        ("import m;\n\n" if position == "ModuleCall.args" else "")
        + f"{head}\n  requires(true)\n  ensures(true)\n  decreases(@Nat.0)\n"
        f"  {effects}\n{{\n  if @Nat.0 == 0 then {{ 0 }} else {{\n    "
        f"{body}\n  }}\n}}\n"
    )
    if generic:
        source += ("\npublic fn main(@Unit -> @Nat)\n  requires(true)\n"
                   f"  ensures(true)\n  {effects}\n{{\n  f(3, true)\n}}\n")
    return source


POSITION_CELLS = [
    (position, flavour, decreasing)
    for position in sorted(POSITIONS)
    for flavour in FLAVOURS
    for decreasing in (False, True)
]


@pytest.mark.parametrize(("position", "flavour", "decreasing"),
                         POSITION_CELLS)
def test_call_in_each_position(position: str, flavour: str,
                               decreasing: bool) -> None:
    """A call in each position is compared with the measure.

    One that does not decrease is never proved: a generic's clone proved
    one inside a `forall` or `exists`, whose domain and predicate the walk
    treated as leaves, and the run trapped (#1524 review).  One that does
    decrease is proved where the walk reads its arguments in the
    activation that makes the call, which pins that the walk reads that
    position: a position it skipped would withhold the proof instead.
    """
    source = _position_program(position, flavour == "generic", decreasing)
    module_text = _IDENT_MODULE if position == "ModuleCall.args" else None
    errors = [d for d in _check(source, module_text) if d.severity == "error"]
    assert errors == [], (source, errors)
    statuses = _decreases_status(source, module_text)
    if not decreasing:
        assert statuses and "verified" not in statuses, (source, statuses)
    elif POSITIONS[position].proved:
        assert statuses == ["verified"], (source, statuses)
    else:
        assert statuses == ["tier3"], (source, statuses)


# =====================================================================
# A call the measure walk misses withholds the proof
# =====================================================================

#: Marks the one call the walk below is made to miss.
_MISSED = 7919

_MISSED_PLAIN = f"""
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{{
  if @Nat.0 == 0 then {{ 0 }} else {{ f(@Nat.0 + {_MISSED}) + f(@Nat.0 - 1) }}
}}
"""

_MISSED_GENERIC = f"""
public forall<T> fn f(@Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{{
  if @Nat.0 == 0 then {{ 0 }} else {{ f(@Nat.0 + {_MISSED}, @T.0) + f(@Nat.0 - 1, @T.0) }}
}}
"""

_MISSED_CELLS = {
    "plain": (_MISSED_PLAIN, None),
    "generic": (_MISSED_GENERIC + _ENTRY, None),
    "generic_module": ("import m;\n" + _ENTRY,
                       "module m;\n" + _MISSED_GENERIC),
}


@pytest.mark.parametrize("cell", sorted(_MISSED_CELLS))
def test_a_call_the_walk_misses_withholds_the_proof(
        cell: str, monkeypatch: pytest.MonkeyPatch) -> None:
    """#1520 / #1524 review: the proof is held to the call graph's calls.

    The measure walk is made to skip one call, as a walk with a missing
    branch would.  The call does not decrease, so a proof built from the
    calls the walk did reach is false.  Which calls are on the cycle is
    enumerated by `vera.callgraph`, independently of that walk, for a
    declaration the graph holds and for a generic's clone alike, so the
    missed call withholds the proof.  Remove that check and this cell
    reads `verified`.
    """
    real = ContractVerifier._walk_for_calls
    missed: list[ast.FnCall] = []

    def walk(self: ContractVerifier, match: Any, expr: ast.Expr,
             *rest: Any) -> None:
        if isinstance(expr, ast.FnCall) and any(
                isinstance(a, ast.BinaryExpr)
                and isinstance(a.right, ast.IntLit)
                and a.right.value == _MISSED for a in expr.args):
            missed.append(expr)
            return
        real(self, match, expr, *rest)

    monkeypatch.setattr(ContractVerifier, "_walk_for_calls", walk)
    source, module_text = _MISSED_CELLS[cell]
    statuses = _decreases_status(source, module_text)
    assert missed, "the walk never met the marked call, so it hid nothing"
    assert statuses and "verified" not in statuses, statuses


# =====================================================================
# An imported generic's measure (#1524 review)
# =====================================================================

_GENERIC_QUANTIFIER_MODULE = """module m;

public forall<T> fn gf(@Nat, @T -> @Bool)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    true
  } else {
    forall(@Nat, 1, fn(@Nat -> @Bool) effects(pure) { gf(@Nat.1 + 1, @T.0) }) && gf(@Nat.0 - 1, @T.0)
  }
}
"""


def test_imported_generic_quantifier_call_is_not_proved() -> None:
    """An importer verifies an imported generic through its clone.

    The call inside the `forall` grows, and the run traps in `gf$Int`; the
    clone's measure was proved from the other call alone.
    """
    source = ("import m;\n\npublic fn main(@Unit -> @Bool)\n  requires(true)\n"
              "  ensures(true)\n  effects(pure)\n{\n  gf(3, 7)\n}\n")
    statuses = _decreases_status(source, _GENERIC_QUANTIFIER_MODULE)
    assert statuses and "verified" not in statuses, statuses


# =====================================================================
# An untranslatable `let` of every sort family (#1524 review)
# =====================================================================
#
# Each cell binds a value of the family's type, then shadows it with an
# untranslatable `let` (`apply_fn` of a closure), and recurses on what it
# reads from the shadowing value.  Read correctly the call does not
# decrease; read as the value it shadows, it does.  `_fresh_slot_var` has a
# sort only for a scalar, so a non-scalar binding was left out of the walk's
# env and the shadowed value was read in its place.  Each family's control
# makes the shadowing value translatable, which shows the proof can read
# that family at all.


def _opaque(ty: str, value: str) -> str:
    return f"apply_fn(fn(@Unit -> @{ty}) effects(pure) {{ {value} }}, ())"


@dataclass(frozen=True)
class Let:
    """One sort family: its type, the outer value, the shadowing value, and
    the branch that reads the shadowing value.  An empty *outer* shadows the
    parameter *param* instead, which *requires* constrains."""

    ty: str
    outer: str
    shadow: str
    read: str
    param: str = ""
    requires: str = "true"


LETS: dict[str, Let] = {
    "int": Let("Int", "0 - 1", "5",
               "if @Int.0 < 0 then { f(@Nat.0 - 1) } else { f(@Nat.0 + 1) }"),
    "bool": Let("Bool", "true", "false",
                "if @Bool.0 then { f(@Nat.0 - 1) } else { f(@Nat.0 + 1) }"),
    "string": Let("String", '"abcd"', '""',
                  'if @String.0 == "abcd" then { f(@Nat.0 - 1) } '
                  "else { f(@Nat.0 + 1) }"),
    "float": Let("Float64", "2.0", "0.5",
                 "if @Float64.0 > 1.0 then { f(@Nat.0 - 1) } "
                 "else { f(@Nat.0 + 1) }"),
    "adt": Let("NList", "NCons(@Nat.0 - 1, NNil)", "NCons(@Nat.0 + 5, NNil)",
               "match @NList.0 { NCons(@Nat, @NList) -> f(@Nat.0), "
               "NNil -> 0 }"),
    "option": Let("Option<Nat>", "Some(@Nat.0 - 1)", "Some(@Nat.0 + 5)",
                  "match @Option<Nat>.0 { Some(@Nat) -> f(@Nat.0), "
                  "None -> 0 }"),
    "tuple": Let("Tuple<Nat, Bool>", "Tuple(@Nat.0 - 1, true)",
                 "Tuple(@Nat.0 + 5, true)",
                 "match @Tuple<Nat, Bool>.0 { "
                 "Tuple(@Nat, @Bool) -> f(@Nat.0) }"),
    "array": Let("Array<Nat>", "[@Nat.0 - 1]", "[@Nat.0 + 5]",
                 "f(@Array<Nat>.0[0])"),
    # `map_size` is uninterpreted, so only a precondition on a `Map`
    # parameter says anything about one: the shadowed value is that.
    "map": Let("Map<Nat, Nat>", "", "map_new()",
               "if map_size(@Map<Nat, Nat>.0) == 1 then "
               "{ f(@Map<Nat, Nat>.0, @Nat.0 - 1) } "
               "else { f(@Map<Nat, Nat>.0, @Nat.0 + 1) }",
               param="@Map<Nat, Nat>, ",
               requires="map_size(@Map<Nat, Nat>.0) == 1"),
}

_NLIST = """private data NList {
  NNil,
  NCons(Nat, NList)
}

"""


def _let_program(family: str, control: bool) -> str:
    let = LETS[family]
    outer = f"    let @{let.ty} = {let.outer};\n" if let.outer else ""
    if control:
        shadow = let.outer or f"@{let.ty}.0"
    else:
        shadow = _opaque(let.ty, let.shadow)
    return (
        _NLIST
        + f"public fn f({let.param}@Nat -> @Nat)\n"
        f"  requires({let.requires})\n  ensures(true)\n"
        "  decreases(@Nat.0)\n  effects(pure)\n{\n"
        "  if @Nat.0 == 0 then { 0 } else {\n"
        f"{outer}"
        f"    let @{let.ty} = {shadow};\n"
        f"    {let.read}\n"
        "  }\n}\n"
    )


@pytest.mark.parametrize("family", sorted(LETS))
def test_let_of_each_sort_family_shadows_what_it_hides(family: str) -> None:
    """The recursive call reads the untranslatable `let`, not its outer."""
    source = _let_program(family, control=False)
    assert [d for d in _check(source) if d.severity == "error"] == []
    statuses = _decreases_status(source)
    assert statuses and "verified" not in statuses, (source, statuses)


@pytest.mark.parametrize("family", sorted(LETS))
def test_let_family_control_is_proved(family: str) -> None:
    """With the shadowing value translatable, the same read is proved."""
    source = _let_program(family, control=True)
    assert [d for d in _check(source) if d.severity == "error"] == []
    assert _decreases_status(source) == ["verified"], source


#: The other reader of the same rule: the `@Nat` binding check.  The inner
#: match reads the untranslatable `let`'s payload, `-5`, and binds it to a
#: `@Nat`; read as the parameter it shadows, whose payload the `if` has
#: established positive, the narrowing was proved and the run trapped.
_NAT_BIND_AFTER_ADT_LET = """
public fn g(@Option<Int> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> if @Int.0 > 0 then {
      let @Option<Int> = apply_fn(fn(@Unit -> @Option<Int>) effects(pure) { Some(0 - 5) }, ());
      match @Option<Int>.0 {
        Some(@Int) -> {
          let @Nat = @Int.0;
          @Nat.0
        },
        None -> 0
      }
    } else {
      0
    },
    None -> 0
  }
}
"""


def test_nat_binding_after_an_untranslatable_adt_let_is_not_proved() -> None:
    assert [d for d in _check(_NAT_BIND_AFTER_ADT_LET)
            if d.severity == "error"] == []
    statuses = _decreases_status(_NAT_BIND_AFTER_ADT_LET, kind="nat_bind")
    assert statuses and "verified" not in statuses, statuses


# =====================================================================
# Census: the gated corpus holds no violation
# =====================================================================


def _corpus_sources() -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    for path in sorted((ROOT / "examples").glob("*.vera")):
        out.append((path.relative_to(ROOT).as_posix(),
                    path.read_text(encoding="utf-8")))
    manifest = json.loads(
        (ROOT / "tests" / "conformance" / "manifest.json").read_text(
            encoding="utf-8"))
    for entry in manifest:
        if entry.get("expected_error"):
            continue
        path = ROOT / "tests" / "conformance" / entry["file"]
        out.append((path.relative_to(ROOT).as_posix(),
                    path.read_text(encoding="utf-8")))
    return out


def _violations(source: str) -> list[str] | None:
    """E137/E138 violations in *source*, or None when it does not parse."""
    from vera.callgraph import CallGraph
    from vera.errors import VeraError

    try:
        program = parse_to_ast(source)
    except VeraError:
        return None
    graph = CallGraph(tld.decl for tld in program.declarations)
    return (
        [f"E137:{fn.name}" for fn in graph.unmeasured()]
        + [f"E138:{s.caller.name}->{s.callee.name}"
           for s in graph.spec_cycle_sites()]
    )


def test_census_examples_and_conformance_hold_the_rule() -> None:
    """No example or positive conformance program violates E137/E138."""
    hits = []
    for name, source in _corpus_sources():
        found = _violations(source)
        assert found is not None, f"{name} does not parse"
        hits += [f"{name}:{v}" for v in found]
    assert hits == []


def _doc_gate() -> Any:
    key = "check_doc_examples"
    if key in sys.modules:
        return sys.modules[key]
    spec = importlib.util.spec_from_file_location(
        key, ROOT / "scripts" / "check_doc_examples.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[key] = module
    spec.loader.exec_module(module)
    return module


def test_census_gated_documents_hold_the_rule() -> None:
    """Every gated documentation block holds the rule, or is marked WRONG.

    The one block that violates it on purpose is SKILL.md's "Missing
    decreases" example, and it has to carry a WRONG marker naming E137 at
    the check stage, so the doc gate holds it to failing there.
    """
    gate = _doc_gate()
    docs, missing = gate.expand_gates(ROOT)
    assert missing == []
    hits = []
    for doc in docs:
        blocks, _problems = gate.scan_document(ROOT / doc)
        for block in blocks:
            if not gate.selects(block):
                continue
            found = _violations(block.content)
            if not found:
                continue
            marked = [a for a in block.annotations
                      if a.stage == "check" and a.category == "WRONG"
                      and set(a.codes) == {v.split(":")[0] for v in found}]
            if not marked:
                hits.append(f"{doc}:{block.line}:{found}")
    assert hits == []


# =====================================================================
# The warm session sees a cycle an edit elsewhere closes (#1520)
# =====================================================================

_OPEN = """
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { h(@Nat.0) + f(@Nat.0 - 1) }
}

public fn h(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  @Nat.0 + 1
}
"""

#: `h`'s BODY now calls back into `f` with a larger argument.  Nothing in
#: `f` changed, and neither did `h`'s contract, so `f`'s cache key held
#: still while its cycle, and so its measure verdict, moved.
_CLOSED = _OPEN.replace("  @Nat.0 + 1\n", "  if @Nat.0 > 5 then { 0 } else { f(@Nat.0 + 1) }\n")


def test_warm_session_rereads_a_cycle_closed_elsewhere(tmp_path: Path) -> None:
    from vera.obligations.session import VerificationSession

    path = tmp_path / "cycle.vera"
    warm = VerificationSession()
    first = warm.verify_source(_OPEN, file=str(path))
    assert "verified" in [o.status for o in first.obligations
                          if o.kind == "decreases" and o.line == 5]
    warm_closed = warm.verify_source(_CLOSED, file=str(path))
    cold_closed = VerificationSession().verify_source(_CLOSED, file=str(path))

    def statuses(result: Any) -> list[str]:
        return [f"{o.line}:{o.status}" for o in result.obligations
                if o.kind == "decreases"]

    assert statuses(warm_closed) == statuses(cold_closed)
    assert "5:verified" not in statuses(cold_closed)
