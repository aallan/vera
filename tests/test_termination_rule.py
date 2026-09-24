"""Every recursive function proves it terminates or says it may not (#1492).

Spec §5.6 requires a ``decreases`` clause on every recursive function, and
§7.7.3 states the rule by effect row: a function without ``Diverge`` must be
proved to terminate.  Recursion is decided over the program's call graph
(:mod:`vera.callgraph`), so the instrument here enumerates the SHAPES a cycle
can take and crosses them with the effect rows and the three ways a function
can answer the rule:

* shapes — a direct self-call; mutual 2- and 3-cycles of top-level
  functions; a ``where`` helper calling itself; a mutual pair of helpers; a
  cycle between a parent and its helper; a cycle across groups (a parent,
  its helper and a top-level function, #1520); a call through a closure;
* rows — ``pure``, ``<IO>``, ``<State<Int>>`` and ``<Exn<Int>>``;
* answers — every cycle member declares ``decreases``; none does; every
  function declares ``Diverge``.

Each cell asserts the check-time outcome: accepted, or ``E137`` on exactly
the functions on the cycle.  Each accepted ``Diverge`` cell is also compiled
(no ``E603``) and run, and must return the value its body computes.

Two further groups hold the rest of the class:

* contract cycles (#1521) — a contract or refinement predicate that calls
  back into its own function is refused with ``E138``, with and without a
  measure;
* the measure obligation over the whole cycle (#1520) — a cycle through a
  function outside the ``where`` group, and a recursive call in a position
  the verifier's call walk used to skip, are never reported ``verified``
  unless every call on the cycle decreases.

The census cell holds ``examples/``, the conformance suite and every gated
documentation block at zero violations.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

from tests.checker_helpers import _check
from tests.codegen_helpers import _compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.verifier import verify

ROOT = Path(__file__).resolve().parent.parent


# =====================================================================
# The shape matrix
# =====================================================================


@dataclass(frozen=True)
class Fn:
    """One function of a shape: it calls *calls* (or nothing)."""

    name: str
    calls: str | None
    helpers: tuple[Fn, ...] = ()
    closure: bool = False


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
}

ROWS: dict[str, str | None] = {
    "pure": None, "io": "IO", "state": "State<Int>", "exn": "Exn<Int>",
}

ANSWERS = ("decreases", "none", "diverge")


def _effects(row: str | None, diverge: bool) -> str:
    parts = (["Diverge"] if diverge else []) + ([row] if row else [])
    return f"effects(<{', '.join(parts)}>)" if parts else "effects(pure)"


def _render(fn: Fn, cycle: frozenset[str], row: str | None, answer: str,
            indent: str = "") -> str:
    diverge = answer == "diverge"
    effects = _effects(row, diverge)
    measure = (f"{indent}  decreases(@Nat.0)\n"
               if answer == "decreases" and fn.name in cycle else "")
    if fn.calls is None:
        step = "@Nat.0"
    elif fn.closure:
        step = (f"apply_fn(fn(@Nat -> @Nat) {effects} {{ {fn.calls}(@Nat.0) "
                f"}}, @Nat.0 - 1) + 2")
    else:
        step = f"{fn.calls}(@Nat.0 - 1) + 2"
    text = (
        f"{indent}{'' if indent else 'public '}fn {fn.name}(@Nat -> @Nat)\n"
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
            _render(h, cycle, row, answer, indent + "  ") for h in fn.helpers
        )
        text += f"{indent}where {{\n{inner}{indent}}}\n"
    return text


def _program(shape: str, row: str, answer: str) -> str:
    fns, cycle = SHAPES[shape]
    return "\n".join(_render(fn, cycle, ROWS[row], answer) for fn in fns)


def _e137_names(source: str) -> set[str]:
    names: set[str] = set()
    for d in _check(source):
        if d.error_code == "E137":
            # "Function 'x' is recursive ..."
            names.add(d.description.split("'")[1])
    return names


CELLS = [
    (shape, row, answer)
    for shape in SHAPES for row in ROWS for answer in ANSWERS
]


@pytest.mark.parametrize(("shape", "row", "answer"), CELLS)
def test_rule_at_check(shape: str, row: str, answer: str) -> None:
    """Accepted with a measure or with Diverge; E137 on the cycle without."""
    source = _program(shape, row, answer)
    diags = _check(source)
    errors = [d for d in diags if d.severity == "error"]
    if answer == "none":
        assert {d.error_code for d in errors} == {"E137"}, (source, errors)
        assert _e137_names(source) == set(SHAPES[shape][1]), source
        for d in errors:
            assert "decreases(@Nat.1 - @Nat.0)" in d.fix
            assert "Diverge" in d.fix
    else:
        assert errors == [], (source, errors)


DIVERGE_CELLS = [(shape, row) for shape in SHAPES for row in ROWS]


@pytest.mark.parametrize(("shape", "row"), DIVERGE_CELLS)
def test_diverge_cell_compiles_and_runs(shape: str, row: str) -> None:
    """A Diverge cell compiles with nothing skipped, and runs its cycle."""
    source = _program(shape, row, "diverge")
    result = _compile(source)
    codes = [d.error_code for d in result.diagnostics]
    assert "E603" not in codes, (source, result.diagnostics)
    assert not [d for d in result.diagnostics if d.severity == "error"]
    # Three hops of `callee(@Nat.0 - 1) + 2` from 3 down to 0: 6, a value
    # no skipped or stubbed function could return by accident.
    assert execute(result, fn_name="f", args=[3]).value == 6


def test_diverge_chain_to_main_runs() -> None:
    """E125 carries Diverge up to main, and the whole chain still builds."""
    source = (
        _program("mutual2", "io", "diverge")
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
        _program("direct", "pure", "diverge")
        + "\npublic fn main(@Unit -> @Nat)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n  f(3)\n}\n"
    )
    assert "E125" in {d.error_code for d in _check(source)}


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
}


@pytest.mark.parametrize("measure", [True, False])
@pytest.mark.parametrize("shape", sorted(_SPEC_CYCLES))
def test_contract_cycle_is_refused(shape: str, measure: bool) -> None:
    """E138 at the call, whether or not the function declares a measure."""
    source = _SPEC_CYCLES[shape].replace(
        "{measure}", "decreases(@Nat.0)\n  " if measure else "")
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


# =====================================================================
# The measure is checked over the whole cycle (#1520)
# =====================================================================


def _decreases_status(source: str) -> list[str]:
    program = parse_to_ast(source)
    result = verify(program, source)
    return [o.status for o in result.obligations if o.kind == "decreases"]


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


def test_decreasing_top_level_cycle_is_proved() -> None:
    """The positive twin: every edge of a top-level pair decreases."""
    source = _program("mutual2", "pure", "decreases")
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
