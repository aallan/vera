"""A generic's ``decreases`` keeps its verdict whoever verifies it (#1569).

An instantiated generic is verified through its monomorphized clones, and a
clone is a copy the call graph (:mod:`vera.callgraph`) never saw.  The
verifier finds the clone's cycle through the declaration it was cloned
from.  It used to find that declaration by the clone's NAME, and a clone
verified through an importer is named by its ``mod$<path>$<name>``
discovery key, which no declaration has.  Its cycle was then unknown, so its
measure was never compared and fell to Tier 3 (``E525``), though the module
verified alone proved it.

The matrix crosses:

* visibility — ``private`` and ``public`` (the importer names only a
  non-generic entry point, so both reach the generic through it);
* flavour — generic (``forall<T>``) and plain;
* placement — the module verified alone, through a file that imports it,
  and through a file that imports a module that imports it;
* helper — none; a ``where`` helper carrying the recursion; a cycle
  between the function and its helper;
* measure — a ``@Nat`` countdown, a count-up gap
  (``decreases(@Nat.0 - @Nat.1)``) and a structural ADT;
* direction — a measure that decreases, and one that does not.

Each cell asserts every ``decreases`` obligation's status.  A decreasing
measure is ``verified`` wherever the program verifies the function; one
that does not decrease leaves the obligation that holds the stuck call at
``tier3``, never ``verified``.  A plain function is verified only by the
file that declares it, so it has no obligation in an importer's run.
"""

from __future__ import annotations

import itertools
from pathlib import Path

import pytest

from tests.module_fixture_helpers import (
    _resolve_and_check,
    build_multi_module,
    module_value,
)
from vera import ast
from vera.verifier import ContractVerifier, VerifyResult, verify

VISIBILITY = ("private", "public")
FLAVOURS = ("generic", "plain")
PLACEMENTS = ("direct", "importer", "transitive")
HELPERS = ("none", "helper", "cycle")
MEASURES = ("nat", "gap", "adt")
DIRECTIONS = ("decreasing", "stuck")

# Per measure: parameters after the leading `@T`, the measure, the
# precondition, the base-case test, the recursive call's arguments when the
# measure decreases and when it does not, and the entry point's arguments.
_MEASURE = {
    "nat": {
        "params": "@Nat", "dec": "@Nat.0", "req": "true",
        "base": "@Nat.0 == 0", "step": "@Nat.0 - 1", "stuck": "@Nat.0",
        "entry": "3",
    },
    "gap": {
        "params": "@Nat, @Nat", "dec": "@Nat.0 - @Nat.1",
        "req": "@Nat.1 <= @Nat.0", "base": "@Nat.1 == @Nat.0",
        "step": "@Nat.1 + 1, @Nat.0", "stuck": "@Nat.1, @Nat.0",
        "entry": "0, 3",
    },
    "adt": {
        "params": "@Chain", "dec": "@Chain.0", "req": "true",
        "entry": "Link(Link(Link(End)))",
    },
}


def _fn(vis: str, generic: bool, name: str, measure: str,
        decreasing: bool, callee: str, helper: bool = False) -> str:
    """A measured function *name* whose recursive call names *callee*."""
    t = "T" if generic else "Bool"
    m = _MEASURE[measure]
    if measure == "adt":
        arg = "@Chain.0" if decreasing else "Link(@Chain.0)"
        body = (f"match @Chain.0 {{ End -> 0, Link(@Chain) -> "
                f"{callee}(@{t}.0, {arg}) + 1 }}")
    else:
        args = m["step"] if decreasing else m["stuck"]
        body = (f"if {m['base']} then {{ 0 }} else "
                f"{{ {callee}(@{t}.0, {args}) + 1 }}")
    head = "" if helper else vis + " " + ("forall<T> " if generic else "")
    return (f"{head}fn {name}(@{t}, {m['params']} -> @Nat)\n"
            f"  requires({m['req']})\n  ensures(true)\n"
            f"  decreases({m['dec']})\n  effects(pure)\n{{\n  {body}\n}}\n")


def _module(vis: str, generic: bool, helper: str, measure: str,
            decreasing: bool) -> str:
    """Module ``m``: the measured function ``count`` and its entry ``three``."""
    t = "T" if generic else "Bool"
    m = _MEASURE[measure]
    out = ["module m;\n"]
    if measure == "adt":
        out.append("public data Chain { End, Link(Chain) }\n")
    if helper == "none":
        out.append(_fn(vis, generic, "count", measure, decreasing, "count"))
    else:
        if helper == "helper":
            # `count` forwards to `go`, which carries the recursion.
            slots = {"nat": "@Nat.0", "gap": "@Nat.1, @Nat.0",
                     "adt": "@Chain.0"}[measure]
            parent = (f"{vis} {'forall<T> ' if generic else ''}"
                      f"fn count(@{t}, {m['params']} -> @Nat)\n"
                      f"  requires({m['req']})\n  ensures(true)\n"
                      f"  effects(pure)\n{{\n  go(@{t}.0, {slots})\n}}\n")
            inner = _fn(vis, generic, "go", measure, decreasing, "go",
                        helper=True)
        else:
            # `count` -> `go` -> `count`; `count`'s edge always decreases.
            parent = _fn(vis, generic, "count", measure, True, "go")
            inner = _fn(vis, generic, "go", measure, decreasing, "count",
                        helper=True)
        nested = "\n".join("  " + ln if ln else ln
                           for ln in inner.splitlines())
        out.append(parent.rstrip("\n") + "\nwhere {\n" + nested + "\n}\n")
    out.append("public fn three(@Unit -> @Nat)\n  requires(true)\n"
               "  ensures(true)\n  effects(pure)\n{\n"
               f"  count(true, {m['entry']})\n}}\n")
    return "\n".join(out)


_A = """module a;

import m(three);

public fn six(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  three(()) + three(())
}
"""


def _main(module: str, entry: str) -> str:
    return (f"import {module}({entry});\n\n"
            "public fn main(@Unit -> @Int)\n  requires(true)\n"
            "  ensures(true)\n  effects(pure)\n{\n"
            f"  nat_to_int({entry}(()))\n}}\n")


def _files(placement: str, module_text: str) -> tuple[dict[str, str], str]:
    """The files of one placement, and the one ``vera verify`` is given."""
    files = {"m.vera": module_text}
    if placement == "direct":
        return files, "m.vera"
    if placement == "importer":
        files["main.vera"] = _main("m", "three")
    else:
        files["a.vera"] = _A
        files["main.vera"] = _main("a", "six")
    return files, "main.vera"


def _verify(tmp_path: Path, files: dict[str, str],
            entry: str) -> VerifyResult:
    """Write *files*, and resolve, check and verify *entry* as `vera verify`
    does, with the checker's tables for each module."""
    program, source, main_path, resolved, arts, errors = (
        _resolve_and_check(tmp_path, files, entry))
    assert errors == [], errors
    result = verify(program, source, file=str(main_path),
                    resolved_modules=resolved,
                    expr_types=arts.expr_semantic_types,
                    expr_target_types=arts.expr_target_types,
                    module_artifacts=arts.module_artifacts)
    assert [d for d in result.diagnostics if d.severity == "error"] == []
    return result


def _decreases(tmp_path: Path, files: dict[str, str],
               entry: str) -> list[str]:
    """The ``decreases`` statuses of verifying *entry*, in source order."""
    obligations = sorted(
        (o.line, o.status) for o in _verify(tmp_path, files, entry).obligations
        if o.kind == "decreases")
    return [status for _line, status in obligations]


def _expected(flavour: str, placement: str, helper: str,
              direction: str) -> list[str]:
    """Every obligation ``verified``, except the one holding a stuck call.

    The stuck call is in ``count`` with no helper, and in ``go`` otherwise,
    which comes after ``count`` in the source.
    """
    if flavour == "plain" and placement != "direct":
        return []
    count = 2 if helper == "cycle" else 1
    if direction == "decreasing":
        return ["verified"] * count
    return ["verified"] * (count - 1) + ["tier3"]


def _cell(cell: tuple[str, ...]) -> object:
    """One matrix cell.  An imported generic's ADT measure translates to an
    `Int` in the importer's run, so it is not compared there (#1577, on
    `main` as on this branch); strict, so the cell reports when that lands.
    """
    _vis, flavour, placement, helper, measure, direction = cell
    marks = []
    if (measure == "adt" and flavour == "generic" and placement != "direct"
            and "verified" in _expected(flavour, placement, helper,
                                        direction)):
        marks.append(pytest.mark.xfail(strict=True, reason="#1577"))
    return pytest.param(*cell, id="-".join(cell), marks=marks)


CELLS = [_cell(c) for c in itertools.product(
    VISIBILITY, FLAVOURS, PLACEMENTS, HELPERS, MEASURES, DIRECTIONS)]


@pytest.mark.parametrize(
    ("vis", "flavour", "placement", "helper", "measure", "direction"), CELLS,
)
def test_decreases_verdict_does_not_depend_on_who_verifies(
    tmp_path: Path, vis: str, flavour: str, placement: str, helper: str,
    measure: str, direction: str,
) -> None:
    module_text = _module(vis, flavour == "generic", helper, measure,
                          direction == "decreasing")
    files, entry = _files(placement, module_text)
    assert _decreases(tmp_path, files, entry) == _expected(
        flavour, placement, helper, direction), module_text


_REPRO_MODULE = """module m;

private forall<T> fn count(@T, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count(@T.0, @Nat.0 - 1) + 1 }
}

public fn three(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  count(true, 3)
}
"""


@pytest.mark.parametrize("placement", PLACEMENTS)
def test_issue_repro(tmp_path: Path, placement: str) -> None:
    """#1569's program, verified alone and through its importers."""
    files, entry = _files(placement, _REPRO_MODULE)
    assert _decreases(tmp_path, files, entry) == ["verified"]


# A private generic whose measure grows until a bound: it terminates, but
# the measure does not decrease, so the runtime guard traps on the first
# recursive call.  Verified through an importer it must not be proved.
_GROWING_MODULE = """module m;

private forall<T> fn count(@T, @Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 > 5 then { 0 } else { count(@T.0, @Nat.0 + 1) }
}

public fn three(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  count(true, 3)
}
"""


@pytest.mark.parametrize("placement", ("importer", "transitive"))
def test_growing_measure_is_not_proved_and_traps(
    tmp_path: Path, placement: str,
) -> None:
    files, entry = _files(placement, _GROWING_MODULE)
    assert _decreases(tmp_path / "v", files, entry) == ["tier3"]
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path / "r", files, entry)
    assert verify_errors == [] and cg_errors == []
    outcome, _message = module_value(result)
    assert outcome == "trap"


@pytest.mark.parametrize("placement", ("importer", "transitive"))
def test_repro_runs(tmp_path: Path, placement: str) -> None:
    """The proved measure's program runs to the value its body computes."""
    files, entry = _files(placement, _REPRO_MODULE)
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, files, entry)
    assert verify_errors == [] and cg_errors == []
    assert module_value(result) == (
        "ok", 3 if placement == "importer" else 6)


# The cycle runs through `g`, a top-level function outside `f`'s `where`
# group, and `g`'s edge grows the measure: the runtime guard traps.  A
# clone's cycle must still be found through the declaration it was cloned
# from, and a cycle outside the clone's group claims no proof (#1520).
_ACROSS_TOP_LEVEL_MODULE = """module m;

private forall<T> fn f(@Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { g(@Nat.0) + f(@Nat.0 - 1, @T.0) }
}

private fn g(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 > 5 then { 0 } else { f(@Nat.0 + 1, true) }
}

public fn three(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(3, true)
}
"""


@pytest.mark.parametrize("placement", PLACEMENTS)
def test_cycle_through_a_top_level_function_is_not_proved(
    tmp_path: Path, placement: str,
) -> None:
    files, entry = _files(placement, _ACROSS_TOP_LEVEL_MODULE)
    statuses = _decreases(tmp_path / "v", files, entry)
    assert statuses and "verified" not in statuses, statuses
    if placement != "direct":
        verify_errors, result, cg_errors = build_multi_module(
            tmp_path / "r", files, entry)
        assert verify_errors == [] and cg_errors == []
        assert module_value(result)[0] == "trap"


# The importer declares its own `count`, so the module's generic is
# verified under its `mod$m$count` key: the shadowed family.
_SHADOWING_LOCALS = {
    "plain": """
private fn count(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}
""",
    "generic": """
private forall<T> fn count(@T, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 > 5 then { 0 } else { count(@T.0, @Nat.0 + 1) + 1 }
}
""",
}

_SHADOWING_MAIN = {
    "plain": "count(nat_to_int(three(())))",
    "generic": "nat_to_int(three(()) + count(1, 0))",
}


@pytest.mark.parametrize("local", ("plain", "generic"))
def test_module_generic_shadowed_by_a_local(
    tmp_path: Path, local: str,
) -> None:
    """The module's clone is proved; the local's growing measure is not."""
    module_text = _REPRO_MODULE.replace("private forall", "public forall")
    main = ("import m(three);\n" + _SHADOWING_LOCALS[local]
            + "\npublic fn main(@Unit -> @Int)\n  requires(true)\n"
            "  ensures(true)\n  effects(pure)\n{\n"
            f"  {_SHADOWING_MAIN[local]}\n}}\n")
    files = {"m.vera": module_text, "main.vera": main}
    result = _verify(tmp_path, files, "main.vera")
    by_file = sorted(
        (Path(o.file or "").name, o.status) for o in result.obligations
        if o.kind == "decreases")
    expected = [("m.vera", "verified")]
    if local == "generic":
        expected.append(("main.vera", "tier3"))
    assert by_file == expected


# `count`'s own edge grows the measure; its edge to `go` decreases, and so
# does `go`'s edge back.  The runtime guard traps on the growing edge.
_UNRENAMED_MODULE = """module m;

private forall<T> fn count(@T, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else {
    if @Nat.0 > 5 then { go(@T.0, @Nat.0 - 1) } else { count(@T.0, @Nat.0 + 1) }
  }
}
where {
  fn go(@T, @Nat -> @Nat)
    requires(true)
    ensures(true)
    decreases(@Nat.0)
    effects(pure)
  {
    if @Nat.0 == 0 then { 0 } else { count(@T.0, @Nat.0 - 1) }
  }
}

public fn three(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  count(true, 3)
}
"""


@pytest.mark.parametrize("renamed", (True, False))
def test_a_call_the_clone_left_under_its_source_name_withholds_the_proof(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, renamed: bool,
) -> None:
    """A clone is renamed to its discovery key, and so are the calls in it
    that name its generic.  If a copy left one under the source name, the
    group, keyed by the new names, would not count it, and the proof would
    rest on the other edges.  The verifier refuses the group instead.

    The cell is driven by making the imported generic's copy keep its calls
    as written; the control (``renamed``) proves the same program is
    otherwise refused only for its growing edge.
    """
    reroute = ContractVerifier._reroute_to_module_qualified

    def keep_calls(self: ContractVerifier, decl: ast.FnDecl,
                   *args: object, **kwargs: object) -> ast.FnDecl:
        if decl.forall_vars and not renamed:
            return decl
        return reroute(self, decl, *args, **kwargs)  # type: ignore[arg-type]

    monkeypatch.setattr(ContractVerifier, "_reroute_to_module_qualified",
                        keep_calls)
    files, entry = _files("importer", _UNRENAMED_MODULE)
    statuses = _decreases(tmp_path, files, entry)
    assert statuses and "verified" not in statuses[:1], statuses
