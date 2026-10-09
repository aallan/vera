"""The verifier's runtime-guard claims reconciled with the checks code
generation emits (the audit's T2a): :mod:`vera.reconcile`,
``vera verify --reconcile`` and the corpus gate
``scripts/check_reconciliation.py``.

Four layers:

* **The corpus.**  One test per program of the gate's corpus — every
  conformance program in the manifest, every example, and the library
  modules beside them — runs check, verify, compile and the join in process
  and fails on a mismatch the gate's ``KNOWN`` allowlist does not list, or
  on a program stopping before the join where the manifest says it should
  not.
* **The allowlist, as strict xfails.**  Every ``KNOWN`` entry (and every
  entry for an issue's own repro, below) is a test asserting that its
  mismatch is GONE.  It fails today, which is the expected failure; the day
  the issue is fixed it passes, a strict xfail turns that into a failure,
  and the entry has to come out.
* **The join's rules.**  Each location class's pairing is load-bearing: a
  real program's pair, with its check (or its record) taken away, becomes
  the mismatch the rule exists to report.
* **The command.**  ``cmd_verify(reconcile=True)`` in process, in both
  output modes, and the envelope of a plain ``vera verify --json``
  unchanged.
"""
from __future__ import annotations

import importlib.util
import json
import re
import sys
from dataclasses import replace
from pathlib import Path
from types import ModuleType

import pytest

from tests.verifier_helpers import ALL_EXAMPLES, EXAMPLES_DIR
from vera.cli import cmd_verify
from vera.obligations.core import ProofObligation
from vera.reconcile import (
    EMITTERS_BY_KIND,
    EXCLUDED_KINDS,
    OBLIGATION_KINDS,
    ReconcileRun,
    join,
    mismatch_diagnostics,
    reconcile_file,
)

ROOT = Path(__file__).resolve().parents[1]


def _load_gate() -> ModuleType:
    """``scripts/check_reconciliation.py``, loaded by path, registered in
    ``sys.modules`` first so its dataclasses resolve their annotations."""
    key = "_reconciliation_gate"
    if key in sys.modules:
        return sys.modules[key]
    spec = importlib.util.spec_from_file_location(
        key, ROOT / "scripts" / "check_reconciliation.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[key] = module
    spec.loader.exec_module(module)
    return module


GATE = _load_gate()
PROGRAMS = GATE.corpus()
_RUNS: dict[str, ReconcileRun] = {}


def _run(path: Path) -> ReconcileRun:
    """One program through the pipeline, once per session."""
    key = str(path)
    if key not in _RUNS:
        _RUNS[key] = reconcile_file(path)
    return _RUNS[key]


def _keys(program: object, run: ReconcileRun) -> set[tuple[str, str, str, str]]:
    return {GATE.mismatch_key(program, m) for m in run.mismatches}


# =====================================================================
# The corpus
# =====================================================================

def test_the_corpus_holds_every_manifest_program_and_example() -> None:
    """The parametrisation below is the manifest and the examples, so a
    glob that stopped matching cannot pass over nothing."""
    manifest = json.loads(
        (ROOT / "tests" / "conformance" / "manifest.json")
        .read_text(encoding="utf-8"))
    rels = {p.rel for p in PROGRAMS}
    for entry in manifest:
        assert f"tests/conformance/{entry['file']}" in rels, entry["file"]
    for name in ALL_EXAMPLES:
        assert (EXAMPLES_DIR / name).resolve().relative_to(ROOT).as_posix() in rels
    assert sum(p.negative for p in PROGRAMS) == sum(
        bool(e.get("expected_error")) for e in manifest)


@pytest.mark.parametrize("program", PROGRAMS, ids=lambda p: p.rel)
def test_program_reconciles(program: object) -> None:
    """No mismatch outside ``KNOWN``, no two mismatches sharing one key, and
    no stop before the join, or arrival at it, that the manifest and the
    gate's tables do not declare."""
    run = _run(program.path)  # type: ignore[attr-defined]
    if run.reconciliation is None:
        assert GATE.stop_problem(program, run) is None, (
            GATE.stop_problem(program, run))
        return
    assert GATE.joined_problem(program) is None, GATE.joined_problem(program)
    assert not GATE.shared_keys(program, run.mismatches), (
        GATE.shared_keys(program, run.mismatches))
    known = {entry.key() for entry in GATE.KNOWN}
    unexpected = sorted(_keys(program, run) - known)
    assert not unexpected, (
        "mismatches no KNOWN entry names (file the class's issue, or "
        f"extend it, and add the entry): {unexpected}\n"
        + "\n".join(f"  {m.kind} {m.obligation} {m.line}:{m.column} "
                    f"{m.function}: {m.detail}" for m in run.mismatches))


def _known_id(entry: object) -> str:
    return (f"#{entry.issue}-{entry.kind}-{entry.obligation}-"  # type: ignore[attr-defined]
            f"{entry.site}")  # type: ignore[attr-defined]


@pytest.mark.parametrize("entry", [
    pytest.param(
        entry, id=_known_id(entry),
        marks=pytest.mark.xfail(
            strict=True, raises=AssertionError,
            reason=f"#{entry.issue}: {entry.kind} {entry.obligation} at "
                   f"{entry.site}"),
    )
    for entry in GATE.KNOWN
])
def test_known_mismatch_is_fixed(entry: object) -> None:
    """Fails while the mismatch stands (the expected failure).  When the
    issue is fixed this passes, the strict xfail reports it, and the entry
    comes out of ``KNOWN``."""
    program = next(p for p in PROGRAMS if p.rel == entry.program)  # type: ignore[attr-defined]
    run = _run(program.path)
    assert run.reconciliation is not None, run.check_errors or run.compile_errors
    assert entry.key() not in _keys(program, run)  # type: ignore[attr-defined]


def test_known_names_each_mismatch_once_and_only_corpus_programs() -> None:
    keys = [entry.key() for entry in GATE.KNOWN]
    assert len(keys) == len(set(keys))
    rels = {p.rel for p in PROGRAMS}
    assert {entry.program for entry in GATE.KNOWN} <= rels
    for entry in GATE.KNOWN:
        assert entry.kind in (
            "recorded_unguarded", "guarded_unrecorded", "no_mapping")
        assert re.fullmatch(r"[\w.]+\.vera:\d+:\d+", entry.site), entry.site


class _Stopped:
    """A run that stopped before the join, as `stop_problem` reads one."""

    def __init__(self, check_errors: list[str], compile_errors: list[str]):
        self.check_errors = check_errors
        self.compile_errors = compile_errors


def test_only_a_declared_program_may_stop_at_compile() -> None:
    """A program the manifest declares at level `check` still compiles
    today; one that stopped compiling would drop out of the join, so only a
    program `COMPILE_STOPS` names may stop there."""
    manifest = json.loads(
        (ROOT / "tests" / "conformance" / "manifest.json")
        .read_text(encoding="utf-8"))
    at_check = {f"tests/conformance/{e['file']}" for e in manifest
                if e.get("level") == "check" and not e.get("expected_error")}
    assert set(GATE.COMPILE_STOPS) <= at_check
    program = next(p for p in PROGRAMS
                   if p.rel in at_check and p.rel not in GATE.COMPILE_STOPS)
    refused = _Stopped([], ["E602: an unsupported construct"])
    assert GATE.stop_problem(program, refused) is not None
    declared = next(p for p in PROGRAMS if p.rel in GATE.COMPILE_STOPS)
    assert GATE.stop_problem(declared, refused) is None
    assert GATE.joined_problem(declared) is not None


def test_two_mismatches_at_one_key_are_a_problem() -> None:
    """A `KNOWN` entry names one mismatch: a second at its key — another
    emitter's, another clone's — is reported, not absorbed."""
    entry = GATE.KNOWN[0]
    program = next(p for p in PROGRAMS if p.rel == entry.program)
    run = _run(program.path)
    mismatch = next(m for m in run.mismatches
                    if GATE.mismatch_key(program, m) == entry.key())
    assert GATE.shared_keys(program, [mismatch]) == []
    second = replace(mismatch, function=mismatch.function + "$clone")
    assert GATE.shared_keys(program, [mismatch, second])


def _open_bug_issues() -> set[int]:
    """The issue numbers KNOWN_ISSUES.md's Bugs table lists — the open
    `bug` issues, one row each."""
    text = (ROOT / "KNOWN_ISSUES.md").read_text(encoding="utf-8")
    section = text.split("## Bugs", 1)[1].split("\n## ", 1)[0]
    return {int(n) for n in re.findall(r"\[#(\d+)\]\(", section)}


def test_every_allowlisted_issue_is_an_open_bug() -> None:
    """An entry names an OPEN bug: a closed issue's row leaves the Bugs
    table, and an entry still citing it would excuse a mismatch nobody is
    tracking."""
    cited = {entry.issue for entry in GATE.KNOWN}
    cited |= {issue for issue, *_ in _REPRO_KNOWN} | {1613}
    assert cited <= _open_bug_issues(), sorted(cited - _open_bug_issues())


# =====================================================================
# The issues' own repros
# =====================================================================

#: The open issues whose mismatch no corpus program shows, each by the
#: repro its issue gives, keyed by the issue's number (and a suffix where an
#: issue holds more than one).
REPROS: dict[str, str] = {
    "1607": """\
private fn pos(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(forall(@Nat, array_length(@Array<Int>.result), fn(@Nat -> @Bool) effects(pure) { @Array<Int>.result[@Nat.0] > 0 }))
  effects(pure)
{
  @Array<Int>.0
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Array<Int> = pos([-5]);
  IO.print(int_to_string(@Array<Int>.0[0]))
}
""",
    "1530": """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(<Exn<Int>>)
{
  if @Nat.0 > 5 then { 0 } else { f(@Nat.0 + 1) }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { 0 }
  } in {
    f(1)
  }
}
""",
    "1582": """\
public fn f(@Nat, @Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  assume({ let Tuple<@Int, @Int> = Tuple(1, @Nat.0); @Int.0 >= 0 });
  7
}
""",
    "1608": """\
private fn h(@Map<String, Nat> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

public fn g(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  h(map_insert(map_new(), "k", float_to_int(@Float64.0)))
}
""",
    "1614": """\
public fn g(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Map<String, Nat> = map_new() |> map_insert("k", float_to_int(@Float64.0));
  7
}
""",
    "1613": """\
public fn g(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Option<Nat>, Int> = Tuple(Some(float_to_int(@Float64.0)), 3);
  7
}
""",
    # #1530, PR #1630 review: the chain guard is declined (the call-valued
    # ADT component), and the declined path's range checks skip the
    # call-valued `@Nat` component, so `sz(@Nat.0)` is claimed `tier3` and
    # checked by nothing: `f(0, 2^63)` returns 0.
    "1530-measure": """\
private data Chain {
  End,
  Link(Int, Chain)
}

private fn mk(@Nat -> @Chain)
  requires(true)
  ensures(true)
  effects(pure)
{
  End
}

private fn sz(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn f(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.1, sz(@Nat.0), mk(@Nat.1))
  effects(pure)
{
  if @Nat.1 == 0 then { 0 } else { f(@Nat.1 - 1, @Nat.0) }
}
""",
}

#: (issue, repro, mismatch kind, obligation kind, line, column): every
#: mismatch each repro shows today.  Keyed by the issue whose class it is,
#: which is not always the repro's own: #1530's repro also returns a
#: `handle` the static `@Nat` rule cannot read (#1557).
_REPRO_KNOWN: tuple[tuple[int, str, str, str, int, int], ...] = (
    (1607, "1607", "recorded_unguarded", "ensures", 3, 3),
    (1607, "1607", "recorded_unguarded", "index_bounds", 3, 92),
    (1530, "1530", "recorded_unguarded", "decreases", 4, 3),
    (1557, "1530", "guarded_unrecorded", "nat_bind", 15, 3),
    (1530, "1530-measure", "recorded_unguarded", "decreases_bound", 25, 21),
    (1582, "1582", "recorded_unguarded", "nat_to_int_coerce", 6, 45),
    (1608, "1608", "guarded_unrecorded", "nat_bind", 14, 32),
    (1614, "1614", "guarded_unrecorded", "nat_bind", 6, 56),
)


@pytest.fixture(scope="session")
def repro_dir(tmp_path_factory: pytest.TempPathFactory) -> Path:
    directory = tmp_path_factory.mktemp("reconcile_repros")
    for issue, source in REPROS.items():
        (directory / f"repro_{issue}.vera").write_text(source, encoding="utf-8")
    return directory


def _repro(repro_dir: Path, name: str) -> ReconcileRun:
    run = _run(repro_dir / f"repro_{name}.vera")
    assert run.reconciliation is not None, (
        run.check_errors or run.compile_errors)
    return run


def _repro_keys(run: ReconcileRun) -> set[tuple[str, str, int, int]]:
    return {(m.kind, m.obligation, m.line, m.column) for m in run.mismatches}


@pytest.mark.parametrize("name", sorted(REPROS))
def test_repro_reconciles(repro_dir: Path, name: str) -> None:
    """Each repro shows exactly its allowlisted mismatches, and no other."""
    run = _repro(repro_dir, name)
    allowed = {(k, o, line, col) for _, repro, k, o, line, col in _REPRO_KNOWN
               if repro == name}
    assert _repro_keys(run) - allowed == set(), sorted(_repro_keys(run))


@pytest.mark.parametrize("entry", [
    pytest.param(
        entry, id=f"#{entry[0]}-repro{entry[1]}-{entry[2]}-{entry[3]}",
        marks=pytest.mark.xfail(
            strict=True, raises=AssertionError,
            reason=f"#{entry[0]}: {entry[2]} {entry[3]} at "
                   f"{entry[4]}:{entry[5]} of #{entry[1]}'s repro"),
    )
    for entry in _REPRO_KNOWN
])
def test_repro_mismatch_is_fixed(
    repro_dir: Path, entry: tuple[int, str, str, str, int, int],
) -> None:
    _issue, repro, kind, obligation, line, column = entry
    run = _repro(repro_dir, repro)
    assert (kind, obligation, line, column) not in _repro_keys(run)


@pytest.mark.xfail(
    strict=True, raises=AssertionError,
    reason="#1613: the `Some` payload has neither a record nor a guard")
def test_1613_payload_is_obligated_and_guarded(repro_dir: Path) -> None:
    """#1613's two sides are silent TOGETHER, so the join has nothing to
    disagree about; its pin is the pair the fix must produce — a `nat_bind`
    record on the payload's line answered by a check."""
    run = _repro(repro_dir, "1613")
    assert run.reconciliation is not None
    assert any(record.kind == "nat_bind" and record.line == 6
               for record, _ in run.reconciliation.pairs)


# =====================================================================
# Red-first: the two directions on the issues that report them
# =====================================================================

def test_a_tier3_ensures_with_no_check_is_recorded_unguarded(
    repro_dir: Path,
) -> None:
    """#1607: a quantified `ensures` recorded `tier3` (E523) has no check in
    the module.  Written before the join existed, and seen failing then."""
    run = _repro(repro_dir, "1607")
    found = {(m.kind, m.obligation, m.line, m.column) for m in run.mismatches}
    assert ("recorded_unguarded", "ensures", 3, 3) in found, found


def test_a_guard_with_no_record_is_guarded_unrecorded(repro_dir: Path) -> None:
    """#1614: the piped `map_insert`'s value is guarded and never
    obligated.  Written before the join existed, and seen failing then."""
    run = _repro(repro_dir, "1614")
    found = {(m.kind, m.obligation, m.line, m.column) for m in run.mismatches}
    assert ("guarded_unrecorded", "nat_bind", 6, 56) in found, found


# =====================================================================
# The join's rules, each shown load-bearing on a real program
# =====================================================================

def test_every_obligation_kind_but_state_decl_has_an_emitter() -> None:
    """The kind map is read off the trap registry: every kind but the one
    with no guard concept is some emitter's runtime half, so no kind's
    records fall through to `no_mapping` today."""
    assert EXCLUDED_KINDS == frozenset({"state_decl"})
    assert set(EMITTERS_BY_KIND) == set(OBLIGATION_KINDS) - EXCLUDED_KINDS
    assert not EXCLUDED_KINDS & set(EMITTERS_BY_KIND)


def _rejoin(run: ReconcileRun, *, records: list[ProofObligation] | None = None,
            checks: list[object] | None = None) -> object:
    """The join over *run*'s program with its records or checks replaced."""
    assert run.verify_result is not None and run.compile_result is not None
    assert run.program is not None
    verify_result = run.verify_result if records is None else replace(
        run.verify_result, obligations=records)
    compile_result = run.compile_result if checks is None else replace(
        run.compile_result, emitted_checks=checks)
    return join(verify_result, compile_result, program=run.program,
                file=str(run.path), resolved_modules=run.resolved_modules)


def _example(name: str) -> ReconcileRun:
    run = _run(EXAMPLES_DIR / name)
    assert run.reconciliation is not None
    return run


#: One real pair per location class: (program, record kind, record line).
_RULE_CASES = [
    ("examples/absolute_value.vera", "nat_to_int_coerce", 5),        # value
    ("tests/conformance/ch05_closure_nat_return.vera", "nat_bind", 25),
    #                                          value: a join's arms
    ("tests/conformance/ch02_generic_over_param_adt.vera",
     "nat_to_int_coerce", 22),                                        # binder
    ("examples/http.vera", "call_pre", 32),        # clause: callee prologue
    ("examples/factorial.vera", "decreases_bound", 5),  # value: a measure
    #                                     component, checked where it stands
    ("tests/conformance/ch05_decreases_guard.vera", "decreases", 8),  # clause
    ("tests/conformance/ch02_byte_refinement.vera", "refine_bind", 55),
    #                                                         parameter
    ("tests/conformance/ch02_byte_refinement.vera", "refine_bind", 30),
    #                                                         return
]


def _pair(path: str, kind: str, line: int) -> tuple[ReconcileRun, list]:
    run = _run(ROOT / path)
    assert run.reconciliation is not None
    pairs = [(r, c) for r, c in run.reconciliation.pairs
             if r.kind == kind and r.line == line]
    assert pairs, f"{path} has no {kind} pair on line {line}"
    return run, pairs


@pytest.mark.parametrize(("path", "kind", "line"), _RULE_CASES)
def test_taking_the_check_away_leaves_the_record_unguarded(
    path: str, kind: str, line: int,
) -> None:
    """A paired record, its answering checks removed, is
    `recorded_unguarded`: the pairing the rule made is what kept it clean."""
    run, pairs = _pair(path, kind, line)
    record = pairs[0][0]
    gone = {id(c) for r, c in pairs if r is record}
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if id(c) not in gone]
    result = _rejoin(run, checks=checks)
    assert any(m.kind == "recorded_unguarded" and m.obligation == kind
               and (m.line, m.column) == (record.line, record.column)
               for m in result.mismatches), result.mismatches


@pytest.mark.parametrize(("path", "kind", "line"), [
    case for case in _RULE_CASES if case[1] != "call_pre"])
def test_taking_the_record_away_leaves_the_check_unrecorded(
    path: str, kind: str, line: int,
) -> None:
    """The reverse: the record removed, the check it answered is
    `guarded_unrecorded`, since no other record accounts for it."""
    run, pairs = _pair(path, kind, line)
    record, check = pairs[0]
    records = [r for r in run.verify_result.obligations  # type: ignore[union-attr]
               if r is not record]
    result = _rejoin(run, records=records)
    assert any(
        m.kind == "guarded_unrecorded"
        and (m.line, m.column, m.function) == (check.line, check.column,
                                               check.function)
        for m in result.mismatches), result.mismatches


def test_a_prologue_check_is_also_its_own_requires_record() -> None:
    """A precondition's prologue check answers its function's `requires`
    record as well as every caller's `call_pre`: without the call site's
    record it is still accounted for."""
    run, pairs = _pair("examples/http.vera", "call_pre", 32)
    record, check = pairs[0]
    records = [r for r in run.verify_result.obligations  # type: ignore[union-attr]
               if r is not record]
    result = _rejoin(run, records=records)
    assert not any(m.kind == "guarded_unrecorded" for m in result.mismatches)
    # `fetch_title`'s own `requires` is Tier 3 (E521), so it is a pair too.
    assert any(r.kind == "requires" for r, c in result.pairs if c is check)


_CALL_IN_A_PRECONDITION = """\
private forall<T> fn first_len(@Array<T> -> @Nat)
  requires(array_length(@Array<T>.0) > 0)
  ensures(true)
  effects(pure)
{
  array_length(@Array<T>.0)
}

public fn g(@Array<Int> -> @Nat)
  requires(first_len(@Array<Int>.0) > 0)
  ensures(true)
  effects(pure)
{
  array_length(@Array<Int>.0)
}
"""


def test_a_clause_check_answers_no_call_written_inside_it(
    tmp_path: Path,
) -> None:
    """A call inside `g`'s `requires` has its own precondition, checked in
    ITS callee's prologue.  `g`'s clause check holds `call_pre` among its
    kinds and spans the call, but it checks `g`'s precondition, not
    `first_len`'s: with `first_len`'s prologue checks gone the call's
    record must be unguarded, not paired with the clause around it."""
    path = tmp_path / "call_in_precondition.vera"
    path.write_text(_CALL_IN_A_PRECONDITION, encoding="utf-8")
    run = _run(path)
    assert run.reconciliation is not None
    record = next(r for r in run.verify_result.obligations  # type: ignore[union-attr]
                  if r.kind == "call_pre" and r.status == "tier3")
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if not c.function.startswith("first_len")]
    result = _rejoin(run, checks=checks)
    assert any(m.kind == "recorded_unguarded" and m.obligation == "call_pre"
               and (m.line, m.column) == (record.line, record.column)
               for m in result.mismatches), [
        (r.kind, r.line, r.column, c.function) for r, c in result.pairs]


_CALL_IN_A_DESTRUCTURE = """\
private fn h(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn g(@Float64 -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Int> = Tuple(h(float_to_int(@Float64.0)), 1);
  @Nat.0
}
"""


def test_a_binder_check_answers_no_call_argument_inside_its_value(
    tmp_path: Path,
) -> None:
    """`h`'s argument narrows into `@Nat` inside the value a destructure
    takes apart, and is guarded at the call.  The destructure's `@Nat`
    binder check answers the narrowing of what it binds — the component —
    not a call's argument written inside it: with the call's guard gone the
    argument's record must be unguarded."""
    path = tmp_path / "call_in_destructure.vera"
    path.write_text(_CALL_IN_A_DESTRUCTURE, encoding="utf-8")
    run = _run(path)
    assert run.reconciliation is not None
    arg = next(r for r in run.verify_result.obligations  # type: ignore[union-attr]
               if r.kind == "nat_bind" and r.status == "tier3")
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if not (c.emitter.endswith("_emit_nat_bind_guard")
                      and (c.line, c.column) == (arg.line, arg.column))]
    result = _rejoin(run, checks=checks)
    assert any(m.kind == "recorded_unguarded" and m.obligation == "nat_bind"
               and (m.line, m.column) == (arg.line, arg.column)
               for m in result.mismatches), [
        (r.kind, r.line, r.column, c.emitter) for r, c in result.pairs]


_COMPONENT_OF_AN_ARGUMENT = """\
type Pos = { @Int | @Int.0 > 0 };

private fn f(@Tuple<Pos, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

public fn g(@Float64, @Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(if @Bool.0 then { Tuple(float_to_int(@Float64.0), 1) } else { Tuple(2, 3) })
}
"""


def test_a_parameter_check_answers_a_component_of_the_argument(
    tmp_path: Path,
) -> None:
    """The verifier records a refined component's narrowing where the
    component is written, inside the argument (through the `if` and the
    `Tuple` that build it), and `f`'s prologue checks that component at the
    parameter's type: the two are one obligation."""
    path = tmp_path / "component_of_an_argument.vera"
    path.write_text(_COMPONENT_OF_AN_ARGUMENT, encoding="utf-8")
    run = _run(path)
    assert run.reconciliation is not None
    prologue = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
                if c.function == "f"]
    assert prologue, run.compile_result.emitted_checks  # type: ignore[union-attr]
    assert {r.line for r, c in run.reconciliation.pairs
            if c in prologue} == {16}
    assert not any(m.function == "f" for m in run.mismatches), run.mismatches


def test_a_program_that_does_not_parse_stops_before_the_join(
    tmp_path: Path,
) -> None:
    """The pipeline is total: a parse error is the program's own refusal,
    reported as a stop, never an exception out of the gate."""
    path = tmp_path / "unparsable.vera"
    path.write_text("public fn f(@Int -> @Int)\n  requires(\n", encoding="utf-8")
    run = reconcile_file(path)
    assert run.check_errors and run.reconciliation is None


_SAME_NAMED_LIB = """\
module lib;

type Pos = { @Int | @Int.0 > 0 };

public fn f(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}
"""

_SAME_NAMED_MAIN = """\
import lib(f);

type Pos = { @Int | @Int.0 > 0 };

private fn f(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  8
}

public fn g(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  lib::f(float_to_int(@Float64.0))
}

public fn h(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(@Pos.0)
}
"""

_SAME_NAMED_HELPERS = """\
type Pos = { @Int | @Int.0 > 0 };

public fn a(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(float_to_int(@Float64.0))
}
where {
  fn g(@Pos -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    7
  }
}

public fn b(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(@Pos.0)
}
where {
  fn g(@Pos -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    8
  }
}
"""


@pytest.mark.parametrize(("files", "entry", "callee"), [
    pytest.param({"lib.vera": _SAME_NAMED_LIB, "main.vera": _SAME_NAMED_MAIN},
                 "main.vera", "mod$lib$f", id="a module call beside a local f"),
    pytest.param({"helpers.vera": _SAME_NAMED_HELPERS}, "helpers.vera",
                 "a$where$g", id="two functions' helpers named g"),
])
def test_a_call_answers_only_the_declaration_it_reaches(
    tmp_path: Path, files: dict[str, str], entry: str, callee: str,
) -> None:
    """A parameter's prologue check answers the calls that reach ITS
    function, not every call to a function of the same name: with the
    reached function's check gone, the argument's record must be
    unguarded, whatever a same-named function elsewhere checks."""
    for name, source in files.items():
        (tmp_path / name).write_text(source, encoding="utf-8")
    run = _run(tmp_path / entry)
    assert run.reconciliation is not None
    record = next(r for r in run.verify_result.obligations  # type: ignore[union-attr]
                  if r.kind == "refine_bind" and r.status == "tier3")
    reached = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
               if c.function == callee and "refine_bind" in c.obligations]
    assert reached, run.compile_result.emitted_checks  # type: ignore[union-attr]
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if c not in reached]
    result = _rejoin(run, checks=checks)
    assert any(m.kind == "recorded_unguarded" and m.obligation == "refine_bind"
               and (m.line, m.column) == (record.line, record.column)
               for m in result.mismatches), [
        (r.kind, r.line, r.column, c.function) for r, c in result.pairs]


# =====================================================================
# One check per obligation site (PR #1630 review)
# =====================================================================
#
# Where one node holds several checks, each record is paired with the check
# of its own site, never a sibling's: removing one of several checks at a
# location leaves exactly that site's record unanswered.

def _written(tmp_path: Path, name: str, source: str) -> ReconcileRun:
    path = tmp_path / name
    path.write_text(source, encoding="utf-8")
    run = reconcile_file(path)
    assert run.reconciliation is not None, (
        run.check_errors or run.compile_errors)
    return run


def _unguarded(result: object, kind: str) -> set[tuple[int, int]]:
    return {(m.line, m.column) for m in result.mismatches  # type: ignore[attr-defined]
            if m.kind == "recorded_unguarded" and m.obligation == kind}


def test_a_measure_component_without_its_own_range_check_is_unguarded(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Code generation range-checking only the first `@Nat` component of
    ackermann's measure leaves `@Nat.0` checked by nothing, at entry and at
    both tail sites; its record must not borrow `@Nat.1`'s checks."""
    from vera.codegen.contracts import ContractsMixin

    first_only = ContractsMixin._dec_nat_measure_indices
    monkeypatch.setattr(
        ContractsMixin, "_dec_nat_measure_indices",
        lambda self, ctx, contract: first_only(self, ctx, contract)[:1])
    run = reconcile_file(
        ROOT / "tests" / "conformance" / "ch05_decreases_guard.vera")
    assert run.reconciliation is not None
    assert _unguarded(run.reconciliation, "decreases_bound") == {(8, 21)}


@pytest.mark.parametrize("gone", [(25, 58), (25, 74)])
def test_a_record_at_a_join_needs_the_check_on_every_arm(
    gone: tuple[int, int],
) -> None:
    """The closure's return narrows at the `if`, and code generation guards
    each arm: with one arm's guard gone, the join's record is unguarded,
    whatever the other arm checks."""
    run, pairs = _pair(
        "tests/conformance/ch05_closure_nat_return.vera", "nat_bind", 25)
    record = pairs[0][0]
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if not ("nat_bind" in c.obligations
                      and (c.line, c.column) == gone)]
    result = _rejoin(run, checks=checks)
    assert _unguarded(result, "nat_bind") == {(record.line, record.column)}


_REFINED_FIELD_IN_A_REFINED_RETURN = """\
type Pos = { @Int | @Int.0 > 0 };

private data Box {
  MkBox(Pos)
}

type GoodBox = { @Box | true };

public fn mk(@Float64 -> @GoodBox)
  requires(true)
  ensures(true)
  effects(pure)
{
  MkBox(float_to_int(@Float64.0))
}
"""


def test_a_return_type_check_answers_no_field_of_the_body(
    tmp_path: Path,
) -> None:
    """The return guard checks `GoodBox`'s own predicate on the box; the
    field's `Pos` is the construction's, checked where it is stored.  With
    that check gone the field's record is unguarded, not answered by the
    return type's check standing at the signature."""
    run = _written(tmp_path, "refined_field.vera",
                   _REFINED_FIELD_IN_A_REFINED_RETURN)
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if not ("refine_bind" in c.obligations
                      and (c.line, c.column) == (14, 9))]
    result = _rejoin(run, checks=checks)
    assert _unguarded(result, "refine_bind") == {(14, 9)}


_BINDERS = """\
type Pos = { @Int | @Int.0 > 0 };

private data Pair<A, B> {
  MkPair(A, B)
}

private forall<T> fn gid(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn visible(@Nat, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match MkPair(@Nat.1, @Nat.0) {
    MkPair(@Int, @Int) -> @Int.1 - @Int.0
  }
}

public fn opaque(@Nat, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match gid(MkPair(@Nat.1, @Nat.0)) {
    MkPair(@Int, @Int) -> @Int.1 - @Int.0
  }
}

public fn destructure(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Pos, @Pos> = Tuple(float_to_int(@Float64.0), float_to_int(@Float64.0));
  7
}
"""


@pytest.mark.parametrize(("gone", "field"), [
    ((21, 12), (20, 16)),
    ((21, 18), (20, 24)),
])
def test_a_sub_pattern_check_answers_only_its_own_field(
    tmp_path: Path, gone: tuple[int, int], field: tuple[int, int],
) -> None:
    """Each sub-pattern of `MkPair(@Int, @Int)` widens the field it binds,
    and the verifier records each widening at that field of the scrutinee
    it can see: with one sub-pattern's guard gone, its field's record is
    unguarded, whatever the other sub-pattern checks."""
    run = _written(tmp_path, "binders.vera", _BINDERS)
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if (c.line, c.column) != gone]
    result = _rejoin(run, checks=checks)
    assert _unguarded(result, "nat_to_int_coerce") == {field}


def test_records_sharing_a_node_need_a_check_each(tmp_path: Path) -> None:
    """Over a scrutinee the verifier cannot see into, it records the two
    widenings at the scrutinee itself, two records at one node: one
    sub-pattern guard answers one of them, never both."""
    run = _written(tmp_path, "binders.vera", _BINDERS)
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if (c.line, c.column) != (31, 18)]
    result = _rejoin(run, checks=checks)
    assert [(m.line, m.column) for m in result.mismatches  # type: ignore[attr-defined]
            if m.kind == "recorded_unguarded"] == [(30, 9)]


def test_a_destructured_component_check_answers_only_its_component(
    tmp_path: Path,
) -> None:
    """`let Tuple<@Pos, @Pos> = Tuple(a, b)` guards each component it binds:
    with only the first component's guard left, the second component's
    record is unguarded."""
    run = _written(tmp_path, "binders.vera", _BINDERS)
    refine = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if c.function == "destructure" and "refine_bind" in c.obligations]
    assert len(refine) == 2, refine
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if c is not refine[1]]
    result = _rejoin(run, checks=checks)
    assert _unguarded(result, "refine_bind") == {(40, 59)}


_SIGNATURE_GUARDS = """\
type Pos = { @Int | @Int.0 > 0 };
type PT = { @Tuple<Pos, Int> | true };

private forall<T> fn gid(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

private fn refined_tuple(@PT -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

private fn nested(@Tuple<Tuple<Pos, Int>, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

public fn main(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = refined_tuple(gid(Tuple(float_to_int(@Float64.0), 1)));
  let @Int = nested(Tuple(gid(Tuple(float_to_int(@Float64.0), 2)), 1));
  let @Int = refined_tuple(Tuple(float_to_int(@Float64.0), 1));
  7
}
"""


def test_the_checks_at_one_signature_type_are_one_site_each(
    tmp_path: Path,
) -> None:
    """`PT`'s own predicate and its `Pos` component are both checked at the
    parameter's type, and the verifier records both at the argument it
    cannot see into.  The component's guard is emitted first: with it gone,
    one of the two records is unguarded, not answered by the top-level
    check beside it."""
    run = _written(tmp_path, "signature_guards.vera", _SIGNATURE_GUARDS)
    guards = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if c.function == "refined_tuple"]
    assert len(guards) == 2, guards
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if c is not guards[0]]
    result = _rejoin(run, checks=checks)
    assert [(m.line, m.column) for m in result.mismatches  # type: ignore[attr-defined]
            if m.kind == "recorded_unguarded"] == [(33, 28)]


def test_a_component_check_answers_no_record_of_the_value_it_sits_in(
    tmp_path: Path,
) -> None:
    """Built where the verifier can see it, `Tuple(a, 1)` has `PT`'s own
    predicate recorded at the tuple and `Pos`'s at `a`: with the top-level
    guard gone, the tuple's record is unguarded, not answered by the
    component guard beside it, which checks a place inside it."""
    run = _written(tmp_path, "signature_guards.vera", _SIGNATURE_GUARDS)
    guards = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if c.function == "refined_tuple"]
    checks = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if c is not guards[1]]
    result = _rejoin(run, checks=checks)
    assert [(m.line, m.column) for m in result.mismatches  # type: ignore[attr-defined]
            if m.kind == "recorded_unguarded"] == [(33, 28), (35, 28)]


def test_a_nested_component_check_names_its_path_below_the_signature(
    tmp_path: Path,
) -> None:
    """A nested tuple component's guard stands at the parameter's type and
    names its place below it, so it answers the record at the component
    the argument hides; with it gone, that record is unguarded."""
    run = _written(tmp_path, "signature_guards.vera", _SIGNATURE_GUARDS)
    assert run.mismatches == [], run.mismatches
    nested = [c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
              if c.function == "nested"]
    assert [c.path for c in nested] == [("Tuple.0", "Tuple.0")]
    result = _rejoin(run, checks=[
        c for c in run.compile_result.emitted_checks  # type: ignore[union-attr]
        if c.function != "nested"])
    assert _unguarded(result, "refine_bind") == {(34, 27)}


_SAFE_ARMS = """\
type IntToNat = fn(Int -> Nat) effects(pure);

private fn literal_arm(@Unit -> @IntToNat)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Nat) effects(pure) { if @Int.0 >= 0 then { @Int.0 } else { 0 } }
}

private fn nat_slot_arm(@Nat -> @IntToNat)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Nat) effects(pure) { if @Int.0 >= 0 then { @Int.0 } else { @Nat.0 + 1 } }
}

private fn match_arm(@Unit -> @IntToNat)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Nat) effects(pure) { match @Int.0 { 0 -> 7, _ -> @Int.0 } }
}
"""


def test_an_arm_that_cannot_narrow_needs_no_check(tmp_path: Path) -> None:
    """Code generation guards only the arms of a join that narrow: a
    non-negative literal and arithmetic over `@Nat` slots are left alone.
    The join's record is answered by the guard on the arm that narrows."""
    run = _written(tmp_path, "safe_arms.vera", _SAFE_ARMS)
    assert run.mismatches == [], run.mismatches
    joins = {r.line for r, _c in run.reconciliation.pairs  # type: ignore[union-attr]
             if r.kind == "nat_bind"}
    assert joins == {8, 16, 24}


def test_a_tier3_unguarded_record_does_not_account_for_a_check() -> None:
    """A record saying its site has no runtime check contradicts the check
    standing there."""
    run = _example("absolute_value.vera")
    assert run.reconciliation is not None
    record, check = next((r, c) for r, c in run.reconciliation.pairs
                         if r.kind == "nat_to_int_coerce")
    records = [replace(r, status="tier3_unguarded") if r is record else r
               for r in run.verify_result.obligations]  # type: ignore[union-attr]
    result = _rejoin(run, records=records)
    found = [m for m in result.mismatches
             if m.kind == "guarded_unrecorded"
             and (m.line, m.column) == (check.line, check.column)]
    assert found and "tier3_unguarded" in found[0].detail


def test_a_record_of_a_kind_no_emitter_answers_is_no_mapping() -> None:
    run = _example("absolute_value.vera")
    record = next(r for r in run.verify_result.obligations  # type: ignore[union-attr]
                  if r.status == "tier3")
    records = [replace(r, kind="unmapped_kind")  # type: ignore[arg-type]
               if r is record else r
               for r in run.verify_result.obligations]  # type: ignore[union-attr]
    result = _rejoin(run, records=records)
    assert any(m.kind == "no_mapping" and m.obligation == "unmapped_kind"
               for m in result.mismatches), result.mismatches


def test_a_state_decl_record_is_excluded() -> None:
    """No runtime check stands for `state_decl`, so even a `tier3` one —
    which the verifier never records — would claim nothing to join."""
    run = _example("absolute_value.vera")
    record = next(r for r in run.verify_result.obligations  # type: ignore[union-attr]
                  if r.status == "tier3")
    records = [*run.verify_result.obligations,  # type: ignore[union-attr]
               replace(record, kind="state_decl")]
    result = _rejoin(run, records=records)
    assert not any(m.obligation == "state_decl" for m in result.mismatches)


def test_a_record_at_no_node_is_no_mapping() -> None:
    run = _example("absolute_value.vera")
    record = next(r for r in run.verify_result.obligations  # type: ignore[union-attr]
                  if r.status == "tier3")
    moved = replace(record, line=999, column=1, end_line=999, end_column=2)
    records = [moved if r is record else r
               for r in run.verify_result.obligations]  # type: ignore[union-attr]
    result = _rejoin(run, records=records)
    assert any(m.kind == "no_mapping" and m.line == 999
               for m in result.mismatches), result.mismatches


def test_a_check_at_no_node_is_no_mapping() -> None:
    run = _example("absolute_value.vera")
    checks = list(run.compile_result.emitted_checks)  # type: ignore[union-attr]
    checks.append(replace(checks[0], line=999, column=1, end_line=999,
                          end_column=2))
    result = _rejoin(run, checks=checks)
    assert any(m.kind == "no_mapping" and m.line == 999
               for m in result.mismatches), result.mismatches


def test_a_record_in_a_function_with_no_code_is_absent() -> None:
    """A generic its own module never instantiates is compiled into no
    function, so its E520 `ensures` has no code to be about."""
    run = _run(ROOT / "tests" / "conformance"
               / "ch08_cross_module_generic_lib.vera")
    assert run.reconciliation is not None
    assert [(r.kind, r.error_code) for r in run.reconciliation.absent] == [
        ("ensures", "E520")]
    assert run.mismatches == []


def test_an_imported_body_is_out_of_scope_here() -> None:
    """An imported module's body is verified by that module's own run, so
    its checks need no record in the importer's."""
    run = _run(ROOT / "tests" / "conformance" / "ch08_import_selective.vera")
    assert run.reconciliation is not None
    outside = run.reconciliation.out_of_scope
    assert any(c.file and Path(c.file).name == "math.vera" for c in outside)
    assert not any(m.file and Path(m.file).name == "math.vera"
                   for m in run.mismatches)


def test_each_mismatch_kind_has_its_diagnostic() -> None:
    """E541 for a claim the module does not answer, W004 for a check no
    record accounts for; both fully tagged, quoting the source line."""
    run = _example("absolute_value.vera")
    record, check = next((r, c) for r, c in run.reconciliation.pairs  # type: ignore[union-attr]
                         if r.kind == "nat_to_int_coerce")
    lost_check = _rejoin(run, checks=[
        c for c in run.compile_result.emitted_checks if c is not check])  # type: ignore[union-attr]
    lost_record = _rejoin(run, records=[
        r for r in run.verify_result.obligations if r is not record])  # type: ignore[union-attr]
    source = run.path.read_text(encoding="utf-8")
    diags = mismatch_diagnostics(
        [*lost_check.mismatches, *lost_record.mismatches],
        {str(run.path): source})
    codes = {(d.error_code, d.severity) for d in diags}
    assert ("E541", "error") in codes and ("W004", "warning") in codes
    for d in diags:
        assert d.rationale and d.spec_ref and d.source_line.strip()
        if d.severity == "error":
            assert d.fix


# =====================================================================
# The command
# =====================================================================

def _cli_json(capsys: pytest.CaptureFixture[str], path: Path,
              **kwargs: object) -> tuple[int, dict[str, object]]:
    rc = cmd_verify(str(path), as_json=True, **kwargs)  # type: ignore[arg-type]
    return rc, json.loads(capsys.readouterr().out)


def test_plain_verify_json_carries_no_reconciliation(
    capsys: pytest.CaptureFixture[str],
) -> None:
    _rc, payload = _cli_json(capsys, EXAMPLES_DIR / "absolute_value.vera")
    assert "reconciliation" not in payload


def test_reconcile_reports_an_unanswered_claim_as_e541(
    capsys: pytest.CaptureFixture[str], repro_dir: Path,
) -> None:
    rc, payload = _cli_json(capsys, repro_dir / "repro_1607.vera",
                            reconcile=True)
    assert rc == 1 and payload["ok"] is False
    assert "E541" in {d["error_code"] for d in payload["diagnostics"]}  # type: ignore[index, union-attr]
    report = payload["reconciliation"]
    assert report["compiled"] is True and report["recorded_unguarded"] == 2  # type: ignore[index]


def test_reconcile_reports_an_unrecorded_check_as_w004(
    capsys: pytest.CaptureFixture[str], repro_dir: Path,
) -> None:
    rc, payload = _cli_json(capsys, repro_dir / "repro_1614.vera",
                            reconcile=True)
    assert rc == 0 and payload["ok"] is True
    assert "W004" in {w["error_code"] for w in payload["warnings"]}  # type: ignore[index, union-attr]
    assert payload["reconciliation"]["guarded_unrecorded"] == 1  # type: ignore[index]


def test_reconcile_text_mode_prints_its_summary(
    capsys: pytest.CaptureFixture[str],
) -> None:
    rc = cmd_verify(str(EXAMPLES_DIR / "absolute_value.vera"), reconcile=True)
    out = capsys.readouterr().out
    assert rc == 0
    assert "Reconciliation: 2 of 2 runtime checks (Tier 3) found in the " \
        "compiled module" in out


def test_reconcile_reports_a_refused_compile(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """A program that verifies but does not compile leaves nothing to join:
    the compile's own error is the answer."""
    rc, payload = _cli_json(
        capsys, ROOT / "tests" / "conformance" / "ch03_typed_holes.vera",
        reconcile=True)
    assert rc == 1
    assert "E614" in {d.get("error_code") for d in payload["diagnostics"]}  # type: ignore[union-attr]
    assert payload["reconciliation"]["compiled"] is False  # type: ignore[index]


def test_reconcile_is_refused_by_other_commands(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
) -> None:
    from vera.cli import main

    monkeypatch.setattr(sys, "argv", [
        "vera", "compile", "--reconcile",
        str(EXAMPLES_DIR / "absolute_value.vera")])
    with pytest.raises(SystemExit) as exc:
        main()
    assert exc.value.code == 1
    assert "--reconcile is only accepted by `vera verify`" in (
        capsys.readouterr().err)
