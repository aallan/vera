"""tests/pipeline.py, the suite's one driver for the compiler pipeline.

Each stage is held to the command it stands in for: over every corpus
program, ``check``, ``verify`` and ``compile`` give exactly the envelope
``vera <stage> --json`` prints and ``compile`` exactly the WAT ``vera compile
--wat`` prints, and over every conformance program whose run is pinned,
``run`` gives the envelope ``vera run --json`` prints.  Programs shaped as no
corpus program is (a trap of each kind after output, an exit status set
through ``IO.exit``, a missing ``main``, every export dropped, an ill-typed and
an unparsed program) are held to every command the same way, bar ``run`` for
the program whose every export is dropped, with the status ``vera run`` exits
with in both modes.  The CLI side runs in process through
``pipeline.cli``, which is itself held to the CLI run as a process.  The
rest pins the driver's own rules: what a stage takes, what reading an
artefact a stage did not make raises, the unchecked compile, and what ``cli``
borrows and gives back.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
import typing
from collections.abc import Iterable, Mapping
from pathlib import Path

import pytest

from tests import pipeline
from vera.codegen import compile as codegen_compile
from vera.errors import ParseError
from vera.obligations.core import ObligationStatus
from vera.runtime.traps import WasmTrapError
from vera.smt import SmtContext, SmtResult

ROOT = Path(__file__).resolve().parent.parent
CONFORMANCE = ROOT / "tests" / "conformance"
EXAMPLES = ROOT / "examples"
MANIFEST: list[dict[str, object]] = json.loads(
    (CONFORMANCE / "manifest.json").read_text(encoding="utf-8"))

CORPUS = sorted(
    [CONFORMANCE / str(e["file"]) for e in MANIFEST]
    + list(EXAMPLES.glob("*.vera")))
PINNED_RUNS = [
    CONFORMANCE / str(e["file"]) for e in MANIFEST
    if e["level"] == "run" and "expected_stdout" in e
]


def _id(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


# =====================================================================
# Each stage reports what its command reports
# =====================================================================


@pytest.mark.parametrize("path", CORPUS, ids=_id)
def test_each_stage_reports_what_its_command_reports(path: Path) -> None:
    assert pipeline.check(path).envelope() == (
        pipeline.cli("check", "--json", path).json())
    assert pipeline.verify(path).envelope() == (
        pipeline.cli("verify", "--json", path).json())
    compiled = pipeline.compile(path)
    envelope = compiled.envelope()
    assert envelope == pipeline.cli("compile", "--json", path).json()
    if envelope["ok"]:
        assert pipeline.cli("compile", "--wat", path).stdout == (
            compiled.wat + "\n")


@pytest.mark.parametrize("path", PINNED_RUNS, ids=_id)
def test_a_run_reports_what_vera_run_reports(path: Path) -> None:
    ran = pipeline.run(path, stdin="")
    assert ran.envelope() == pipeline.cli("run", "--json", path).json()
    assert ran.returncode == pipeline.cli("run", path).returncode


_IO_MAIN = (
    "public fn main(@Unit -> @Unit)\n"
    "  requires(true)\n  ensures(true)\n  effects(<IO>)\n{\n")
_PRINTS_FIRST = _IO_MAIN + '  IO.print("before");\n  IO.stderr("note");\n'

#: Programs whose shapes no corpus program has: a trap of each kind after
#: output on both streams, an exit status set through `IO.exit`, an entry
#: chosen because there is no `main`, a compile that drops every export, and
#: programs the check and the parser refuse.
_OFF_CORPUS: dict[str, str] = {
    "trap-divide-by-zero": _PRINTS_FIRST + (
        "  let @Int = 0;\n  let @Int = 10 / @Int.0;\n"
        '  IO.print("after")\n}\n'),
    "trap-precondition": (
        "private fn positive(@Int -> @Int)\n"
        "  requires(@Int.0 > 0)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Int.0\n}\n\n" + _PRINTS_FIRST
        + '  let @Int = positive(0);\n  IO.print("after")\n}\n'),
    "trap-overflow": _PRINTS_FIRST + (
        "  let @Int = 9223372036854775807;\n  let @Int = @Int.0 + 1;\n"
        '  IO.print("after")\n}\n'),
    "trap-index": _PRINTS_FIRST + (
        "  let @Array<Int> = [1, 2];\n  let @Int = @Array<Int>.0[5];\n"
        '  IO.print("after")\n}\n'),
    "exit-3": _IO_MAIN + '  IO.print("bye");\n  IO.exit(3)\n}\n',
    "stderr-then-exit-2": _IO_MAIN + '  IO.stderr("failing");\n  IO.exit(2)\n}\n',
    "no-main": (
        "public fn only_one(-> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n  4243\n}\n"),
    "every-export-dropped": (
        "private fn tally(-> @Int) requires(true) ensures(true) effects(pure) {\n"
        '  let @Map<String, Array<Int>> = map_insert(map_new(), "a", [1, 2]);\n'
        "  map_size(@Map<String, Array<Int>>.0)\n}\n\n"
        "public fn main(-> @Int) requires(true) ensures(true) effects(pure) {\n"
        "  tally()\n}\n"),
    "ill-typed": (
        "public fn f(@Int -> @Bool)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n"),
    "unparsed": "public fn f(@Int -> @Int) {",
}

#: `vera run` refuses to run a `main` code generation dropped, and says why;
#: the driver leaves that refusal to the CLI (`pipeline.cli`).
_RUN_REFUSED_BY_THE_CLI = {"every-export-dropped"}


@pytest.mark.parametrize("name", sorted(_OFF_CORPUS))
def test_each_stage_reports_what_its_command_reports_off_the_corpus(
    name: str, tmp_path: Path,
) -> None:
    path = tmp_path / f"{name}.vera"
    path.write_text(_OFF_CORPUS[name], encoding="utf-8")
    assert pipeline.check(path).envelope() == (
        pipeline.cli("check", "--json", path).json())
    assert pipeline.verify(path).envelope() == (
        pipeline.cli("verify", "--json", path).json())
    assert pipeline.compile(path).envelope() == (
        pipeline.cli("compile", "--json", path).json())
    if name in _RUN_REFUSED_BY_THE_CLI:
        return
    ran = pipeline.run(path, stdin="")
    as_json = pipeline.cli("run", "--json", path)
    assert ran.envelope() == as_json.json()
    assert ran.returncode == as_json.returncode == (
        pipeline.cli("run", path).returncode)


def test_the_off_corpus_shapes_are_the_ones_named() -> None:
    """Each cell above reaches the branch it is there for."""
    def ran(name: str) -> pipeline.Ran:
        return pipeline.run(_OFF_CORPUS[name], stdin="")

    kinds = {name: ran(name).trap for name in _OFF_CORPUS
             if name.startswith("trap-")}
    assert {name: t.kind if t else None for name, t in kinds.items()} == {
        "trap-divide-by-zero": "divide_by_zero",
        "trap-precondition": "contract_violation",
        "trap-overflow": "overflow",
        "trap-index": "index_out_of_bounds",
    }
    assert all(t is not None and t.frames and t.stdout == "before"
               and t.stderr == "note" for t in kinds.values())
    assert (ran("exit-3").returncode, ran("stderr-then-exit-2").returncode) == (3, 2)
    assert ran("no-main").envelope()["function"] == "only_one"
    dropped = pipeline.compile(_OFF_CORPUS["every-export-dropped"])
    assert dropped.ok and dropped.exports == []
    assert dropped.envelope()["ok"] is False


# =====================================================================
# Every obligation status reaches `vera verify --json` as itself
# =====================================================================

#: Every status an obligation can have, read from the type that declares
#: them, so a status added there is a cell below before any program has it.
_STATUSES: tuple[str, ...] = typing.get_args(ObligationStatus)

_PURE = "  requires(true)\n  ensures(true)\n  effects(pure)\n"
_POS_INT = "type PosInt = { @Int | @Int.0 > 0 };\n\n"

#: A disclosed callee: `mk`'s narrowing to `@Nat` is neither proved nor
#: guarded, so its caller's precondition holds only from a disclosed fact.
_DISCLOSED_CALLEE = (
    "public fn mk(@Int -> @Option<Nat>)\n" + _PURE
    + "{\n  int_to_nat(handle[Exn<Int>] {\n"
    "    throw(@Nat) -> { nat_to_int(@Nat.0) }\n  } in {\n"
    "    throw(@Int.0)\n  })\n}\n\n"
    "public fn needs_nonneg(@Int -> @Int)\n"
    "  requires(@Int.0 >= 0)\n  ensures(true)\n  effects(pure)\n"
    "{\n  @Int.0\n}\n\n"
    "public fn use_it(@Int -> @Int)\n" + _PURE
    + "{\n  match mk(@Int.0) {\n"
    "    Some(@Nat) -> needs_nonneg(nat_to_int(@Nat.0)),\n"
    "    None -> 0\n  }\n}\n")

#: For each status, and for each (status, code) pair a test that reads the
#: verifier's obligations asserts on, a program whose verification records
#: it.  The corpus records `verified`, `tier3` and an uncoded `violated` and
#: nothing else, so without these `vera verify --json`'s rendering of the
#: other statuses and codes would be held by no program at all.
_STATUS_PROGRAMS: dict[tuple[str, str | None], str] = {
    ("verified", None): (
        "public fn f(@Int -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result == @Int.0)\n  effects(pure)\n{\n  @Int.0\n}\n"),
    ("violated", "E501"): (
        "private fn positive(@Int -> @Int)\n"
        "  requires(@Int.0 > 0)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Int.0\n}\n\n"
        "public fn f(@Int -> @Int)\n" + _PURE + "{\n  positive(0)\n}\n"),
    ("violated", "E503"): (
        "public fn f(@Int -> @Nat)\n" + _PURE
        + "{\n  let @Nat = @Int.0;\n  @Nat.0\n}\n"),
    ("violated", "E505"): (
        _POS_INT + "public fn f(@Int -> @Int)\n" + _PURE
        + "{\n  let @PosInt = @Int.0;\n  @PosInt.0\n}\n"),
    ("violated", "E507"): (
        "public fn f(@Int -> @Int)\n"
        "  requires(@Int.0 > 0)\n  ensures(true)\n  effects(pure)\n"
        "{\n  assert(@Int.0 < 0);\n  @Int.0\n}\n"),
    ("violated", "E526"): (
        "public fn f(@Int -> @Int)\n" + _PURE + "{\n  10 / @Int.0\n}\n"),
    ("violated", "E536"): (
        "public fn halve(@Nat -> @Nat)\n"
        "  requires(@Nat.0 > 9223372036854775807)\n  ensures(true)\n"
        "  decreases(@Nat.0)\n  effects(pure)\n"
        "{\n  if @Nat.0 == 0 then {\n    0\n  } else {\n"
        "    halve(@Nat.0 / 2)\n  }\n}\n"),
    ("tier3", None): (
        "public fn f(@Float64 -> @Int)\n" + _PURE
        + "{\n  float_to_int(@Float64.0)\n}\n"),
    ("tier3", "E506"): (
        _POS_INT + "public fn f(@Float64 -> @PosInt)\n" + _PURE
        + "{\n  float_to_int(@Float64.0)\n}\n"),
    ("tier3", "E522"): (
        "public fn bump(@Unit -> @Unit)\n  requires(true)\n"
        "  ensures(new(State<Int>) == old(State<Int>) + 1)\n"
        "  effects(<State<Int>>)\n"
        "{\n  let @Int = get(());\n  put(@Int.0 + 1);\n  ()\n}\n"),
    ("tier3", "E525"): (
        "private data Chain {\n  Tip,\n  Link(Tuple<Chain, Int>)\n}\n\n"
        "public fn length(@Chain -> @Nat)\n  requires(true)\n"
        "  ensures(true)\n  decreases(@Chain.0)\n  effects(pure)\n"
        "{\n  match @Chain.0 {\n    Tip -> 0,\n"
        "    Link(@Tuple<Chain, Int>) -> match @Tuple<Chain, Int>.0 {\n"
        "      Tuple(@Chain, @Int) -> 1 + length(@Chain.0)\n    }\n"
        "  }\n}\n"),
    ("tier3", "E532"): _DISCLOSED_CALLEE,
    ("tier3", "E534"): (
        _POS_INT + "private fn mk(@Int -> @Option<PosInt>)\n" + _PURE
        + "{\n  Some(@Int.0)\n}\n\n"
        "public fn f(@Int -> @Int)\n" + _PURE
        + "{\n  match mk(@Int.0) {\n    Some(@PosInt) -> 100 / @PosInt.0,\n"
        "    None -> 1\n  }\n}\n"),
    ("tier3", "E535"): (
        "public fn f(@Int, @Array<Int> -> @Int)\n" + _PURE
        + "{\n  assert(array_length(@Array<Int>.0) > @Int.0);\n  @Int.0\n}\n"),
    ("tier3_unguarded", "E504"): _DISCLOSED_CALLEE,
    ("tier3_unguarded", "E506"): (
        "type PosInt = { @Int | @Int.0 > 0 };\n\n"
        "type Tiny = { @PosInt | @PosInt.0 < 10 };\n\n"
        "private fn mk(@Float64 -> @Option<PosInt>)\n" + _PURE
        + "{\n  let @Option<Tiny> = Some(float_to_int(@Float64.0));\n"
        "  @Option<Tiny>.0\n}\n\n"
        "private fn consume(@Option<PosInt> -> @Int)\n"
        "  requires(true)\n  ensures(@Int.result > 0)\n  effects(pure)\n"
        "{\n  match @Option<PosInt>.0 {\n    Some(@PosInt) -> @PosInt.0,\n"
        "    None -> 41\n  }\n}\n\n"
        "public fn f(@Float64 -> @Int)\n"
        "  requires(true)\n  ensures(@Int.result > 0)\n  effects(pure)\n"
        "{\n  consume(mk(@Float64.0))\n}\n"),
    ("tier3_unguarded", "E537"): (
        "private fn risky(@Nat -> @Nat)\n  requires(true)\n  ensures(true)\n"
        "  effects(<Exn<Int>>)\n"
        "{\n  if @Nat.0 == 0 then { throw(1) } else { @Nat.0 }\n}\n\n"
        "public fn walk(@Nat -> @Nat)\n  requires(true)\n  ensures(true)\n"
        "  decreases(risky(@Nat.0))\n  effects(<Exn<Int>>)\n"
        "{\n  if @Nat.0 == 0 then { 0 } else { walk(@Nat.0 / 2) }\n}\n"),
    ("tier3_unguarded", "E538"): (
        "public fn f(@Int -> @Int)\n  requires(@Int.0 > 5 && @Int.0 < 3)\n"
        "  ensures(@Int.result > 0)\n  effects(pure)\n{\n  @Int.0\n}\n"),
    ("timeout", "E524"): (
        "public fn f(@Int -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result == @Int.0)\n  effects(pure)\n{\n  @Int.0\n}\n"),
}

#: The pairs whose program is verified under a solver that answers every
#: query "unknown".  No budget makes Z3 run out of time on a given query
#: reliably, on every host, so the verdict a timeout produces is given to the
#: solver and everything downstream of it is the real verifier.
_SOLVER_UNDECIDED = frozenset({("timeout", "E524")})


def _pair_id(pair: tuple[str, str | None]) -> str:
    return f"{pair[0]}-{pair[1] or 'uncoded'}"


def _pairs(obligations: Iterable[Mapping[str, object]]) -> list[tuple[object, object]]:
    return [(o["status"], o.get("error_code")) for o in obligations]


def _undecided(self: SmtContext, goal: object, assumptions: object) -> SmtResult:
    return SmtResult(status="unknown")


@pytest.mark.parametrize("status", _STATUSES)
def test_every_obligation_status_has_a_program(status: str) -> None:
    """A status the verifier can record and no program here verifies to
    would reach `vera verify --json` with nothing holding how it is
    rendered."""
    assert any(s == status for s, _code in _STATUS_PROGRAMS), (
        f"no program in _STATUS_PROGRAMS verifies to `{status}`; add one, so "
        f"the command's rendering of `{status}` is held")


@pytest.mark.parametrize(
    "pair", sorted(_STATUS_PROGRAMS, key=_pair_id), ids=_pair_id)
def test_each_obligation_status_reaches_the_json_as_itself(
    pair: tuple[str, str | None], tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The verifier records the pair, `vera verify --json` renders every
    record's status and code as itself, and the stage's envelope is the
    command's.  The record is the oracle, so the JSON is held to what was
    verified rather than to another rendering of it."""
    if pair in _SOLVER_UNDECIDED:
        monkeypatch.setattr(SmtContext, "check_valid", _undecided)
    path = tmp_path / f"{_pair_id(pair)}.vera"
    path.write_text(_STATUS_PROGRAMS[pair], encoding="utf-8")
    verified = pipeline.verify(path)
    records = [(o.status, o.error_code or None) for o in verified.obligations]
    assert pair in records, (
        f"the program for {_pair_id(pair)} no longer verifies to it: {records}")
    stage = verified.envelope()
    command = pipeline.cli("verify", "--json", path).json()
    assert _pairs(command["obligations"]) == records, (
        "`vera verify --json` renders an obligation as other than the "
        "verifier recorded it")
    assert stage == command
    sides = {"records": records, "stage": _pairs(stage["obligations"]),
             "command": _pairs(command["obligations"])}
    for status in ("tier3_unguarded", "timeout"):
        present = {side: any(s == status for s, _code in got)
                   for side, got in sides.items()}
        assert len(set(present.values())) == 1, (status, present)


@pytest.mark.parametrize("name,distrust", [
    ("factorial.vera", False),
    ("safe_divide.vera", False),
    ("refinement_types.vera", False),
    ("factorial.vera", True),
])
def test_contract_testing_reports_what_vera_test_reports(
    name: str, distrust: bool,
) -> None:
    path = EXAMPLES / name
    tested = pipeline.contract_test(path, trials=5, distrust=distrust)
    flags = ["--distrust"] if distrust else []
    envelope = pipeline.cli("test", "--json", "--trials", "5", *flags, path).json()
    assert tested.ok == envelope["ok"]
    summary = tested.result.summary
    assert {k: getattr(summary, k) for k in envelope["summary"]} == (
        envelope["summary"])
    assert [(f.fn_name, f.category) for f in tested.result.functions] == [
        (f["name"], f["category"]) for f in envelope["functions"]]


def test_the_corpus_is_all_there() -> None:
    """The differential above is over the whole corpus, not whatever a glob
    happened to find: every manifest entry and every example is a cell."""
    assert len(CORPUS) == len(MANIFEST) + len(list(EXAMPLES.glob("*.vera")))
    assert len(PINNED_RUNS) > 100


# =====================================================================
# The CLI in process is the CLI
# =====================================================================


_HELLO = EXAMPLES / "hello_world.vera"
_FACTORIAL = EXAMPLES / "factorial.vera"


@pytest.mark.parametrize("args", [
    ("check", _HELLO),
    ("check", "--json", _FACTORIAL),
    ("verify", _FACTORIAL),
    ("verify", "--json", _FACTORIAL),
    ("compile", "--wat", _HELLO),
    ("run", _HELLO),
    ("run", "--json", _FACTORIAL, "--fn", "factorial", "--", "5"),
    ("check", ROOT / "no-such-file.vera"),
], ids=lambda a: " ".join(Path(x).name if isinstance(x, Path) else x for x in a))
def test_cli_in_process_prints_what_the_cli_process_prints(
    args: tuple[str | Path, ...],
) -> None:
    argv = [os.fspath(a) for a in args]
    process = subprocess.run(
        [sys.executable, "-m", "vera.cli", *argv],
        capture_output=True, text=True, encoding="utf-8", check=False,
        cwd=ROOT, stdin=subprocess.DEVNULL, timeout=300,
    )
    mine = pipeline.cli(*argv)
    assert (mine.returncode, mine.stdout, mine.stderr) == (
        process.returncode, process.stdout, process.stderr)


#: A test file whose stage, or whose command, does not return within its
#: budget.  The spin stops by itself after 30 s, so a watchdog that does not
#: fire leaves a run that ends, and fails the assertions below, rather than a
#: worker that spins for ever.
_A_HANG = '''\
import time

import vera.cli
from tests import pipeline

_SOURCE = (
    "public fn f(@Int -> @Int)\\n  requires(true)\\n  ensures(true)\\n"
    "  effects(pure)\\n{\\n  @Int.0\\n}\\n")


def _spin(*args, **kwargs):
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        pass


def test_a_stage_past_its_budget(monkeypatch):
    monkeypatch.setattr(pipeline, "DEFAULT_BUDGET_S", 2.0, raising=False)
    monkeypatch.setattr(pipeline, "_verify_program", _spin)
    pipeline.verify(_SOURCE)


def test_a_command_past_its_budget(monkeypatch, tmp_path):
    monkeypatch.setattr(pipeline, "DEFAULT_BUDGET_S", 2.0, raising=False)
    monkeypatch.setattr(vera.cli, "cmd_check", _spin)
    path = tmp_path / "f.vera"
    path.write_text(_SOURCE, encoding="utf-8")
    pipeline.cli("check", path)
'''


@pytest.mark.parametrize(("hang", "runner"), [
    ("test_a_stage_past_its_budget", ("-n", "1")),
    ("test_a_command_past_its_budget", ("-n", "1")),
    ("test_a_stage_past_its_budget", ("-p", "no:xdist")),
], ids=["stage-xdist", "command-xdist", "stage-plain"])
def test_a_call_past_its_budget_ends_its_run_naming_the_test(
    hang: str, runner: tuple[str, str], tmp_path: Path,
) -> None:
    """A stage call, or a command, that does not return within its budget
    ends the process that runs it, after writing every thread's traceback to
    the stderr the run started with; under pytest-xdist the report names the
    test the worker was running.  The repository's conftest is loaded, as
    every run of the suite loads it, because it is what hands the watchdog
    that stderr."""
    test_file = tmp_path / "test_a_hang.py"
    test_file.write_text(_A_HANG, encoding="utf-8")
    env = {name: value for name, value in os.environ.items()
           if not name.startswith(("GIT_", "PYTEST_", "COV_CORE_"))}
    started = time.monotonic()
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider",
         "-p", "tests.conftest", *runner, "--rootdir", str(tmp_path),
         f"{test_file}::{hang}"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=ROOT, env=env, timeout=120, check=False,
    )
    elapsed = time.monotonic() - started
    output = proc.stdout + proc.stderr
    assert "Timeout (0:00:02)!" in output and "in _spin" in output, output
    assert elapsed < 25, (elapsed, output)
    if runner[0] == "-n":
        assert f"crashed while running 'test_a_hang.py::{hang}'" in output, output
    else:
        assert proc.returncode == 1, output


def test_budgets_nest_and_a_default_keeps_the_one_in_force(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An inner budget is armed for its block and the enclosing one armed
    again for what it has left; a default inside a budget arms nothing, so a
    stage's call of the stages before it keeps its caller's budget; the
    outermost cancels the timer on every path out."""
    calls: list[tuple[object, ...]] = []
    monkeypatch.setattr(
        pipeline.faulthandler, "dump_traceback_later",
        lambda seconds, **kwargs: calls.append(("arm", round(seconds))))
    monkeypatch.setattr(
        pipeline.faulthandler, "cancel_dump_traceback_later",
        lambda: calls.append(("cancel",)))
    with pipeline._budget(600):
        with pipeline._budget(None):
            pass
        with pipeline._budget(5):
            pass
    assert calls == [("arm", 600), ("arm", 5), ("arm", 600), ("cancel",)], calls
    calls.clear()
    with pytest.raises(ZeroDivisionError), pipeline._budget(None):
        _ = 1 / 0
    assert calls == [("arm", pipeline.DEFAULT_BUDGET_S), ("cancel",)], calls
    calls.clear()
    pipeline.verify(_FACTORIAL, budget_s=300)
    assert calls == [("arm", 300), ("cancel",)], calls


def test_cli_gives_back_what_it_borrows(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("VERA_W24_PROBE", "kept")
    monkeypatch.delenv("VERA_W24_ABSENT", raising=False)
    argv, stdin, stdout, stderr = sys.argv, sys.stdin, sys.stdout, sys.stderr
    result = pipeline.cli(
        "check", "--json", _HELLO,
        env={"VERA_W24_PROBE": None, "VERA_W24_ABSENT": "set"},
    )
    assert result.returncode == 0 and result.json()["ok"] is True
    assert (sys.argv, sys.stdin, sys.stdout, sys.stderr) == (
        argv, stdin, stdout, stderr)
    assert os.environ["VERA_W24_PROBE"] == "kept"
    assert "VERA_W24_ABSENT" not in os.environ


@pytest.mark.parametrize("code,status,printed", [
    (None, 0, ""), (0, 0, ""), (3, 3, ""), (True, 1, ""), (False, 0, ""),
    ("stopped", 1, "stopped\n"),
])
def test_an_exit_code_becomes_the_status_python_exits_with(
    code: object, status: int, printed: str,
    capsys: pytest.CaptureFixture[str],
) -> None:
    got = pipeline._exit_status(code)
    assert (got, type(got)) == (status, int)
    assert capsys.readouterr().err == printed


def test_cli_hands_the_command_its_stdin_and_environment(tmp_path: Path) -> None:
    program = tmp_path / "echo.vera"
    program.write_text(
        "public fn main(@Unit -> @Unit)\n"
        "  requires(true)\n  ensures(true)\n  effects(<IO>)\n"
        "{\n"
        "  let @String = IO.read_line(());\n"
        "  IO.print(@String.0);\n"
        "  match IO.get_env(\"VERA_W24_PROBE\") {\n"
        "    Some(@String) -> IO.print(@String.0),\n"
        "    None -> IO.print(\"-\")\n"
        "  }\n"
        "}\n",
        encoding="utf-8",
    )
    ran = pipeline.cli("run", program, stdin="hello\n",
                       env={"VERA_W24_PROBE": "!"})
    assert (ran.returncode, ran.stdout) == (0, "hello!\n"), ran.stderr


def test_cli_writes_the_bytes_the_cli_process_writes(tmp_path: Path) -> None:
    """On bytes, as a pipe carries them: a text-mode capture of the process
    would read the carriage return as a newline, so a comparison of decoded
    text cannot tell the two apart.  Each newline is the platform's line
    separator in both, and the text a command wrote is still its own."""
    program = tmp_path / "bytes.vera"
    program.write_text(
        "public fn main(@Unit -> @Unit)\n"
        "  requires(true)\n  ensures(true)\n  effects(<IO>)\n"
        "{\n"
        '  IO.print("a\\rb\\n→\\tc");\n'
        '  IO.stderr("note\\n")\n'
        "}\n",
        encoding="utf-8",
    )
    process = subprocess.run(
        [sys.executable, "-m", "vera.cli", "run", str(program)],
        capture_output=True, check=False, cwd=ROOT,
        stdin=subprocess.DEVNULL, timeout=300,
    )
    mine = pipeline.cli("run", program)
    assert (mine.returncode, mine.stdout_bytes, mine.stderr_bytes) == (
        process.returncode, process.stdout, process.stderr)
    assert (mine.stdout, mine.stderr) == ("a\rb\n→\tc\n", "note\n")


# =====================================================================
# What a stage takes
# =====================================================================


def test_source_text_is_checked_as_the_file_it_came_from() -> None:
    text = _FACTORIAL.read_text(encoding="utf-8")
    assert pipeline.verify(text, file=str(_FACTORIAL)).envelope() == (
        pipeline.verify(_FACTORIAL).envelope())
    assert pipeline.check(text).file is None


def test_a_path_resolves_its_imports_and_source_text_does_not() -> None:
    path = EXAMPLES / "modules.vera"
    assert pipeline.check(path).ok
    assert pipeline.check(path).modules
    text = pipeline.check(path.read_text(encoding="utf-8"), file=str(path))
    assert text.modules is None and not text.ok


def test_modules_given_replace_resolution(tmp_path: Path) -> None:
    entry = pipeline.write_tree(tmp_path, {
        "main.vera": (
            "import lib(twice);\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  twice(21)\n}\n"),
        "lib.vera": (
            "module lib;\n\n"
            "public fn twice(@Int -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  @Int.0 * 2\n}\n"),
    })
    resolved = pipeline.check(entry)
    assert resolved.ok and resolved.modules
    assert pipeline.run(entry).value == 42
    given = pipeline.run(entry.read_text(encoding="utf-8"),
                         modules=resolved.modules)
    assert given.value == 42


def test_compile_builds_the_module_vera_codegen_compile_builds() -> None:
    """The stage builds its own generator, to hand it back; the module it
    builds is the one the public function builds from the same tables."""
    path = EXAMPLES / "modules.vera"
    checked = pipeline.check(path, collect_module_artifacts=True)
    artifacts = checked.artifacts
    expected = codegen_compile(
        checked.program, source=checked.source, file=checked.file,
        resolved_modules=checked.resolved,
        expr_semantic_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
    )
    built = pipeline.compile(path)
    assert built.generator is not None
    assert built.wat == expected.wat


_UNCHECKED = """fn helper(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  helper(@Int.0)
}
"""


def test_an_unchecked_compile_builds_what_the_check_refuses() -> None:
    assert not pipeline.check(_UNCHECKED).ok
    refused = pipeline.compile(_UNCHECKED)
    assert not refused.ok and refused.generator is None
    with pytest.raises(pipeline.StageFailed, match="Missing visibility"):
        refused.result
    built = pipeline.compile(_UNCHECKED, checked=False)
    assert built.ok and built.checked is None
    assert pipeline.run(built, fn="f", args=[41]).value == 42
    assert pipeline.run(_UNCHECKED, fn="f", args=[41], checked=False).value == 42


# =====================================================================
# Reading what a stage did not make
# =====================================================================


_UNPARSED = "public fn f(@Int -> @Int) {"
_ILL_TYPED = """public fn f(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""
_TRAPS = """public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = 0;
  10 / @Int.0
}
"""


def test_a_parse_error_is_a_result_and_reading_past_it_raises_it() -> None:
    checked = pipeline.check(_UNPARSED)
    assert not checked.ok
    assert [d.error_code for d in checked.errors] == ["E001"]
    with pytest.raises(ParseError):
        checked.program
    with pytest.raises(ParseError):
        pipeline.verify(_UNPARSED).result
    with pytest.raises(ParseError):
        pipeline.compile(_UNPARSED).result
    with pytest.raises(ParseError):
        pipeline.run(_UNPARSED).value


def test_a_refusing_check_stops_the_stages_after_it() -> None:
    verified = pipeline.verify(_ILL_TYPED)
    assert not verified.ok and not verified.ran
    with pytest.raises(pipeline.StageFailed, match="the check reported"):
        verified.result
    ran = pipeline.run(_ILL_TYPED, fn="f", args=[1])
    assert not ran.ok and ran.module is None and ran.returncode == 1
    with pytest.raises(pipeline.StageFailed):
        ran.value


def test_a_verify_past_the_check_verifies_what_the_check_refused() -> None:
    past = pipeline.verify(_ILL_TYPED, past_check=True)
    assert past.ran and not past.ok
    assert past.checked.errors
    assert past.result.obligations is not None
    assert pipeline.verify(_UNPARSED, past_check=True).ran is False


def test_a_compile_past_the_check_builds_what_the_check_refused() -> None:
    refused = pipeline.compile(_ILL_TYPED)
    assert refused.generator is None
    past = pipeline.compile(_ILL_TYPED, past_check=True)
    assert past.generator is not None
    assert past.checked is not None and past.checked.errors
    assert not past.ok
    assert "f" in past.result.exports


def test_a_trap_is_a_result_and_reading_the_value_raises_it() -> None:
    ran = pipeline.run(_TRAPS)
    assert not ran.ok and ran.returncode == 1
    assert ran.trap is not None and ran.trap.kind == "divide_by_zero"
    with pytest.raises(WasmTrapError):
        ran.value


def test_every_compile_holds_the_call_indirect_table_invariant() -> None:
    """#1185, asserted on every module the stage builds."""
    with pytest.raises(AssertionError, match="#1185"):
        pipeline.assert_no_orphan_call_indirect(
            "(module\n  (func $f\n    call_indirect (type 0)\n  )\n)")
    pipeline.assert_no_orphan_call_indirect(
        "(module\n  (table 1 funcref)\n  (func $f\n    call_indirect (type 0)\n  )\n)")
    pipeline.assert_no_orphan_call_indirect("(module\n  (table 1 funcref)\n)")


def test_stderr_is_captured_as_vera_run_captures_it(
    capsys: pytest.CaptureFixture[str],
) -> None:
    source = (
        "public fn main(@Unit -> @Unit)\n"
        "  requires(true)\n  ensures(true)\n  effects(<IO>)\n"
        "{\n  IO.stderr(\"note\")\n}\n")
    assert pipeline.run(source).stderr == "note"
    assert capsys.readouterr().err == ""
    assert pipeline.run(source, capture_stderr=False).stderr == ""
    assert capsys.readouterr().err == "note"
