"""Conformance test suite — spec-anchored feature validation.

Each test corresponds to a small .vera program in tests/conformance/ that
exercises one language feature.  The manifest (manifest.json) declares the
deepest pipeline stage each program must pass: parse, check, verify, or run.
A run-level entry also declares what the run prints and how it exits
(``expected_stdout`` and ``expected_exit``, or a reasoned
``nondeterministic_stdout``), and the run stage compares both; the rule lives
in scripts/conformance_golden.py, which scripts/check_conformance.py shares.

Every stage runs in process, through tests/pipeline.py: the check, the verify
and the negatives read the stage's result, and the run stage reads what
``vera run`` writes, as the bytes a process writes.  The programs
``CLI_SMOKE`` names also run through ``python -m vera.cli`` as a process,
which is held to the in-process CLI byte for byte.

This module is part of the full test suite and runs in CI alongside the
unit tests and example round-trip tests.
"""

from __future__ import annotations

import faulthandler
import importlib.util
import json
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path
from typing import Any, NamedTuple

import pytest

from tests import pipeline
from vera.errors import Diagnostic
from vera.formatter import format_source
from vera.parser import parse_file

# ---------------------------------------------------------------------------
# Load manifest
# ---------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parent.parent
CONFORMANCE_DIR = Path(__file__).parent / "conformance"
MANIFEST: list[dict] = json.loads(
    (CONFORMANCE_DIR / "manifest.json").read_text(encoding="utf-8")
)

_GOLDEN = ROOT / "scripts" / "conformance_golden.py"


def _load_golden() -> Any:
    """scripts/conformance_golden.py, the run-stage rule both harnesses use."""
    spec = importlib.util.spec_from_file_location("conformance_golden", _GOLDEN)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


golden = _load_golden()

_RECONCILIATION_GATE = ROOT / "scripts" / "check_reconciliation.py"


def _load_reconciliation_gate() -> Any:
    """scripts/check_reconciliation.py, whose `KNOWN` list names the one
    failure the verify stage may carry: an E541 the reconciliation reports
    today.  Registered in ``sys.modules`` under the key
    tests/test_reconciliation.py loads it by, so the two share one module."""
    key = "_reconciliation_gate"
    if key in sys.modules:
        return sys.modules[key]
    spec = importlib.util.spec_from_file_location(key, _RECONCILIATION_GATE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[key] = module
    spec.loader.exec_module(module)
    return module


reconciliation_gate = _load_reconciliation_gate()


def _sites(diagnostics: Sequence[Diagnostic]) -> list[tuple[str, str | None, int, int]]:
    """Each diagnostic as the gate's rule reads it: code, file, line, column."""
    return [(d.error_code, d.location.file, d.location.line, d.location.column)
            for d in diagnostics]

#: What the run environment removes (`conformance_golden.run_env`), as the
#: changes `pipeline.cli` makes for the length of one command.
_RUN_ENV: dict[str, str | None] = {name: None for name in golden.NEUTRALISED_ENV}

_LEVEL_ORDER = {"parse": 0, "check": 1, "verify": 2, "run": 3}


def _report(diagnostics: Sequence[Diagnostic]) -> str:
    """The diagnostics as the CLI prints them."""
    return "\n".join(d.format() for d in diagnostics)


def _at_least(entry: dict, level: str) -> bool:
    """Return True if the entry's declared level is >= *level*."""
    return _LEVEL_ORDER.get(entry["level"], 0) >= _LEVEL_ORDER[level]


# ---------------------------------------------------------------------------
# Parametrised conformance tests
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("entry", MANIFEST, ids=lambda e: e["id"])
class TestConformance:
    """Conformance suite — one class, one test per pipeline stage."""

    def test_parse(self, entry: dict) -> None:
        """Every conformance program must parse without errors."""
        path = str(CONFORMANCE_DIR / entry["file"])
        tree = parse_file(path)
        assert tree is not None

    def test_check(self, entry: dict) -> None:
        """Programs at level check/verify/run must type-check cleanly — or,
        for a negative entry (``expected_error``), must FAIL at the stage
        ``expected_error_stage`` names with that error code
        (ch08_circular_import → E011 at check).

        A COMPILE-stage negative also asserts that check is clean, because
        "the checker accepts it and codegen must refuse it" is exactly the
        property that class of diagnostic exists for — a negative that
        started failing at check would otherwise still pass."""
        if not _at_least(entry, "check"):
            pytest.skip("parse-only")
        path = CONFORMANCE_DIR / entry["file"]
        expected_error = entry.get("expected_error")
        if expected_error is not None:
            # A negative's positive obligation stops at check, so it is
            # declared at level "check" whichever stage it fails at; a
            # verify/run negative would otherwise silently skip its declared
            # stage.  Fail fast on a mislabel.
            assert entry["level"] == "check", (
                f"expected_error is only valid at level 'check'; "
                f"{entry['id']} is level {entry['level']!r}"
            )
            stage = entry.get("expected_error_stage", "check")
            assert stage in ("check", "compile"), (
                f"{entry['id']}: expected_error_stage must be 'check' or "
                f"'compile'; got {stage!r}"
            )
            if stage == "compile":
                pre = pipeline.check(path)
                assert pre.ok, (
                    f"{entry['id']} is a compile-stage negative, so it must "
                    f"type-check cleanly:\n{_report(pre.errors)}"
                )
            refused = pipeline.check(path) if stage == "check" else pipeline.compile(path)
            payload = refused.envelope()
            codes = [d.get("error_code")
                     for d in payload.get("diagnostics", [])]
            assert payload.get("ok") is False and expected_error in codes, (
                f"Expected {entry['id']} to fail {stage} with "
                f"{expected_error}; got ok={payload.get('ok')} "
                f"codes={codes}\n{json.dumps(payload, indent=2)}"
            )
            return
        checked = pipeline.check(path)
        assert checked.ok, (
            f"Type-check failed for {entry['id']}:\n{_report(checked.errors)}"
        )

    def test_verify(self, entry: dict) -> None:
        """Programs at level verify/run must verify contracts cleanly, as
        ``vera verify`` does by default: with the reconciliation join, so a
        runtime-check claim the compiled module does not answer fails the
        stage.  The one failure it may carry is an E541 at a site
        scripts/check_reconciliation.py's ``KNOWN`` names for the program,
        under its open issue; the gate and tests/test_reconciliation.py hold
        that list to what the join reports."""
        if not _at_least(entry, "verify"):
            pytest.skip(f"{entry['level']}-only")
        verified = pipeline.verify(CONFORMANCE_DIR / entry["file"], reconcile=True)
        unlisted = reconciliation_gate.unlisted_verify_errors(
            f"tests/conformance/{entry['file']}", _sites(verified.errors))
        assert verified.ran and not unlisted, (
            f"Verification failed for {entry['id']}:\n{_report(verified.errors)}"
        )

    def test_run(self, entry: dict) -> None:
        """Programs at level run must compile and execute, exiting with the
        entry's ``expected_exit`` and printing exactly its
        ``expected_stdout`` (or, under a ``nondeterministic_stdout`` reason,
        exiting as declared with the output left unpinned).  An exit status
        of 0 alone is not a pass: a program that prints the wrong value, or
        nothing, exits 0 too.  ``vera run`` runs in process, and the bytes it
        writes are compared as the bytes a process writes."""
        if not _at_least(entry, "run"):
            pytest.skip(f"{entry['level']}-only")
        problems = golden.entry_problems(entry)
        if problems:
            pytest.fail("\n".join(problems))
        ran = pipeline.cli("run", CONFORMANCE_DIR / entry["file"], env=_RUN_ENV,
                           budget_s=golden.RUN_TIMEOUT_SECONDS)
        outcome = golden.RunOutcome(
            exit=ran.returncode, stdout=ran.stdout_bytes, stderr=ran.stderr_bytes)
        mismatch = golden.run_mismatch(entry, outcome)
        if mismatch is not None:
            pytest.fail(mismatch)

    def test_format_idempotent(self, entry: dict) -> None:
        """Every conformance program must be in canonical format."""
        path = CONFORMANCE_DIR / entry["file"]
        source = path.read_text(encoding="utf-8")
        formatted = format_source(source)
        assert formatted == source, (
            f"Not in canonical format: {entry['id']}\n"
            f"Run: vera fmt --write {path}"
        )


# ---------------------------------------------------------------------------
# The stages run in process
# ---------------------------------------------------------------------------

#: One program of each shape a stage treats differently: a run whose imports
#: resolve from disk, a verify-level program with a module of contracts, a
#: negative the check refuses, and a negative code generation refuses behind a
#: clean check.
_STAGE_SHAPES = (
    "ch08_transitive_module_import",
    "ch07_cross_module_contracts",
    "ch08_circular_import",
    "ch08_module_prelude_adt_contention_rejected",
)

_ENTRIES = {entry["id"]: entry for entry in MANIFEST}


def _stages() -> list[str]:
    return [name for name, value in vars(TestConformance).items()
            if name.startswith("test_") and callable(value)]


def test_no_stage_starts_a_process(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every stage of every shape runs in process: a process the suite starts
    costs more than the stage it runs, and coverage does not see inside it."""

    def refuse(self: object, args: object, *rest: object, **kwargs: object) -> None:
        raise AssertionError(f"a conformance stage started a process: {args!r}")

    monkeypatch.setattr(subprocess.Popen, "__init__", refuse)
    for name in _STAGE_SHAPES:
        for stage in _stages():
            try:
                getattr(TestConformance(), stage)(_ENTRIES[name])
            except pytest.skip.Exception:
                continue


def test_the_run_stage_runs_under_its_budget(monkeypatch: pytest.MonkeyPatch) -> None:
    """In process there is no child to stop, so the run's budget is a
    watchdog that ends the worker, naming the test, rather than letting a
    program that never stops stall the job: armed for the run, disarmed
    after it."""
    calls: list[tuple[object, ...]] = []
    monkeypatch.setattr(
        faulthandler, "dump_traceback_later",
        lambda timeout, **kwargs: calls.append(("arm", timeout, kwargs.get("exit"))),
    )
    monkeypatch.setattr(
        faulthandler, "cancel_dump_traceback_later",
        lambda: calls.append(("disarm",)),
    )
    TestConformance().test_run(_ENTRIES["ch01_int_literals"])
    assert calls == [("arm", golden.RUN_TIMEOUT_SECONDS, True), ("disarm",)], calls


# ---------------------------------------------------------------------------
# The verify stage and the reconciliation gate's KNOWN list
# ---------------------------------------------------------------------------

#: The conformance program `vera verify` refuses by default, with the E541
#: the reconciliation gate lists under its open issue.
_KNOWN_E541 = next(entry for entry in reconciliation_gate.KNOWN
                   if entry.kind == "recorded_unguarded"
                   and entry.program.startswith("tests/conformance/"))


def _known_e541_site() -> tuple[str, str | None, int, int]:
    _name, line, column = _KNOWN_E541.site.rsplit(":", 2)
    return ("E541", str(ROOT / _KNOWN_E541.program), int(line), int(column))


def test_the_verify_stage_holds_the_known_e541_and_nothing_else() -> None:
    """The listed program fails `vera verify` with exactly its listed E541
    when the join runs, and verifies clean without it: the stage passes on
    the listed error and on nothing more."""
    path = ROOT / _KNOWN_E541.program
    joined = pipeline.verify(path, reconcile=True)
    errors = _sites(joined.errors)
    assert [code for code, *_ in errors] == ["E541"], errors
    assert reconciliation_gate.unlisted_verify_errors(
        _KNOWN_E541.program, errors) == []
    assert pipeline.verify(path).ok


@pytest.mark.parametrize("cell", ["another_site", "another_program", "another_code"])
def test_an_error_the_known_list_does_not_name_fails_the_verify_stage(
    cell: str,
) -> None:
    """The listed error's nearest neighbours each fail the stage: the same
    code one line on, the same site in another program, another code at the
    same site."""
    program = _KNOWN_E541.program
    code, file, line, column = _known_e541_site()
    if cell == "another_site":
        line += 1
    elif cell == "another_program":
        program = "tests/conformance/ch01_int_literals.vera"
        file = str(ROOT / program)
    else:
        code = "E500"
    error = (code, file, line, column)
    assert reconciliation_gate.unlisted_verify_errors(program, [error]) == [error]


# ---------------------------------------------------------------------------
# The CLI smoke: a few corpus programs through `python -m vera.cli`
# ---------------------------------------------------------------------------

#: The CLI smoke: the corpus programs that still cross the CLI as a process,
#: the commands each one is run through, and why it is here.  Every other test
#: drives the pipeline in process, through `tests/pipeline.py`; these hold
#: `python -m vera.cli`, started as a process, to the in-process CLI the
#: stages read, byte for byte.  Between them they run every command that takes
#: a program, and both of the exits the corpus has: success, and a refusal at
#: the check and at code generation.  No corpus program traps, exits through
#: `IO.exit`, fails to parse or reads its stdin; `CLI_EXIT_SHAPES` below holds
#: those exits, and the rest the corpus lacks, to the process with programs of
#: its own.
CLI_SMOKE: dict[str, tuple[tuple[tuple[str, ...], ...], str]] = {
    "tests/conformance/ch01_int_literals.vera": (
        (("run",), ("parse",), ("ast", "--json"), ("fmt", "--check")),
        "a returned value, which `vera run` prints itself; the parse tree, the "
        "typed AST and the formatter's verdict on one program",
    ),
    "tests/conformance/ch01_string_escapes.vera": (
        (("run",),),
        "`IO.print` through the live tee, with a tab, a backslash, a quote and "
        "a newline inside one write",
    ),
    "tests/conformance/ch07_unit_fn_nontail.vera": (
        (("run", "--json"),),
        "three lines of output packed into the run's JSON envelope, with no tee",
    ),
    "tests/conformance/ch04_arithmetic.vera": (
        (("compile", "--wat"),),
        "the module's text, which `vera compile --wat` prints",
    ),
    "tests/conformance/ch08_transitive_module_import.vera": (
        (("check",), ("verify",), ("run",)),
        "imports resolved from disk, two modules deep, at every stage",
    ),
    "tests/conformance/ch07_cross_module_contracts.vera": (
        (("verify", "--json"), ("test",)),
        "an imported module's contracts: the obligations of the JSON envelope, "
        "and contract testing's report",
    ),
    "tests/conformance/ch04_primitive_obligations.vera": (
        (("test", "--json"),),
        "contract testing's JSON envelope over several proved functions",
    ),
    "tests/conformance/ch08_circular_import.vera": (
        (("check",), ("check", "--json")),
        "the check's refusal (E011), exit status 1, as text and as JSON",
    ),
    "tests/conformance/ch08_module_prelude_adt_contention_rejected.vera": (
        (("check",), ("compile", "--json")),
        "the check's refusal (E158) of a module's declaration, exit status 1, "
        "from `check` and from `compile --json`",
    ),
    "examples/hello_world.vera": (
        (("run",),),
        "an example, run as its README says",
    ),
}

_SMOKE = [
    (program, command)
    for program, (commands, _why) in CLI_SMOKE.items()
    for command in commands
]


def _vera(*args: str, stdin: str = "") -> subprocess.CompletedProcess[bytes]:
    """``python -m vera.cli <args>`` as a process, from the repository root,
    so the compiler it imports is this checkout's; in the run environment,
    reading *stdin* through a pipe as a parent writes it in text mode
    (`pipeline.stdin_bytes`), and with its output kept as the bytes it
    wrote.  An empty *stdin* is a pipe with nothing in it, not the null
    device, which Windows reports as a terminal."""
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, input=pipeline.stdin_bytes(stdin),
        env=golden.run_env(), cwd=ROOT, timeout=golden.RUN_TIMEOUT_SECONDS,
        check=False,
    )


@pytest.mark.parametrize(
    ("program", "command"), _SMOKE,
    ids=[f"{Path(p).stem}:{'_'.join(c)}" for p, c in _SMOKE],
)
def test_the_cli_process_prints_what_the_stages_read(
    program: str, command: tuple[str, ...],
) -> None:
    """The process and the in-process CLI agree: the exit status, and every
    byte of both streams.  The stages read the in-process CLI, so this is what
    makes their verdicts the verdicts of the command a user runs."""
    path = str(ROOT / program)
    process = _vera(*command, path)
    mine = pipeline.cli(*command, path, env=_RUN_ENV)
    assert (process.returncode, process.stdout, process.stderr) == (
        mine.returncode, mine.stdout_bytes, mine.stderr_bytes)


class _ExitShape(NamedTuple):
    """A program with an exit the corpus has none of, and how it exits.

    A tuple rather than a dataclass: scripts/render_status.py loads this
    module outside `sys.modules`, where a dataclass cannot be built.
    """

    #: The program.
    source: str
    #: The commands it runs through.
    commands: tuple[tuple[str, ...], ...]
    #: The status every one of them exits with.
    exit: int
    #: Text every one of them writes, which only that exit writes.
    shows: str
    #: Why it is here.
    why: str
    #: What it reads on stdin.
    stdin: str = ""


_IO_MAIN = (
    "public fn main(@Unit -> @Unit)\n"
    "  requires(true)\n  ensures(true)\n  effects(<IO>)\n{\n")
_READ_CHAR = _IO_MAIN + (
    "  match IO.read_char(()) {\n"
    "    Ok(@String) -> IO.print(@String.0),\n"
    '    Err(@String) -> IO.print(string_concat("ERR:", @String.0))\n'
    "  }\n}\n")

#: The exits no corpus program has, each a program of its own, run through
#: `python -m vera.cli` by the smoke's driver and held to the in-process CLI
#: the same way: the exit status, and every byte of both streams.  Each cell
#: also asserts the exit it is named for, so a program that stopped reaching
#: it would fail here rather than smoke a different exit.  A module whose
#: every export code generation drops has no program the check accepts (the
#: Array-valued map it was spelled with is E135 at check, #1680), so its
#: exit is held in process, where the drop is injected
#: (`tests/test_dropped_entry_1183_1186.py`, `tests/test_pipeline.py`).
CLI_EXIT_SHAPES: dict[str, _ExitShape] = {
    "trap": _ExitShape(
        _IO_MAIN + '  IO.print("before → x");\n  IO.stderr("note é");\n'
        "  let @Int = 0;\n  let @Int = 10 / @Int.0;\n"
        '  IO.print("after")\n}\n',
        (("run",), ("run", "--json")), 1, "Integer division by zero",
        "a trap after a non-ASCII write to each stream: the output before "
        "it, the trap's message, its backtrace and its fix"),
    "exit-7": _ExitShape(
        _IO_MAIN + '  IO.print("bye");\n  IO.exit(7)\n}\n',
        (("run",), ("run", "--json")), 7, "bye",
        "`IO.exit(7)`: the status the program chose, in both modes"),
    "unparsed": _ExitShape(
        "public fn f(@Int -> @Int) {",
        (("check",), ("check", "--json"), ("verify",), ("run",)), 1, "E001",
        "a parse error, at each command that parses"),
    "verify-refusal": _ExitShape(
        "public fn f(@Int -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result > @Int.0)\n  effects(pure)\n{\n  @Int.0\n}\n",
        (("verify",), ("verify", "--json")), 1, "E500",
        "a postcondition the verifier refutes, with its counterexample"),
    "read-char-empty": _ExitShape(
        _READ_CHAR, (("run",),), 0, "ERR:EOF",
        "`IO.read_char` on an empty stdin, which asks stdin for its "
        "descriptor before it reads"),
    "read-char-line": _ExitShape(
        _READ_CHAR, (("run",),), 0, "ü",
        "`IO.read_char` on a one-line stdin, whose first character is not "
        "ASCII", stdin="ü-line\n"),
    "non-ascii-streams": _ExitShape(
        _IO_MAIN + '  IO.print("café → ✓");\n  IO.stderr("naïve — ✗")\n}\n',
        (("run",),), 0, "naïve — ✗",
        "a run that writes non-ASCII to stdout and to stderr, which reach "
        "the pipe as UTF-8 on every platform"),
    "internal-error": _ExitShape(
        "public fn f(@Nat -> @Tuple<Int, Int>)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n"
        "  let @Option<Tuple<Int, Int>> = Some(Tuple(@Nat.0, @Nat.0));\n"
        "  match @Option<Tuple<Int, Int>>.0 {\n"
        "    Some(@Tuple<Int, Int>) -> @Tuple<Int, Int>.0,\n"
        "    None -> Tuple(1, 1)\n  }\n}\n",
        (("verify",), ("verify", "--json")), 1, "E699",
        "an internal compiler error (E699), which #1594's program reaches; "
        "once #1594 is fixed this cell needs another program that does"),
}

_EXIT_CELLS = [
    (shape, command)
    for shape, spec in CLI_EXIT_SHAPES.items()
    for command in spec.commands
]


@pytest.mark.parametrize(
    ("shape", "command"), _EXIT_CELLS,
    ids=[f"{s}:{'_'.join(c)}" for s, c in _EXIT_CELLS],
)
def test_the_cli_process_exits_as_the_in_process_cli_does(
    shape: str, command: tuple[str, ...], tmp_path: Path,
) -> None:
    """The process and the in-process CLI agree on an exit the corpus does
    not have: the exit status, and every byte of both streams."""
    spec = CLI_EXIT_SHAPES[shape]
    path = tmp_path / f"{shape}.vera"
    path.write_text(spec.source, encoding="utf-8")
    process = _vera(*command, str(path), stdin=spec.stdin)
    mine = pipeline.cli(*command, path, stdin=spec.stdin, env=_RUN_ENV)
    assert (process.returncode, process.stdout, process.stderr) == (
        mine.returncode, mine.stdout_bytes, mine.stderr_bytes)
    assert mine.returncode == spec.exit and spec.shows in (
        mine.stdout + mine.stderr), (
        f"{shape} no longer exits as named: {mine.returncode}\n"
        f"{mine.stdout}{mine.stderr}")


def test_every_smoke_program_is_in_the_corpus() -> None:
    """A smoke program the corpus no longer holds would smoke nothing."""
    corpus = {f"tests/conformance/{e['file']}" for e in MANIFEST}
    for program in CLI_SMOKE:
        assert program in corpus or program.startswith("examples/"), program
        assert (ROOT / program).is_file(), program


# ---------------------------------------------------------------------------
# The run stage's expectations: the manifest declares them, the rule holds
# ---------------------------------------------------------------------------


def test_every_run_level_entry_declares_its_run() -> None:
    """Every run-level entry names its exit status and pins its stdout, or
    says why its stdout cannot be pinned, and no entry does both; no entry
    below the run level carries a run-stage key, which nothing would ever
    compare.  A new run-level program without them fails here, by name,
    rather than passing its run stage on exit status alone."""
    problems = golden.manifest_problems(MANIFEST)
    assert not problems, "\n".join(problems)


def _entry(level: str = "run", **keys: object) -> dict[str, object]:
    return {"id": "ch99_probe", "file": "ch99_probe.vera", "level": level, **keys}


class TestRunStageRule:
    """scripts/conformance_golden.py on plain data, without running a program.

    Each malformed shape names the key at fault, so a check that merely
    reported "something is wrong" would not pass these."""

    def test_a_pinned_output_and_exit_status_is_complete(self) -> None:
        assert golden.entry_problems(_entry(expected_stdout="42\n", expected_exit=0)) == []

    def test_a_reasoned_escape_with_an_exit_status_is_complete(self) -> None:
        entry = _entry(nondeterministic_stdout="prints the wall clock", expected_exit=0)
        assert golden.entry_problems(entry) == []

    def test_an_entry_below_the_run_level_needs_none_of_them(self) -> None:
        assert golden.entry_problems(_entry("check")) == []

    @pytest.mark.parametrize(
        ("keys", "named"),
        [
            ({"expected_exit": 0}, "expected_stdout"),
            ({"expected_stdout": "42\n"}, "expected_exit"),
            (
                {"expected_stdout": "42\n", "nondeterministic_stdout": "clock",
                 "expected_exit": 0},
                "both",
            ),
            ({"nondeterministic_stdout": True, "expected_exit": 0}, "nondeterministic_stdout"),
            ({"nondeterministic_stdout": "", "expected_exit": 0}, "nondeterministic_stdout"),
            ({"nondeterministic_stdout": "  ", "expected_exit": 0}, "nondeterministic_stdout"),
            ({"expected_stdout": 42, "expected_exit": 0}, "expected_stdout"),
            ({"expected_stdout": "42\n", "expected_exit": True}, "expected_exit"),
            ({"expected_stdout": "42\n", "expected_exit": "0"}, "expected_exit"),
        ],
        ids=[
            "no-stdout-no-reason", "no-exit", "both-pinned-and-escaped",
            "bare-flag", "empty-reason", "blank-reason", "stdout-not-text",
            "exit-a-bool", "exit-a-string",
        ],
    )
    def test_a_malformed_run_entry_names_its_fault(
        self, keys: dict[str, object], named: str,
    ) -> None:
        problems = golden.entry_problems(_entry("run", **keys))
        assert problems, keys
        assert any(named in p for p in problems), problems

    @pytest.mark.parametrize("level", ["parse", "check", "verify"])
    @pytest.mark.parametrize(
        "key", ["expected_stdout", "expected_exit", "nondeterministic_stdout"],
    )
    def test_a_run_stage_key_below_the_run_level_is_a_problem(
        self, level: str, key: str,
    ) -> None:
        value: object = 0 if key == "expected_exit" else "42\n"
        problems = golden.entry_problems(_entry(level, **{key: value}))
        assert len(problems) == 1 and key in problems[0], problems

    def test_the_manifest_reports_every_entry_at_fault(self) -> None:
        manifest = [
            _entry(expected_stdout="1\n", expected_exit=0),
            {**_entry(expected_exit=0), "id": "ch99_a"},
            {**_entry("verify", expected_stdout="2\n"), "id": "ch99_b"},
        ]
        problems = golden.manifest_problems(manifest)
        assert [p.split(":")[0] for p in problems] == ["ch99_a", "ch99_b"]


class TestRunComparison:
    """How one run is judged against its entry: on bytes, exit status first."""

    PINNED = _entry(expected_stdout="42\n", expected_exit=0)

    @staticmethod
    def _outcome(stdout: bytes, exit: int | None = 0, stderr: bytes = b"") -> Any:
        return golden.RunOutcome(exit=exit, stdout=stdout, stderr=stderr)

    def test_the_declared_run_matches(self) -> None:
        assert golden.run_mismatch(self.PINNED, self._outcome(b"42\n"), linesep="\n") is None

    def test_a_wrong_value_reports_the_program_and_both_outputs_in_full(self) -> None:
        mismatch = golden.run_mismatch(
            self.PINNED, self._outcome(b"41\n", stderr=b"a note\n"), linesep="\n",
        )
        assert mismatch is not None
        assert mismatch.startswith("ch99_probe: ")
        assert repr("42\n") in mismatch and repr("41\n") in mismatch
        assert "a note" in mismatch

    def test_printing_nothing_is_a_mismatch(self) -> None:
        assert golden.run_mismatch(self.PINNED, self._outcome(b""), linesep="\n") is not None

    def test_a_long_output_is_shown_whole(self) -> None:
        long = "x" * 5000 + "\n"
        entry = _entry(expected_stdout=long, expected_exit=0)
        mismatch = golden.run_mismatch(entry, self._outcome(b"y\n"), linesep="\n")
        assert mismatch is not None and repr(long) in mismatch

    def test_a_different_exit_status_is_a_mismatch(self) -> None:
        mismatch = golden.run_mismatch(self.PINNED, self._outcome(b"42\n", exit=3), linesep="\n")
        assert mismatch is not None
        assert "expected 0" in mismatch and "got 3" in mismatch

    def test_a_carriage_return_is_not_a_newline(self) -> None:
        """A text-mode capture translates newlines on every platform, so
        ``a\\rb`` would compare equal to ``a\\nb``; the comparison is on the
        bytes, where it does not."""
        entry = _entry(expected_stdout="a\nb\n", expected_exit=0)
        assert golden.run_mismatch(entry, self._outcome(b"a\rb\n"), linesep="\n") is not None
        assert golden.run_mismatch(entry, self._outcome(b"a\r\nb\n"), linesep="\n") is not None

    def test_each_newline_reaches_a_windows_pipe_as_crlf(self) -> None:
        """The CLI prints through a text-mode stdout, which writes the line
        separator for each newline: the same entry holds on both platforms,
        exactly."""
        entry = _entry(expected_stdout="a\r\nb\n", expected_exit=0)
        assert golden.run_mismatch(entry, self._outcome(b"a\r\r\nb\r\n"), linesep="\r\n") is None
        assert golden.run_mismatch(entry, self._outcome(b"a\r\nb\r\n"), linesep="\r\n") is not None
        assert golden.run_mismatch(entry, self._outcome(b"a\r\r\nb\r\n"), linesep="\n") is not None

    def test_a_run_that_did_not_exit_is_a_mismatch_whatever_it_declares(self) -> None:
        """A stopped run has no exit status, so no declared one can match it:
        not a pinned entry's, and not an escaped one's either, whose exit
        status is still compared.  A sentinel integer could collide with a
        declared status; ``None`` cannot."""
        escaped = _entry(nondeterministic_stdout="prints the wall clock", expected_exit=0)
        for entry in (self.PINNED, escaped):
            mismatch = golden.run_mismatch(entry, self._outcome(b"42\n", exit=None), linesep="\n")
            assert mismatch is not None and "did not exit" in mismatch, mismatch

    def test_a_run_past_its_budget_is_stopped_and_has_no_exit_status(self) -> None:
        """A budget no ``vera run`` can meet: the process is stopped, and the
        outcome says it did not exit rather than inventing a status."""
        outcome = golden.run_program(CONFORMANCE_DIR / "ch01_int_literals.vera", timeout=0.01)
        assert outcome.exit is None, outcome

    def test_an_unpinned_output_still_has_its_exit_status_compared(self) -> None:
        entry = _entry(nondeterministic_stdout="prints the wall clock", expected_exit=0)
        assert golden.run_mismatch(entry, self._outcome(b"1791580123501\n"), linesep="\n") is None
        assert golden.run_mismatch(entry, self._outcome(b"", exit=1), linesep="\n") is not None

    def test_the_run_environment_drops_what_changes_a_program_and_keeps_eager_gc(self) -> None:
        """The eager-GC lane sets VERA_EAGER_GC for this very comparison, so
        the variable must reach the program; a database URL must not, or a
        developer's shell would decide what ch09_db prints."""
        env = golden.run_env({
            "VERA_EAGER_GC": "1", "VERA_DB_URL": "sqlite:///elsewhere.db", "PATH": "/bin",
        })
        assert env == {"VERA_EAGER_GC": "1", "PATH": "/bin"}
