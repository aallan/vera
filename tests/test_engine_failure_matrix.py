"""The class instrument for what stops a mutation run (scripts/mutate_diff.py).

When mutmut's stats pass or its clean run stops on a failure, the lane reads
the pass's log.  ``engine_failure`` names an exception the engine's own code
raised, and ``run_dropping`` then stops at that attempt and drops no test;
any other failure is the test's, which ``run_dropping`` drops before it runs
again.  This file generates that log from the real logs' templates in
``tests/test_mutate_diff.py`` (pytest 9.2.0's reports, drawn 80 columns
wide, the width both lanes hand the engine) over the four things the rule
reads:

- the report: a test failing in its own body, an error at setup, an error
  at teardown, and pytest's internal error (a hook raising outside a test's
  phases, every line prefixed ``INTERNALERROR> ``);
- the deciding frame, the first going outward from the innermost past the
  standard library's: the engine's (the installed ``mutmut`` package), the
  copy's (``mutants/``), a third party's, and the standard library's under
  the engine's or under the copy's;
- the exception: an ordinary one; a ``RecursionError`` printed in full, a
  recursion through the code under test and the engine's trampoline
  (``RECURSION_LOG``); and a ``RecursionError`` compressed, a function
  recursing on itself, printed three times and then ``[Previous line
  repeated 960 more times]`` (``SELF_RECURSION_LOG``,
  ``ENGINE_RECURSION_LOG``);
- where captured output lies: none; a captured section before the report,
  an earlier report's, holding a traceback of the engine's frame
  (``LONG_NAME_LOG``'s setup error and its ``Captured log setup``); the
  traceback inside the report's captured section, printed by a test that
  then fails in its own body (``CAPTURED_LOG``); the same behind banners the
  test printed shorter than pytest's rule (``BANNER_LOG``); and the same
  behind a banner 80 wide with one fill character at both ends.

The test's name is 73 characters long, as vera's sentence-named tests are,
so pytest draws each report's rule with one or two fill characters either
side of its title (``LONG_NAME_LOG``).

Each cell asserts the verdict MUTATION.md § CI: the diff lane, The oracle,
states, and nothing else: the engine's (one attempt, no test dropped, the
exception and the engine's frame named) or the test's (the test dropped,
and the run goes again; an internal error names no test, so the run stops
there, as at base).

Two products are not cells, since pytest prints neither log (pytest 9.2.0,
measured): an internal error with captured output in any placement, because
pytest ends the session at the internal error and prints no report and no
captured section after it; and a captured section before a setup error's
report, because the engine runs pytest with ``-x``, so a test's setup error
is the first report its pass prints.  The cells of the night and of each
probe stay in ``tests/test_mutate_diff.py`` and ``tests/test_mutate_sweep.py``
as the incident pins.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

import pytest

from tests.test_mutate_diff import BANNER_LOG, CAPTURED_LOG, LONG_NAME_LOG, NIGHT_LOG, md

pytestmark = pytest.mark.matrix(decides=["scripts/mutate_diff.py"])

#: The terminal width both lanes hand the engine (``COLUMNS``).
WIDTH = 80
NAME = "test_a_name_vera_writes_as_a_sentence_a_name_vera_writes_as_a_sentence_a_"
TEST = f"tests/test_m.py::{NAME}"
VENV = "/venv/lib/python3.12/site-packages"
COPY = "/work/tree/mutants"
STDLIB = "/python/lib/python3.12"
ORDINARY = "LookupError: the generated log's own exception"
RECURSION = "RecursionError: maximum recursion depth exceeded"

REPORTS = ["failed", "setup", "teardown"]
PARTIES = ["engine", "copy", "third", "stdlib-engine", "stdlib-copy"]
EXCEPTIONS = ["ordinary", "recursion-full", "recursion-compressed"]
PLACEMENTS = ["none", "inside", "short-banner", "full-banner"]


def _rule(fill: str, title: str) -> str:
    """A rule as pytest's ``TerminalWriter.sep`` draws it, WIDTH wide or, for
    a long title, one fill character either side of it."""
    half = max((WIDTH - len(title) - 2) // 2, 1)
    line = f"{fill * half} {title} {fill * half}"
    return line + fill if len(line) < WIDTH else line


def _frame(file: str, line: int, func: str, code: str | None = None) -> list[str]:
    return [f'  File "{file}", line {line}, in {func}', *([f"    {code}"] if code else [])]


# The frames, as the templates print them.
FROM_CALL = _frame(f"{VENV}/_pytest/runner.py", 361, "from_call", "result: TResult | None = func()")
WRAP_SESSION = _frame(f"{VENV}/_pytest/main.py", 333, "wrap_session",
                      "session.exitstatus = doit(config, session) or 0")
WRAPPER = _frame(f"{VENV}/mutmut/mutation/trampoline.py", 172, "_trampoline_wrapper",
                 "return trampoline(*args, **kwargs)")
CALLS_ORIGINAL = _frame(f"{VENV}/mutmut/mutation/trampoline.py", 100, "trampoline",
                        "return orig_func(*call_args, **kwargs)")
RECORDS_HIT = _frame(f"{VENV}/mutmut/mutation/trampoline.py", 97, "trampoline",
                     "record_trampoline_hit(orig_qual_name, caller=caller_name)")
STATS = _frame(f"{VENV}/mutmut/stats.py", 163, "record_trampoline_hit",
               "file_path = Path(filename).resolve(strict=True)")
ASKS_MUTANT = _frame(f"{VENV}/mutmut/mutation/trampoline.py", 85, "trampoline",
                     "mutant_under_test = get_mutant_under_test()")
GETS_MUTANT = _frame(f"{VENV}/mutmut/mutation/trampoline.py", 54, "get_mutant_under_test",
                     'if "MUTANT_UNDER_TEST" in os.environ:')
ENGINE_WALK = _frame(f"{VENV}/mutmut/rec.py", 2, "walk", "return walk(n + 1)")
CODE = _frame(f"{COPY}/vera/m.py", 9, "x_f__mutmut_orig", "return x + 1")
CODE_CALLS_WALK = _frame(f"{COPY}/vera/m.py", 5, "f", "return walk(0)")
DEEP = _frame(f"{COPY}/vera/m.py", 9, "x_deep__mutmut_orig", "return 0 if n == 0 else deep(n - 1) + 1")
COPY_WALK = _frame(f"{COPY}/tests/helpers.py", 4, "walk", "return walk(n + 1)")
THIRD = _frame(f"{VENV}/foo/core.py", 41, "load", "return _parse(data)")
THIRD_WALK = _frame(f"{VENV}/foo/tree.py", 7, "walk", "return walk(node.parent)")
THIRD_HOOK = _frame(f"{VENV}/foo/plugin.py", 8, "pytest_runtest_makereport", "return load(item)")
STDLIB_RAISES = [*_frame(f"{STDLIB}/pathlib.py", 1240, "resolve",
                         "s = self._flavour.realpath(self, strict=strict)"),
                 *_frame("<frozen posixpath>", 427, "realpath")]
FROZEN_OS = _frame("<frozen os>", 714, "__getitem__")
REPEATED = ["  [Previous line repeated 960 more times]"]

#: The copy's frame each report's code runs under: the test's body, a
#: fixture at setup or after its ``yield``, a hook of the copy's conftest.
CONTEXT = {
    "failed": _frame(f"{COPY}/tests/test_m.py", 21, NAME, "assert f(1) == 2"),
    "setup": _frame(f"{COPY}/tests/test_m.py", 12, "fixture", "f(1)"),
    "teardown": _frame(f"{COPY}/tests/test_m.py", 14, "fixture", "f(1)"),
    "internal": _frame(f"{COPY}/tests/conftest.py", 3, "pytest_runtest_makereport", "f(1)"),
}
#: The engine's own hook pytest calls at each phase (the night's is the
#: teardown's, ``mutmut/runners/harness.py:157``).
HOOK = {"setup": ("pytest_runtest_setup", 150), "teardown": ("pytest_runtest_teardown", 157),
        "internal": ("pytest_runtest_makereport", 140)}


def _hook(report: str, code: str) -> list[str]:
    func, line = HOOK[report]
    return _frame(f"{VENV}/mutmut/runners/harness.py", line, func, code)


def _frames(report: str, party: str, exception: str, *, printed: bool) -> list[str]:
    """The cell's traceback's frames, outermost first: the report's own (its
    phase run by pytest), or one a test printed (from its own frame in)."""
    outer = [] if printed else WRAP_SESSION if report == "internal" else FROM_CALL
    context = CONTEXT[report]
    owner = party.removeprefix("stdlib-")
    # pytest calls the engine's code itself at a phase, or a test calls it.
    hooked = report != "failed" and not printed
    if exception == "recursion-full":
        leaf = {"engine": WRAPPER + ASKS_MUTANT + GETS_MUTANT, "copy": [], "third": THIRD}[owner]
        tail = {"stdlib-engine": FROZEN_OS, "stdlib-copy": STDLIB_RAISES}.get(party, [])
        return outer + context + (WRAPPER + CALLS_ORIGINAL + DEEP) * 4 + leaf + tail
    if exception == "recursion-compressed":
        walk = {"engine": ENGINE_WALK, "copy": COPY_WALK, "third": THIRD_WALK}[owner] * 3 + REPEATED
        if owner == "engine":
            calls = _hook(report, "walk(0)") if hooked else context + CODE_CALLS_WALK
        elif owner == "third" and report == "internal" and not printed:
            calls = THIRD_HOOK
        else:
            calls = context
        return outer + calls + walk + (FROZEN_OS if party.startswith("stdlib") else [])
    if owner == "engine":
        raises = _hook(report, "state().record(item._nodeid)") if hooked else (
            context + WRAPPER + RECORDS_HIT + STATS)
    elif owner == "copy":
        raises = context + WRAPPER + CALLS_ORIGINAL + CODE
    else:
        raises = THIRD_HOOK + THIRD if report == "internal" and not printed else context + THIRD
    return outer + raises + (STDLIB_RAISES if party.startswith("stdlib") else [])


def _traceback(report: str, party: str, exception: str, *, printed: bool) -> list[str]:
    return ["Traceback (most recent call last):", *_frames(report, party, exception, printed=printed),
            ORDINARY if exception == "ordinary" else RECURSION]


#: The report's own failure when the cell's traceback is captured output:
#: the test's assertion, or its fixture raising at setup or at teardown.
OWN_FAILURE = {
    "failed": [*_frame(f"{COPY}/tests/test_m.py", 23, NAME, "assert g(3) == 7"),
               "AssertionError: assert 6 == 7", " +  where 6 = g(3)"],
    "setup": [*_frame(f"{COPY}/tests/test_m.py", 12, "fixture", "raise RuntimeError('the fixture cannot start')"),
              "RuntimeError: the fixture cannot start"],
    "teardown": [*_frame(f"{COPY}/tests/test_m.py", 14, "fixture", "raise RuntimeError('the fixture cannot stop')"),
                 "RuntimeError: the fixture cannot stop"],
}
PHASE = {"failed": "call", "setup": "setup", "teardown": "teardown"}
PROGRESS = {"failed": ".F", "setup": "E", "teardown": ".E"}
TITLE = {"failed": NAME, "setup": f"ERROR at setup of {NAME}", "teardown": f"ERROR at teardown of {NAME}"}
SUMMARY = {"failed": f"FAILED {TEST}", "setup": f"ERROR {TEST}", "teardown": f"ERROR {TEST}"}
SHORT_BANNERS = ["=============== the program's own banner ===============", "--- a heading the program printed ---"]
FULL_BANNER = _rule("=", "the program's own banner")


def _own(report: str) -> list[str]:
    return ["Traceback (most recent call last):", *FROM_CALL, *OWN_FAILURE[report]]


def _decoy(report: str) -> list[str]:
    """A traceback of the engine's frame a test printed: a call with one
    argument too many raising in the trampoline (``CAPTURED_LOG``)."""
    return ["Traceback (most recent call last):", *CONTEXT[report], *WRAPPER, *CALLS_ORIGINAL,
            "TypeError: x_f__mutmut_orig() takes 1 positional argument but 2 were given"]


def _log(report: str, party: str, exception: str, placement: str) -> str:
    """The log of the stopped pass, as mutmut prints it."""
    done = ["    done in 24ms (2 files mutated, 0 ignored, 0 unmodified)", ""]
    if report == "internal":
        rows = _traceback(report, party, exception, printed=False)
        return "\n".join([*done, *(f"INTERNALERROR> {row}" for row in rows), "", "no tests ran in 0.01s",
                          "failed to collect stats. runner returned 3", ""])
    summary = [SUMMARY[report]]
    if placement == "before":
        # An earlier report of the same test, its captured output holding a
        # traceback of the engine's frame: a call failure's teardown error,
        # in the ERRORS section pytest prints first, or the setup error
        # before a teardown error.
        earlier = "teardown" if report == "failed" else "setup"
        body = [_rule("=", "ERRORS"), _rule("_", TITLE[earlier]), *_own(earlier),
                _rule("-", f"Captured stderr {PHASE[earlier]}"), *_decoy(earlier),
                *([_rule("=", "FAILURES")] if report == "failed" else []),
                _rule("_", TITLE[report]), *_traceback(report, party, exception, printed=False)]
        summary.append(SUMMARY[earlier])
    else:
        body = [_rule("=", "FAILURES" if report == "failed" else "ERRORS"), _rule("_", TITLE[report])]
        if placement == "none":
            body += _traceback(report, party, exception, printed=False)
        else:
            body += [*_own(report), _rule("-", f"Captured stderr {PHASE[report]}"),
                     *{"inside": [], "short-banner": SHORT_BANNERS, "full-banner": [FULL_BANNER]}[placement],
                     *_traceback(report, party, exception, printed=True)]
    return "\n".join([*done, PROGRESS[report], *body, _rule("=", "short test summary info"),
                      *summary, "!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!",
                      "1 failed in 0.01s", "failed to collect stats. runner returned 1", ""])


def _verdict(report: str, party: str, exception: str, placement: str) -> tuple[int, list[str], str | None]:
    """The rule's verdict, read off the cell's coordinates alone: the
    attempts, the tests dropped, the exception named."""
    # A test's captured output is no report and is not read, up to the next
    # of pytest's rules, which a banner 79 wide or more is.
    read = placement in ("none", "before", "full-banner")
    # Outward from the innermost frame past the standard library's, the
    # first frame decides.
    engine = party in ("engine", "stdlib-engine")
    # A RecursionError is the engine's only when none of its ten innermost
    # frames is the copy's: a recursion through the code under test is the
    # test's wherever it ran out of stack.
    through_the_copy = exception == "recursion-full"
    if read and engine and not through_the_copy:
        if exception == "recursion-compressed":
            return 1, [], f"{RECURSION} (mutmut/rec.py:2)"
        printed = placement == "full-banner"
        where = ("mutmut/stats.py:163" if printed or report == "failed"
                 else f"mutmut/runners/harness.py:{HOOK[report][1]}")
        return 1, [], f"{ORDINARY} ({where})"
    if report == "internal":
        return 1, [], None  # no report names a test to drop
    return 2, [TEST], None


def _run(log: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[int, list[str], str | None]:
    """``run_dropping`` against an engine that prints the cell's log until
    its test is deselected, and then passes."""
    attempts = 0

    def run_engine(cmd: Any, *, cwd: Path, budget_s: float, log_path: Path, env: Any = None,
                   grace_s: Any = None) -> Any:
        nonlocal attempts
        attempts += 1
        deselected = f"--deselect={TEST}" in (cwd / "pyproject.toml").read_text(encoding="utf-8")
        log_path.write_text("" if deselected else log, encoding="utf-8")
        return md.EngineRun(0 if deselected else 1, None, 0.1)

    monkeypatch.setattr(md, "run_engine", run_engine)
    run, _, dropped = md.run_dropping(
        ["mutmut", "run"], tree=tmp_path, pyproject=tmp_path / "pyproject.toml",
        config_for=lambda dropped: "".join(f"--deselect={test}\n" for test in dropped),
        budget_s=100.0, workdir=tmp_path, env={})
    return attempts, dropped, run.error


def test_the_generator_draws_pytests_rules() -> None:
    """The premise of every cell: the rules the logs are drawn with are the
    ones the real logs hold, short titles and long."""
    for template, rules in (
        (NIGHT_LOG, [_rule("=", "ERRORS"), _rule("_", "ERROR at teardown of test_f"),
                     _rule("=", "short test summary info")]),
        (CAPTURED_LOG, [_rule("=", "FAILURES"), _rule("_", "test_g"), _rule("-", "Captured stderr call")]),
        (LONG_NAME_LOG, [_rule("_", TITLE["setup"]), _rule("_", TITLE["teardown"]),
                         _rule("-", "Captured log setup")]),
        (BANNER_LOG, SHORT_BANNERS),
    ):
        for rule in rules:
            assert rule in template.splitlines(), rule
    assert len(FULL_BANNER) == WIDTH and len(max(SHORT_BANNERS, key=len)) < md._RULE_WIDTH


@pytest.mark.parametrize("placement", PLACEMENTS)
@pytest.mark.parametrize("exception", EXCEPTIONS)
@pytest.mark.parametrize("party", PARTIES)
@pytest.mark.parametrize("report", REPORTS)
def test_a_report_is_the_engines_or_the_tests(
    report: str, party: str, exception: str, placement: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    log = _log(report, party, exception, placement)
    assert _run(log, tmp_path, monkeypatch) == _verdict(report, party, exception, placement), log


@pytest.mark.parametrize("exception", EXCEPTIONS)
@pytest.mark.parametrize("party", PARTIES)
@pytest.mark.parametrize("report", ["failed", "teardown"])
def test_a_captured_section_before_the_report_ends_at_its_rule(
    report: str, party: str, exception: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    log = _log(report, party, exception, "before")
    assert _run(log, tmp_path, monkeypatch) == _verdict(report, party, exception, "before"), log


@pytest.mark.parametrize("exception", EXCEPTIONS)
@pytest.mark.parametrize("party", PARTIES)
def test_an_internal_error_is_the_engines_or_stops_the_run(
    party: str, exception: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    log = _log("internal", party, exception, "none")
    assert _run(log, tmp_path, monkeypatch) == _verdict("internal", party, exception, "none"), log
