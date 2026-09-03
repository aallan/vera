"""Tests for scripts/check_corpus_differential.py — the burndown
instrument that compiles the corpus at two revisions and reports which
programs moved.

The differential itself is far too slow to run from a test: it compiles
every corpus program twice, once per revision, in its own subprocess.
What is tested here is everything *around* those two compiles — the
corpus enumeration, the four-way mover classification, the comparison
and its counts, the report, the exit code, and the ``--json`` shape —
with every compile result injected.

Injection is not only a speed measure.  The one-sided-failure cases
(``compiles only at HEAD`` / ``compiles only at <base>``) need a
revision pair where a program's compilability *changed*, and the shipped
corpus deliberately has no such pair: at any two revisions CI has passed
on, the same programs compile.  Those two cases are exactly the class
the PR #1323 record called out as mis-described, so they are reachable
on demand here rather than left to a lucky revision.

Two conventions are inherited from ``tests/test_check_examples_run.py``
and asserted throughout: an enumeration that matches nothing must be an
ERROR rather than a silent pass (otherwise a moved corpus root switches
the instrument off while it still reports success), and each check is
exercised in both directions — a classification that can only ever
answer "identical" would otherwise report a green differential over a
compiler that moved under it.
"""

from __future__ import annotations

import argparse
import importlib.util
import io
import json
import os
import subprocess
import threading
from pathlib import Path, PureWindowsPath
from typing import Any
from unittest import mock

import pytest

_SCRIPT = (
    Path(__file__).parent.parent / "scripts" / "check_corpus_differential.py"
)
_ROOT = Path(__file__).parent.parent


def _load() -> Any:
    spec = importlib.util.spec_from_file_location(
        "check_corpus_differential", _SCRIPT
    )
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_MOD = _load()


# ---------------------------------------------------------------------------
# Injected compile results
# ---------------------------------------------------------------------------


def _ok(digest: str, size: int = 512) -> Any:
    """A program that compiled, with the given WAT digest."""
    return _MOD.Artifact(ok=True, digest=digest, size=size, error="")


def _failed(error: str = "[E101] type mismatch") -> Any:
    """A program that did not compile, with the reason the CLI gave."""
    return _MOD.Artifact(ok=False, digest=None, size=0, error=error)


def _info() -> Any:
    return _MOD.RunInfo(
        base_ref="origin/main",
        base_sha="0123456789abcdef",
        base_root="/scratch/vera-base-0123456789ab",
        head_root="/repo",
    )


# ---------------------------------------------------------------------------
# Corpus enumeration
# ---------------------------------------------------------------------------


class TestCorpusEnumeration:
    """What gets compiled, and the refusal to compile nothing."""

    def test_the_real_corpus_spans_both_roots_and_recurses(self) -> None:
        """The corpus is `examples/` plus `tests/conformance/`, at any
        depth.  The nested `examples/vera/` and `tests/conformance/vera/`
        modules are corpus too — `examples/modules.vera` is built from
        them, so a non-recursive glob would compare a program whose
        inputs the differential never looked at (the same gap
        `scripts/check_corpus_canonical.py` records having had)."""
        files = _MOD.corpus_files(_ROOT)
        rel = {p.relative_to(_ROOT).as_posix() for p in files}

        assert len(rel) > 100
        assert any(r.startswith("examples/") for r in rel)
        assert any(r.startswith("tests/conformance/") for r in rel)
        assert "examples/vera/math.vera" in rel
        assert "tests/conformance/vera/util.vera" in rel

    def test_an_empty_corpus_is_an_error_not_a_skip(self) -> None:
        """A differential over zero programs finds zero movers and would
        report that as success.  The enumeration matching nothing must
        fail the run instead."""
        message = _MOD.corpus_guard([], Path("/nowhere"))
        assert message is not None
        assert "could not find" in message

    def test_a_populated_corpus_passes_the_guard(self) -> None:
        """The other direction: the guard must not fail every run."""
        assert _MOD.corpus_guard([Path("/repo/examples/a.vera")],
                                 Path("/repo")) is None


# ---------------------------------------------------------------------------
# Mover classification — the four cases
# ---------------------------------------------------------------------------


class TestMoverClassification:
    """One program, two revisions, four outcomes.

    Both directions of the failure axis are separate cells, and named
    separately: a classifier that lumps them together reports a program
    that *stopped* compiling as one that *started*, which is the
    mis-description the PR #1323 record names.
    """

    def test_identical_wat_is_not_a_mover(self) -> None:
        assert _MOD.classify(_ok("abc"), _ok("abc"), "origin/main") is None

    def test_differing_wat_is_a_mover(self) -> None:
        verdict = _MOD.classify(_ok("abc"), _ok("def"), "origin/main")
        assert verdict is not None
        kind, reason = verdict
        assert kind == "wat-differs"
        assert "WAT differs" in reason

    def test_compiling_only_at_head_is_a_mover(self) -> None:
        """Base failed, HEAD succeeded — the working tree made a program
        compilable, which is a move even though no WAT can be compared."""
        verdict = _MOD.classify(_failed("[E101] boom"), _ok("abc"),
                                "origin/main")
        assert verdict is not None
        kind, reason = verdict
        assert kind == "head-only"
        assert "compiles only at HEAD" in reason
        assert "[E101] boom" in reason

    def test_compiling_only_at_base_is_a_mover(self) -> None:
        """The reverse direction, and the one that matters most: the
        working tree BROKE a program that used to compile.  The reason
        must name the base revision, not HEAD."""
        verdict = _MOD.classify(_ok("abc"), _failed("[E620] dropped"),
                                "origin/main")
        assert verdict is not None
        kind, reason = verdict
        assert kind == "base-only"
        assert "compiles only at origin/main" in reason
        assert "[E620] dropped" in reason

    def test_failing_at_both_revisions_is_not_a_mover(self) -> None:
        """The negative conformance fixtures live here: they fail to
        compile at every revision, so they are not movers.  They are
        counted separately rather than folded into `identical`, because
        a run whose corpus was entirely uncompilable would otherwise
        report a wall of agreement it never measured."""
        assert _MOD.classify(_failed(), _failed("other"),
                             "origin/main") is None


# ---------------------------------------------------------------------------
# The comparison
# ---------------------------------------------------------------------------


class TestComparison:
    """The per-program verdicts, rolled up."""

    def _mixed(self) -> Any:
        base = {
            "a.vera": _ok("same"),
            "b.vera": _ok("same"),
            "c.vera": _ok("old"),
            "d.vera": _failed("[E101] base"),
            "e.vera": _ok("gone"),
            "f.vera": _failed("[E101] base"),
        }
        head = {
            "a.vera": _ok("same"),
            "b.vera": _ok("same"),
            "c.vera": _ok("new"),
            "d.vera": _ok("added"),
            "e.vera": _failed("[E101] head"),
            "f.vera": _failed("[E101] head"),
        }
        return _MOD.compare(base, head, "origin/main")

    def test_counts_partition_the_corpus(self) -> None:
        c = self._mixed()
        assert c.compared == 6
        assert c.identical == 2
        assert c.both_failed == 1
        assert len(c.movers) == 3
        assert c.compared == c.identical + c.both_failed + len(c.movers)

    def test_each_mover_keeps_its_own_kind(self) -> None:
        """By position, not by count: three movers of three different
        kinds are exactly the case a classifier that mislabels one of
        them still gets the count right on."""
        c = self._mixed()
        assert {m.path: m.kind for m in c.movers} == {
            "c.vera": "wat-differs",
            "d.vera": "head-only",
            "e.vera": "base-only",
        }

    def test_movers_are_reported_in_path_order(self) -> None:
        c = self._mixed()
        assert [m.path for m in c.movers] == sorted(m.path for m in c.movers)

    def test_a_program_missing_from_one_side_is_reported_not_ignored(
        self,
    ) -> None:
        """A program the base side never reported on cannot be compared.
        Dropping it silently would shrink the corpus mid-run and still
        print a clean verdict; it is surfaced instead, and it is not
        counted as agreement."""
        c = _MOD.compare(
            {"a.vera": _ok("same")},
            {"a.vera": _ok("same"), "b.vera": _ok("x")},
            "origin/main",
        )
        assert c.unreported == ["b.vera"]
        assert c.identical == 1
        assert c.compared == 1

    def test_a_program_the_head_side_never_reported_is_unreported_too(
        self,
    ) -> None:
        """The mirror direction (#1330 review).

        `unreported` is a symmetric difference, so both directions are
        one expression — but only the base-missing one was exercised,
        and an implementation that iterated the head map alone would
        pass every other cell in this class while under-reporting the
        corpus.  This is the direction that hides a truncated HEAD run,
        which is the worse of the two: the base side is a fixed
        revision, the head side is the tree under test.
        """
        c = _MOD.compare(
            {"a.vera": _ok("same"), "b.vera": _ok("x")},
            {"a.vera": _ok("same")},
            "origin/main",
        )
        assert c.unreported == ["b.vera"]
        assert c.identical == 1
        assert c.compared == 1

    def test_both_sides_missing_a_different_program_are_both_reported(
        self,
    ) -> None:
        """Neither direction shadows the other."""
        c = _MOD.compare(
            {"a.vera": _ok("same"), "base_only.vera": _ok("x")},
            {"a.vera": _ok("same"), "head_only.vera": _ok("y")},
            "origin/main",
        )
        assert c.unreported == ["base_only.vera", "head_only.vera"]
        assert c.compared == 1


# ---------------------------------------------------------------------------
# Report, exit code, JSON
# ---------------------------------------------------------------------------


class TestReportAndExitCode:
    """What a run prints, and what it exits."""

    def _clean(self) -> Any:
        return _MOD.compare(
            {"a.vera": _ok("same"), "b.vera": _failed()},
            {"a.vera": _ok("same"), "b.vera": _failed()},
            "origin/main",
        )

    def _moved(self) -> Any:
        return _MOD.compare(
            {"a.vera": _ok("old"), "b.vera": _ok("kept")},
            {"a.vera": _ok("new"), "b.vera": _failed("[E620] dropped")},
            "origin/main",
        )

    def test_a_clean_run_exits_zero_and_says_so(self, capsys: Any) -> None:
        assert _MOD.emit(_info(), self._clean(), as_json=False) == 0
        out = capsys.readouterr().out
        assert "No movers" in out

    def test_a_run_with_movers_exits_one(self, capsys: Any) -> None:
        assert _MOD.emit(_info(), self._moved(), as_json=False) == 1
        capsys.readouterr()

    def test_every_mover_is_named_with_its_reason(self, capsys: Any) -> None:
        _MOD.emit(_info(), self._moved(), as_json=False)
        captured = capsys.readouterr()
        report = captured.out + captured.err
        assert "a.vera" in report
        assert "WAT differs" in report
        assert "b.vera" in report
        assert "compiles only at origin/main" in report

    def test_the_both_failed_count_is_reported_not_hidden(
        self, capsys: Any
    ) -> None:
        """A corpus where half the programs compile at neither revision
        agrees vacuously.  The count is printed so a reader of a green
        run knows how much of it was measured."""
        _MOD.emit(_info(), self._clean(), as_json=False)
        out = capsys.readouterr().out
        # The whole line, not just the digit: `identical WAT: 1` and the
        # run's SHA both contain a "1", so a bare `"1" in out` stayed green
        # on a regression that printed `compiled at neither revision: 0`
        # (#1329 review).
        assert "compiled at neither revision: 1" in out

    def test_an_unreported_program_exits_one(self, capsys: Any) -> None:
        """A truncated run is a failed run, not a clean one — even with
        no movers among the programs that did report."""
        comparison = _MOD.compare(
            {"a.vera": _ok("same")},
            {"a.vera": _ok("same"), "b.vera": _ok("x")},
            "origin/main",
        )
        assert _MOD.emit(_info(), comparison, as_json=False) == 1
        capsys.readouterr()

    def test_json_carries_the_verdict_and_the_run_identity(
        self, capsys: Any
    ) -> None:
        code = _MOD.emit(_info(), self._moved(), as_json=True)
        payload = json.loads(capsys.readouterr().out)

        assert code == 1
        assert payload["ok"] is False
        assert payload["base_ref"] == "origin/main"
        assert payload["base_sha"] == "0123456789abcdef"
        assert payload["base_root"] == "/scratch/vera-base-0123456789ab"
        assert payload["head_root"] == "/repo"
        assert payload["compared"] == 2
        assert payload["identical"] == 0
        assert payload["both_failed"] == 0
        assert payload["unreported"] == []
        assert {m["path"]: m["kind"] for m in payload["movers"]} == {
            "a.vera": "wat-differs",
            "b.vera": "base-only",
        }
        assert all("reason" in m for m in payload["movers"])

    def test_json_flags_a_clean_run_ok(self, capsys: Any) -> None:
        code = _MOD.emit(_info(), self._clean(), as_json=True)
        payload = json.loads(capsys.readouterr().out)
        assert code == 0
        assert payload["ok"] is True
        assert payload["movers"] == []
        assert payload["both_failed"] == 1


# ---------------------------------------------------------------------------
# The compiler canary
# ---------------------------------------------------------------------------


class TestCompilerCanary:
    """Which `vera` each side actually imported.

    The load-bearing guard of the whole instrument.  Both sides run the
    same CLI under different `PYTHONPATH`s, and the venv carries an
    editable install of a *third* checkout whose finder sits on
    `sys.meta_path`.  If either side resolves `vera` somewhere other
    than its own root, the run compares a revision against itself and
    reports 0 movers — a green verdict that measured nothing.
    """

    def test_a_compiler_under_the_expected_root_passes(self) -> None:
        assert _MOD.canary_error(
            "/scratch/base/vera/__init__.py", Path("/scratch/base"), "base"
        ) is None

    def test_a_compiler_outside_the_expected_root_is_an_error(self) -> None:
        root = Path("/scratch/base")
        message = _MOD.canary_error(
            "/usr/lib/site-packages/vera/__init__.py", root, "base"
        )
        assert message is not None
        assert "base" in message
        assert "/usr/lib/site-packages/vera/__init__.py" in message
        # The root is asserted by the property "it is this path", not by a
        # POSIX shape: the message renders it with the host's separators,
        # and `\scratch\base` is the correct rendering on Windows.
        assert str(root) in message
        assert "different checkout" in message

    def test_the_root_in_the_message_is_the_root_it_was_given(self) -> None:
        """Non-vacuity for the assertion above: `str(root) in message`
        would also hold if the message quoted some other path that
        happened to contain it, so a different root must change it."""
        elsewhere = _MOD.canary_error(
            "/usr/lib/site-packages/vera/__init__.py", Path("/other/root"), "base"
        )
        assert elsewhere is not None
        assert str(Path("/other/root")) in elsewhere
        assert str(Path("/scratch/base")) not in elsewhere

    def test_an_import_failure_is_an_error_that_says_so(self) -> None:
        """A side that could not import `vera` at all reports no path;
        that is a failed run, not an absent objection.

        The message must say the import failed.  Asserting only that
        *some* message came back is satisfied by the wrong branch: an
        empty path resolves to the process's own directory, which is not
        under the expected root either, so a missing import-failure
        check still objects — while claiming the side compiled with
        another checkout's compiler, which is not what happened.
        """
        message = _MOD.canary_error("", Path("/scratch/base"), "base")
        assert message is not None
        assert "base" in message
        assert "could not import" in message


# ---------------------------------------------------------------------------
# Collection
# ---------------------------------------------------------------------------


class TestCollection:
    """How per-file results are keyed, with the compile injected."""

    def test_results_are_keyed_by_repo_relative_posix_path(self) -> None:
        """Both sides compile the *working tree's* files, so both maps
        must be keyed against that one corpus root.  An absolute key
        would work only by accident — the base compiler runs from a
        scratch checkout elsewhere — and a side-specific key would leave
        every program unreported.  POSIX form because the key is
        compared as a string (CLAUDE.md's cross-platform rule)."""
        root = Path("/repo")
        files = [
            root / "examples" / "a.vera",
            root / "tests" / "conformance" / "vera" / "b.vera",
        ]
        seen: list[Path] = []

        def fake_compile(path: Path) -> Any:
            seen.append(path)
            return _ok(f"digest-of-{path.name}")

        results = _MOD.collect(files, root, fake_compile)

        assert set(results) == {
            "examples/a.vera",
            "tests/conformance/vera/b.vera",
        }
        assert results["examples/a.vera"].digest == "digest-of-a.vera"
        assert seen == files


# ---------------------------------------------------------------------------
# The failure reason
# ---------------------------------------------------------------------------


class TestFailureReason:
    """What a one-sided mover's line says the compile failed of.

    Measured, not imagined: the first version took the first line of
    stderr that did not begin with ``warning:``, and a real run against
    v0.1.9 reported a *warning's* quoted source line
    (``public fn read_some(@Unit -> @Int)``) as the reason a program did
    not compile.  A diagnostic is a block, and only its first line
    carries the marker.
    """

    _WARNING_BLOCK = (
        "warning: [E604] Error at /repo/x.vera, line 3, column 1:\n"
        "\n"
        "    public fn read_some(@Unit -> @Int)\n"
        "           ^\n"
        "\n"
        "  Function 'read_some' has unsupported parameter type.\n"
    )

    def test_the_reason_is_the_error_not_a_warnings_source_line(self) -> None:
        stderr = (
            self._WARNING_BLOCK
            + "[E154] Error at /repo/x.vera, line 9, column 8:\n"
            "\n    public forall<VeraFn> fn pick(@VeraFn -> @Int)\n"
        )
        reason = _MOD._first_error(stderr, Path("/repo/x.vera"))
        assert "[E154]" in reason
        assert "read_some" not in reason

    def test_the_compiled_files_path_is_not_repeated_in_the_reason(
        self,
    ) -> None:
        """The reason is already attached to a named program, and the
        absolute path of a corpus file under a scratch checkout is long
        enough to push the diagnostic out of the truncated line."""
        stderr = "[E154] Error at /repo/x.vera, line 9, column 8:\n"
        reason = _MOD._first_error(stderr, Path("/repo/x.vera"))
        assert "/repo/x.vera" not in reason
        assert "x.vera" in reason

    def test_a_posix_form_path_is_stripped_under_a_windows_renderer(self) -> None:
        """The diagnostic's spelling of the path need not be the host's.

        Stripping on ``str(path)`` alone is a separator-shaped match: on
        Windows the same path renders `\\repo\\x.vera`, so a diagnostic
        carrying the POSIX form goes unstripped and its absolute path
        pushes the message past the truncation — the silent
        matches-nothing failure, not a loud one.  ``PureWindowsPath``
        reproduces that rendering on any host, so this cell fails on
        macOS too rather than only in the Windows CI cell.
        """
        stderr = "[E154] Error at /repo/x.vera, line 9, column 8:\n"
        reason = _MOD._first_error(stderr, PureWindowsPath("/repo/x.vera"))
        assert "/repo/x.vera" not in reason
        assert "x.vera" in reason
        assert "[E154]" in reason

    def test_a_native_form_path_is_stripped_under_a_windows_renderer(self) -> None:
        """The complement: the same path as Windows itself would print it."""
        stderr = "[E154] Error at \\repo\\x.vera, line 9, column 8:\n"
        reason = _MOD._first_error(stderr, PureWindowsPath("/repo/x.vera"))
        assert "\\repo\\x.vera" not in reason
        assert "x.vera" in reason

    def test_a_crash_reports_its_exception_not_its_first_line(self) -> None:
        """No diagnostic marker at all — a compiler crash.  The useful
        line is the exception, which is last."""
        stderr = (
            "Traceback (most recent call last):\n"
            '  File "/repo/vera/cli.py", line 1, in main\n'
            "AssertionError: slot table is empty\n"
        )
        reason = _MOD._first_error(stderr, Path("/repo/x.vera"))
        assert reason == "AssertionError: slot table is empty"

    def test_silence_still_gives_a_reason(self) -> None:
        assert _MOD._first_error("", Path("/repo/x.vera")) != ""


# ---------------------------------------------------------------------------
# What the instrument is not
# ---------------------------------------------------------------------------


class TestNotAPreCommitHook:
    """The module docstring's claim, asserted rather than trusted."""

    def test_the_instrument_is_not_wired_into_pre_commit(self) -> None:
        """It compiles the whole corpus twice.  As a commit hook that is
        minutes per commit, which is why it is a burndown instrument the
        maintainer runs deliberately.  If it is ever wired in, the
        module docstring saying it is not must change in the same
        commit."""
        config = (_ROOT / ".pre-commit-config.yaml").read_text(
            encoding="utf-8"
        )
        assert "check_corpus_differential" not in config


class TestParallelCollection:
    """The `jobs > 1` branch, which no cell reached (#1329 review).

    Every other collection cell runs at the default `jobs=1`, so the
    sequential branch was covered and the parallel one was not.  The
    parallel branch pairs keys with results *positionally* — it zips a
    list built from `files` against `ThreadPoolExecutor.map`'s output —
    so it is correct only while `map` yields in input order.  If that
    ever stopped holding, every artifact would be attributed to the
    wrong program and the run would invent movers out of nothing, which
    is the one failure this instrument must not have.
    """

    def test_results_stay_paired_with_their_keys(self) -> None:
        root = Path("/repo")
        files = [root / "examples" / f"p{index}.vera" for index in range(24)]

        def fake_compile(path: Path) -> Any:
            return _ok(f"digest-of-{path.name}")

        results = _MOD.collect(files, root, fake_compile, jobs=4)

        assert len(results) == len(files)
        for path in files:
            assert results[f"examples/{path.name}"].digest == f"digest-of-{path.name}"

    def test_the_parallel_branch_is_the_one_being_exercised(self) -> None:
        """Non-vacuity: `jobs=4` must not quietly fall through to the
        sequential path, or this class tests nothing new.

        The property is *where* the work ran, not how many threads the
        pool chose to spawn.  `ThreadPoolExecutor` creates a worker only
        when no idle one is available, so a handful of trivial callables
        can be drained by a single worker before `map` finishes
        submitting them: measured over 200 trials on a 12-core host the
        distinct-thread count came out 2, 3 or 4, and on a 2-core CI
        runner it is 1.  Asserting `len(threads) > 1` therefore inherited
        the host's scheduling — green here, red on every CI cell.  What
        *is* invariant is that the pool never executes inline: the
        calling thread ran work in 0 of those 200 trials, and 0 of any,
        because `submit` always hands the callable to a worker.
        """
        root = Path("/repo")
        files = [root / "examples" / f"p{index}.vera" for index in range(8)]
        threads: set[int] = set()

        def fake_compile(path: Path) -> Any:
            threads.add(threading.get_ident())
            return _ok(path.name)

        _MOD.collect(files, root, fake_compile, jobs=4)
        assert threads, "no compile ran at all"
        assert threading.get_ident() not in threads, (
            "a compile ran on the calling thread, so `jobs=4` fell through "
            "to the sequential branch"
        )

    def test_the_sequential_branch_runs_inline(self) -> None:
        """The complement, and the reason the cell above is not vacuous:
        `jobs=1` must run on the caller, so the two branches are told
        apart by the same observation rather than by a count."""
        root = Path("/repo")
        files = [root / "examples" / f"p{index}.vera" for index in range(8)]
        threads: set[int] = set()

        def fake_compile(path: Path) -> Any:
            threads.add(threading.get_ident())
            return _ok(path.name)

        _MOD.collect(files, root, fake_compile, jobs=1)
        assert threads == {threading.get_ident()}

    def test_both_branches_agree(self) -> None:
        root = Path("/repo")
        files = [root / "examples" / f"p{index}.vera" for index in range(8)]

        def fake_compile(path: Path) -> Any:
            return _ok(f"digest-of-{path.name}")

        assert _MOD.collect(files, root, fake_compile, jobs=1) == _MOD.collect(
            files, root, fake_compile, jobs=4
        )


class TestSideEnvironment:
    """`_side_env`, which had no test at all (#1329 review)."""

    def test_pythonpath_is_replaced_not_extended(
        self, monkeypatch: Any
    ) -> None:
        """The caller's `PYTHONPATH` usually names the head checkout —
        that is how this repo is driven.  Inheriting it on the base side
        puts the head compiler first on the path, so the differential
        compares a revision against itself and reports zero movers: the
        vacuity `canary_error` exists to catch, arriving one layer down.
        """
        monkeypatch.setenv("PYTHONPATH", "/repo")
        env = _MOD._side_env(Path("/scratch/base"))
        assert env["PYTHONPATH"] == str(Path("/scratch/base"))
        assert "/repo" not in env["PYTHONPATH"]

    def test_bytecode_writing_is_off_for_both_checkouts(
        self, monkeypatch: Any
    ) -> None:
        """Scrubbed from the ambient environment first, deliberately.

        This suite is itself run with `PYTHONDONTWRITEBYTECODE=1`, and
        `_side_env` copies `os.environ` — so without the scrub the
        assertion is satisfied by the caller's shell and passes with the
        line under test deleted.  It measures the function only when the
        variable is absent to begin with.
        """
        monkeypatch.delenv("PYTHONDONTWRITEBYTECODE", raising=False)
        env = _MOD._side_env(Path("/scratch/base"))
        assert env["PYTHONDONTWRITEBYTECODE"] == "1"

    def test_the_rest_of_the_environment_is_inherited(
        self, monkeypatch: Any
    ) -> None:
        """Only those two keys are the function's business: the base
        compiler still needs the venv's interpreter and its PATH."""
        monkeypatch.setenv("VERA_SIDE_ENV_PROBE", "kept")
        assert _MOD._side_env(Path("/scratch/base"))["VERA_SIDE_ENV_PROBE"] == "kept"


class TestTimeoutValidation:
    """`--timeout` must be able to elapse (#1329 review).

    Zero or negative expires before any compile finishes, so both sides
    fail every program, `compare` counts them all as `both_failed`, and
    `emit` reports "No movers" with exit 0 over a corpus that never
    compiled — a green run measuring nothing.
    """

    @pytest.mark.parametrize("value", ["0", "-1"])
    def test_a_non_positive_budget_is_rejected(self, value: str) -> None:
        with pytest.raises(argparse.ArgumentTypeError, match="greater than zero"):
            _MOD._positive_seconds(value)

    def test_a_positive_budget_is_accepted(self) -> None:
        assert _MOD._positive_seconds("120") == 120

    @pytest.mark.parametrize("value", ["0", "-1"])
    def test_the_parser_refuses_it_too(self, value: str) -> None:
        """Wired into `--timeout`, not merely defined beside it."""
        with pytest.raises(SystemExit):
            _MOD._parse_args(["--timeout", value])


class TestUndecodableCompilerOutput:
    """A compiler byte the codec cannot read must stay data (#1329 review).

    Strict decoding raises `UnicodeDecodeError` out of `subprocess.run`
    itself — a `ValueError`, which neither handler in `compile_one`
    catches — and `collect` iterates `ThreadPoolExecutor.map`, so that
    one program would abort the whole corpus run.
    """

    def test_the_compile_asks_for_lenient_decoding(
        self, monkeypatch: Any
    ) -> None:
        seen: dict[str, Any] = {}

        def fake_run(*args: Any, **kwargs: Any) -> Any:
            seen.update(kwargs)
            raise subprocess.TimeoutExpired(cmd="x", timeout=1)

        monkeypatch.setattr(_MOD.subprocess, "run", fake_run)
        _MOD.compile_one("python", Path("/scratch"), 5, Path("/repo/a.vera"))
        assert seen.get("encoding") == "utf-8"
        assert seen.get("errors") == "replace"

    def test_strict_decoding_is_what_would_have_raised(self) -> None:
        """The reason the kwarg above matters, measured rather than
        asserted: the same bytes through the same decoder raise on
        strict and survive on replace.

        Measured through `io.TextIOWrapper`, which is not a stand-in —
        it is the mechanism.  `subprocess.Popen` wraps each captured
        pipe in exactly this object with exactly the `encoding` and
        `errors` it was given, so this reproduces `compile_one`'s
        decode without a child process.

        Spawning one was the previous shape and it made the cell
        environment-dependent: what a child puts on a pipe depends on
        the OS, and the three Windows cells failed here with "DID NOT
        RAISE".  The decode itself never varied — both calls named
        `encoding="utf-8"` — but the byte reaching them did.  Note the
        byte is only undecodable in UTF-8: `b"\\x97".decode("cp1252")`
        is an em dash, so a decode left to the platform default would
        not raise on Windows either.  Naming the codec is what makes
        this deterministic, and it is the same codec the script names.
        """
        undecodable = b"\x97"

        def decode(**kwargs: Any) -> str:
            return io.TextIOWrapper(
                io.BytesIO(undecodable), encoding="utf-8", **kwargs
            ).read()

        with pytest.raises(UnicodeDecodeError):
            decode()
        assert decode(errors="replace") == "\ufffd"

    def test_the_byte_is_undecodable_in_the_codec_the_script_names(self) -> None:
        """Non-vacuity: the fixture must be undecodable in UTF-8 and not
        merely unusual, or the cell above proves nothing about the
        codec `compile_one` actually passes."""
        with pytest.raises(UnicodeDecodeError):
            b"\x97".decode("utf-8")
        assert b"\x97".decode("cp1252") == "\u2014"


def _seed_repo(root: Path) -> str:
    """A one-commit git repo shaped enough for `base_checkout`."""
    root.mkdir(parents=True, exist_ok=True)
    run = lambda *a: subprocess.run(  # noqa: E731
        ["git", "-C", str(root), *a], check=True,
        capture_output=True, text=True, encoding="utf-8",
    )
    run("init", "-b", "main")
    run("config", "user.email", "differential-test@example.invalid")
    run("config", "user.name", "Differential Test")
    (root / "vera").mkdir(exist_ok=True)
    (root / "vera" / "__init__.py").write_text("__version__ = '0'\n", encoding="utf-8")
    run("add", ".")
    run("commit", "-m", "seed")
    return subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        check=True, capture_output=True, text=True, encoding="utf-8",
    ).stdout.strip()


class TestBaseCheckoutReuse:
    """The persistent base checkout is reused, so it must be CLEAN (#1330).

    `rev-parse HEAD` proves the commit and nothing about the tree.  A
    reused checkout survives between runs by design, so an edit made
    under it — a stray print, an abandoned bisect — becomes the base
    compiler on the next run.  The canary cannot object: it proves which
    checkout was imported, and a modified one is still that checkout.  A
    dirty base makes "0 movers" mean nothing and can manufacture movers
    out of the edit.
    """

    @pytest.fixture(autouse=True)
    def _hermetic_git_env(self, monkeypatch: Any) -> None:
        # Pre-commit exports GIT_DIR/GIT_INDEX_FILE into the hook's
        # environment, which would override each call's `-C` and drive
        # the developer's own repository instead of the tmp one.
        for name in [k for k in os.environ if k.startswith("GIT_")]:
            monkeypatch.delenv(name, raising=False)

    def test_a_clean_reused_checkout_is_accepted(self, tmp_path: Path) -> None:
        repo = tmp_path / "repo"
        sha = _seed_repo(repo)
        work = tmp_path / "work"
        first, error = _MOD.base_checkout(repo, sha, work)
        assert error == "" and first is not None

        again, error = _MOD.base_checkout(repo, sha, work)
        assert error == "", "the clean checkout must be reused, not refused"
        assert again == first

    def test_a_dirty_reused_checkout_is_refused(self, tmp_path: Path) -> None:
        repo = tmp_path / "repo"
        sha = _seed_repo(repo)
        work = tmp_path / "work"
        dest, error = _MOD.base_checkout(repo, sha, work)
        assert error == "" and dest is not None

        # The edit a reused checkout can carry between runs.  HEAD is
        # untouched, so the commit check still passes.
        (dest / "vera" / "__init__.py").write_text(
            "__version__ = '0'\nSTRAY = True\n", encoding="utf-8"
        )

        again, error = _MOD.base_checkout(repo, sha, work)
        assert again is None, "a modified base compiled the differential"
        assert "clean checkout" in error
        assert "--work-dir" in error, "the refusal must keep its recreate guidance"

    def test_an_untracked_file_also_makes_it_dirty(self, tmp_path: Path) -> None:
        """An added file is as much a different compiler as an edited one."""
        repo = tmp_path / "repo"
        sha = _seed_repo(repo)
        work = tmp_path / "work"
        dest, error = _MOD.base_checkout(repo, sha, work)
        assert error == "" and dest is not None

        (dest / "vera" / "sitecustomize_probe.py").write_text("x = 1\n", encoding="utf-8")

        again, error = _MOD.base_checkout(repo, sha, work)
        assert again is None and "clean checkout" in error

    def test_the_commit_check_alone_would_not_have_caught_it(
        self, tmp_path: Path
    ) -> None:
        """Non-vacuity: the dirty tree must still be at the right commit,
        or this class is testing the pre-existing `rev-parse` check."""
        repo = tmp_path / "repo"
        sha = _seed_repo(repo)
        work = tmp_path / "work"
        dest, _ = _MOD.base_checkout(repo, sha, work)
        assert dest is not None
        (dest / "vera" / "__init__.py").write_text("STRAY = True\n", encoding="utf-8")

        head = subprocess.run(
            ["git", "-C", str(dest), "rev-parse", "HEAD"],
            check=True, capture_output=True, text=True, encoding="utf-8",
        ).stdout.strip()
        assert head == sha
        assert (dest / "vera" / "__init__.py").is_file()


# =====================================================================
# #1374 — the base checkout does not outlive the run unless asked to
# =====================================================================


class TestBaseCheckoutCleanup:
    """The instrument tidies up after itself by default.

    Leaving the checkout in place was a deliberate reuse optimisation — a
    burndown session runs the differential repeatedly against one base and
    paid for one checkout — but the tree it leaves is a full second copy of
    the repository INSIDE the repository, and `pytest tests/` then walked its
    `spec/` as an authored doc surface (#1374).  The default is now removal;
    `--keep-base` is how a repeated-run session opts back into the reuse.
    """

    def test_keep_base_defaults_to_off(self) -> None:
        assert _MOD._parse_args([]).keep_base is False

    def test_keep_base_is_settable(self) -> None:
        assert _MOD._parse_args(["--keep-base"]).keep_base is True

    def test_release_removes_a_worktree_it_created(self, tmp_path: Path) -> None:
        """Removal goes through `git worktree remove`, not a tree delete.

        `base_checkout` creates the checkout with `git worktree add`, so the
        repository's worktree registry holds an entry for it; deleting the
        directory alone would leave that entry behind as a prunable stale
        record, which the next run's cleanliness check cannot see.
        """
        calls: list[list[str]] = []

        def fake_run(cmd: list[str], **kw: object) -> Any:
            calls.append(cmd)
            return subprocess.CompletedProcess(cmd, 0, "", "")

        with mock.patch.object(_MOD.subprocess, "run", fake_run):
            _MOD.release_base_checkout(tmp_path / "repo", tmp_path / "base")

        assert calls, "nothing was run"
        assert calls[0][:4] == ["git", "-C", str(tmp_path / "repo"), "worktree"]
        assert "remove" in calls[0]
        assert str(tmp_path / "base") in calls[0]

    def test_release_is_silent_when_git_cannot_start(
        self, tmp_path: Path,
    ) -> None:
        """`check=False` suppresses a non-zero EXIT, not a failure to START.

        A missing `git`, an exhausted descriptor table or a permission error
        raises `OSError` out of `subprocess.run` — and this runs from a
        `finally`, so the exception would replace the verdict the whole run
        exists to produce with a traceback (PR #1372 review).
        """
        def fake_run(cmd: list[str], **kw: object) -> Any:
            raise OSError(2, "No such file or directory: 'git'")

        with mock.patch.object(_MOD.subprocess, "run", fake_run):
            _MOD.release_base_checkout(tmp_path / "repo", tmp_path / "base")

    def test_release_is_silent_when_git_declines(self, tmp_path: Path) -> None:
        """Cleanup is best-effort: a failed removal must not turn a clean
        differential into a failing one.

        The verdict this script exists to report is already computed by the
        time cleanup runs, and losing it to a housekeeping error would be a
        worse failure than the leftover directory.
        """
        def fake_run(cmd: list[str], **kw: object) -> Any:
            return subprocess.CompletedProcess(cmd, 128, "", "fatal: nope")

        with mock.patch.object(_MOD.subprocess, "run", fake_run):
            _MOD.release_base_checkout(tmp_path / "repo", tmp_path / "base")
