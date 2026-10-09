"""Conformance test suite — spec-anchored feature validation.

Each test corresponds to a small .vera program in tests/conformance/ that
exercises one language feature.  The manifest (manifest.json) declares the
deepest pipeline stage each program must pass: parse, check, verify, or run.
A run-level entry also declares what the run prints and how it exits
(``expected_stdout`` and ``expected_exit``, or a reasoned
``nondeterministic_stdout``), and the run stage compares both; the rule lives
in scripts/conformance_golden.py, which scripts/check_conformance.py shares.

This module is part of the full test suite and runs in CI alongside the
unit tests and example round-trip tests.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from vera.formatter import format_source
from vera.parser import parse_file

# ---------------------------------------------------------------------------
# Load manifest
# ---------------------------------------------------------------------------

CONFORMANCE_DIR = Path(__file__).parent / "conformance"
MANIFEST: list[dict] = json.loads(
    (CONFORMANCE_DIR / "manifest.json").read_text(encoding="utf-8")
)

_GOLDEN = Path(__file__).resolve().parent.parent / "scripts" / "conformance_golden.py"


def _load_golden() -> Any:
    """scripts/conformance_golden.py, the run-stage rule both harnesses use."""
    spec = importlib.util.spec_from_file_location("conformance_golden", _GOLDEN)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


golden = _load_golden()

_LEVEL_ORDER = {"parse": 0, "check": 1, "verify": 2, "run": 3}


def _at_least(entry: dict, level: str) -> bool:
    """Return True if the entry's declared level is >= *level*."""
    return _LEVEL_ORDER.get(entry["level"], 0) >= _LEVEL_ORDER[level]


def _vera(*args: str) -> subprocess.CompletedProcess[str]:
    """Run a vera CLI command and return the completed process."""
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )


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
        (ch08_circular_import → E011 at check;
        ch08_module_prelude_adt_contention_rejected → E621 at compile).

        A COMPILE-stage negative also asserts that check is clean, because
        "the checker accepts it and codegen must refuse it" is exactly the
        property that class of diagnostic exists for — a negative that
        started failing at check would otherwise still pass."""
        if not _at_least(entry, "check"):
            pytest.skip("parse-only")
        path = str(CONFORMANCE_DIR / entry["file"])
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
                pre = _vera("check", path)
                assert "OK:" in pre.stdout, (
                    f"{entry['id']} is a compile-stage negative, so it must "
                    f"type-check cleanly:\n{pre.stdout}\n{pre.stderr}"
                )
            result = _vera(stage, "--json", path)
            try:
                payload = json.loads(result.stdout)
            except json.JSONDecodeError as exc:
                # A stage died before emitting the envelope; without the
                # streams this arrives as a bare decode error about an
                # empty document (#1330 review).
                raise AssertionError(
                    f"{entry['file']}: {stage} --json produced no JSON envelope "
                    f"({exc}).\nstdout:\n{result.stdout}\n"
                    f"stderr:\n{result.stderr}"
                ) from exc
            codes = [d.get("error_code")
                     for d in payload.get("diagnostics", [])]
            assert payload.get("ok") is False and expected_error in codes, (
                f"Expected {entry['id']} to fail {stage} with "
                f"{expected_error}; got ok={payload.get('ok')} "
                f"codes={codes}\n{result.stdout}"
            )
            return
        result = _vera("check", path)
        assert "OK:" in result.stdout, (
            f"Type-check failed for {entry['id']}:\n{result.stdout}\n{result.stderr}"
        )

    def test_verify(self, entry: dict) -> None:
        """Programs at level verify/run must verify contracts cleanly."""
        if not _at_least(entry, "verify"):
            pytest.skip(f"{entry['level']}-only")
        path = str(CONFORMANCE_DIR / entry["file"])
        result = _vera("verify", path)
        assert "OK:" in result.stdout, (
            f"Verification failed for {entry['id']}:\n{result.stdout}\n{result.stderr}"
        )

    def test_run(self, entry: dict) -> None:
        """Programs at level run must compile and execute, exiting with the
        entry's ``expected_exit`` and printing exactly its
        ``expected_stdout`` (or, under a ``nondeterministic_stdout`` reason,
        exiting as declared with the output left unpinned).  An exit status
        of 0 alone is not a pass: a program that prints the wrong value, or
        nothing, exits 0 too."""
        if not _at_least(entry, "run"):
            pytest.skip(f"{entry['level']}-only")
        problems = golden.entry_problems(entry)
        if problems:
            pytest.fail("\n".join(problems))
        outcome = golden.run_program(CONFORMANCE_DIR / entry["file"])
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
        problems = golden.entry_problems(_entry(**keys))
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
    def _outcome(stdout: bytes, exit: int = 0, stderr: bytes = b"") -> Any:
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
