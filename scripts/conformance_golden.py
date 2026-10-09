#!/usr/bin/env python
r"""What a run-level conformance program must print, for both harnesses.

A run-level entry in ``tests/conformance/manifest.json`` says what
``vera run <file>`` does, not only that it exits:

- ``expected_exit``: the exit status, an integer.  Every run-level entry
  carries it.
- ``expected_stdout``: everything the run writes to stdout, exactly, as a
  JSON string.  A program whose ``main`` returns 42 has ``"42\n"``, since
  ``vera run`` prints a returned value and ends its output with a newline.
- ``nondeterministic_stdout``: in place of ``expected_stdout``, for a program
  whose output is not a function of its source (one that prints the wall
  clock), the reason the output cannot be pinned.  It is text that says
  something, never a bare flag, and an entry carries it or
  ``expected_stdout``, never both.  The exit status is compared all the same.

An entry below the run level carries none of the three: it has no run stage,
so a value there would be compared with nothing.

``tests/test_conformance.py`` and ``scripts/check_conformance.py`` both check
the manifest with :func:`entry_problems`, run a program with
:func:`run_program` and judge the run with :func:`run_mismatch`, so the rule
is written once and the two harnesses cannot drift apart.
"""

from __future__ import annotations

import os
import subprocess
import sys
from collections.abc import Iterable, Mapping
from pathlib import Path
from typing import Any, NamedTuple

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_examples_run import NEUTRALISED_ENV

EXPECTED_STDOUT = "expected_stdout"
EXPECTED_EXIT = "expected_exit"
NONDETERMINISTIC_STDOUT = "nondeterministic_stdout"
RUN_STAGE_KEYS = (EXPECTED_STDOUT, EXPECTED_EXIT, NONDETERMINISTIC_STDOUT)


class RunOutcome(NamedTuple):
    """What one ``vera run`` did: its exit status, and its two streams as the
    bytes the process wrote."""

    exit: int
    stdout: bytes
    stderr: bytes


# ---------------------------------------------------------------------------
# The manifest: what a run-level entry must declare
# ---------------------------------------------------------------------------


def entry_problems(entry: Mapping[str, Any]) -> list[str]:
    """Why *entry*'s run-stage keys do not say what its run must do; empty
    when they do.  Each problem names the entry and the key at fault."""
    name = entry.get("id", "<an entry with no id>")
    level = entry.get("level")
    if level != "run":
        return [
            f"{name}: carries {key}, but a {level!r}-level entry has no run "
            f"stage to compare it with"
            for key in RUN_STAGE_KEYS
            if key in entry
        ]

    problems: list[str] = []
    if EXPECTED_EXIT not in entry:
        problems.append(
            f"{name}: a run-level entry names its exit status in {EXPECTED_EXIT}"
        )
    elif not _is_exit_status(entry[EXPECTED_EXIT]):
        problems.append(
            f"{name}: {EXPECTED_EXIT} is an exit status, an integer, "
            f"not {entry[EXPECTED_EXIT]!r}"
        )

    pinned = EXPECTED_STDOUT in entry
    escaped = NONDETERMINISTIC_STDOUT in entry
    if pinned and escaped:
        problems.append(
            f"{name}: carries both {EXPECTED_STDOUT} and "
            f"{NONDETERMINISTIC_STDOUT}; its output is pinned or it is not"
        )
    elif not pinned and not escaped:
        problems.append(
            f"{name}: a run-level entry pins its output in {EXPECTED_STDOUT}, "
            f"or says in {NONDETERMINISTIC_STDOUT} why it cannot"
        )
    if pinned and not isinstance(entry[EXPECTED_STDOUT], str):
        problems.append(
            f"{name}: {EXPECTED_STDOUT} is the output as text, "
            f"not {entry[EXPECTED_STDOUT]!r}"
        )
    if escaped:
        reason = entry[NONDETERMINISTIC_STDOUT]
        if not isinstance(reason, str) or not reason.strip():
            problems.append(
                f"{name}: {NONDETERMINISTIC_STDOUT} is the reason the output "
                f"cannot be pinned, so it must say something, not {reason!r}"
            )
    return problems


def manifest_problems(manifest: Iterable[Mapping[str, Any]]) -> list[str]:
    """Every entry's problems, in manifest order."""
    return [problem for entry in manifest for problem in entry_problems(entry)]


def _is_exit_status(value: object) -> bool:
    # A JSON `true` loads as a bool, which Python counts as an int.
    return isinstance(value, int) and not isinstance(value, bool)


# ---------------------------------------------------------------------------
# One run, and how it is judged
# ---------------------------------------------------------------------------


def run_env(base: Mapping[str, str] | None = None) -> dict[str, str]:
    """The environment a run gets: *base* (by default the inherited one)
    less the variables that change what a program does, the list
    ``scripts/check_examples_run.py`` keeps for the examples.  Everything
    else passes through, ``VERA_EAGER_GC`` among it: CI's eager-GC lane sets
    it to run this same comparison with a collection at every allocation."""
    env = dict(os.environ if base is None else base)
    for name in NEUTRALISED_ENV:
        env.pop(name, None)
    return env


def run_program(path: Path) -> RunOutcome:
    """``vera run <path>``, run the way both harnesses judge it.

    stdin is an immediate end of file, so what the run reads does not depend
    on what started the harness; the environment is :func:`run_env`'s; and
    stdout is kept as the bytes the process wrote, because a text-mode
    capture translates a lone ``\r`` into a newline before any comparison
    could see it.
    """
    proc = subprocess.run(
        [sys.executable, "-m", "vera.cli", "run", str(path)],
        capture_output=True,
        stdin=subprocess.DEVNULL,
        env=run_env(),
        check=False,
    )
    return RunOutcome(exit=proc.returncode, stdout=proc.stdout, stderr=proc.stderr)


def wire_bytes(text: str, linesep: str = os.linesep) -> bytes:
    r"""The bytes ``vera run`` writes for a program whose stdout is *text*.

    The CLI prints through a text-mode ``sys.stdout``, which writes the
    platform's line separator for each ``\n``: unchanged on POSIX, ``\r\n``
    on Windows.  Nothing else changes, so one manifest value holds on every
    platform and the comparison is still exact.
    """
    return text.replace("\n", linesep).encode("utf-8")


def run_mismatch(
    entry: Mapping[str, Any],
    outcome: RunOutcome,
    linesep: str = os.linesep,
) -> str | None:
    """How *outcome* departs from what *entry* declares, with the expected
    and the actual output in full; None when it does not.  *entry* is one
    :func:`entry_problems` finds nothing wrong with."""
    lines: list[str] = []
    if outcome.exit != entry[EXPECTED_EXIT]:
        lines.append(
            f"exit status: expected {entry[EXPECTED_EXIT]}, got {outcome.exit}"
        )
    if EXPECTED_STDOUT in entry:
        expected = wire_bytes(entry[EXPECTED_STDOUT], linesep)
        if outcome.stdout != expected:
            lines.append(f"stdout expected: {_shown(expected)}")
            lines.append(f"stdout actual:   {_shown(outcome.stdout)}")
    if not lines:
        return None
    stderr = outcome.stderr.decode("utf-8", "backslashreplace").rstrip("\n")
    return "\n".join([
        f"{entry['id']}: `vera run {entry['file']}` does not do what its "
        f"manifest entry declares",
        *(f"  {line}" for line in lines),
        "  stderr:" + ("".join(f"\n    {s}" for s in stderr.split("\n"))
                       if stderr else " (empty)"),
    ])


def _shown(data: bytes) -> str:
    """*data* as a string literal: every character visible, nothing cut."""
    return repr(data.decode("utf-8", "backslashreplace"))
