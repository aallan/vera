#!/usr/bin/env python3
"""Mutation testing scoped to a diff: mutate the lines a change touches.

The pull request lane of MUTATION.md § CI.  From ``git diff <base>...<head>``
over ``vera/``, the script finds the functions mutmut mutates as units (a
top-level function, or a method of a top-level class; a nested function is
part of the one that encloses it) whose code the diff changes, and runs
mutmut over the lines of those functions near the diff:

1. Each changed line is mapped to the unit that holds it, by ``ast``: an
   added line to the head's unit, a removed line to the base's.  A unit
   counts as changed when its code differs from the merge base's (its
   ``ast`` with docstrings set aside) or it is new; a change to a docstring,
   a comment or the layout alone changes no unit.  Changed lines outside
   every unit (module-level code, a class body, a method of a nested class)
   are reported, since mutmut mutates function bodies only, and so is a unit
   mutmut never mutates (a decorated function bar a lone ``@staticmethod``
   or ``@classmethod``, ``__new__``, ``__getattribute__``, ``__setattr__``,
   or one under a ``# pragma: no mutate block``).
2. The head commit is extracted into a scratch tree (``git archive``; the
   repository is never touched).  In each file the diff changes, every unit
   it does NOT change gets ``# pragma: no mutate block`` on its header, so
   mutmut generates mutants for the changed units only (a whole file's
   mutants for ``vera/verifier.py`` are a 213 MB module that took 447 s to
   generate; the changed units alone took 41 s).  The edit adds comments
   only, and the script checks the file's ``ast`` and line count are
   unchanged.
3. Inside those units, mutmut generates only the mutants whose node starts
   in the window: within two lines (``--context``) of a line the diff adds,
   or of a point where it removes lines and adds none, or on the first line
   of a node of :data:`ENCLOSING_KINDS` that spans such a line, since mutmut
   places a mutant on the line its node starts on, and some nodes' mutants
   change a line further down (a call's argument, a ``match``'s ``case``).
   A one-line edit inside a long function so mutates the lines near it, not
   the function: the 330 mutants of the four functions pull request #1760
   changed ran out the budget at 97 decided (CI run 39664225706).  The
   engine is this script run with ``--as-engine`` (:func:`engine_main`),
   which counts each unit's mutants on every line and in the window with
   mutmut's own visitor, then hands each narrowed file's window to mutmut's
   covered-lines hook, the filter it reads a node's start line against; the
   lane checks the mutants mutmut lists against those counts.
4. The scratch tree's ``[tool.mutmut]`` is the repository's, with
   ``only_mutate`` set to those files and the test selection replaced by
   the changed modules' declared oracles (:func:`oracle_map`: the class
   instruments whose ``matrix`` marker names the module, the test files
   named after it, and its :data:`ORACLE_FAMILIES`), with the pull
   request's own changed test files that reach the compiler in process
   (they import ``vera``, directly or through a ``tests/`` helper) added to
   each, bar the families left out on purpose (:data:`NOT_ORACLE`).
   ``tests/mutation_oracle.py`` confines each function's tests to its own
   module's oracle (``MUTATION_ORACLE_MAP``); the matrices run at their
   sample under a seed fixed for the run, and each survivor on the diff's
   own lines is run again against its module's instruments in full
   (:func:`full_cell_probe`).  A changed function of a
   module no test file declares (:data:`UNDECLARED`) is named, not mutated.
   mutmut runs in two passes: the first names each changed unit's first
   window mutant (:func:`first_mutant`), which also makes the clean run the
   changed units' covering tests, and the second names the mutants the
   first left undecided, in what is left of the budget, since mutmut runs a
   run's mutants cheapest first across every function and a widely covered
   function's would otherwise wait behind them all.  Its stats pass records
   which tests reach each function, and each mutant runs only those tests,
   fastest first, stopping at the first failure.  A
   test that fails inside mutmut's copy with no mutant active (as one that
   reads a file the copy lacks, or ``vera/``'s source text, which in the copy
   is mutmut's generated file, does) stops that pass; it is no oracle there,
   so the lane drops it, runs again, and names it in the summary and the
   record.  An exception the engine's own code raises stops the pass the
   same way, and no test is at fault: the run stops there, drops no
   further test, and the summary and the record name the exception and the
   engine's frame (:func:`engine_failure`).
5. The run has a wall-clock budget.  When it runs out, mutmut is
   interrupted, then its process group terminated, then killed, and what it
   decided so far is reported.

Outputs: a table per function on stdout (and in ``--summary``, the job
summary in CI), under a line that names the selection rule and counts the
functions, their mutants on every line and in the window, and the mutants
generated, decided and surviving, the oracle and each pass's phases in
seconds; the first ``MAX_SHOWN_SURVIVORS`` survivors' ``mutmut show``
diffs; and a JSON record (``--json``) that lists every survivor with its
diff, as far as the show budget (``SHOW_BUDGET_S``) reaches.  ``--list``
lists the window's mutants with their code from mutmut's visitor and runs
no test.

The exit code is red for a defect or an unmeasured diff.  It is 1 when a
mutant of the diff survives, whatever else stopped the run; 2 when the run
itself failed, whether or not the budget ran out first: the engine failed or
counted no window, mutmut reported a mutant of a function the lane did not
map to the diff or more or fewer of a function's mutants than its window
holds, or the lane itself failed before mutmut decided anything; 3 when a
changed function with mutants in its window had none decided (not
measured); and 0 otherwise, a run that decided some of every function's
mutants before the budget ran out included.
An exit 0 says what it decided in the headline: every mutant killed or timed
out, or, where the budget ran out or a mutant was left undecided (``not
checked``, ``suspicious``, ``segfault``, interrupted), that the run is
incomplete, which a ``::warning::`` annotation repeats on the pull request.
A function no test of its module's declared oracle reaches has every mutant
``no tests``: it is not measured (exit 3), and its row names the module
whose oracle reached nothing.

Usage:
    python scripts/mutate_diff.py                      # origin/main...HEAD
    python scripts/mutate_diff.py --base <sha> --head <sha> --budget 2400 \\
        --json out.json --summary "$GITHUB_STEP_SUMMARY"
"""

from __future__ import annotations

import argparse
import ast
import bisect
import fnmatch
import io
import json
import os
import re
import signal
import subprocess
import sys
import tarfile
import shutil
import tempfile
import threading
import time
import tokenize
from collections import Counter
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import asdict, dataclass, field, replace
from pathlib import Path
from typing import Any

import tomllib

ROOT = Path(__file__).resolve().parent.parent

#: mutmut's separator between a class and its method in a mangled name.
SEP = "ǁ"

#: The comment that keeps mutmut from generating mutants for a function.
PRAGMA = "# pragma: no mutate block"

#: Names mutmut never mutates (``NEVER_MUTATE_FUNCTION_NAMES`` in mutmut 3).
NEVER_MUTATED = frozenset({"__getattribute__", "__setattr__", "__new__"})

#: The one decorator a function may carry and still be mutated.
LONE_DECORATORS = frozenset({"staticmethod", "classmethod"})

#: Every status ``mutmut results`` prints (mutmut 3's ``status_by_exit_code``),
#: with how the lane reads it: caught, a survivor, not observable in process,
#: excluded by the engine, or undecided (the run stopped short of it).
STATUSES: dict[str, str] = {
    "killed": "caught",
    "timeout": "caught",
    "caught by type check": "caught",
    "survived": "survived",
    "no tests": "unobserved",
    "skipped": "excluded",
    "not checked": "undecided",
    "check was interrupted by user": "undecided",
    "suspicious": "undecided",
    "segfault": "undecided",
}

#: Changed test files the lane does not add to the selection: the families
#: the repository's selection leaves out on purpose (subprocess and Node
#: suites, which import the un-mutated package, and tooling suites, which
#: test scripts/ and read the repository's git state), and this lane's own.
NOT_ORACLE = (
    "tests/test_check_*.py",
    "tests/test_cli*.py",
    "tests/test_conformance*.py",
    "tests/test_browser*.py",
    "tests/test_build_site*.py",
    "tests/test_mutate_diff.py",
)

#: What mutmut prints when no selected test reaches any mutated function;
#: every mutant of the diff is then not observable in process.
NO_TESTS_SENTENCE = "could not find any test case for any mutant"

DEFAULT_BUDGET_S = 2400

#: Lines either side of a changed line whose mutants the lane keeps.
CONTEXT_LINES = 2

#: The variable the matrix sample reads the changed files from
#: (``tests/matrix_sample.py``): a marked file that names one of them, or is
#: one, runs every cell.
MATRIX_CHANGED_ENV = "VERA_MATRIX_CHANGED"

#: The variable the matrix sample reads its seed from (``tests/matrix_sample.py``
#: ``SEED_ENV``).  The lanes name their seed here, never as ``--matrix-seed``:
#: mutmut hands ``pytest_add_cli_args`` to every pytest run it starts, and a
#: run whose plugins do not define that option refuses it (the stats pass of a
#: project with no such plugin, runs 45419776604 and 45419781665).
MATRIX_SEED_ENV = "VERA_MATRIX_SEED"

#: The variable that names the window file for the engine's ``run``.
WINDOW_ENV = "MUTATE_DIFF_WINDOW"

#: The first argument that runs this script as the engine (:func:`engine_main`).
ENGINE_ARG = "--as-engine"

#: The exit status of an engine that cannot apply the window: an engine
#: failure to the lane, never a survivor's 1.
NO_WINDOW_EXIT = 3

#: The engine's ``count`` command (:func:`count_units`): how many mutants
#: mutmut's own visitor makes in each named unit, which the nightly sweep
#: plans its sample from.
COUNT_ARG = "count"

#: The engine's command that shows named mutants' code (:func:`show_mutants`),
#: a name of its own: mutmut's ``show <mutant>``, which the lane asks for a
#: survivor's diff, reaches mutmut unchanged.
SHOW_ARG = "show-mutations"

#: The exit status of a ``count`` the engine could not make.
NO_COUNT_EXIT = 4

#: The variables naming the files ``tests/mutation_oracle.py`` appends the
#: node id of each test it keeps out of the oracle to: one that starts a
#: Python or ``vera`` process, and one that reads the compiler's source.
SKIPS_ENV = "MUTATION_ORACLE_SKIPS"
SOURCE_SKIPS_ENV = "MUTATION_ORACLE_SOURCE_SKIPS"

#: The variable naming the file the plugin appends the node id of each test
#: that fails in mutmut's stats pass or its clean run to: under the fork
#: server those passes run in a child whose pytest output never reaches the
#: log, so the test that stopped the pass is read from here (#1829).
FAILURES_ENV = "MUTATION_ORACLE_FAILURES"

#: The kinds of node (libcst's names) whose mutants mutmut 3.8 places on the
#: node's first line though the text they change can lie below it
#: (``mutation_operators`` in ``mutmut.mutation.mutators``): a call (an
#: argument's ``None`` and its removal, a ``dict`` keyword's rename, a string
#: method's swap after a receiver of several lines), a ``match`` (a ``case``'s
#: removal), an assignment, plain or annotated (its value), an augmented
#: assignment (its operator, after its target), a binary or boolean operation
#: (its operator, after its left operand), a comparison's operator and right
#: operand, which start with the line break before the operator, a
#: conditional expression (its test, after its value) and a lambda (its body).
ENCLOSING_KINDS = ("Call", "Match", "Assign", "AnnAssign", "AugAssign", "BinaryOperation",
                   "BooleanOperation", "ComparisonTarget", "IfExp", "Lambda")


def rule(context: int) -> str:
    """The selection rule's name, as the summary prints it."""
    return (f"the mutants whose node starts within {context} line{'s' if context != 1 else ''} "
            "of a line the diff adds or of a point where it removes lines, or on the first "
            "line of a call, match, assignment, operation, comparison, conditional expression "
            "or lambda that spans one of those lines")

#: Seconds for each short engine command (``results``, ``show``, ``--version``).
ENGINE_CALL_TIMEOUT_S = 300

#: Tests the lane drops from one run before it calls the run stopped short.
MAX_COPY_DROPS = 5

#: What mutmut prints when its stats pass or its clean run of the covering
#: tests stops on a failing test (both run with ``-x``).
_COPY_STOPS = ("failed to collect stats", "Failed to run clean test")

#: The longest ``engine_error`` the lane records (:func:`engine_failure`).
ENGINE_ERROR_CHARS = 500

#: A traceback's frame, as Python prints it: mutmut runs pytest with
#: ``--tb=native``.
_FRAME = re.compile(r'^  File "(?P<file>.+)", line (?P<line>\d+), in (?P<func>.+)$')

#: A file of the installed engine: the ``mutmut`` package.
_ENGINE_FILE = re.compile(r"[\\/](?:site|dist)-packages[\\/](?P<path>mutmut[\\/].+)$")

#: A frame no party's code is in: the standard library (a frozen module, a
#: file under ``lib/pythonX.Y/`` outside the installed packages) or code
#: compiled from a string.
_NEUTRAL_FILE = re.compile(r"^<[^>]*>$|[\\/]lib[\\/]python\d+\.\d+[\\/](?!(?:site|dist)-packages[\\/])")

#: The prefix pytest puts on every line of an exception it reports as its
#: own internal error: a hook raising outside a test's phases, as a stats
#: hook's ``pytest_runtest_makereport`` or ``pytest_runtest_logstart`` would.
_INTERNAL_ERROR = "INTERNALERROR> "

#: pytest's rule, heading a section or a report of its output: a title
#: between runs of one fill character, drawn the terminal's width (80 in
#: mutmut's copy, where both lanes hand the engine ``COLUMNS=80``; one less
#: on Windows), the fill as short as one character either side of a long
#: title.  A line the program printed in that shape, but shorter, is no
#: rule.  The rule that heads what a test printed or logged (``Captured
#: stderr call``) starts a section that runs to the next rule.
_RULE = re.compile(r"^([-_=])\1* .+ \1+$")
_RULE_WIDTH = 79
_CAPTURED = re.compile(r"^-+ Captured .+ -+$")

#: pytest's closing line, the session's counts: bare under ``-q`` (mutmut's
#: runs), between rules otherwise.  A traceback this follows is a report
#: pytest went on from.
_SUMMARY = re.compile(r"^(?:no tests ran|\d+ \w+(?:, \d+ \w+)*) in \d+\.\d+s(?: \(.*\))?$")

#: Python's traceback printer prints a frame repeated in a row three times,
#: then this count of the rest.
_REPEATED = re.compile(r"^\s*\[Previous line repeated (\d+) more times?\]$")

#: A file of what mutmut's copy holds: its tests and the code under test.
_COPY_FILE = re.compile(r"(?:^|[\\/])(?:mutants|tests)[\\/]")

#: A ``RecursionError`` runs out of stack in whatever frame it reached, and
#: inside the copy every call through mutmut's trampoline adds the engine's
#: frames, so it is the engine's only when none of its innermost frames
#: outside the standard library, this many, is the copy's.  A frame printed
#: with a repeat count counts that many more times, up to this many.
RECURSION_FRAMES = 10

#: Survivors whose ``mutmut show`` diff the summary carries: a step summary
#: over 1 MiB is dropped whole.  The record carries every survivor's diff
#: that the show budget reaches.
MAX_SHOWN_SURVIVORS = 60

#: Seconds the lane spends asking the engine for survivors' diffs; a
#: survivor past it is named in the record with
#: :data:`SHOW_BUDGET_NOTE` in place of its diff.
SHOW_BUDGET_S = 300
SHOW_BUDGET_NOTE = "(not shown: the show budget ran out)"

#: The engine's command that lists the window's mutants with their code
#: (:func:`list_window`), from mutmut's visitor alone: no test runs.
LIST_ARG = "list-window"

#: The spinner titles of the engine's phases in its log, and the key each
#: phase's start goes under in a pass's ``phases``.
PHASE_TITLES = (("Running stats", "stats_s"), ("Listing all tests", "listing_s"),
                ("Running clean tests", "clean_s"), ("Running forced fail test", "forced_s"),
                ("Running mutation testing", "mutants_s"))


class DiffError(ValueError):
    """The diff text is not what ``git diff -U0`` prints."""


class ConfigError(ValueError):
    """The scratch tree's ``[tool.mutmut]`` cannot be rewritten."""


class ResultsError(ValueError):
    """``mutmut results`` printed something the lane does not model."""


class NarrowError(ValueError):
    """The narrowing edit would move a line or change a node."""


class LaneError(RuntimeError):
    """A step of the lane outside mutmut failed (git, most often)."""


# ---------------------------------------------------------------------------
# The diff
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FileChange:
    """One file's changes: the head lines a hunk adds (a changed line is
    removed and added), the base lines it removes, and, for each hunk that
    removes lines and adds none, the head line it removes them after."""

    old_path: str | None
    new_path: str | None
    added: frozenset[int]
    removed: frozenset[int]
    deleted_after: frozenset[int] = frozenset()


_HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def _diff_path(spec: str, prefix: str) -> str | None:
    spec = spec.rstrip("\n")
    if spec == "/dev/null":
        return None
    if spec.startswith('"'):
        raise DiffError(f"a quoted path is not supported: {spec}")
    if not spec.startswith(prefix):
        raise DiffError(f"expected a path starting {prefix!r}: {spec}")
    return spec[len(prefix):]


def parse_diff(text: str) -> list[FileChange]:
    """The ``.py`` files of a ``git diff -U0``, with the head lines each
    adds and the base lines each removes."""
    changes: list[FileChange] = []
    section: dict[str, Any] | None = None

    def flush() -> None:
        if section is None:
            return
        path = section["new"] or section["old"]
        if path is not None and path.endswith(".py"):
            changes.append(FileChange(
                old_path=section["old"], new_path=section["new"],
                added=frozenset(section["added"]),
                removed=frozenset(section["removed"]),
                deleted_after=frozenset(section["deleted_after"]),
            ))

    for line in text.splitlines():
        if line.startswith("diff --git "):
            flush()
            match = re.match(r"^diff --git a/(\S+) b/(\S+)$", line)
            if match is None:
                raise DiffError(f"unsupported file header: {line}")
            section = {"old": match.group(1), "new": match.group(2),
                       "added": set(), "removed": set(), "deleted_after": set(),
                       "hunks": False}
            continue
        if section is None:
            if line.startswith("@@"):
                raise DiffError(f"a hunk outside any file section: {line}")
            continue
        if not section["hunks"]:
            if line.startswith("--- "):
                section["old"] = _diff_path(line[4:], "a/")
            elif line.startswith("+++ "):
                section["new"] = _diff_path(line[4:], "b/")
            elif line.startswith("new file mode"):
                section["old"] = None
            elif line.startswith("deleted file mode"):
                section["new"] = None
        hunk = _HUNK.match(line)
        if hunk is not None:
            section["hunks"] = True
            old_start, new_start = int(hunk.group(1)), int(hunk.group(3))
            old_count = 1 if hunk.group(2) is None else int(hunk.group(2))
            new_count = 1 if hunk.group(4) is None else int(hunk.group(4))
            section["removed"].update(range(old_start, old_start + old_count))
            section["added"].update(range(new_start, new_start + new_count))
            if new_count == 0:
                # `+n,0`: the hunk's lines went after head line n.
                section["deleted_after"].add(new_start)
    flush()
    return changes


def window(change: FileChange, context: int = CONTEXT_LINES) -> frozenset[int]:
    """The head lines whose mutants the lane keeps: those within ``context``
    lines of a line the change adds, or of a point where it removes lines
    and adds none (between head lines ``n`` and ``n + 1``)."""
    lines: set[int] = set()
    for line in change.added:
        lines.update(range(line - context, line + context + 1))
    for after in change.deleted_after:
        lines.update(range(after + 1 - context, after + context + 1))
    return frozenset(n for n in lines if n >= 1)


# ---------------------------------------------------------------------------
# Units: the functions mutmut mutates
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Unit:
    """A function mutmut mutates as one, by the name it mangles it to."""

    key: str
    qualname: str
    path: str
    start: int
    end: int
    code: str
    excluded: str | None


class _StripDocstrings(ast.NodeTransformer):
    def _strip(self, node: Any) -> Any:
        self.generic_visit(node)
        body = node.body
        if (body and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant)
                and isinstance(body[0].value.value, str)):
            node.body = body[1:]
        return node

    visit_FunctionDef = visit_AsyncFunctionDef = visit_ClassDef = _strip


def _code(node: ast.AST) -> str:
    """The node's code: its ``ast``, docstrings set aside, positions dropped."""
    copy = ast.parse(ast.unparse(node)).body[0]
    return ast.dump(_StripDocstrings().visit(copy))


def _header_end(lines: Sequence[str], node: ast.FunctionDef | ast.AsyncFunctionDef) -> tuple[int, int | None]:
    """The line that ends a function's header (the one holding its colon at
    bracket depth 0), and the column of a comment on that line, if any."""
    first = node.lineno
    text = "".join(lines[first - 1:node.end_lineno or first])
    depth = 0
    colon_row = None
    try:
        for tok in tokenize.generate_tokens(io.StringIO(text).readline):
            if colon_row is None:
                if tok.type == tokenize.OP and tok.string in "([{":
                    depth += 1
                elif tok.type == tokenize.OP and tok.string in ")]}":
                    depth -= 1
                elif tok.type == tokenize.OP and tok.string == ":" and depth == 0:
                    colon_row = tok.start[0]
            elif tok.start[0] != colon_row:
                break
            elif tok.type == tokenize.COMMENT:
                return first + colon_row - 1, tok.start[1]
    except (tokenize.TokenError, IndentationError, SyntaxError) as exc:
        raise NarrowError(f"cannot read the header of {node.name}: {exc}") from exc
    if colon_row is None:
        raise NarrowError(f"no header colon found for {node.name}")
    return first + colon_row - 1, None


def _header_comment(lines: Sequence[str], node: ast.FunctionDef | ast.AsyncFunctionDef) -> str:
    """The comment on the line that ends the function's header, if any."""
    try:
        row, col = _header_end(lines, node)
    except NarrowError:
        return ""
    return "" if col is None else lines[row - 1][col:].rstrip("\r\n")


def _is_block_pragma(comment: str) -> bool:
    """mutmut's reading of a header comment: ``# pragma: no mutate block``."""
    if "# pragma:" not in comment or "no mutate" not in comment:
        return False
    tail = comment.partition("no mutate")[2].strip()
    words = tail.lstrip(": ").split(",", 1)[0].split()
    return bool(words) and words[0] == "block"


def _excluded(node: ast.FunctionDef | ast.AsyncFunctionDef, lines: Sequence[str]) -> str | None:
    if _is_block_pragma(_header_comment(lines, node)):
        return "pragma"
    if node.name in NEVER_MUTATED:
        return "never mutated"
    decorators = node.decorator_list
    if decorators and not (len(decorators) == 1 and isinstance(decorators[0], ast.Name)
                           and decorators[0].id in LONE_DECORATORS):
        return "decorated"
    return None


def scan_units(source: str, path: str = "") -> dict[str, Unit]:
    """Every unit mutmut mutates in ``source``, keyed by its mangled name."""
    lines = source.splitlines(keepends=True)
    units: dict[str, Unit] = {}
    for node, cls in _unit_nodes(ast.parse(source)):
        key = _key(node.name, cls)
        start = min([d.lineno for d in node.decorator_list] + [node.lineno])
        units[key] = Unit(
            key=key, qualname=f"{cls}.{node.name}" if cls else node.name,
            path=path, start=start, end=node.end_lineno or node.lineno,
            code=_code(node), excluded=_excluded(node, lines),
        )
    return units


def _unit_nodes(tree: ast.Module) -> list[tuple[ast.FunctionDef | ast.AsyncFunctionDef, str | None]]:
    """The module's units, each with its class: its top-level functions and
    the methods of its top-level classes, the ones mutmut mutates."""
    found: list[tuple[ast.FunctionDef | ast.AsyncFunctionDef, str | None]] = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            found.append((node, None))
        elif isinstance(node, ast.ClassDef):
            found += [(m, node.name) for m in node.body
                      if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))]
    return found


def _key(name: str, cls: str | None) -> str:
    """mutmut's mangled name for a function or a method."""
    return f"x{SEP}{cls}{SEP}{name}" if cls else f"x_{name}"


@dataclass
class FileVerdict:
    """What one file's change does to its units."""

    path: str
    changed: list[Unit]
    deleted: list[str]
    outside: list[int]
    unchanged_code: list[str]
    outside_removed: list[int] = field(default_factory=list)


def _is_code(lines: Sequence[str], number: int) -> bool:
    """Whether a source line holds code: not blank and not a comment alone."""
    text = lines[number - 1].strip() if 0 < number <= len(lines) else ""
    return bool(text) and not text.startswith("#")


def classify(change: FileChange, base_src: str | None, head_src: str | None) -> FileVerdict:
    """Map the change's lines to units, and keep the units whose code changed.

    An added line belongs to the head unit that holds it, and a removed line
    to the base unit that held it: lines removed from a function's end leave
    no head line inside it, so only the base side names the function."""
    base_units = scan_units(base_src, change.old_path or "") if base_src is not None else {}
    if head_src is None:
        return FileVerdict(path=change.old_path or "", changed=[],
                           deleted=[u.qualname for u in base_units.values()],
                           outside=[], unchanged_code=[])
    path = change.new_path or ""
    head_units = scan_units(head_src, path)
    head_lines = head_src.splitlines()
    base_lines = base_src.splitlines() if base_src is not None else []
    spans = sorted(head_units.values(), key=lambda u: u.start)
    base_spans = sorted(base_units.values(), key=lambda u: u.start)
    touched: set[str] = set()
    outside: list[int] = []
    outside_removed: list[int] = []
    for line in sorted(change.added):
        unit = next((u for u in spans if u.start <= line <= u.end), None)
        if unit is not None:
            touched.add(unit.key)
        elif _is_code(head_lines, line):
            outside.append(line)
    for line in sorted(change.removed):
        unit = next((u for u in base_spans if u.start <= line <= u.end), None)
        if unit is not None:
            if unit.key in head_units:
                touched.add(unit.key)
        elif _is_code(base_lines, line):
            outside_removed.append(line)
    changed: list[Unit] = []
    unchanged: list[str] = []
    for unit in spans:
        if unit.key not in touched:
            continue
        before = base_units.get(unit.key)
        if before is not None and before.code == unit.code:
            unchanged.append(unit.qualname)
        else:
            changed.append(unit)
    deleted = [u.qualname for k, u in base_units.items() if k not in head_units]
    return FileVerdict(path=path, changed=changed, deleted=deleted, outside=outside,
                       unchanged_code=unchanged, outside_removed=outside_removed)


# ---------------------------------------------------------------------------
# mutmut's names
# ---------------------------------------------------------------------------


def module_name(path: str) -> str:
    """``vera/smt.py`` -> ``vera.smt``; a package's ``__init__.py`` is the package."""
    parts = path.removesuffix(".py").split("/")
    if parts[-1] == "__init__":
        parts = parts[:-1]
    return ".".join(parts)


def mutant_glob(path: str, key: str) -> str:
    """The glob that selects one unit's mutants and no other unit's."""
    return f"{module_name(path)}.{key}__mutmut_*"


def first_mutant(path: str, key: str) -> str:
    """The name of one unit's first window mutant, which the lane's first
    pass hands mutmut for each changed unit.  mutmut reads the clean run's
    tests off the names it is handed (``tests_for_mutant_names``): a name
    adds its function's covering tests, where a glob, matched against the
    functions' names, which hold no ``__mutmut_``, adds none, and a run of
    globs alone runs the whole selection clean (#1838).  A unit whose window
    holds no mutant has no such mutant, and the name selects nothing."""
    return f"{module_name(path)}.{key}__mutmut_1"


def unit_of_mutant(name: str) -> tuple[str, str]:
    """A mutant's (module, unit key)."""
    mangled = name.partition("__mutmut_")[0]
    parts = mangled.split(".")
    for i in range(len(parts) - 1, -1, -1):
        if parts[i].startswith(("x_", f"x{SEP}")):
            return ".".join(parts[:i]), ".".join(parts[i:])
    raise ResultsError(f"not a mutmut mutant name: {name}")


def _mutant_number(name: str) -> int:
    return int(name.rpartition("__mutmut_")[2])


# ---------------------------------------------------------------------------
# The scratch tree
# ---------------------------------------------------------------------------


def narrow(source: str, keep: Iterable[str]) -> str:
    """``source`` with ``# pragma: no mutate block`` on every unit not kept.

    The comment goes where mutmut reads a header's pragma: after the colon
    that ends the header, or at the end of a one-line ``def``, ahead of a
    comment already there.  A unit already under the block pragma is left
    as it is.  Only comments are added, which the result's ``ast`` and line
    count are checked for."""
    keep = set(keep)
    lines = source.splitlines(keepends=True)
    for node, cls in _unit_nodes(ast.parse(source)):
        if _key(node.name, cls) in keep:
            continue
        row, col = _header_end(lines, node)
        line = lines[row - 1]
        text = line.rstrip("\r\n")
        newline = line[len(text):]
        if col is None:
            lines[row - 1] = f"{text.rstrip()}  {PRAGMA}{newline}"
        elif not _is_block_pragma(text[col:]):
            lines[row - 1] = f"{text[:col]}{PRAGMA}  {text[col:]}{newline}"
    out = "".join(lines)
    if out.count("\n") != source.count("\n"):
        raise NarrowError("the narrowing edit moved a line")
    try:
        narrowed = ast.parse(out)
    except SyntaxError as exc:
        raise NarrowError(f"the narrowing edit broke the syntax: {exc}") from exc
    if ast.dump(narrowed) != ast.dump(ast.parse(source)):
        raise NarrowError("the narrowing edit changed a node")
    return out


def _toml_value(value: Any) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return repr(value)
    if isinstance(value, str):
        return json.dumps(value)
    if isinstance(value, list):
        return "[\n" + "".join(f"    {_toml_value(v)},\n" for v in value) + "]"
    raise ConfigError(f"a [tool.mutmut] value the rewrite does not model: {value!r}")


def rewrite_config(text: str, *, only_mutate: Sequence[str], extra_tests: Sequence[str],
                   extra_args: Sequence[str] = (), also_copy: Sequence[str] | None = None,
                   selection: Sequence[str] | None = None) -> str:
    """``text`` with ``[tool.mutmut]``'s ``only_mutate`` replaced, its test
    selection replaced by ``selection`` when given, ``extra_tests`` added to
    the selection and ``extra_args`` to its pytest arguments, and
    ``also_copy`` replaced when given; everything else unchanged."""
    data = tomllib.loads(text)
    cfg = data.get("tool", {}).get("mutmut")
    if not isinstance(cfg, dict):
        raise ConfigError("pyproject.toml has no [tool.mutmut] table")
    new = dict(cfg)
    new["only_mutate"] = list(only_mutate)
    if also_copy is not None:
        new["also_copy"] = list(also_copy)
    tests = list(cfg.get("pytest_add_cli_args_test_selection", []) if selection is None else selection)
    tests += [t for t in extra_tests if t not in tests]
    new["pytest_add_cli_args_test_selection"] = tests
    if extra_args:
        new["pytest_add_cli_args"] = list(cfg.get("pytest_add_cli_args", [])) + list(extra_args)
    section = "[tool.mutmut]\n" + "".join(
        f"{key} = {_toml_value(value)}\n" for key, value in new.items()) + "\n"
    match = re.search(r"(?ms)^\[tool\.mutmut\][ \t]*\n.*?(?=^\[|\Z)", text)
    if match is None:
        raise ConfigError("cannot find the [tool.mutmut] table's text")
    out = text[:match.start()] + section + text[match.end():]
    expected = dict(data)
    expected["tool"] = {**data["tool"], "mutmut": new}
    if tomllib.loads(out) != expected:
        raise ConfigError("the rewritten pyproject.toml does not read back as intended")
    return out


#: Variables that point git at a repository other than ``-C``'s: a git hook
#: sets them, and ``--repo`` is the repository the lane reads.
_GIT_LOCATORS = ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR")


def _git_env() -> dict[str, str]:
    return {k: v for k, v in os.environ.items() if k not in _GIT_LOCATORS}


def _git(repo: Path, *args: str) -> str:
    result = subprocess.run(["git", "-C", str(repo), *args], capture_output=True,
                            text=True, encoding="utf-8", env=_git_env(), check=False)
    if result.returncode != 0:
        raise LaneError(f"git {' '.join(args)} failed: {result.stderr.strip()}")
    return result.stdout


def _extract(repo: Path, rev: str, dest: Path) -> None:
    archive = subprocess.run(["git", "-C", str(repo), "archive", "--format=tar", rev],
                             capture_output=True, env=_git_env(), check=False)
    if archive.returncode != 0:
        raise LaneError(f"git archive {rev} failed: {archive.stderr.decode('utf-8', 'replace')}")
    with tarfile.open(fileobj=io.BytesIO(archive.stdout)) as tar:
        tar.extractall(dest, filter="data")


def _imports(source: str) -> set[str]:
    """The modules a source imports, anywhere in it, ``tests.<x>`` for a
    name imported from the ``tests`` package or relative to it."""
    found: set[str] = set()
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.Import):
            found |= {alias.name for alias in node.names}
        elif isinstance(node, ast.ImportFrom):
            module = node.module or ""
            if node.level == 1:
                module = f"tests.{module}" if module else "tests"
            elif node.level:
                continue
            found.add(module)
            if module == "tests":
                found |= {f"tests.{alias.name}" for alias in node.names}
    return found


def _names_vera(modules: Iterable[str]) -> bool:
    return any(m == "vera" or m.startswith("vera.") for m in modules)


def reaches_compiler(source: str, helpers: Mapping[str, str]) -> bool:
    """Whether a test module imports the compiler, directly or through one
    of the ``tests/`` helper modules in ``helpers`` (name -> source)."""
    modules = _imports(source)
    if _names_vera(modules):
        return True
    for module in modules:
        parts = module.split(".")
        if len(parts) >= 2 and parts[0] == "tests" and parts[1] in helpers:
            if _names_vera(_imports(helpers[parts[1]])):
                return True
    return False


def oracle_tests(changed: Iterable[str], tree: Path) -> tuple[list[str], list[str]]:
    """The changed test files that join the selection, and the ones left out.

    A file joins when it is a ``tests/test_*.py`` module that reaches the
    compiler in process (it imports ``vera``, directly or through a helper)
    and is not one of the families the repository's selection leaves out
    on purpose (``NOT_ORACLE``)."""
    helpers = {p.stem: p.read_text(encoding="utf-8")
               for p in sorted((tree / "tests").glob("*.py")) if not p.name.startswith("test_")}
    joined: list[str] = []
    left: list[str] = []
    for path in sorted(set(changed)):
        if not (fnmatch.fnmatch(path, "tests/test_*.py") and "/" not in path.removeprefix("tests/")):
            continue
        if any(fnmatch.fnmatch(path, pattern) for pattern in NOT_ORACLE):
            left.append(path)
            continue
        source = (tree / path).read_text(encoding="utf-8")
        (joined if reaches_compiler(source, helpers) else left).append(path)
    return joined, left


# ---------------------------------------------------------------------------
# The declared oracle
# ---------------------------------------------------------------------------


#: The rule a module's declared oracle is read by, as records and the
#: sweep's state name it: a change to the rule starts a new cycle.
ORACLE_RULE = "marker+name+family/1"

#: The variable naming the oracle map (:func:`oracle_map`) to
#: ``tests/mutation_oracle.py``, which takes each test out of mutmut's
#: record for every function whose module's oracle does not hold its file.
ORACLE_MAP_ENV = "MUTATION_ORACLE_MAP"

#: The families of a module's declared oracle, beyond the class instruments
#: whose ``matrix`` marker names it and the test files named after it: a
#: module glob, and the test files (globs) every module it matches holds.
#: MUTATION.md § Oracle renders this table (:func:`family_table`); a module
#: entry of one file names the admitted test files that import that module,
#: where no instrument names it and no file is named after it.
ORACLE_FAMILIES: tuple[tuple[tuple[str, ...], tuple[str, ...]], ...] = (
    (("vera/verifier.py", "vera/smt.py"), ("tests/test_verifier_*.py", "tests/test_obligations.py")),
    (("vera/checker/*",), ("tests/test_checker_*.py",)),
    (("vera/obligations/*",), ("tests/test_obligations.py", "tests/test_lsp.py")),
    (("vera/codegen/*", "vera/wasm/*"), ("tests/test_codegen*.py", "tests/test_wasm*.py")),
    (("vera/lsp/*",), ("tests/test_lsp*.py",)),
    (("vera/browser/emit.py",), ("tests/test_family_naming.py", "tests/test_per_owner_adt_identity_1317.py")),
    (("vera/markdown_grammar.py",), ("tests/test_markdown.py",)),
    (("vera/carriers.py",), ("tests/test_binder_position_generator.py",
                             "tests/test_boundary_guard_correctness_1466.py",
                             "tests/test_element_facts_statable_1430.py")),
    (("vera/envflags.py", "vera/runtime/text.py"), ("tests/test_runtime_traps.py",)),
    (("vera/module_view.py",), ("tests/test_module_environment_1493.py",
                                "tests/test_adt_membership_scope_1253.py",
                                "tests/test_warning_severity_1513.py")),
    (("vera/regularity.py",), ("tests/test_nonregular_data_rejected_1429.py",)),
    (("vera/runtime/__init__.py",), ("tests/test_secret_redaction_1854.py",)),
    (("vera/runtime/server.py",), ("tests/test_serve.py", "tests/test_handler_signature_1442.py",
                                   "tests/test_named_traps_1479.py")),
    (("vera/skip.py",), ("tests/test_codegen*.py", "tests/test_closure_boundary_widths_1255_1256_1269.py",
                         "tests/test_declared_widths_1525.py", "tests/test_emitted_checks_1479.py",
                         "tests/test_duplicate_names_1433.py", "tests/test_gc_mark_width_1510.py",
                         "tests/test_obligation_table_1695.py")),
    (("vera/slots.py",), ("tests/test_evaluated_position_obligations_1480.py",
                          "tests/test_naming_env_provenance_1208.py",
                          "tests/test_slot_naming_blast_radius.py")),
)

#: The modules with a function mutmut mutates and no declared oracle, each
#: with why.  The sweep decides their mutants ``undeclared`` and runs none;
#: the diff lane names a changed function of one in its row and headline and
#: runs none of its mutants.  A self-test holds every entry still undeclared
#: and every undeclared module listed.
UNDECLARED: dict[str, str] = {
    "vera/__init__.py": ("its one function reads the installed version while the package is "
                         "imported, so no mutant of it runs after mutmut's fork"),
}


def matrix_decides(source: str) -> list[str] | None:
    """The modules a test file's ``pytestmark`` ``matrix`` marker names in
    ``decides=``, read from its syntax tree, a marker over several lines
    included; None for a file with no such marker."""
    for node in ast.parse(source).body:
        if isinstance(node, ast.Assign):
            targets, value = node.targets, node.value
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            targets, value = [node.target], node.value
        else:
            continue
        if not any(isinstance(t, ast.Name) and t.id == "pytestmark" for t in targets):
            continue
        for part in ast.walk(value):
            if (isinstance(part, ast.Call) and isinstance(part.func, ast.Attribute)
                    and part.func.attr == "matrix"):
                for keyword in part.keywords:
                    if keyword.arg == "decides":
                        value = ast.literal_eval(keyword.value)
                        return [value] if isinstance(value, str) else [str(v) for v in value]
                return []
    return None


def named_tests(module: str, tests: Iterable[str]) -> list[str]:
    """The test files named after ``module``: ``tests/test_<stem>.py`` and
    ``tests/test_<stem>_*.py``, and in a package also
    ``tests/test_<package>_<stem>[_*].py``; a package's ``__init__.py`` is
    named by ``tests/test_<package>.py``."""
    parts = module.removeprefix("vera/").removesuffix(".py").split("/")
    stem, package = parts[-1], parts[-2] if len(parts) > 1 else None
    found: list[str] = []
    for test in tests:
        body = test.removeprefix("tests/test_").removesuffix(".py")
        if stem == "__init__":
            if package is not None and body == package:
                found.append(test)
            continue
        names = [stem] + ([f"{package}_{stem}"] if package is not None else [])
        if any(body == name or body.startswith(name + "_") for name in names):
            found.append(test)
    return sorted(found)


def family_tests(module: str, tests: Iterable[str]) -> list[str]:
    """The test files :data:`ORACLE_FAMILIES` gives ``module``."""
    globs = [g for modules, files in ORACLE_FAMILIES
             if any(fnmatch.fnmatch(module, m) for m in modules) for g in files]
    return sorted(t for t in tests if any(fnmatch.fnmatch(t, g) for g in globs))


def oracle_map(tree: Path) -> dict[str, Any]:
    """Each module's declared oracle under ``tree``: the admitted test files
    (:func:`oracle_tests`) whose ``matrix`` marker names it, the ones named
    after it, and its families (:data:`ORACLE_FAMILIES`).  ``{"rule":
    ORACLE_RULE, "modules": {path: [test file, ...]}}``, every ``vera/``
    module a key, an undeclared one's list empty."""
    tests = sorted(p.relative_to(tree).as_posix() for p in (tree / "tests").glob("test_*.py"))
    admitted, _ = oracle_tests(tests, tree)
    decides = {t: matrix_decides((tree / t).read_text(encoding="utf-8")) or [] for t in admitted}
    modules: dict[str, list[str]] = {}
    for path in sorted(p.relative_to(tree).as_posix() for p in (tree / "vera").rglob("*.py")):
        files = {t for t, named in decides.items() if path in named}
        files |= set(named_tests(path, admitted)) | set(family_tests(path, admitted))
        modules[path] = sorted(files)
    return {"rule": ORACLE_RULE, "modules": modules}


def oracle_of(oracle: Mapping[str, Any], modules: Iterable[str]) -> list[str]:
    """The union of ``modules``' declared oracles in the map ``oracle``."""
    return sorted({t for m in modules for t in oracle["modules"].get(m, [])})


def has_units(source: str) -> bool:
    """Whether a module holds a function mutmut mutates."""
    return any(u.excluded is None for u in scan_units(source).values())


def family_table() -> str:
    """MUTATION.md § Oracle's family table, rendered from
    :data:`ORACLE_FAMILIES`."""
    rows = ["| Modules | Test files |", "|---|---|"]
    for modules, files in ORACLE_FAMILIES:
        rows.append(f"| {', '.join(f'`{m}`' for m in modules)} | {', '.join(f'`{f}`' for f in files)} |")
    return "\n".join(rows) + "\n"


# ---------------------------------------------------------------------------
# The window, inside the engine
# ---------------------------------------------------------------------------


class WindowError(RuntimeError):
    """The installed mutmut cannot generate only the window's mutants."""


def enclosing_spans(source: str) -> list[tuple[int, int]]:
    """The first and last line of every node of :data:`ENCLOSING_KINDS` in
    ``source``, by the position provider mutmut's visitor reads a node's
    start line from."""
    import libcst as cst
    from libcst.metadata import MetadataWrapper, PositionProvider

    kinds = tuple(getattr(cst, name) for name in ENCLOSING_KINDS)
    positions = MetadataWrapper(cst.parse_module(source), unsafe_skip_copy=True).resolve(
        PositionProvider)
    return sorted((p.start.line, p.end.line) for node, p in positions.items()
                  if isinstance(node, kinds))


def first_lines(spans: Iterable[tuple[int, int]], lines: Iterable[int]) -> frozenset[int]:
    """The first line of each span that holds one of ``lines``: the line
    mutmut places the mutants of a node of :data:`ENCLOSING_KINDS` on, when
    the text they change can lie on one of ``lines``."""
    ordered = sorted(set(lines))
    found: set[int] = set()
    for first, last in spans:
        at = bisect.bisect_left(ordered, first)
        if at < len(ordered) and ordered[at] <= last:
            found.add(first)
    return frozenset(found)


def _unit_counts(create_mutations: Callable[..., Any], path: str, source: str,
                 lines: Iterable[int] | None) -> Counter[str]:
    """How many mutants mutmut's own visitor makes in each unit of
    ``source``, of every line or of ``lines`` alone: a mutation counts for the
    top-level function or top-level class's method that holds it, the ones
    mutmut writes a copy of each mutant for (``_compute_mutated_function_hashes``
    indexes them the same way)."""
    import libcst as cst

    module, mutations, _classes, _functions = create_mutations(
        path, source, None if lines is None else set(lines))
    keys: dict[Any, str] = {}
    for stmt in module.body:
        if isinstance(stmt, cst.FunctionDef):
            keys[stmt] = _key(stmt.name.value, None)
        elif isinstance(stmt, cst.ClassDef) and isinstance(stmt.body, cst.IndentedBlock):
            keys.update({m: _key(m.name.value, stmt.name.value) for m in stmt.body.body
                         if isinstance(m, cst.FunctionDef)})
    return Counter(keys[m.contained_by_top_level_function] for m in mutations
                   if m.contained_by_top_level_function in keys)


def install_window(engine: Any, window_file: Path) -> None:
    """Make the engine module ``engine`` (``mutmut.__main__``) generate only
    the mutants the window keeps, and write the counts the lane checks it by.

    mutmut generates a mutant only for a node that starts on a line its
    covered-lines hook names (``get_covered_lines_for_file``, the filter
    ``mutate_only_covered_lines`` feeds); the hook here names each narrowed
    file's window, and leaves every other file to the hook it replaces.  The
    window is the lines the lane names and the first line of each node of
    :data:`ENCLOSING_KINDS` that spans one of them (:func:`first_lines`),
    unless the window is ``exact``: the nightly sweep names the lines mutmut
    places mutants on (:func:`count_units`), and takes those alone.  Before
    that, each file's mutants are counted per unit by mutmut's own visitor,
    of every line and of the window's (:func:`_unit_counts`), so the lane
    can check what the engine generated against the window.  A mutmut
    without the hook or the visitor raises :class:`WindowError`."""
    spec = json.loads(window_file.read_text(encoding="utf-8"))
    exact = bool(spec.get("exact", False))
    hook = getattr(engine, "get_covered_lines_for_file", None)
    if not callable(hook):
        raise WindowError("mutmut.__main__ has no get_covered_lines_for_file, the hook mutmut 3.8 "
                          "reads the lines to mutate from, so the window cannot reach its generator")
    try:
        from mutmut.mutation.file_mutation import create_mutations
    except ImportError as exc:
        raise WindowError(f"mutmut's visitor is not there to count the window by: {exc}") from exc
    kept: dict[str, frozenset[int]] = {}
    counts: dict[str, dict[str, dict[str, int]]] = {}
    for path, named in spec["lines"].items():
        source = Path(path).read_text(encoding="utf-8")
        lines = kept[path] = (frozenset(named) if exact
                              else frozenset(named) | first_lines(enclosing_spans(source), named))
        held = _unit_counts(create_mutations, path, source, None)
        inside = _unit_counts(create_mutations, path, source, lines)
        counts[path] = {key: {"held": held[key], "window": inside[key]}
                        for key in sorted(set(held) | set(inside))}
        if path in spec.get("changed", {}):
            # Which of each unit's window mutants sit on no changed line:
            # the window's neighbours, which do not gate the pull request.
            for key, numbers in neighbour_numbers(path, source, lines, spec["changed"][path],
                                                  spec.get("removed_after", {}).get(path, [])).items():
                counts[path].setdefault(key, {"held": held[key], "window": inside[key]})["neighbours"] = numbers
    Path(spec["record"]).write_text(json.dumps({"files": counts}, indent=1) + "\n", encoding="utf-8")

    def covered(filename: str, covered_lines: Any) -> Any:
        lines = kept.get(Path(filename).as_posix())
        return hook(filename, covered_lines) if lines is None else set(lines)

    engine.get_covered_lines_for_file = covered


def _unit_line_counts(path: str, source: str) -> dict[str, dict[int, int]]:
    """How many mutants mutmut's own visitor makes in each unit of
    ``source``, by the line it places them on: the mutated node's first
    line, the line its covered-lines hook reads a node against.  mutmut's
    ``create_mutations`` run step by step with its metadata kept, so each
    mutation's node resolves to a position; the same visitor over the same
    module, so the counts are the ones ``mutmut run`` generates."""
    import libcst as cst
    from libcst.metadata import MetadataWrapper, PositionProvider
    from mutmut.mutation.file_mutation import MutationVisitor
    from mutmut.mutation.mutators import mutation_operators
    from mutmut.mutation.pragma_handling import get_ignored_lines

    wrapper = MetadataWrapper(cst.parse_module(source))
    visitor = MutationVisitor(mutation_operators, get_ignored_lines(path, source, wrapper, None), None)
    wrapper.visit(visitor)
    positions = wrapper.resolve(PositionProvider)
    keys: dict[Any, str] = {}
    for stmt in wrapper.module.body:
        if isinstance(stmt, cst.FunctionDef):
            keys[stmt] = _key(stmt.name.value, None)
        elif isinstance(stmt, cst.ClassDef) and isinstance(stmt.body, cst.IndentedBlock):
            keys.update({m: _key(m.name.value, stmt.name.value) for m in stmt.body.body
                         if isinstance(m, cst.FunctionDef)})
    counts: dict[str, dict[int, int]] = {}
    for mutation in visitor.mutations:
        key = keys.get(mutation.contained_by_top_level_function)
        if key is None:
            continue
        line = positions[mutation.original_node].start.line
        by_line = counts.setdefault(key, {})
        by_line[line] = by_line.get(line, 0) + 1
    return counts


def count_units(request: str) -> str:
    """The engine's ``count`` command: for each file of ``request`` (JSON,
    ``{"sources": {path: source}, "units": {path: [key, ...]}}``), how many
    mutants mutmut's own visitor makes in each named unit of its source and
    on which lines, as JSON ``{path: {key: {"mutants": n, "lines": {line:
    k}}}}``, zero and no lines for a unit it makes none in.  The count is
    the one ``mutmut run`` generates: a unit's mutants are ``<key>__mutmut_1``
    to ``<key>__mutmut_n`` in the copy, and with a window of its lines
    (:func:`install_window`) the mutants on those lines alone, numbered from
    one in the order of the lines."""
    data = json.loads(request)
    sources, units = data["sources"], data["units"]
    counts: dict[str, dict[str, dict[str, Any]]] = {}
    for path, keys in units.items():
        by_line = _unit_line_counts(path, sources[path])
        counts[path] = {}
        for key in keys:
            lines = by_line.get(str(key), {})
            counts[path][str(key)] = {"mutants": sum(lines.values()),
                                      "lines": {str(line): n for line, n in sorted(lines.items())}}
    return json.dumps(counts)


def show_mutants(request: str) -> str:
    """The engine's ``show`` command: for each named mutant of ``request``
    (JSON, ``{"sources": {path: source}, "mutants": {path: {key: [n, ...]}}}``,
    ``n`` the number mutmut gives a mutant in a run over the whole unit), the
    code mutmut's own visitor changes and what it changes it to, as JSON
    ``{path: {key: {n: {"line": l, "original": text, "mutated": text}}}}``.
    mutmut numbers a unit's mutants from one in the order its visitor makes
    them (``mutmut.mutation.file_mutation``), the order :func:`_unit_line_counts`
    counts them in; a number past the unit's mutants is left out."""
    import libcst as cst
    from libcst.metadata import MetadataWrapper, PositionProvider
    from mutmut.mutation.file_mutation import MutationVisitor
    from mutmut.mutation.mutators import mutation_operators
    from mutmut.mutation.pragma_handling import get_ignored_lines

    data = json.loads(request)
    shown: dict[str, dict[str, dict[str, Any]]] = {}
    for path, wanted in data["mutants"].items():
        source = data["sources"][path]
        wrapper = MetadataWrapper(cst.parse_module(source))
        visitor = MutationVisitor(mutation_operators, get_ignored_lines(path, source, wrapper, None), None)
        wrapper.visit(visitor)
        positions = wrapper.resolve(PositionProvider)
        keys: dict[Any, str] = {}
        for stmt in wrapper.module.body:
            if isinstance(stmt, cst.FunctionDef):
                keys[stmt] = _key(stmt.name.value, None)
            elif isinstance(stmt, cst.ClassDef) and isinstance(stmt.body, cst.IndentedBlock):
                keys.update({m: _key(m.name.value, stmt.name.value) for m in stmt.body.body
                             if isinstance(m, cst.FunctionDef)})
        by_key: dict[str, list[Any]] = {}
        for mutation in visitor.mutations:
            key = keys.get(mutation.contained_by_top_level_function)
            if key is not None:
                by_key.setdefault(key, []).append(mutation)

        def text(node: Any) -> str:
            return wrapper.module.code_for_node(node) if isinstance(node, cst.CSTNode) else ""

        shown[path] = {}
        for key, numbers in wanted.items():
            made = by_key.get(str(key), [])
            shown[path][str(key)] = {
                str(n): {"line": positions[made[n - 1].original_node].start.line,
                         "original": text(made[n - 1].original_node),
                         "mutated": text(made[n - 1].mutated_node)}
                for n in (int(v) for v in numbers) if 1 <= n <= len(made)}
    return json.dumps(shown)


def touched_lines(original: Any, mutated: Any, positions: Mapping[Any, Any]) -> frozenset[int]:
    """The lines a mutation is on: its node's first line, and the first line
    of each child of the node it removes or replaces (one the mutated node
    does not hold), the rule mutmut reads an ignored line by."""
    import libcst as cst

    lines = {positions[original].start.line}
    kept = mutated.children if isinstance(mutated, cst.CSTNode) else []
    for child in original.children:
        if not any(child is k for k in kept) and child in positions:
            lines.add(positions[child].start.line)
    return frozenset(lines)


def neighbour_numbers(path: str, source: str, lines: Iterable[int],
                      changed: Iterable[int], removed_after: Iterable[int] = ()) -> dict[str, list[int]]:
    """For each unit, the numbers the window's run gives its mutants (from
    one, in the order mutmut's visitor makes them over ``lines``) that are on
    no ``changed`` line (:func:`touched_lines`) and whose node spans no point
    the diff removed lines after (``removed_after``: a node that lost a line,
    such as an operand of a condition over several lines, is the diff's
    own): the mutants the two-line window pulled in from the lines around
    the diff's own.  A whole statement removed leaves no node spanning its
    point, so the mutants around it are neighbours."""
    import libcst as cst
    from libcst.metadata import MetadataWrapper, PositionProvider
    from mutmut.mutation.file_mutation import MutationVisitor
    from mutmut.mutation.mutators import mutation_operators
    from mutmut.mutation.pragma_handling import get_ignored_lines

    wanted = frozenset(changed)
    points = sorted(set(removed_after))
    wrapper = MetadataWrapper(cst.parse_module(source))
    visitor = MutationVisitor(mutation_operators, get_ignored_lines(path, source, wrapper, None), set(lines))
    wrapper.visit(visitor)
    positions = wrapper.resolve(PositionProvider)
    keys: dict[Any, str] = {}
    for stmt in wrapper.module.body:
        if isinstance(stmt, cst.FunctionDef):
            keys[stmt] = _key(stmt.name.value, None)
        elif isinstance(stmt, cst.ClassDef) and isinstance(stmt.body, cst.IndentedBlock):
            keys.update({m: _key(m.name.value, stmt.name.value) for m in stmt.body.body
                         if isinstance(m, cst.FunctionDef)})
    made: dict[str, int] = {}
    out: dict[str, list[int]] = {}
    for mutation in visitor.mutations:
        key = keys.get(mutation.contained_by_top_level_function)
        if key is None:
            continue
        made[key] = made.get(key, 0) + 1
        out.setdefault(key, [])
        span = positions[mutation.original_node]
        if (not touched_lines(mutation.original_node, mutation.mutated_node, positions) & wanted
                and not any(span.start.line <= p < span.end.line for p in points)):
            out[key].append(made[key])
    return out


def read_window_neighbours(path: Path) -> dict[tuple[str, str], frozenset[int]]:
    """The engine's neighbours of each unit (:func:`neighbour_numbers`), by
    ``(path, key)``; none where it wrote none, so every survivor gates."""
    try:
        files = json.loads(path.read_text(encoding="utf-8"))["files"]
        return {(file, key): frozenset(int(n) for n in rec.get("neighbours", []))
                for file, units in files.items() for key, rec in units.items()}
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        return {}


#: The variable naming the file ``tests/mutation_oracle.py`` appends each
#: mutant's first failing test to.
KILLERS_ENV = "MUTATION_ORACLE_KILLERS"
#: The diff lane's second look at its survivors on the diff's own lines
#: (:func:`full_cell_probe`): the seconds of the budget kept back from the
#: engine for it, and the most one survivor's probe may take.
FULL_PROBE_RESERVE_S = 600.0
FULL_PROBE_CAP_S = 300.0


def run_probe(mutants_dir: Path, mutants: Sequence[str], tests: Sequence[str], pytest_args: Sequence[str],
              env: Mapping[str, str], budget_s: float, killers_file: Path, *, cap_s: float,
              run: Callable[..., Any] = subprocess.run, drop: Iterable[str] = (),
              what: str = "the probe's tests", out_of_time: str = "not named: the time for probes ran out",
              ) -> dict[str, str]:
    """Each mutant's killer: pytest run in the engine's generated tree with
    the mutant active (``MUTANT_UNDER_TEST``, as mutmut runs one) over
    ``tests``, stopping at the first failure, which the oracle plugin names
    (``KILLERS_ENV``).  No mutmut run, so no stats pass: a probe costs the
    tests up to its killer, at most ``cap_s``, all of them at most
    ``budget_s``.  A killer counts only when that test, run alone in the
    same tree with no mutant active, passes (:func:`_passes_alone`, once a
    test).  A mutant no test fails is named why, as ``not ...``; the
    variables in ``drop`` are not passed on."""
    out: dict[str, str] = {}
    started = time.monotonic()
    leave = set(drop)
    baseline: dict[str, bool] = {}
    for name in mutants:
        left = budget_s - (time.monotonic() - started)
        if left <= 1:
            out[name] = out_of_time
            continue
        child = {k: v for k, v in env.items() if k not in leave}
        child.update({"MUTANT_UNDER_TEST": name, KILLERS_ENV: str(killers_file), "PYTHONPATH": str(mutants_dir)})
        try:
            done = run([sys.executable, "-m", "pytest", "-x", "-q", "-p", "no:cacheprovider", *pytest_args, *tests],
                       cwd=str(mutants_dir), env=child, capture_output=True, text=True, encoding="utf-8",
                       errors="replace", timeout=min(cap_s, left), check=False)
            code = done.returncode
        except subprocess.TimeoutExpired:
            code = None
        named: dict[str, str] = {}
        if killers_file.exists():
            for line in killers_file.read_text(encoding="utf-8", errors="replace").splitlines():
                mutant, _, nodeid = line.partition("\t")
                if mutant and nodeid:
                    named.setdefault(mutant, nodeid)
        if name in named:
            # A killer counts only if it passes with no mutant active: a test
            # red in the copy for a reason of its own kills nothing.
            nodeid = named[name]
            if nodeid not in baseline:
                baseline[nodeid] = _passes_alone(mutants_dir, nodeid, pytest_args, env, leave, run)
            out[name] = (nodeid if baseline[nodeid]
                         else f"not named: its only failing test fails with no mutant active ({nodeid})")
        elif code is None:
            out[name] = f"not named: no test failed in the probe's {min(cap_s, left):.0f} s"
        elif code == 0:
            out[name] = f"not named: no test of {what} fails with it"
        else:
            out[name] = f"not named: the probe exited {code} with no test failing"
    return out


#: The most seconds a named killer's run with no mutant active may take.
BASELINE_CAP_S = 120.0


def _passes_alone(mutants_dir: Path, nodeid: str, pytest_args: Sequence[str], env: Mapping[str, str],
                  leave: Iterable[str], run: Callable[..., Any]) -> bool:
    """Whether test ``nodeid`` passes alone in the generated tree, with the
    probe's arguments and no mutant active, within ``BASELINE_CAP_S``."""
    drop = {*leave, "MUTANT_UNDER_TEST", KILLERS_ENV}
    child = {k: v for k, v in env.items() if k not in drop}
    child["PYTHONPATH"] = str(mutants_dir)
    try:
        done = run([sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider", *pytest_args, nodeid],
                   cwd=str(mutants_dir), env=child, capture_output=True, text=True, encoding="utf-8",
                   errors="replace", timeout=BASELINE_CAP_S, check=False)
    except subprocess.TimeoutExpired:
        return False
    return done.returncode == 0


def full_cell_probe(rows: Sequence[UnitResult], tree: Path, oracle: Mapping[str, Any], pytest_args: Sequence[str],
                    env: Mapping[str, str], budget_s: float, killers_file: Path, *,
                    cap_s: float = FULL_PROBE_CAP_S, run: Callable[..., Any] = subprocess.run) -> None:
    """The lane's second look at each survivor on the diff's own lines: its
    module's class instruments (the oracle files whose ``matrix`` marker
    names the module) at ``--matrix=full``, the mutant active.  The engine
    ran every instrument at its sample, so a mutant only a cell the sample
    left out kills survived there (#1926's eight in
    `_emit_written_store_guard`).  A test that fails is its killer: the
    survivor is recorded killed, by that test, in ``full_kills``, and leaves
    the survivors.  A probe that finds none, does not finish, or cannot run
    (no instrument names the module) leaves it a survivor, its reason in
    ``probes``: never a silent pass."""
    deadline = time.monotonic() + budget_s
    for row in rows:
        if not row.survivors:
            continue
        files = [t for t in oracle.get("modules", {}).get(row.path, [])
                 if (tree / t).is_file() and row.path in (matrix_decides((tree / t).read_text(encoding="utf-8")) or [])]
        if not files:
            row.probes.update({n: "not run: no class instrument names its module" for n in row.survivors})
            continue
        found = run_probe(tree / "mutants", row.survivors, files, [*pytest_args, "--matrix=full"], env,
                          deadline - time.monotonic(), killers_file, cap_s=cap_s, run=run, drop=(ORACLE_MAP_ENV, MATRIX_CHANGED_ENV),
                          what="its module's instruments in full",
                          out_of_time="not looked at: the probe's share of the budget ran out")
        for name, killer in found.items():
            if killer.startswith("not "):
                row.probes[name] = killer
            else:
                row.full_kills[name] = killer
        row.survivors = [n for n in row.survivors if n not in row.full_kills]


def split_neighbours(rows: Sequence[UnitResult],
                     neighbours: Mapping[tuple[str, str], frozenset[int]]) -> None:
    """Move each row's survivors on no changed line into ``neighbours``: a
    pull request is gated on its own lines, and a survivor on a line the
    window pulled in is the standing sweep's (#1888)."""
    for row in rows:
        apart = neighbours.get((row.path, row.key), frozenset())
        row.neighbours = [n for n in row.survivors if _mutant_number(n) in apart]
        row.survivors = [n for n in row.survivors if _mutant_number(n) not in apart]


def list_window(request: str) -> str:
    """The engine's ``list-window`` command: for each file of ``request``
    (JSON, ``{"sources": {path: source}, "lines": {path: [line, ...]}}``),
    the mutants ``mutmut run`` generates in that window (the lines named and
    the first line of each node of :data:`ENCLOSING_KINDS` that spans one,
    as :func:`install_window` widens it), by mutmut's own visitor and no
    test: ``{path: {key: [{"n": n, "line": l, "original": text, "mutated":
    text}, ...]}}``, ``n`` the number the window's run gives the mutant, from
    one in the order the visitor makes a unit's mutants."""
    import libcst as cst
    from libcst.metadata import MetadataWrapper, PositionProvider
    from mutmut.mutation.file_mutation import MutationVisitor
    from mutmut.mutation.mutators import mutation_operators
    from mutmut.mutation.pragma_handling import get_ignored_lines

    data = json.loads(request)
    listed: dict[str, dict[str, list[dict[str, Any]]]] = {}
    for path, named in data["lines"].items():
        source = data["sources"][path]
        lines = set(named) | first_lines(enclosing_spans(source), named)
        wrapper = MetadataWrapper(cst.parse_module(source))
        visitor = MutationVisitor(mutation_operators, get_ignored_lines(path, source, wrapper, None), lines)
        wrapper.visit(visitor)
        positions = wrapper.resolve(PositionProvider)
        keys: dict[Any, str] = {}
        for stmt in wrapper.module.body:
            if isinstance(stmt, cst.FunctionDef):
                keys[stmt] = _key(stmt.name.value, None)
            elif isinstance(stmt, cst.ClassDef) and isinstance(stmt.body, cst.IndentedBlock):
                keys.update({m: _key(m.name.value, stmt.name.value) for m in stmt.body.body
                             if isinstance(m, cst.FunctionDef)})

        def text(node: Any) -> str:
            return wrapper.module.code_for_node(node) if isinstance(node, cst.CSTNode) else ""

        units: dict[str, list[dict[str, Any]]] = {}
        for mutation in visitor.mutations:
            key = keys.get(mutation.contained_by_top_level_function)
            if key is None:
                continue
            made = units.setdefault(key, [])
            made.append({"n": len(made) + 1, "line": positions[mutation.original_node].start.line,
                         "original": text(mutation.original_node), "mutated": text(mutation.mutated_node)})
        listed[path] = units
    return json.dumps(listed)


def engine_main(args: Sequence[str]) -> int:
    """mutmut's command line, its ``run`` generating only the window's
    mutants when :data:`WINDOW_ENV` names the lane's window file: the lane's
    default engine, this script run with :data:`ENGINE_ARG` first.  An engine
    that cannot apply the window stops with :data:`NO_WINDOW_EXIT` before it
    generates anything, which the lane reads as an engine failure."""
    if args[:1] == [COUNT_ARG]:
        try:
            sys.stdout.write(count_units(sys.stdin.read()))
        except (ImportError, KeyError, TypeError, ValueError) as exc:
            print(f"mutate_diff: the units cannot be counted: {exc}", file=sys.stderr)
            return NO_COUNT_EXIT
        return 0
    if args[:1] == [LIST_ARG]:
        try:
            sys.stdout.write(list_window(sys.stdin.read()))
        except (ImportError, KeyError, TypeError, ValueError) as exc:
            print(f"mutate_diff: the window's mutants cannot be listed: {exc}", file=sys.stderr)
            return NO_COUNT_EXIT
        return 0
    if args[:1] == [SHOW_ARG]:
        try:
            sys.stdout.write(show_mutants(sys.stdin.read()))
        except (ImportError, KeyError, TypeError, ValueError) as exc:
            print(f"mutate_diff: the mutants cannot be shown: {exc}", file=sys.stderr)
            return NO_COUNT_EXIT
        return 0
    import mutmut.__main__ as engine

    window_file = os.environ.get(WINDOW_ENV)
    if window_file and args[:1] == ["run"]:
        try:
            install_window(engine, Path(window_file))
        except (WindowError, OSError, ValueError, KeyError) as exc:
            print(f"mutate_diff: the window cannot be applied: {exc}", file=sys.stderr)
            return NO_WINDOW_EXIT
    try:
        engine.cli(args=list(args), prog_name="mutmut")
    except SystemExit as exit_:
        code = exit_.code
        return code if isinstance(code, int) else (0 if code is None else 1)
    return 0


# ---------------------------------------------------------------------------
# The engine
# ---------------------------------------------------------------------------


@dataclass
class EngineRun:
    """How a run of the engine ended."""

    returncode: int | None
    stopped: str | None
    elapsed_s: float
    #: The exception the engine's own code raised that stopped its stats pass
    #: or its clean run (:func:`engine_failure`), or None.
    error: str | None = None


#: mutmut's progress line: mutants decided (bar the not checked) of all.
_PROGRESS = re.compile(r"^(\d+)/(\d+)\s")


def engine_rows(text: str) -> list[str]:
    """The rows of an engine log, its spinner frames stripped."""
    rows = [r.strip() for r in re.split(r"[\r\n]+", text) if r.strip()]
    return [re.sub(r"^[⠀-⣿]\s*", "", r) for r in rows]


class PhaseWatch(threading.Thread):
    """When each of the engine's phases started in a pass, and when its
    first mutant was decided, seconds from ``started_at``: read off the
    newest of the pass's logs (``<log_name>-<attempt>.log``) every
    ``poll_s`` seconds, as the nightly sweep's heartbeat reads its slice's."""

    def __init__(self, workdir: Path, log_name: str, started_at: float, poll_s: float = 10.0) -> None:
        super().__init__(name=f"phases-{log_name}", daemon=True)
        self.workdir, self.log_name, self.started_at, self.poll_s = workdir, log_name, started_at, poll_s
        self.phases: dict[str, float | None] = {key: None for _, key in PHASE_TITLES}
        self.phases["first_mutant_s"] = None
        self._stopping = threading.Event()

    def observe(self, at: float, status: str | None) -> None:
        """Note the engine's status ``status``, seen ``at`` seconds in."""
        if not status:
            return
        at = round(at, 1)
        for title, key in PHASE_TITLES:
            if status.startswith(title) and self.phases[key] is None:
                self.phases[key] = at
        progress = _PROGRESS.match(status)
        if progress is not None:
            if self.phases["mutants_s"] is None:
                self.phases["mutants_s"] = at
            if int(progress.group(1)) > 0 and self.phases["first_mutant_s"] is None:
                self.phases["first_mutant_s"] = at

    def rows(self) -> list[str]:
        """The newest log's last rows (its last 8 KiB): every status since
        the last look, unless the engine wrote more than that between two."""
        def attempt(path: Path) -> int:
            tail = path.stem.rpartition("-")[2]
            return int(tail) if tail.isdigit() else 0

        logs = sorted(self.workdir.glob(f"{self.log_name}-*.log"), key=attempt)
        if not logs:
            return []
        try:
            with logs[-1].open("rb") as fh:
                fh.seek(0, io.SEEK_END)
                fh.seek(max(0, fh.tell() - 8192))
                return engine_rows(fh.read().decode("utf-8", errors="replace"))
        except OSError:
            return []

    def look(self) -> None:
        at = time.monotonic() - self.started_at
        for row in self.rows():
            self.observe(at, row)

    def run(self) -> None:
        while not self._stopping.wait(self.poll_s):
            self.look()

    def stop(self) -> dict[str, float | None]:
        """Stop watching, take a last look, and return the phases."""
        self._stopping.set()
        if self.is_alive():
            self.join(timeout=self.poll_s + 5)
        self.look()
        return dict(self.phases)


def _signal_group(pid: int, sig: int) -> bool:
    """Send ``sig`` to the process group ``pid`` leads; False where the
    group has no member left to signal.  A group whose every member has
    gone answers ESRCH.  One whose last member has exited and is not yet
    reaped answers EPERM on macOS, where a zombie can be sent nothing (Linux
    delivers to it and reports no error), so EPERM is the same answer: a
    group this process started holds no member it may not signal."""
    try:
        os.killpg(pid, sig)
    except (ProcessLookupError, PermissionError):
        return False
    return True


def _end_group(proc: subprocess.Popen[Any], grace_s: float) -> None:
    """End ``proc``'s process group: a terminate, then after ``grace_s`` a
    kill to whatever of the group is left (a test's subprocess included)."""
    if os.name != "posix":
        proc.kill()
        return
    for sig, wait in ((signal.SIGTERM, grace_s), (signal.SIGKILL, None)):
        if not _signal_group(proc.pid, sig):
            return
        try:
            proc.wait(timeout=wait)
        except subprocess.TimeoutExpired:
            continue
    _signal_group(proc.pid, signal.SIGKILL)


def run_engine(cmd: Sequence[str], *, cwd: Path, budget_s: float, log_path: Path,
               env: Mapping[str, str] | None = None,
               grace_s: tuple[float, float] = (60.0, 30.0),
               before_stop: Callable[[], None] | None = None) -> EngineRun:
    """Run ``cmd`` within ``budget_s`` wall-clock seconds, its output to
    ``log_path``.  Past the budget: ``before_stop`` (what the caller reads
    of the run before any signal reaches it), then an interrupt, then after
    ``grace_s[0]`` a terminate to its process group, then after
    ``grace_s[1]`` a kill.  Anything else that ends the wait (a keyboard
    interrupt, a signal the caller turned into an exception, a test's
    timeout) ends the engine's whole process group before it propagates:
    the engine runs in a session of its own, so nothing else would."""
    start = time.monotonic()
    posix = os.name == "posix"
    with log_path.open("w", encoding="utf-8") as log:
        proc = subprocess.Popen(list(cmd), cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                env=None if env is None else dict(env),
                                start_new_session=posix)
        try:
            return EngineRun(proc.wait(timeout=budget_s), None, time.monotonic() - start)
        except subprocess.TimeoutExpired:
            pass
        except BaseException:
            _end_group(proc, grace_s[1])
            raise
        try:
            return _stop_engine(proc, posix, grace_s, before_stop, start)
        except BaseException:
            _end_group(proc, grace_s[1])
            raise


def _stop_engine(proc: subprocess.Popen[Any], posix: bool, grace_s: tuple[float, float],
                 before_stop: Callable[[], None] | None, start: float) -> EngineRun:
    """The budget's stop of :func:`run_engine`'s engine."""
    if before_stop is not None:
        before_stop()
    steps: list[tuple[Any, float | None]] = []
    if posix:
        steps = [(lambda: proc.send_signal(signal.SIGINT), grace_s[0]),
                 (lambda: _signal_group(proc.pid, signal.SIGTERM), grace_s[1]),
                 (lambda: _signal_group(proc.pid, signal.SIGKILL), None)]
    else:
        steps = [(proc.terminate, grace_s[1]), (proc.kill, None)]
    returncode = None
    for send, grace in steps:
        try:
            send()
        except ProcessLookupError:
            pass
        try:
            returncode = proc.wait(timeout=grace)
            break
        except subprocess.TimeoutExpired:
            continue
    if posix:
        # What the engine started (a test's subprocess) is still in its
        # group once the engine itself has stopped.
        _signal_group(proc.pid, signal.SIGKILL)
    return EngineRun(returncode, "budget", time.monotonic() - start)


def run_dropping(cmd: Sequence[str], *, tree: Path, pyproject: Path,
                 config_for: Callable[[Sequence[str]], str], budget_s: float, workdir: Path,
                 env: Mapping[str, str], before_stop: Callable[[], None] | None = None,
                 log_name: str = "mutmut-run", dropped: Sequence[str] = (),
                 ) -> tuple[EngineRun, Path, list[str]]:
    """Run the engine in ``tree`` within ``budget_s``; when a test stops its
    stats pass or its clean run (it fails inside mutmut's copy with no mutant
    active, so it is no oracle there), drop it and run again in what is left
    of the budget, up to ``MAX_COPY_DROPS`` tests.  When the engine's own code
    raised instead (:func:`engine_failure`), no test is at fault: the run
    stops there, drops no further test, and the returned run's ``error``
    names the exception and the engine's frame.  ``config_for(dropped)`` is the
    ``pyproject.toml`` text for a run without the tests dropped so far.
    Returns the last run, its log and the tests dropped, ``dropped`` (the
    tests an earlier pass dropped, which every attempt starts without)
    first.  ``before_stop`` goes to :func:`run_engine`; each attempt's log
    is ``<log_name>-<attempt>.log`` in ``workdir``."""
    stop_hook: dict[str, Any] = {} if before_stop is None else {"before_stop": before_stop}
    dropped = list(dropped)
    remaining = budget_s
    attempt = 0
    failures = Path(env[FAILURES_ENV]) if env.get(FAILURES_ENV) else None
    while True:
        attempt += 1
        pyproject.write_text(config_for(dropped), encoding="utf-8")
        if failures is not None:
            failures.unlink(missing_ok=True)  # each attempt's failures are its own
        log = workdir / f"{log_name}-{attempt}.log"
        run = run_engine(cmd, cwd=tree, budget_s=remaining, log_path=log, env=env, **stop_hook)
        remaining -= run.elapsed_s
        if run.stopped is not None or run.returncode != 1:
            return run, log, dropped
        text = log.read_text(encoding="utf-8", errors="replace")
        run.error = engine_failure(text)
        failing = None if run.error is not None else copy_failure(text, failures)
        if (failing is None or failing in dropped or len(dropped) >= MAX_COPY_DROPS
                or remaining <= 0):
            return run, log, dropped
        dropped.append(failing)


def copy_failure(log: str, failures: Path | None = None) -> str | None:
    """The test that stopped mutmut's stats pass or its clean run, when that
    is how the run stopped: read off the log's ``FAILED`` line, or, when the
    log has none because the pass ran in the fork server's child, the first
    node id the plugin appended to ``failures`` (:data:`FAILURES_ENV`)."""
    if not any(stop in log for stop in _COPY_STOPS):
        return None
    match = re.search(r"^(?:FAILED|ERROR) (.+?)(?: - .*)?$", log, re.M)
    if match:
        return match.group(1).strip()
    if failures is not None and failures.exists():
        for line in failures.read_text(encoding="utf-8").splitlines():
            if line.strip():
                return line.strip()
    return None


def engine_failure(log: str) -> str | None:
    """The exception the engine's own code raised that stopped its stats pass
    or its clean run, read off its log: the exception's first line and the
    engine's frame, ``AttributeError: … (mutmut/runners/harness.py:157)``;
    None when the log names no such stop, or a test's code raised.
    Without a stop sentence, the traceback the log ends with is the
    engine's death: pytest's usage-error exit, which the harness raises
    past the pass that would have printed one (#1822).  Its message is
    read whole, a line after the exception's first being the message's,
    unless pytest's session summary or a rule follows: then the pass went
    on, and the traceback is a report the run survived.

    The log of a run its stats pass or its clean run stopped holds that
    pass's output alone: mutmut prints it only when the pass fails, and
    exits there.  Its reports carry tracebacks in Python's own form, an
    internal error's with :data:`_INTERNAL_ERROR` on every line; what a test
    printed or logged, from its :data:`_CAPTURED` rule to the next of
    pytest's rules (:data:`_RULE`, drawn :data:`_RULE_WIDTH` wide or more),
    is no report and is not read.
    Going outward from a traceback's innermost frame, past the frames no
    party's code is in (:data:`_NEUTRAL_FILE`), the first frame decides: a
    file of the installed ``mutmut`` package is the engine's code (a hook of
    its stats pass, its trampoline), and any other (the test, the code under
    test, a library either calls, pytest) is the test's.  A
    ``RecursionError`` is the engine's only when, besides, no frame of the
    copy lies among its :data:`RECURSION_FRAMES` innermost frames outside
    the standard library, a frame printed with a repeat count
    (:data:`_REPEATED`) counting that many more times."""
    stopped = any(stop in log for stop in _COPY_STOPS)
    lines: list[str] = []
    captured = False
    for row in log.splitlines():
        row = row.removeprefix(_INTERNAL_ERROR)
        rule = row.rstrip()
        if len(rule) >= _RULE_WIDTH and _RULE.match(rule):
            captured = _CAPTURED.match(rule) is not None
        if not captured:
            lines.append(row)
    starts = [at for at, line in enumerate(lines)
              if line.rstrip() == "Traceback (most recent call last):"]
    for start in starts:
        if not stopped and start != starts[-1]:
            # Without a stop sentence, only the traceback the log ends
            # with can be where the engine died.
            continue
        frames: list[re.Match[str]] = []
        raised: str | None = None
        after: list[str] = []
        for at, row in enumerate(lines[start + 1:], start + 1):
            frame = _FRAME.match(row.rstrip())
            repeated = _REPEATED.match(row)
            if frame is not None:
                frames.append(frame)
            elif repeated is not None and frames:
                frames += [frames[-1]] * min(int(repeated.group(1)), RECURSION_FRAMES)
            elif row.strip() and not row[0].isspace():
                raised = row.strip()
                after = lines[at + 1:]
                break
        if raised is None:
            continue
        if not stopped and any(_went_on(row) for row in after):
            # The pass went on past the exception: a report the run
            # survived.  Otherwise the lines after it are its message.
            continue
        kept = [f for f in frames if not _NEUTRAL_FILE.search(f["file"])]
        deciding = kept[-1] if kept else None
        engine = _ENGINE_FILE.search(deciding["file"]) if deciding is not None else None
        if deciding is None or engine is None:
            continue
        if (raised.split(":", 1)[0].rsplit(".", 1)[-1] == "RecursionError"
                and any(_COPY_FILE.search(f["file"]) for f in kept[-RECURSION_FRAMES:])):
            continue
        where = f" ({engine['path'].replace(chr(92), '/')}:{deciding['line']})"
        if len(raised) + len(where) > ENGINE_ERROR_CHARS:
            raised = raised[:ENGINE_ERROR_CHARS - len(where) - 1] + "…"
        return raised + where
    return None


def _went_on(row: str) -> bool:
    """Whether *row* is a line pytest prints past a report it went on from:
    its session summary, or one of its rules."""
    rule = row.rstrip()
    return (_SUMMARY.match(rule) is not None
            or len(rule) >= _RULE_WIDTH and _RULE.match(rule) is not None)


def parse_results(text: str) -> dict[str, str]:
    """``mutmut results --all true``: one ``    <mutant>: <status>`` a line."""
    results: dict[str, str] = {}
    for line in text.splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r"    (\S+__mutmut_\d+): (.+)", line)
        if match is None:
            raise ResultsError(f"a line the lane cannot parse: {line!r}")
        name, status = match.group(1), match.group(2).strip()
        if status not in STATUSES:
            raise ResultsError(f"a status the lane does not model: {status!r} ({name})")
        if name in results:
            raise ResultsError(f"a mutant listed twice: {name}")
        results[name] = status
    return results


@dataclass
class UnitResult:
    """One changed unit's mutants and what became of them."""

    path: str
    key: str
    qualname: str
    excluded: str | None
    mutants: int
    counts: dict[str, int]
    survivors: list[str]
    observable: bool
    diffs: dict[str, str] = field(default_factory=dict)
    #: The unit's mutants on every line, and in the window, by mutmut's own
    #: visitor; None where the engine counted none.
    held: int | None = None
    window: int | None = None
    #: The survivors on no line the diff changes, which the two-line window
    #: pulled in (:func:`split_neighbours`): listed, never gating.
    neighbours: list[str] = field(default_factory=list)
    #: Survivors on the diff's own lines a cell of their module's instruments
    #: at ``--matrix=full`` kills, by that test (:func:`full_cell_probe`).
    full_kills: dict[str, str] = field(default_factory=dict)
    #: Why the probe left each survivor it looked at a survivor.
    probes: dict[str, str] = field(default_factory=dict)


def tally(units: Sequence[Unit], results: Mapping[str, str]) -> list[UnitResult]:
    """Each unit's results, counted against the unit their name mangles."""
    owned: dict[tuple[str, str], list[tuple[str, str]]] = {
        (module_name(u.path), u.key): [] for u in units}
    for name, status in results.items():
        owner = unit_of_mutant(name)
        if owner in owned:
            owned[owner].append((name, status))
    rows: list[UnitResult] = []
    for unit in units:
        items = owned[(module_name(unit.path), unit.key)]
        counts = dict(Counter(status for _, status in items))
        survivors = sorted((n for n, s in items if s == "survived"), key=_mutant_number)
        observable = not items or any(s != "no tests" for _, s in items)
        rows.append(UnitResult(path=unit.path, key=unit.key, qualname=unit.qualname,
                               excluded=unit.excluded, mutants=len(items), counts=counts,
                               survivors=survivors, observable=observable))
    return rows


def outside_units(units: Sequence[Unit], results: Mapping[str, str]) -> list[str]:
    """The mutants mutmut reported for a unit the diff does not change."""
    owned = {(module_name(u.path), u.key) for u in units}
    return sorted(n for n in results if unit_of_mutant(n) not in owned)


def read_window_counts(path: Path) -> dict[tuple[str, str], tuple[int, int]] | None:
    """The engine's count of each unit's mutants, ``(path, key) -> (held,
    window)`` (:func:`install_window`), or None when it wrote none that reads."""
    try:
        files = json.loads(path.read_text(encoding="utf-8"))["files"]
        return {(file, key): (int(n["held"]), int(n["window"]))
                for file, units in files.items() for key, n in units.items()}
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        return None


def place_in_window(rows: Sequence[UnitResult],
                    counts: Mapping[tuple[str, str], tuple[int, int]]) -> list[str]:
    """Give each row its unit's counts, and name each unit whose mutants
    mutmut lists differ in number from the window's.  The engine writes a
    file's mutants together, so a unit with any listed was generated whole,
    and its count is the window's when the window reached the generator; a
    unit with none listed (the run stopped before its file) is not judged."""
    outside: list[str] = []
    for row in rows:
        row.held, row.window = counts.get((row.path, row.key), (0, 0))
        if row.mutants and row.mutants != row.window:
            outside.append(f"`{row.path}` `{row.qualname}`: {row.mutants} generated, "
                           f"{row.window} in the window")
    return outside


def selection(rows: Sequence[UnitResult]) -> dict[str, int | None]:
    """What the selection measured: the functions, their mutants on every
    line and in the window, the mutants generated and decided, and the
    survivors."""
    counted = all(r.held is not None and r.window is not None for r in rows)
    return {
        "functions": len(rows),
        "held": sum(r.held or 0 for r in rows) if counted else None,
        "window": sum(r.window or 0 for r in rows) if counted else None,
        "generated": sum(r.mutants for r in rows),
        "decided": sum(n for r in rows for status, n in r.counts.items()
                       if STATUSES[status] != "undecided"),
        "survived": sum(len(r.survivors) for r in rows),
        "neighbours_survived": sum(len(r.neighbours) for r in rows),
    }


def failed(stopped: str | None, failure: str) -> str:
    """How the run stopped once ``failure`` (``engine`` or ``unmapped``) is
    found too.  A failure outranks the budget, which leaves a run only
    incomplete, so a run the budget stopped that then failed is red; of two
    failures the first is the one recorded."""
    return failure if stopped in (None, "budget") else stopped


#: The lane's exit status when the diff was not measured: some changed
#: function with mutants in its window had none decided.
NOT_MEASURED = 3


def measured(row: UnitResult) -> int:
    """How many of a row's mutants a test measured: killed, timed out,
    caught by the type checker, or survived.  A ``no tests`` mutant is
    decided and measures nothing: no test of its module's declared oracle
    reaches the function."""
    return sum(n for status, n in row.counts.items() if STATUSES[status] in ("caught", "survived"))


def not_measured(rows: Sequence[UnitResult]) -> list[UnitResult]:
    """The changed functions with mutants in their window and none a test
    measured: the run says nothing of them, whether it stopped before them,
    never reached them, or no declared test reaches them."""
    return [r for r in rows if (r.window or r.mutants) and not measured(r)]


def exit_code(rows: Sequence[UnitResult], *, stopped: str | None) -> int:
    """1: a survivor on a line the diff changes, whatever stopped the run (a
    survivor on a neighbour line the window pulled in gates nothing:
    :func:`split_neighbours`); 2: the run itself failed (the engine, or a
    mutant the lane did not map); 3 (:data:`NOT_MEASURED`): a changed
    function with mutants in its window had none decided; 0 otherwise, a
    run that decided some of every function's mutants and not all of them
    included."""
    if any(row.survivors for row in rows):
        return 1
    if stopped in ("engine", "unmapped"):
        return 2
    if not_measured(rows):
        return NOT_MEASURED
    return 0


def _incomplete(rows: Sequence[UnitResult], stopped: str | None) -> str | None:
    """Why the run did not decide every mutant of the diff, or None."""
    if stopped == "budget":
        return "the budget ran out before every mutant was decided"
    if stopped == "engine":
        return "the engine stopped before every mutant was decided"
    if stopped == "unmapped":
        return ("mutmut's mutants do not match the functions or the window the lane mapped "
                "to the diff, so the diff is not decided")
    statuses = {status for row in rows for status, n in row.counts.items() if n}
    if any(STATUSES[s] == "undecided" for s in statuses):
        return "mutants of the diff were left undecided"
    return None


# ---------------------------------------------------------------------------
# The report
# ---------------------------------------------------------------------------


_COLUMNS = ("killed", "timeout", "survived")


def selection_line(window_: Mapping[str, Any]) -> str:
    """The selection rule and what it measured, for the summary's head:
    the functions, their mutants and the window's, and what became of the
    generated ones."""
    head = f"Selection: {window_['rule']}."
    if window_.get("error"):
        return f"{head} Not checked: {window_['error']}."
    sel = window_.get("selection") or {}
    held = "?" if sel.get("held") is None else sel["held"]
    inside = "?" if sel.get("window") is None else sel["window"]
    return (f"{head} {sel.get('functions', 0)} function(s) hold {held} mutant(s), {inside} of "
            f"them in the window; mutmut generated {sel.get('generated', 0)}, decided "
            f"{sel.get('decided', 0)}, and {sel.get('survived', 0)} survived.")


def render(record: Mapping[str, Any]) -> str:
    """The job summary: the run's outcome, a row per changed function, the
    survivors' diffs, and what the diff changes that mutmut cannot mutate."""
    out = ["## Mutation testing over this diff", ""]
    out.append(f"`{record['merge_base'][:12]}...{record['head'][:12]}`, "
               f"mutmut {record['engine_version'] or '(not run)'}, "
               f"budget {record['budget_s']:g} s, {record['elapsed_s']:.0f} s elapsed.")
    out.append("")
    out.append(f"**{record['outcome']}**")
    out.append("")
    if record.get("engine_error"):
        out.append(f"Stopped by the engine: `{record['engine_error']}`.  The exception was raised in "
                   "mutmut's own code.")
        out.append("")
    if record.get("window"):
        out.append(selection_line(record["window"]))
        out.append("")
    if record.get("oracle"):
        out.append(f"Oracle: {record['oracle']['tests']} test file(s) the changed modules declare "
                   f"({record['oracle']['rule']}), every matrix at its sample, seed "
                   f"`{record.get('matrix_seed')}`.")
        out.append("")
    if record.get("budget_split"):
        split = record["budget_split"]
        out.append(f"Budget: {split['engine_s']:.0f} s to the engine, every matrix at its sample; "
                   f"{split['probe_s']:.0f} s left to look again at the survivors on the diff's own lines "
                   f"with their module's instruments in full, at most {split['probe_cap_s']:.0f} s each "
                   f"({split.get('probed', 0)} looked at, {split.get('killed_in_full', 0)} killed there).")
        out.append("")
    if record.get("passes"):
        out.append("| Pass | Named | Stats | Listing | Clean | Forced | Mutants | First mutant | Ended | Decided |")
        out.append("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
        for p in record["passes"]:
            ph = p.get("phases") or {}
            cell = [("" if ph.get(k) is None else f"{ph[k]:.0f} s")
                    for k in ("stats_s", "listing_s", "clean_s", "forced_s", "mutants_s", "first_mutant_s")]
            out.append(f"| {p['pass']} | {p['named']} | " + " | ".join(cell)
                       + f" | {p['elapsed_s']:.0f} s run | {p['decided']} |")
        out.append("")
        out.append("Each phase's start is in seconds from the lane's start; a pass's run time is its own.")
        out.append("")
    functions = record["functions"]
    if functions:
        out.append("| Function | Mutants | Killed | Timeout | Survived | Other |")
        out.append("|---|---:|---:|---:|---:|---|")
        for row in functions:
            name = f"`{row['path']}` `{row['qualname']}`"
            if row["excluded"]:
                out.append(f"| {name} | 0 | | | | not mutated: {row['excluded']} |")
                continue
            counts = row["counts"]
            other = ", ".join(f"{s} {n}" for s, n in sorted(counts.items())
                              if s not in _COLUMNS)
            settled = sum(n for s, n in counts.items() if STATUSES.get(s) != "undecided")
            if row["mutants"] and not row["observable"]:
                other = (f"not measured: no test of `{row['path']}`'s declared oracle reaches it")
            elif (row["mutants"] or row.get("window")) and not settled:
                other = ("not decided: the run stopped first" if not row["mutants"]
                         else f"not decided; {other}" if other else "not decided")
            elif not row["mutants"]:
                other = ("no result: the run stopped first" if record["stopped"]
                         else "mutmut generated no mutant for it")
            out.append(f"| {name} | {row['mutants']} | {counts.get('killed', 0)} | "
                       f"{counts.get('timeout', 0)} | {counts.get('survived', 0)} | {other} |")
        out.append("")
    else:
        out.append("The diff changes no function mutmut mutates.")
        out.append("")
    survivors = [s for row in functions for s in row["survivors"]]
    if survivors:
        out.append("### Survivors")
        out.append("")
        shown = [s for s in survivors if s["diff"]][:MAX_SHOWN_SURVIVORS]
        for survivor in shown:
            out.append(f"`{survivor['name']}`" + (f" ({survivor['probe']})" if survivor.get("probe") else ""))
            out.append("")
            out.append("```diff")
            out.extend(survivor["diff"].rstrip("\n").splitlines())
            out.append("```")
            out.append("")
        if len(survivors) > len(shown):
            out.append(f"{len(survivors) - len(shown)} more survivors are in the JSON record "
                       "(the `mutation-diff` artifact), each with its diff unless the show "
                       "budget ran out first.")
            out.append("")
    full = [(row, k) for row in functions for k in row.get("killed_in_full", [])]
    if full:
        out.append("### Killed by a cell the sample left out")
        out.append("")
        out.append("Each survived the engine's run, where every matrix ran at its sample, and a cell of "
                   "its module's instruments at `--matrix=full` kills it, with the mutant active:")
        out.append("")
        out.extend(f"- `{k['name']}`: `{k['test']}`" for _, k in full)
        out.append("")
    apart = [s for row in functions for s in row.get("neighbour_survivors", [])]
    if apart:
        out.append("### Survivors on unchanged lines: not this pull request's")
        out.append("")
        out.append("Each sits on a line the diff does not change, which the two-line window pulled in. "
                   "It does not fail this check: the standing sweep issue #1888 records it, and the "
                   "pull request owes it nothing.")
        out.append("")
        shown = [s for s in apart if s["diff"]][:MAX_SHOWN_SURVIVORS]
        for survivor in shown:
            out.append(f"`{survivor['name']}`")
            out.append("")
            out.append("```diff")
            out.extend(survivor["diff"].rstrip("\n").splitlines())
            out.append("```")
            out.append("")
        if len(apart) > len(shown):
            out.append(f"{len(apart) - len(shown)} more are in the JSON record (`neighbour_survivors`).")
            out.append("")
    if record.get("dropped_tests"):
        out.append("### Dropped from the oracle")
        out.append("")
        out.append("Each failed inside mutmut's copy with no mutant active, so it is no oracle "
                   "there, and the run went again without it (the test shards run it outside the "
                   "copy):")
        out.append("")
        out.extend(f"- `{test}`" for test in record["dropped_tests"])
        out.append("")
    if record.get("subprocess_tests"):
        shown = record["subprocess_tests"][:30]
        out.append("### Not oracles in mutmut's copy")
        out.append("")
        out.append(f"{len(record['subprocess_tests'])} test(s) start a Python or `vera` process, which "
                   "inside mutmut's copy runs the mutated modules afresh and records nothing for the "
                   "stats pass, so `tests/mutation_oracle.py` skipped them there"
                   + (":" if len(shown) == len(record["subprocess_tests"])
                      else f"; the first {len(shown)}, the record lists every one:"))
        out.append("")
        out.extend(f"- `{test}`" for test in shown)
        out.append("")
    if record.get("source_tests"):
        shown = record["source_tests"][:30]
        if not record.get("subprocess_tests"):
            out.append("### Not oracles in mutmut's copy")
            out.append("")
        out.append(f"{len(record['source_tests'])} test(s) read the compiler's source, which inside "
                   "mutmut's copy holds every mutant of the mutated functions inlined, so "
                   "`tests/mutation_oracle.py` skipped them there"
                   + (":" if len(shown) == len(record["source_tests"])
                      else f"; the first {len(shown)}, the record lists every one:"))
        out.append("")
        out.extend(f"- `{test}`" for test in shown)
        out.append("")
    notes = []
    for item in record["files"]:
        if item["outside"] or item["outside_removed"]:
            notes.append(f"`{item['path']}`: {len(item['outside'])} added and "
                         f"{len(item['outside_removed'])} removed line(s) of code outside every "
                         "function (mutmut mutates function bodies only)")
        if item["unchanged_code"]:
            notes.append(f"`{item['path']}`: lines changed, code unchanged in "
                         + ", ".join(f"`{q}`" for q in item["unchanged_code"]))
        if item["deleted"]:
            notes.append(f"`{item['path']}`: deleted " + ", ".join(f"`{q}`" for q in item["deleted"]))
    if record["outside_diff"]:
        names = ", ".join(f"`{n}`" for n in record["outside_diff"][:10])
        notes.append(f"{len(record['outside_diff'])} mutant(s) mutmut reported for functions the "
                     f"lane did not map to the diff, which stops the run short: {names}")
    if record.get("outside_window"):
        notes.append("functions whose generated mutants differ in number from their window's, "
                     "which stops the run short: " + "; ".join(record["outside_window"][:10]))
    if record["extra_tests"]:
        notes.append("the pull request's own test files, added to the selection: "
                     + ", ".join(f"`{t}`" for t in record["extra_tests"]))
    if record["tests_left_out"]:
        notes.append("changed test files left out of the selection (no in-process "
                     "compiler test, or a family the selection omits): "
                     + ", ".join(f"`{t}`" for t in record["tests_left_out"]))
    if notes:
        out.append("### Not in the table")
        out.append("")
        out.extend(f"- {note}" for note in notes)
        out.append("")
    if record["engine_tail"]:
        out.append("### The engine's last lines")
        out.append("")
        out.append("```")
        out.extend(record["engine_tail"])
        out.append("```")
        out.append("")
    return "\n".join(out)


def outcome(code: int, rows: Sequence[UnitResult], stopped: str | None, *,
            undeclared: int = 0) -> str:
    """The headline: what the run decided, and how many changed functions
    are in a module with no declared oracle (``undeclared``), whose mutants
    the lane does not run."""
    head = _outcome(code, rows, stopped)
    apart = sum(len(r.neighbours) for r in rows)
    if apart:
        if head == "Pass: every mutant of the diff is killed or timed out.":
            head = "Pass: every mutant on the diff's own lines is killed or timed out."
        head = (f"{head.removesuffix('.')}; {apart} survivor(s) on unchanged lines the window pulled in, "
                "not this pull request's (listed apart for the standing sweep issue #1888).")
    if undeclared:
        head = (f"{head.removesuffix('.')}; {undeclared} changed function(s) in a module with "
                "no declared oracle, not mutated.")
    return head


def _outcome(code: int, rows: Sequence[UnitResult], stopped: str | None) -> str:
    """The headline: what the run decided.  An exit 0 claims every mutant
    killed or timed out only when every changed function had mutants and an
    in-process test reached them and the run decided every mutant; otherwise
    it says what was not tested, or that the run is incomplete."""
    unfinished = _incomplete(rows, stopped)
    if code == NOT_MEASURED:
        gaps = not_measured(rows)
        unreached = [r for r in gaps if r.mutants and not r.observable]
        head = f"Not measured: {len(gaps)} function(s) had no mutant decided"
        if unreached:
            head += (f" by a test ({len(unreached)} reached by no test of their module's "
                     "declared oracle)")
        return head + (f"; {unfinished}." if unfinished else ".")
    if code == 0 and unfinished is not None:
        return f"Incomplete: {unfinished}."
    if code == 0:
        if not rows:
            return "Pass: nothing to mutate."
        empty = [r for r in rows if not r.mutants]
        skipped = sum(r.counts.get("skipped", 0) for r in rows)
        if not empty and not skipped:
            return "Pass: every mutant of the diff is killed or timed out."
        parts = []
        if empty:
            parts.append(f"{len(empty)} function(s) with no mutant")
        if skipped:
            parts.append(f"{skipped} mutant(s) skipped by the engine")
        return "Pass: no mutant survived; " + "; ".join(parts) + "."
    if code == 1:
        n = sum(len(r.survivors) for r in rows)
        if stopped is not None and unfinished is not None:
            return f"Fail: {n} mutant(s) of the diff survive; {unfinished}."
        return f"Fail: {n} mutant(s) of the diff survive."
    return f"Incomplete: {unfinished or 'the run stopped short'}."


def annotation(code: int, headline: str) -> str | None:
    """The workflow command that marks a green check whose run did not
    finish, on the pull request beside the check; None for a red check or a
    finished run."""
    if code == 0 and headline.startswith("Incomplete:"):
        return f"::warning title=mutation (diff)::{headline}"
    return None


def _engine_call(engine: Sequence[str], args: Sequence[str], *, cwd: Path | None,
                 env: Mapping[str, str], stdin: str | None = None,
                 timeout_s: float | None = None) -> subprocess.CompletedProcess[str] | None:
    """A short engine command, or None when it does not finish in
    ``timeout_s`` (``ENGINE_CALL_TIMEOUT_S`` by default)."""
    try:
        return subprocess.run([*engine, *args], cwd=cwd, capture_output=True, text=True,
                              encoding="utf-8", env=dict(env), check=False, input=stdin,
                              timeout=ENGINE_CALL_TIMEOUT_S if timeout_s is None else timeout_s)
    except subprocess.TimeoutExpired:
        return None


def skipped_tests(path: Path) -> list[str]:
    """The node ids ``tests/mutation_oracle.py`` appended to ``path``, each
    once (it appends on every skip: the stats pass, the forced-fail run);
    one node id a line, since a parametrised id can hold a space."""
    if not path.exists():
        return []
    return sorted({line for line in path.read_text(encoding="utf-8").splitlines() if line.strip()})


def _engine_version(engine: Sequence[str], env: Mapping[str, str]) -> str:
    result = _engine_call(engine, ["--version"], cwd=None, env=env)
    match = re.search(r"(\d+\.\d+[\w.]*)", result.stdout) if result is not None else None
    return match.group(1) if match else ""


def _default_engine() -> list[str]:
    """This script as the engine (:func:`engine_main`), under this
    interpreter, which the ``[mutation]`` extra gives mutmut."""
    return [sys.executable, str(Path(__file__).resolve()), ENGINE_ARG]


def _tail(path: Path, lines: int = 40) -> list[str]:
    """The engine log's last lines, its spinner frames dropped.  When the log
    holds a Python fault dump, the dump's first lines take the first half of
    the window: the fatal error and the innermost frames, which name the test
    that was running, rather than pytest's outermost frames alone."""
    if not path.exists():
        return []
    text = path.read_text(encoding="utf-8", errors="replace")
    # The dump's first line follows the spinner's status text, which mutmut
    # writes without a newline; it opens a row of its own here, or the row
    # would go with the spinner frames below.
    text = text.replace("Fatal Python error", "\nFatal Python error")
    rows = [r.rstrip() for r in re.split(r"[\r\n]+", text)
            if r.strip() and not re.match(r"\s*[\u2800-\u28ff] ", r)]
    for i, row in enumerate(rows):
        if row.startswith("Fatal Python error"):
            head = rows[i:i + lines // 2]
            return head + rows[max(i + len(head), len(rows) - (lines - len(head))):]
    return rows[-lines:]


def _context(value: str) -> int:
    try:
        lines = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"{value!r} is not a whole number of lines") from exc
    if lines < 0:
        raise argparse.ArgumentTypeError(f"the context is 0 lines or more, not {lines}")
    return lines


def _list(args: argparse.Namespace, engine: Sequence[str], tree: Path, files: Sequence[str],
          kept: Mapping[str, Sequence[int]], record: dict[str, Any], env: Mapping[str, str]) -> int:
    """``--list``: the window's mutants, each with its code before and
    after, from mutmut's visitor over the narrowed files (the engine's
    :data:`LIST_ARG` command); no test runs and no worker starts.  Exit 0
    with the list, 2 when the engine cannot make it."""
    request = json.dumps({"sources": {p: (tree / p).read_text(encoding="utf-8") for p in files},
                          "lines": {p: list(kept[p]) for p in files}})
    listed = _engine_call(engine, [LIST_ARG], cwd=tree, env=env, stdin=request)
    if listed is None or listed.returncode != 0:
        error = ("the engine did not finish listing" if listed is None
                 else (listed.stderr.strip() or f"the engine exited {listed.returncode}"))
        record.update(list=None, list_error=error)
        print(f"mutate_diff --list: {error}", file=sys.stderr)
        code = 2
    else:
        mutants = json.loads(listed.stdout)
        record.update(list=mutants, list_error=None)
        for path, units in mutants.items():
            for key, made in units.items():
                print(f"{path} {key}: {len(made)} mutant(s) in the window")
                for m in made:
                    print(f"  {m['n']:>4} L{m['line']}: {m['original']!r} -> {m['mutated']!r}")
        code = 0
    if args.json:
        Path(args.json).write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n",
                                   encoding="utf-8")
    return code


@dataclass
class PassResult:
    """One engine pass of the lane: its last run, log and the tests dropped
    so far, ``mutmut results`` after it, how it stopped, the engine's phases
    in it (seconds from the lane's start), and a tail to report when the
    listing failed."""

    number: int
    run: EngineRun
    log: Path
    dropped: list[str]
    results: dict[str, str]
    stopped: str | None
    no_tests: bool
    phases: dict[str, float | None]
    tail: list[str] = field(default_factory=list)

    def record(self, named: int) -> dict[str, Any]:
        """The pass as the JSON record lists it."""
        return {"pass": self.number, "named": named, "elapsed_s": round(self.run.elapsed_s, 1),
                "stopped": self.stopped, "engine_exit": self.run.returncode,
                "decided": sum(1 for s in self.results.values() if STATUSES[s] != "undecided"),
                "phases": self.phases}


def _pass(number: int, names: Sequence[str], engine: Sequence[str], args: argparse.Namespace,
          tree: Path, pyproject: Path, workdir: Path, env: Mapping[str, str],
          config_for: Callable[[Sequence[str]], str], budget_s: float, dropped: Sequence[str],
          started: float) -> PassResult:
    """Run the engine over the mutants ``names`` within ``budget_s``, then
    list what it decided (``mutmut results --all true``)."""
    log_name = f"mutmut-pass{number}"
    watch = PhaseWatch(workdir, log_name, started)
    watch.start()
    try:
        run, log, dropped_now = run_dropping(
            [*engine, "run", "--max-children", str(args.max_children), *names],
            tree=tree, pyproject=pyproject, budget_s=budget_s, workdir=workdir, env=env,
            config_for=config_for, log_name=log_name, dropped=dropped)
    finally:
        phases = watch.stop()
    no_tests = run.returncode == 1 and NO_TESTS_SENTENCE in log.read_text(
        encoding="utf-8", errors="replace")
    stopped = run.stopped or (None if run.returncode == 0 or no_tests else "engine")
    listed = _engine_call(engine, ["results", "--all", "true"], cwd=tree,
                          env={k: v for k, v in env.items() if k != WINDOW_ENV})
    results: dict[str, str] = {}
    tail: list[str] = []
    if listed is None:
        stopped = failed(stopped, "engine")
        tail = [f"mutmut results did not finish in {ENGINE_CALL_TIMEOUT_S} s"]
    elif listed.returncode != 0:
        stopped = failed(stopped, "engine")
    else:
        try:
            results = parse_results(listed.stdout)
        except ResultsError as exc:
            stopped = failed(stopped, "engine")
            tail = [str(exc)]
    return PassResult(number, run, log, dropped_now, results, stopped, no_tests, phases, tail)


def main(argv: Sequence[str] | None = None) -> int:
    """Run the lane; return its exit code."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default=str(ROOT), help="the repository (default: this one)")
    parser.add_argument("--base", default="origin/main",
                        help="the base; the diff is from its merge base with --head")
    parser.add_argument("--head", default="HEAD", help="the head commit (default HEAD)")
    parser.add_argument("--budget", type=float, default=DEFAULT_BUDGET_S,
                        help=f"wall-clock seconds for mutmut (default {DEFAULT_BUDGET_S})")
    parser.add_argument("--context", type=_context, default=CONTEXT_LINES,
                        help="lines either side of a changed line whose mutants are kept "
                        f"(default {CONTEXT_LINES})")
    parser.add_argument("--max-children", type=int, default=os.cpu_count() or 1,
                        help="mutmut's parallel workers (default: every CPU)")
    parser.add_argument("--workdir", help="an empty or absent directory for the scratch "
                        "tree and logs (default: a new temporary directory)")
    parser.add_argument("--json", help="write the JSON record here")
    parser.add_argument("--summary", help="append the Markdown summary here")
    parser.add_argument("--engine", nargs="+", help="the mutmut command (default: this "
                        f"script run with {ENGINE_ARG} under this interpreter)")
    parser.add_argument("--list", action="store_true",
                        help="list the window's mutants with their code, from mutmut's "
                        "visitor alone, and run no test")
    args = parser.parse_args(argv)

    repo = Path(args.repo).resolve()
    if args.workdir:
        # Absolute: the engine runs in the scratch tree, and paths reach it
        # through its environment (MUTATION_ORACLE_SKIPS).
        workdir = Path(args.workdir).resolve()
        if workdir.exists() and any(workdir.iterdir()):
            parser.error(f"--workdir {workdir} is not empty")
        workdir.mkdir(parents=True, exist_ok=True)
    else:
        workdir = Path(tempfile.mkdtemp(prefix="vera-mutate-diff-"))
    engine = list(args.engine) if args.engine else _default_engine()
    started = time.monotonic()
    try:
        return _lane(args, repo, workdir, engine, started)
    except Exception as exc:  # noqa: BLE001 — a failure of the lane is exit 2, reported; 1 means a survivor
        return _lane_failed(args, exc, started)


def _lane_failed(args: argparse.Namespace, exc: Exception, started: float) -> int:
    """Report a failure of the lane itself: exit 2, with the reason."""
    import traceback

    traceback.print_exc()
    error = f"{type(exc).__name__}: {exc}"
    summary = ("## Mutation testing over this diff\n\n"
               f"**Incomplete: the lane stopped before mutmut decided the diff.**\n\n"
               f"```\n{error}\n```\n")
    print(summary)
    if args.summary:
        with open(args.summary, "a", encoding="utf-8") as fh:
            fh.write(summary + "\n")
    if args.json:
        record = {"schema": 1, "exit_code": 2, "stopped": "lane", "error": error,
                  "outcome": "Incomplete: the lane stopped before mutmut decided the diff.",
                  "elapsed_s": round(time.monotonic() - started, 1), "functions": [], "files": []}
        Path(args.json).write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n",
                                   encoding="utf-8")
    return 2


def _lane(args: argparse.Namespace, repo: Path, workdir: Path, engine: list[str],
          started: float) -> int:
    """The lane: the diff, the scratch tree, the engine, the report."""
    base = _git(repo, "rev-parse", "--verify", f"{args.base}^{{commit}}").strip()
    head = _git(repo, "rev-parse", "--verify", f"{args.head}^{{commit}}").strip()
    merge_base = _git(repo, "merge-base", base, head).strip()
    # The prefixes are named because parse_diff reads them, and a developer's
    # git config can drop them (`diff.noprefix`).
    diff = _git(repo, "-c", "core.quotePath=false", "diff", "-U0", "--no-color",
                "--no-ext-diff", "--src-prefix=a/", "--dst-prefix=b/", "-M",
                merge_base, head, "--", "vera/")
    verdicts: list[FileVerdict] = []
    change_of: dict[str, FileChange] = {}
    for change in parse_diff(diff):
        base_src = _git(repo, "show", f"{merge_base}:{change.old_path}") if change.old_path else None
        head_src = _git(repo, "show", f"{head}:{change.new_path}") if change.new_path else None
        verdicts.append(classify(change, base_src, head_src))
        change_of[verdicts[-1].path] = change
    units = [u for v in verdicts for u in v.changed]
    changed_tests = _git(repo, "diff", "--name-only", "--diff-filter=d", merge_base, head,
                         "--", "tests/").split()
    # The files the pull request changes that a matrix can be decided by:
    # its instruments that name a changed module, or are changed, run in
    # full, as the pull request's test jobs run them.
    matrix_changed = _git(repo, "-c", "core.quotePath=false", "diff", "--name-only", merge_base,
                          head, "--", "vera/", "tests/").split()
    tree = workdir / "tree"
    oracle: dict[str, Any] = {"rule": ORACLE_RULE, "modules": {}}
    if any(u.excluded is None for u in units):
        tree.mkdir()
        _extract(repo, head, tree)
        # Today's plugin, so a replay of an older head confines its oracle
        # as this lane does.
        if (ROOT / "tests" / "mutation_oracle.py").is_file() and (tree / "tests").is_dir():
            shutil.copyfile(ROOT / "tests" / "mutation_oracle.py", tree / "tests" / "mutation_oracle.py")
        oracle = oracle_map(tree)
        units = [u if u.excluded is not None or oracle["modules"].get(u.path)
                 else replace(u, excluded="no declared oracle: " + UNDECLARED.get(
                     u.path, "no test file declares the module"))
                 for u in units]
    mutable = [u for u in units if u.excluded is None]

    # The engine runs the selected tests, and a test that spawns git must
    # not inherit a hook's GIT_DIR.  The copy caches bytecode: a mutated
    # module compiles in tens of seconds (vera/checker/calls.py with its
    # 3,515 mutants inlined is 24 MB and takes 47 s) and loads from its .pyc
    # in a fifth of a second, and under the fork server every pass and every
    # mutant's worker is a fresh process (#1829); the copy is written once a
    # run, before any import, so a stale .pyc cannot arise.
    env = _git_env()
    env.pop("PYTHONDONTWRITEBYTECODE", None)
    # pytest draws its rules the terminal's width, which engine_failure reads.
    env["COLUMNS"] = "80"
    # tests/mutation_oracle.py, which [tool.mutmut] loads, appends here each
    # test it keeps out of the oracle: for starting a Python or vera process,
    # and for reading the compiler's source.
    skips = workdir / "oracle-skips.txt"
    source_skips = workdir / "oracle-source-skips.txt"
    env[SKIPS_ENV] = str(skips)
    env[SOURCE_SKIPS_ENV] = str(source_skips)
    env[FAILURES_ENV] = str(workdir / "oracle-failures.txt")
    record: dict[str, Any] = {
        "schema": 2, "base": base, "merge_base": merge_base, "head": head,
        "engine_version": "", "budget_s": args.budget, "elapsed_s": 0.0,
        "workdir": workdir.as_posix(), "extra_tests": [], "tests_left_out": [],
        "files": [{"path": v.path, "changed": [u.qualname for u in v.changed],
                   "deleted": v.deleted, "outside": v.outside,
                   "outside_removed": v.outside_removed,
                   "unchanged_code": v.unchanged_code} for v in verdicts],
        "stopped": None, "engine_exit": None, "engine_error": None, "outside_diff": [],
        "outside_window": [], "engine_tail": [], "dropped_tests": [], "subprocess_tests": [],
        "source_tests": [], "window": None, "oracle": None, "matrix_seed": None, "passes": [],
    }
    rows: list[UnitResult] = []
    stopped: str | None = None
    if mutable:
        extra_tests, left_out = oracle_tests(changed_tests, tree)
        record["extra_tests"], record["tests_left_out"] = extra_tests, left_out
        files = sorted({u.path for u in mutable})
        # The declared oracle: the changed modules' declared test files, and
        # the pull request's own changed test files, which join each changed
        # module's oracle for this run.  The plugin confines each function's
        # tests to its module's (MUTATION_ORACLE_MAP).
        for path in files:
            oracle["modules"][path] = sorted(set(oracle["modules"][path]) | set(extra_tests))
        tests = oracle_of(oracle, files)
        map_file = workdir / "oracle-map.json"
        map_file.write_text(json.dumps(oracle, indent=1) + "\n", encoding="utf-8")
        env[ORACLE_MAP_ENV] = str(map_file)
        # Every matrix at its sample in the engine's run, under the run's
        # seed: run in full under mutmut's stats tracer, the changed modules'
        # instruments took a whole budget's stats pass (#1907's replay, run
        # 45406471525).  The cells the sample leaves out get their look at
        # the survivors alone (full_cell_probe).
        env.pop(MATRIX_CHANGED_ENV, None)
        record["matrix_changed"] = matrix_changed
        seed = f"diff-{head[:12]}"
        record["matrix_seed"] = seed
        env[MATRIX_SEED_ENV] = seed
        record["oracle"] = {"rule": oracle["rule"], "tests": len(tests),
                            "modules": {path: oracle["modules"][path] for path in files}}
        for path in files:
            keep = {u.key for u in mutable if u.path == path}
            source = (tree / path).read_text(encoding="utf-8")
            (tree / path).write_text(narrow(source, keep), encoding="utf-8")
        pyproject = tree / "pyproject.toml"
        config = pyproject.read_text(encoding="utf-8")
        # The window: each narrowed file's lines near the diff, inside the
        # units it changes, which the engine's run alone is handed.
        kept = {path: sorted(window(change_of[path], args.context) & {
                    n for u in mutable if u.path == path for n in range(u.start, u.end + 1)})
                for path in files}
        counts_file = workdir / "window-counts.json"
        window_file = workdir / "window.json"
        # The lines the diff changes in each file, so the engine can name the
        # window's mutants on none of them (neighbour_numbers).
        window_file.write_text(json.dumps({"context": args.context, "record": str(counts_file),
                                           "lines": kept,
                                           "changed": {path: sorted(change_of[path].added) for path in files},
                                           "removed_after": {path: sorted(change_of[path].deleted_after)
                                                             for path in files}},
                                          indent=1) + "\n", encoding="utf-8")
        record["window"] = {"context": args.context, "rule": rule(args.context), "lines": kept}
        if args.list:
            return _list(args, engine, tree, files, kept, record, env)
        record["engine_version"] = _engine_version(engine, env)

        def config_for(dropped: Sequence[str]) -> str:
            return rewrite_config(config, only_mutate=files, selection=tests, extra_tests=(),
                                  extra_args=[f"--deselect={test}" for test in dropped])

        # Two passes: mutmut runs a run's mutants cheapest first across every
        # function, so one run over all of them leaves a widely covered
        # function undecided whenever the budget runs out.  The first pass
        # names one window mutant of each changed function; the second the
        # mutants the first left undecided, in what is left of the budget.
        lane_start = time.monotonic()
        engine_budget = max(float(args.budget) - FULL_PROBE_RESERVE_S, float(args.budget) / 2)
        run_env = {**env, WINDOW_ENV: str(window_file)}
        first = [first_mutant(u.path, u.key) for u in mutable]
        done = _pass(1, first, engine, args, tree, pyproject, workdir, run_env, config_for,
                     engine_budget, (), started)
        owned = {(module_name(u.path), u.key) for u in mutable}
        rest = sorted(n for n, s in done.results.items()
                      if STATUSES[s] == "undecided" and unit_of_mutant(n) in owned)
        remaining = engine_budget - (time.monotonic() - lane_start)
        record["passes"].append(done.record(len(first)))
        if done.stopped is None and rest and not done.no_tests:
            if remaining > 0:
                done = _pass(2, rest, engine, args, tree, pyproject, workdir, run_env, config_for,
                             remaining, done.dropped, started)
                record["passes"].append(done.record(len(rest)))
            else:
                done.stopped = "budget"
        run, log, dropped, results, stopped, no_tests = (
            done.run, done.log, done.dropped, done.results, done.stopped, done.no_tests)
        if done.tail:
            record["engine_tail"] = done.tail
        record["dropped_tests"] = dropped
        record["engine_error"] = run.error
        record["subprocess_tests"] = skipped_tests(skips)
        record["source_tests"] = skipped_tests(source_skips)
        record["engine_exit"] = run.returncode
        if no_tests:
            results = {name: "no tests" for name in results}
        rows = tally(mutable, results)
        record["outside_diff"] = outside_units(mutable, results)
        if record["outside_diff"]:
            # In the narrowed tree every mutant belongs to a changed unit; one
            # that does not means the mapping or the narrowing went wrong.
            stopped = failed(stopped, "unmapped")
        counts = read_window_counts(counts_file)
        if counts is None:
            # Nothing says the engine generated the window's mutants alone.
            stopped = failed(stopped, "engine")
            record["window"]["error"] = (
                "the engine wrote no count of the window, so what it generated cannot be "
                "checked against the window")
        else:
            record["outside_window"] = place_in_window(rows, counts)
            if record["outside_window"]:
                stopped = failed(stopped, "unmapped")
        split_neighbours(rows, read_window_neighbours(counts_file))
        probe_budget = max(float(args.budget) - (time.monotonic() - lane_start), 0.0)
        record["budget_split"] = {"engine_s": round(engine_budget, 1), "probe_s": round(probe_budget, 1),
                                  "probe_cap_s": FULL_PROBE_CAP_S}
        if (tree / "mutants").is_dir():
            full_cell_probe(rows, tree, oracle, tomllib.loads(config_for(dropped))["tool"]["mutmut"].get(
                "pytest_add_cli_args", []), env, probe_budget, workdir / "oracle-killers.txt")
        else:
            for row in rows:
                row.probes.update({n: "not run: the engine left no generated tree" for n in row.survivors})
        record["budget_split"]["probed"] = sum(len(r.full_kills) + len(r.probes) for r in rows)
        record["budget_split"]["killed_in_full"] = sum(len(r.full_kills) for r in rows)
        show_until = time.monotonic() + SHOW_BUDGET_S
        for row, name in [(row, name) for row in rows for name in [*row.survivors, *row.neighbours]]:
            left = show_until - time.monotonic()
            if left <= 0:
                row.diffs[name] = SHOW_BUDGET_NOTE
                continue
            shown = _engine_call(engine, ["show", name], cwd=tree, env=env,
                                 timeout_s=min(ENGINE_CALL_TIMEOUT_S, left))
            if shown is None:
                row.diffs[name] = f"(mutmut show did not finish in {min(ENGINE_CALL_TIMEOUT_S, left):.0f} s)"
            else:
                row.diffs[name] = shown.stdout if shown.returncode == 0 else shown.stderr
        if stopped is not None and not record["engine_tail"]:
            record["engine_tail"] = _tail(log)
    if args.list:
        # No function to mutate: an empty list.
        record.update(list={}, list_error=None)
        print("mutate_diff --list: the diff changes no function mutmut mutates")
        if args.json:
            Path(args.json).write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n",
                                       encoding="utf-8")
        return 0
    excluded_rows = [UnitResult(path=u.path, key=u.key, qualname=u.qualname,
                                excluded=u.excluded, mutants=0, counts={}, survivors=[],
                                observable=True) for u in units if u.excluded is not None]
    code = exit_code(rows, stopped=stopped)
    if record["window"] is not None:
        record["window"]["selection"] = selection(rows)
    record["stopped"] = stopped
    record["exit_code"] = code
    record["outcome"] = outcome(code, rows, stopped, undeclared=sum(
        1 for u in units if (u.excluded or "").startswith("no declared oracle")))
    record["elapsed_s"] = round(time.monotonic() - started, 1)
    record["functions"] = [
        {**{k: v for k, v in asdict(row).items() if k not in ("diffs", "neighbours", "full_kills", "probes")},
         "survivors": [{"name": n, "diff": row.diffs.get(n, ""), "probe": row.probes.get(n)} for n in row.survivors],
         "killed_in_full": [{"name": n, "test": t} for n, t in sorted(row.full_kills.items())],
         "neighbour_survivors": [{"name": n, "diff": row.diffs.get(n, "")} for n in row.neighbours]}
        for row in [*rows, *excluded_rows]
    ]
    summary = render(record)
    print(summary)
    warning = annotation(code, record["outcome"])
    if warning is not None:
        print(warning)
    if args.summary:
        with open(args.summary, "a", encoding="utf-8") as fh:
            fh.write(summary + "\n")
    if args.json:
        Path(args.json).write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n",
                                   encoding="utf-8")
    return code


if __name__ == "__main__":
    if sys.argv[1:2] == [ENGINE_ARG]:
        raise SystemExit(engine_main(sys.argv[2:]))
    raise SystemExit(main())
