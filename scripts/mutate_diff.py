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
   ``only_mutate`` set to those files and the pull request's own changed
   test files that reach the compiler in process (they import ``vera``,
   directly or through a ``tests/`` helper) added to the test selection, bar
   the families the selection leaves out on purpose.  mutmut then runs over
   one glob per changed unit (``vera.smt.xǁSmtContextǁreset__mutmut_*``):
   its stats pass records which tests reach each function, and each mutant
   runs only those tests, fastest first, stopping at the first failure.  A
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
generated, decided and surviving; the first ``MAX_SHOWN_SURVIVORS``
survivors' ``mutmut show`` diffs; and a JSON record (``--json``) that lists
every survivor.

The exit code is red for a defect and green for an unfinished run.  It is 1
when a mutant of the diff survives, whatever else stopped the run; 2 when the
run itself failed, whether or not the budget ran out first: the engine
failed or counted no window, mutmut reported a mutant of a function the lane
did not map to the diff or more or fewer of a function's mutants than its
window holds, or the lane itself failed before mutmut decided anything; and
0 otherwise, a run the budget stopped included.
An exit 0 says what it decided in the headline: every mutant killed or timed
out, or how many functions no in-process test reaches, or, where the budget
ran out or a mutant was left undecided (``not checked``, ``suspicious``,
``segfault``, interrupted), that the run is incomplete, which a
``::warning::`` annotation repeats on the pull request.
A function no in-process test reaches has every mutant ``no tests``: it is
reported as not observable in process, the rule MUTATION.md states for
``cli.py``, and does not fail the run.

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
import tempfile
import time
import tokenize
from collections import Counter
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import asdict, dataclass, field
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

#: The variable that names the window file for the engine's ``run``.
WINDOW_ENV = "MUTATE_DIFF_WINDOW"

#: The first argument that runs this script as the engine (:func:`engine_main`).
ENGINE_ARG = "--as-engine"

#: The exit status of an engine that cannot apply the window: an engine
#: failure to the lane, never a survivor's 1.
NO_WINDOW_EXIT = 3

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

#: The rule that heads a section or a report of pytest's output, and the
#: one that heads a section of what a test printed or logged (``Captured
#: stderr call``), which runs to the next rule.
_SECTION = re.compile(r"^[-_=]{3,} .+ [-_=]{3,}$")
_CAPTURED = re.compile(r"^-{3,} Captured .+ -{3,}$")

#: A file of what mutmut's copy holds: its tests and the code under test.
_COPY_FILE = re.compile(r"(?:^|[\\/])(?:mutants|tests)[\\/]")

#: A ``RecursionError`` runs out of stack in whatever frame it reached, and
#: inside the copy every call through mutmut's trampoline adds the engine's
#: frames, so it is the engine's only when none of its innermost frames
#: outside the standard library, this many, is the copy's.
RECURSION_FRAMES = 10

#: Survivors whose ``mutmut show`` diff the summary carries: a step summary
#: over 1 MiB is dropped whole, and the record lists every survivor.
MAX_SHOWN_SURVIVORS = 60


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
                   extra_args: Sequence[str] = (), also_copy: Sequence[str] | None = None) -> str:
    """``text`` with ``[tool.mutmut]``'s ``only_mutate`` replaced, ``extra_tests``
    added to its test selection and ``extra_args`` to its pytest arguments, and
    ``also_copy`` replaced when given; everything else unchanged."""
    data = tomllib.loads(text)
    cfg = data.get("tool", {}).get("mutmut")
    if not isinstance(cfg, dict):
        raise ConfigError("pyproject.toml has no [tool.mutmut] table")
    new = dict(cfg)
    new["only_mutate"] = list(only_mutate)
    if also_copy is not None:
        new["also_copy"] = list(also_copy)
    selection = list(cfg.get("pytest_add_cli_args_test_selection", []))
    selection += [t for t in extra_tests if t not in selection]
    new["pytest_add_cli_args_test_selection"] = selection
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
    :data:`ENCLOSING_KINDS` that spans one of them (:func:`first_lines`).
    Before that, each file's mutants are counted per unit by mutmut's own
    visitor, of every line and of the window's (:func:`_unit_counts`), so
    the lane can check what the engine generated against the window.  A
    mutmut without the hook or the visitor raises :class:`WindowError`."""
    spec = json.loads(window_file.read_text(encoding="utf-8"))
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
        lines = kept[path] = frozenset(named) | first_lines(enclosing_spans(source), named)
        held = _unit_counts(create_mutations, path, source, None)
        inside = _unit_counts(create_mutations, path, source, lines)
        counts[path] = {key: {"held": held[key], "window": inside[key]}
                        for key in sorted(set(held) | set(inside))}
    Path(spec["record"]).write_text(json.dumps({"files": counts}, indent=1) + "\n", encoding="utf-8")

    def covered(filename: str, covered_lines: Any) -> Any:
        lines = kept.get(Path(filename).as_posix())
        return hook(filename, covered_lines) if lines is None else set(lines)

    engine.get_covered_lines_for_file = covered


def engine_main(args: Sequence[str]) -> int:
    """mutmut's command line, its ``run`` generating only the window's
    mutants when :data:`WINDOW_ENV` names the lane's window file: the lane's
    default engine, this script run with :data:`ENGINE_ARG` first.  An engine
    that cannot apply the window stops with :data:`NO_WINDOW_EXIT` before it
    generates anything, which the lane reads as an engine failure."""
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


def run_engine(cmd: Sequence[str], *, cwd: Path, budget_s: float, log_path: Path,
               env: Mapping[str, str] | None = None,
               grace_s: tuple[float, float] = (60.0, 30.0)) -> EngineRun:
    """Run ``cmd`` within ``budget_s`` wall-clock seconds, its output to
    ``log_path``.  Past the budget: an interrupt, then after ``grace_s[0]``
    a terminate to its process group, then after ``grace_s[1]`` a kill."""
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
        steps: list[tuple[Any, float | None]] = []
        if posix:
            steps = [(lambda: proc.send_signal(signal.SIGINT), grace_s[0]),
                     (lambda: os.killpg(proc.pid, signal.SIGTERM), grace_s[1]),
                     (lambda: os.killpg(proc.pid, signal.SIGKILL), None)]
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
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        return EngineRun(returncode, "budget", time.monotonic() - start)


def run_dropping(cmd: Sequence[str], *, tree: Path, pyproject: Path,
                 config_for: Callable[[Sequence[str]], str], budget_s: float, workdir: Path,
                 env: Mapping[str, str]) -> tuple[EngineRun, Path, list[str]]:
    """Run the engine in ``tree`` within ``budget_s``; when a test stops its
    stats pass or its clean run (it fails inside mutmut's copy with no mutant
    active, so it is no oracle there), drop it and run again in what is left
    of the budget, up to ``MAX_COPY_DROPS`` tests.  When the engine's own code
    raised instead (:func:`engine_failure`), no test is at fault: the run
    stops there, drops no further test, and the returned run's ``error``
    names the exception and the engine's frame.  ``config_for(dropped)`` is the
    ``pyproject.toml`` text for a run without the tests dropped so far.
    Returns the last run, its log and the tests dropped."""
    dropped: list[str] = []
    remaining = budget_s
    attempt = 0
    while True:
        attempt += 1
        pyproject.write_text(config_for(dropped), encoding="utf-8")
        log = workdir / f"mutmut-run-{attempt}.log"
        run = run_engine(cmd, cwd=tree, budget_s=remaining, log_path=log, env=env)
        remaining -= run.elapsed_s
        if run.stopped is not None or run.returncode != 1:
            return run, log, dropped
        text = log.read_text(encoding="utf-8", errors="replace")
        run.error = engine_failure(text)
        failing = None if run.error is not None else copy_failure(text)
        if (failing is None or failing in dropped or len(dropped) >= MAX_COPY_DROPS
                or remaining <= 0):
            return run, log, dropped
        dropped.append(failing)


def copy_failure(log: str) -> str | None:
    """The test that stopped mutmut's stats pass or its clean run, read off
    its log, when that is how the run stopped."""
    if not any(stop in log for stop in _COPY_STOPS):
        return None
    match = re.search(r"^(?:FAILED|ERROR) (.+?)(?: - .*)?$", log, re.M)
    return match.group(1).strip() if match else None


def engine_failure(log: str) -> str | None:
    """The exception the engine's own code raised that stopped its stats pass
    or its clean run, read off its log: the exception's first line and the
    engine's frame, ``AttributeError: … (mutmut/runners/harness.py:157)``;
    None when the log names no such stop, or a test's code raised.

    The log of a run its stats pass or its clean run stopped holds that
    pass's output alone: mutmut prints it only when the pass fails, and
    exits there.  Its reports carry tracebacks in Python's own form, an
    internal error's with :data:`_INTERNAL_ERROR` on every line; what a test
    printed or logged (:data:`_CAPTURED`) is no report and is not read.
    Going outward from a traceback's innermost frame, past the frames no
    party's code is in (:data:`_NEUTRAL_FILE`), the first frame decides: a
    file of the installed ``mutmut`` package is the engine's code (a hook of
    its stats pass, its trampoline), and any other (the test, the code under
    test, a library either calls, pytest) is the test's.  A
    ``RecursionError`` is the engine's only when, besides, no frame of the
    copy lies among its :data:`RECURSION_FRAMES` innermost frames outside
    the standard library."""
    if not any(stop in log for stop in _COPY_STOPS):
        return None
    lines: list[str] = []
    captured = False
    for row in log.splitlines():
        row = row.removeprefix(_INTERNAL_ERROR)
        if _SECTION.match(row.rstrip()):
            captured = _CAPTURED.match(row.rstrip()) is not None
        if not captured:
            lines.append(row)
    for start, line in enumerate(lines):
        if line.rstrip() != "Traceback (most recent call last):":
            continue
        frames: list[re.Match[str]] = []
        raised: str | None = None
        for row in lines[start + 1:]:
            frame = _FRAME.match(row.rstrip())
            if frame is not None:
                frames.append(frame)
            elif row.strip() and not row[0].isspace():
                raised = row.strip()
                break
        if raised is None:
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
    }


def failed(stopped: str | None, failure: str) -> str:
    """How the run stopped once ``failure`` (``engine`` or ``unmapped``) is
    found too.  A failure outranks the budget, which leaves a run only
    incomplete, so a run the budget stopped that then failed is red; of two
    failures the first is the one recorded."""
    return failure if stopped in (None, "budget") else stopped


def exit_code(rows: Sequence[UnitResult], *, stopped: str | None) -> int:
    """1: a survivor, whatever stopped the run; 2: the run itself failed (the
    engine, or a mutant the lane did not map); 0 otherwise, an incomplete run
    (the budget ran out, a mutant left undecided) included."""
    statuses = {status for row in rows for status, n in row.counts.items() if n}
    if "survived" in statuses:
        return 1
    if stopped in ("engine", "unmapped"):
        return 2
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
            if row["mutants"] and not row["observable"]:
                other = "not observable in process (no in-process test reaches it)"
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
        shown = [s for s in survivors if s["diff"]]
        for survivor in shown:
            out.append(f"`{survivor['name']}`")
            out.append("")
            out.append("```diff")
            out.extend(survivor["diff"].rstrip("\n").splitlines())
            out.append("```")
            out.append("")
        if len(survivors) > len(shown):
            out.append(f"{len(survivors) - len(shown)} more survivors are in the JSON record, "
                       "by name, without their diffs.")
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


def outcome(code: int, rows: Sequence[UnitResult], stopped: str | None) -> str:
    """The headline: what the run decided.  An exit 0 claims every mutant
    killed or timed out only when every changed function had mutants and an
    in-process test reached them and the run decided every mutant; otherwise
    it says what was not tested, or that the run is incomplete."""
    unfinished = _incomplete(rows, stopped)
    if code == 0 and unfinished is not None:
        return f"Incomplete: {unfinished}."
    if code == 0:
        if not rows:
            return "Pass: nothing to mutate."
        unobserved = [r for r in rows if r.mutants and not r.observable]
        empty = [r for r in rows if not r.mutants]
        skipped = sum(r.counts.get("skipped", 0) for r in rows)
        if not unobserved and not empty and not skipped:
            return "Pass: every mutant of the diff is killed or timed out."
        parts = []
        if unobserved:
            parts.append(f"{sum(r.mutants for r in unobserved)} mutant(s) in "
                         f"{len(unobserved)} function(s) not observable in process")
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
                 env: Mapping[str, str]) -> subprocess.CompletedProcess[str] | None:
    """A short engine command, or None when it does not finish in time."""
    try:
        return subprocess.run([*engine, *args], cwd=cwd, capture_output=True, text=True,
                              encoding="utf-8", env=dict(env), check=False,
                              timeout=ENGINE_CALL_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        return None


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
    mutable = [u for u in units if u.excluded is None]
    changed_tests = _git(repo, "diff", "--name-only", "--diff-filter=d", merge_base, head,
                         "--", "tests/").split()

    # The engine runs the selected tests, and a test that spawns git must
    # not inherit a hook's GIT_DIR.
    env = _git_env()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    # tests/mutation_oracle.py, which [tool.mutmut] loads, appends here each
    # test it keeps out of the oracle for starting a Python or vera process.
    skips = workdir / "oracle-skips.txt"
    env["MUTATION_ORACLE_SKIPS"] = str(skips)
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
        "window": None,
    }
    rows: list[UnitResult] = []
    stopped: str | None = None
    if mutable:
        tree = workdir / "tree"
        tree.mkdir()
        _extract(repo, head, tree)
        extra_tests, left_out = oracle_tests(changed_tests, tree)
        record["extra_tests"], record["tests_left_out"] = extra_tests, left_out
        files = sorted({u.path for u in mutable})
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
        window_file.write_text(json.dumps({"context": args.context, "record": str(counts_file),
                                           "lines": kept}, indent=1) + "\n", encoding="utf-8")
        record["window"] = {"context": args.context, "rule": rule(args.context), "lines": kept}
        record["engine_version"] = _engine_version(engine, env)
        globs = [mutant_glob(u.path, u.key) for u in mutable]
        run, log, dropped = run_dropping(
            [*engine, "run", "--max-children", str(args.max_children), *globs],
            tree=tree, pyproject=pyproject, budget_s=args.budget, workdir=workdir,
            env={**env, WINDOW_ENV: str(window_file)},
            config_for=lambda dropped: rewrite_config(
                config, only_mutate=files, extra_tests=extra_tests,
                extra_args=[f"--deselect={test}" for test in dropped]))
        record["dropped_tests"] = dropped
        record["engine_error"] = run.error
        if skips.exists():
            # One node id a line: a parametrised id can hold a space.
            record["subprocess_tests"] = sorted(
                {line for line in skips.read_text(encoding="utf-8").splitlines() if line.strip()})
        record["engine_exit"] = run.returncode
        no_tests = run.returncode == 1 and NO_TESTS_SENTENCE in log.read_text(
            encoding="utf-8", errors="replace")
        stopped = run.stopped or (None if run.returncode == 0 or no_tests else "engine")
        listed = _engine_call(engine, ["results", "--all", "true"], cwd=tree, env=env)
        results: dict[str, str] = {}
        if listed is None:
            stopped = failed(stopped, "engine")
            record["engine_tail"] = [f"mutmut results did not finish in {ENGINE_CALL_TIMEOUT_S} s"]
        elif listed.returncode != 0:
            stopped = failed(stopped, "engine")
        else:
            try:
                results = parse_results(listed.stdout)
            except ResultsError as exc:
                stopped = failed(stopped, "engine")
                record["engine_tail"] = [str(exc)]
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
        to_show = [(row, name) for row in rows for name in row.survivors][:MAX_SHOWN_SURVIVORS]
        for row, name in to_show:
            shown = _engine_call(engine, ["show", name], cwd=tree, env=env)
            if shown is None:
                row.diffs[name] = f"(mutmut show did not finish in {ENGINE_CALL_TIMEOUT_S} s)"
            else:
                row.diffs[name] = shown.stdout if shown.returncode == 0 else shown.stderr
        if stopped is not None and not record["engine_tail"]:
            record["engine_tail"] = _tail(log)
    excluded_rows = [UnitResult(path=u.path, key=u.key, qualname=u.qualname,
                                excluded=u.excluded, mutants=0, counts={}, survivors=[],
                                observable=True) for u in units if u.excluded is not None]
    code = exit_code(rows, stopped=stopped)
    if record["window"] is not None:
        record["window"]["selection"] = selection(rows)
    record["stopped"] = stopped
    record["exit_code"] = code
    record["outcome"] = outcome(code, rows, stopped)
    record["elapsed_s"] = round(time.monotonic() - started, 1)
    record["functions"] = [
        {**{k: v for k, v in asdict(row).items() if k != "diffs"},
         "survivors": [{"name": n, "diff": row.diffs.get(n, "")} for n in row.survivors]}
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
