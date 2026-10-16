#!/usr/bin/env python3
"""Mutation testing scoped to a diff: mutate the functions a change touches.

The pull request lane of MUTATION.md § CI.  From ``git diff <base>...<head>``
over ``vera/``, the script finds the functions mutmut mutates as units (a
top-level function, or a method of a top-level class; a nested function is
part of the one that encloses it) whose code the diff changes, and runs
mutmut over exactly those functions:

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
3. The scratch tree's ``[tool.mutmut]`` is the repository's, with
   ``only_mutate`` set to those files and the pull request's own changed
   test files that reach the compiler in process (they import ``vera``,
   directly or through a ``tests/`` helper) added to the test selection, bar
   the families the selection leaves out on purpose.  mutmut then runs over
   one glob per changed unit (``vera.smt.xǁSmtContextǁreset__mutmut_*``):
   its stats pass records which tests reach each function, and each mutant
   runs only those tests, fastest first, stopping at the first failure.  A
   test that fails inside mutmut's copy with no mutant active (one that reads
   a file the copy lacks, or ``vera/``'s source text, which in the copy is
   mutmut's generated file) stops that pass; it is no oracle there, so the
   lane drops it, runs again, and names it in the summary and the record.
4. The run has a wall-clock budget.  When it runs out, mutmut is
   interrupted, then its process group terminated, then killed, and what it
   decided so far is reported.

Outputs: a table per function on stdout (and in ``--summary``, the job
summary in CI), the first ``MAX_SHOWN_SURVIVORS`` survivors' ``mutmut show``
diffs, and a JSON record (``--json``) that lists every survivor.

The exit code is 0 when no mutant of the diff survives and none is left
undecided, the headline saying whether every mutant was killed or timed out
or how many functions no in-process test reaches; 1 when one survives; and 2
when the run stopped short: the budget ran out, the engine failed, a mutant
was left undecided (``not checked``, ``suspicious``, ``segfault``,
interrupted), or mutmut reported a mutant of a function the lane did not
map to the diff.  A run that cannot finish says so; it never passes.  A
function no in-process test reaches has every mutant ``no tests``: it is
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
from collections.abc import Iterable, Mapping, Sequence
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

#: Seconds for each short engine command (``results``, ``show``, ``--version``).
ENGINE_CALL_TIMEOUT_S = 300

#: Tests the lane drops from one run before it calls the run stopped short.
MAX_COPY_DROPS = 5

#: What mutmut prints when its stats pass or its clean run of the covering
#: tests stops on a failing test (both run with ``-x``).
_COPY_STOPS = ("failed to collect stats", "Failed to run clean test")

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
    removed and added), and the base lines it removes."""

    old_path: str | None
    new_path: str | None
    added: frozenset[int]
    removed: frozenset[int]


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
            ))

    for line in text.splitlines():
        if line.startswith("diff --git "):
            flush()
            match = re.match(r"^diff --git a/(\S+) b/(\S+)$", line)
            if match is None:
                raise DiffError(f"unsupported file header: {line}")
            section = {"old": match.group(1), "new": match.group(2),
                       "added": set(), "removed": set(), "hunks": False}
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
    flush()
    return changes


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
                   extra_args: Sequence[str] = ()) -> str:
    """``text`` with ``[tool.mutmut]``'s ``only_mutate`` replaced, ``extra_tests``
    added to its test selection and ``extra_args`` to its pytest arguments;
    everything else unchanged."""
    data = tomllib.loads(text)
    cfg = data.get("tool", {}).get("mutmut")
    if not isinstance(cfg, dict):
        raise ConfigError("pyproject.toml has no [tool.mutmut] table")
    new = dict(cfg)
    new["only_mutate"] = list(only_mutate)
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
# The engine
# ---------------------------------------------------------------------------


@dataclass
class EngineRun:
    """How a run of the engine ended."""

    returncode: int | None
    stopped: str | None
    elapsed_s: float


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


def copy_failure(log: str) -> str | None:
    """The test that stopped mutmut's stats pass or its clean run, read off
    its log, when that is how the run stopped."""
    if not any(stop in log for stop in _COPY_STOPS):
        return None
    match = re.search(r"^(?:FAILED|ERROR) (.+?)(?: - .*)?$", log, re.M)
    return match.group(1).strip() if match else None


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


def exit_code(rows: Sequence[UnitResult], *, stopped: str | None) -> int:
    """0: no survivor and nothing undecided; 1: a survivor; 2: stopped short."""
    statuses = {status for row in rows for status, n in row.counts.items() if n}
    if stopped is not None or any(STATUSES[s] == "undecided" for s in statuses):
        return 2
    if "survived" in statuses:
        return 1
    return 0


# ---------------------------------------------------------------------------
# The report
# ---------------------------------------------------------------------------


_COLUMNS = ("killed", "timeout", "survived")


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
        out.append("Each failed inside mutmut's copy with no mutant active (it reads a file the copy "
                   "lacks, or `vera/`'s source text, which in the copy is mutmut's generated file), "
                   "so it is no oracle there; the run went again without it:")
        out.append("")
        out.extend(f"- `{test}`" for test in record["dropped_tests"])
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
    in-process test reached them; otherwise it says what was not tested."""
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
        return f"Fail: {n} mutant(s) of the diff survive."
    if stopped == "budget":
        return "Incomplete: the budget ran out before every mutant was decided."
    if stopped == "engine":
        return "Incomplete: the engine stopped before every mutant was decided."
    if stopped == "unmapped":
        return ("Incomplete: mutmut reported mutants of functions the lane did not map to "
                "the diff, so the diff is not decided.")
    return "Incomplete: mutants of the diff were left undecided."


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
    beside = Path(sys.executable).with_name("mutmut")
    return [str(beside)] if beside.exists() else ["mutmut"]


def _tail(path: Path, lines: int = 40) -> list[str]:
    """The engine log's last lines, its spinner frames dropped."""
    if not path.exists():
        return []
    text = path.read_text(encoding="utf-8", errors="replace")
    rows = [r.rstrip() for r in re.split(r"[\r\n]+", text)
            if r.strip() and not re.match(r"\s*[\u2800-\u28ff] ", r)]
    return rows[-lines:]


def main(argv: Sequence[str] | None = None) -> int:
    """Run the lane; return its exit code."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default=str(ROOT), help="the repository (default: this one)")
    parser.add_argument("--base", default="origin/main",
                        help="the base; the diff is from its merge base with --head")
    parser.add_argument("--head", default="HEAD", help="the head commit (default HEAD)")
    parser.add_argument("--budget", type=float, default=DEFAULT_BUDGET_S,
                        help=f"wall-clock seconds for mutmut (default {DEFAULT_BUDGET_S})")
    parser.add_argument("--max-children", type=int, default=os.cpu_count() or 1,
                        help="mutmut's parallel workers (default: every CPU)")
    parser.add_argument("--workdir", help="an empty or absent directory for the scratch "
                        "tree and logs (default: a new temporary directory)")
    parser.add_argument("--json", help="write the JSON record here")
    parser.add_argument("--summary", help="append the Markdown summary here")
    parser.add_argument("--engine", nargs="+", help="the mutmut command (default: the "
                        "mutmut beside this interpreter)")
    args = parser.parse_args(argv)

    repo = Path(args.repo).resolve()
    if args.workdir:
        workdir = Path(args.workdir)
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
    for change in parse_diff(diff):
        base_src = _git(repo, "show", f"{merge_base}:{change.old_path}") if change.old_path else None
        head_src = _git(repo, "show", f"{head}:{change.new_path}") if change.new_path else None
        verdicts.append(classify(change, base_src, head_src))
    units = [u for v in verdicts for u in v.changed]
    mutable = [u for u in units if u.excluded is None]
    changed_tests = _git(repo, "diff", "--name-only", "--diff-filter=d", merge_base, head,
                         "--", "tests/").split()

    # The engine runs the selected tests, and a test that spawns git must
    # not inherit a hook's GIT_DIR.
    env = _git_env()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    record: dict[str, Any] = {
        "schema": 1, "base": base, "merge_base": merge_base, "head": head,
        "engine_version": "", "budget_s": args.budget, "elapsed_s": 0.0,
        "workdir": workdir.as_posix(), "extra_tests": [], "tests_left_out": [],
        "files": [{"path": v.path, "changed": [u.qualname for u in v.changed],
                   "deleted": v.deleted, "outside": v.outside,
                   "outside_removed": v.outside_removed,
                   "unchanged_code": v.unchanged_code} for v in verdicts],
        "stopped": None, "engine_exit": None, "outside_diff": [], "engine_tail": [],
        "dropped_tests": [],
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
        record["engine_version"] = _engine_version(engine, env)
        globs = [mutant_glob(u.path, u.key) for u in mutable]
        dropped: list[str] = []
        remaining = args.budget
        attempt = 0
        while True:
            attempt += 1
            pyproject.write_text(rewrite_config(
                config, only_mutate=files, extra_tests=extra_tests,
                extra_args=[f"--deselect={test}" for test in dropped]), encoding="utf-8")
            log = workdir / f"mutmut-run-{attempt}.log"
            run = run_engine([*engine, "run", "--max-children", str(args.max_children), *globs],
                             cwd=tree, budget_s=remaining, log_path=log, env=env)
            remaining -= run.elapsed_s
            failing = (copy_failure(log.read_text(encoding="utf-8", errors="replace"))
                       if run.stopped is None and run.returncode == 1 else None)
            if (failing is None or failing in dropped or len(dropped) >= MAX_COPY_DROPS
                    or remaining <= 0):
                break
            # The test cannot pass in mutmut's copy with no mutant active, so it
            # is no oracle there: drop it, and run again.
            dropped.append(failing)
        record["dropped_tests"] = dropped
        record["engine_exit"] = run.returncode
        no_tests = run.returncode == 1 and NO_TESTS_SENTENCE in log.read_text(
            encoding="utf-8", errors="replace")
        stopped = run.stopped or (None if run.returncode == 0 or no_tests else "engine")
        listed = _engine_call(engine, ["results", "--all", "true"], cwd=tree, env=env)
        results: dict[str, str] = {}
        if listed is None:
            stopped = stopped or "engine"
            record["engine_tail"] = [f"mutmut results did not finish in {ENGINE_CALL_TIMEOUT_S} s"]
        elif listed.returncode != 0:
            stopped = stopped or "engine"
        else:
            try:
                results = parse_results(listed.stdout)
            except ResultsError as exc:
                stopped = stopped or "engine"
                record["engine_tail"] = [str(exc)]
        if no_tests:
            results = {name: "no tests" for name in results}
        rows = tally(mutable, results)
        record["outside_diff"] = outside_units(mutable, results)
        if record["outside_diff"]:
            # In the narrowed tree every mutant belongs to a changed unit; one
            # that does not means the mapping or the narrowing went wrong.
            stopped = stopped or "unmapped"
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
    if args.summary:
        with open(args.summary, "a", encoding="utf-8") as fh:
            fh.write(summary + "\n")
    if args.json:
        Path(args.json).write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n",
                                   encoding="utf-8")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
