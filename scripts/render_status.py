#!/usr/bin/env python
"""Write TESTING.md's generated status from the tree.

A count lives in one place, and that place is generated.  This script
measures the tree and writes three blocks into TESTING.md, each between a
pair of `render_status` markers, and nowhere else:

- ``status``: the headline test totals (the tests collected, the test files
  and their lines) and the counts of conformance programs, examples, corpus
  programs, built-in functions, effects, spec chapters, pre-commit hooks,
  CI jobs and gate scripts;
- ``test-files``: one row per test file, with its collected tests, its lines
  and the first paragraph of its module docstring;
- ``skipped-tests``: every conformance-stage test the suite skips, asked of
  ``tests/test_conformance.py`` itself rather than restated.

The test counts are a collection's, not a run's.  ``pytest --collect-only
-o addopts= --matrix=full`` counts the stress tests and every cell of the
class-instrument matrices, so a file's count is its whole size rather than
the pull-request gate's weekly sample, and the counts are the same on every
machine that runs it.  A run's passed, skipped and xfailed split depends on
the platform and costs the whole suite, so the block does not state one.

The release PR runs this script and commits what it writes.
``scripts/check_doc_counts.py --release`` fails when a block is not what the
script would write now (`stale_blocks`); between releases nothing reads the
blocks, so a fix PR never has a count to update.
"""

from __future__ import annotations

import argparse
import ast
import importlib.util
import itertools
import json
import re
import subprocess
import sys
from collections.abc import Callable, Mapping
from pathlib import Path
from typing import Any, NamedTuple

ROOT = Path(__file__).resolve().parent.parent
DOCUMENT = "TESTING.md"
BLOCKS = ("status", "test-files", "skipped-tests")

# What the collection is asked for: every test, quietly.  `-o addopts=`
# drops pyproject's `-m 'not stress'`, and `--matrix=full` keeps every cell
# of a file marked `matrix`, which a default collection samples
# (tests/matrix_sample.py).
COLLECT_ARGS = ("--collect-only", "-q", "-o", "addopts=", "--matrix=full")

# About ten seconds on an idle machine.  The release PR runs this, so the
# budget is generous; an expired one is a reason, not a traceback.
COLLECT_TIMEOUT_SECONDS = 300

# The stage methods of the conformance tests replace these three module
# names with a stop, so a stage that does not skip stops at the first piece
# of work it reaches (`conformance_skips`).
_CONFORMANCE_WORK = ("_vera", "parse_file", "format_source")

_LEVEL_ORDER = ("parse", "check", "verify", "run")


def begin_marker(name: str) -> str:
    return f"<!-- render_status:begin {name} -->"


def end_marker(name: str) -> str:
    return f"<!-- render_status:end {name} -->"


class Collection(NamedTuple):
    """What a collection counted: the total, and each file's share."""

    total: int
    per_file: dict[str, int]


class Skip(NamedTuple):
    """One conformance-stage test the suite skips."""

    test: str
    program: str
    level: str
    message: str
    about: str


class Tree(NamedTuple):
    """Everything the blocks state, measured once by `measure`."""

    collection: Collection
    test_files: dict[str, tuple[int, str]]
    manifest: list[dict[str, Any]]
    examples: int
    corpus: int
    builtins: int
    effects: int
    chapters: int
    hooks: dict[str, int]
    ci_jobs: int
    matrix_cells: dict[str, int]
    gate_scripts: int
    skips: list[Skip]


# ---------------------------------------------------------------------------
# Measuring
# ---------------------------------------------------------------------------


def parse_collection(stdout: str) -> Collection | str:
    """The total and per-file counts of a quiet collection's output.

    The node ids come first, one per line, up to the first blank line; the
    summary line after them says how many were collected.  The two must
    agree, or the output is not one this reader understands.
    """
    lines = stdout.splitlines()
    ids: list[str] = []
    for line in lines:
        if not line.strip():
            break
        if "::" in line:
            ids.append(line)
    summary = re.search(r"^(\d+)(?:/\d+)? tests? collected", stdout, re.M)
    if summary is None:
        return "the pytest collection printed no `N tests collected` line"
    total = int(summary.group(1))
    if total != len(ids):
        return (
            f"the pytest collection says {total} tests were collected but "
            f"lists {len(ids)} node ids"
        )
    per_file: dict[str, int] = {}
    for node in ids:
        path = node.split("::", 1)[0]
        name = path.removeprefix("tests/")
        per_file[name] = per_file.get(name, 0) + 1
    return Collection(total, per_file)


def _pytest_command(root: Path) -> list[str]:
    venv = root / ".venv" / "bin" / "pytest"
    if venv.exists():
        return [str(venv)]
    return [sys.executable, "-m", "pytest"]


def collect(
    root: Path, *, run: Callable[..., Any] = subprocess.run
) -> Collection | str:
    """The collection of every test under `root`, or why it failed."""
    command = [*_pytest_command(root), *COLLECT_ARGS]
    try:
        result = run(
            command,
            cwd=str(root),
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=COLLECT_TIMEOUT_SECONDS,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return (
            f"pytest collection did not finish within {COLLECT_TIMEOUT_SECONDS} s,"
            " which a loaded machine can cause; run it again"
        )
    if result.returncode != 0:
        detail = "\n".join(
            f"{result.stdout or ''}{result.stderr or ''}".strip().splitlines()[-20:]
        )
        return f"pytest collection failed:\n{detail or '(no output)'}"
    return parse_collection(result.stdout)


def summary_of(source: str) -> str:
    """The first paragraph of a module's docstring, on one line and safe in
    a table cell; empty when the module has none."""
    try:
        doc = ast.get_docstring(ast.parse(source)) or ""
    except SyntaxError:
        return ""
    paragraph = re.split(r"\n\s*\n", doc.strip(), maxsplit=1)[0]
    return " ".join(paragraph.split()).replace("|", "\\|")


def registry_counts(root: Path) -> tuple[int, int]:
    """The built-in functions and the effects, as `vera builtins` and
    `vera effects` list them.  The caller puts `root` first on `sys.path`,
    so these are the counts of the tree being measured."""
    from vera.introspect import builtins_payload, effects_payload

    builtins = builtins_payload()["items"]
    effects = effects_payload()["items"]
    assert isinstance(builtins, list) and isinstance(effects, list)
    return len(builtins), sum(1 for item in effects if item["kind"] == "effect")


def _conformance_module(path: Path) -> Any:
    spec = importlib.util.spec_from_file_location("_render_status_conformance", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class _Reached(Exception):
    """A conformance stage reached a piece of work, so it does not skip."""


def _stop(*_args: object, **_kwargs: object) -> None:
    raise _Reached


def _about(entry: dict[str, Any]) -> str:
    title = str(entry.get("title", ""))
    code = entry.get("expected_error")
    if code is None:
        return title
    stage = entry.get("expected_error_stage", "check")
    where = "" if stage == "check" else f" at `{stage}`"
    return f"{title}; negative: `expected_error: {code}`{where}"


def conformance_skips(root: Path) -> list[Skip]:
    """Every conformance-stage test that skips, asked of the tests.

    Each stage method of `TestConformance` is called on each manifest
    entry with the module's three pieces of work (`_CONFORMANCE_WORK`)
    replaced by a stop.  A stage that skips raises pytest's `Skipped`
    before it reaches any of them; one that does not reaches one and
    stops.  So the rows are the suite's own skip decision, not a second
    statement of the level rule, and a change to that rule reaches the
    table at the next release without an edit here.
    """
    import pytest

    module = _conformance_module(root / "tests" / "test_conformance.py")
    for name in _CONFORMANCE_WORK:
        if not hasattr(module, name):
            raise RuntimeError(
                f"tests/test_conformance.py no longer defines `{name}`, which"
                " render_status replaces to find the stages that skip"
            )
        setattr(module, name, _stop)
    cls = module.TestConformance
    ids: Callable[[Any], str] = next(
        mark.kwargs["ids"]
        for mark in getattr(cls, "pytestmark", [])
        if mark.name == "parametrize" and mark.args[0] == "entry"
    )
    stages = [name for name, value in vars(cls).items()
              if name.startswith("test_") and callable(value)]
    found: list[tuple[str, int, Skip]] = []
    for entry in module.MANIFEST:
        for index, stage in enumerate(stages):
            try:
                getattr(cls(), stage)(entry)
            except _Reached:
                continue
            except pytest.skip.Exception as exc:
                test_id = ids(entry)
                found.append((test_id, index, Skip(
                    test=f"{stage}[{test_id}]",
                    program=str(entry["file"]),
                    level=str(entry["level"]),
                    message=str(exc.msg),
                    about=_about(entry),
                )))
    return [skip for _id, _index, skip in sorted(found, key=lambda f: f[:2])]


def _hooks_by_stage(precommit_text: str) -> dict[str, int]:
    import yaml

    config = yaml.safe_load(precommit_text)
    stages: dict[str, int] = {}
    for repo in config["repos"]:
        for hook in repo["hooks"]:
            declared = hook.get("stages") or ["pre-commit"]
            label = "push" if declared == ["pre-push"] else (
                "commit" if declared in (["pre-commit"], ["commit"]) else "+".join(declared)
            )
            stages[label] = stages.get(label, 0) + 1
    return stages


def matrix_size(matrix: dict[str, Any]) -> int:
    """How many cells a job's `strategy.matrix` runs, by GitHub's rules: the
    product of the axes less each `exclude`, plus each `include` that cannot
    be added to an existing cell without overwriting one of its axis
    values."""
    axes = {k: v for k, v in matrix.items() if k not in ("include", "exclude")}
    cells = [
        dict(zip(axes, values, strict=True))
        for values in itertools.product(*axes.values())
    ] if axes else []
    for excluded in matrix.get("exclude", []):
        cells = [c for c in cells
                 if not all(c.get(k) == v for k, v in excluded.items())]
    added = 0
    for extra in matrix.get("include", []):
        fits = any(
            all(cell[k] == v for k, v in extra.items() if k in axes)
            for cell in cells
        )
        if not fits:
            added += 1
    return len(cells) + added


def _ci(ci_text: str) -> tuple[int, dict[str, int]]:
    import yaml

    jobs = yaml.safe_load(ci_text)["jobs"]
    cells = {
        name: matrix_size(job["strategy"]["matrix"])
        for name, job in jobs.items()
        if isinstance(job.get("strategy"), dict) and "matrix" in job["strategy"]
    }
    return len(jobs), cells


def measure(
    root: Path,
    *,
    collect: Callable[[Path], Collection | str] = collect,
    registry: Callable[[Path], tuple[int, int]] = registry_counts,
    skips: Callable[[Path], list[Skip]] = conformance_skips,
) -> Tree | str:
    """Measure the tree under `root`, or say why it could not be measured.

    The collection, the registries and the conformance skips are
    parameters, so a test can measure a synthetic tree without a pytest
    subprocess or a compiler.
    """
    collection = collect(root)
    if isinstance(collection, str):
        return collection
    tests = root / "tests"
    names = set(collection.per_file) | {p.name for p in tests.glob("test_*.py")}
    test_files: dict[str, tuple[int, str]] = {}
    for name in sorted(names):
        source = (tests / name).read_text(encoding="utf-8")
        test_files[name] = (len(source.splitlines()), summary_of(source))
    manifest = json.loads(
        (tests / "conformance" / "manifest.json").read_text(encoding="utf-8")
    )
    builtins, effects = registry(root)
    ci_jobs, matrix_cells = _ci(
        (root / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    )
    return Tree(
        collection=collection,
        test_files=test_files,
        manifest=manifest,
        examples=len(list((root / "examples").glob("*.vera"))),
        corpus=sum(
            len(list((root / d).rglob("*.vera")))
            for d in ("examples", "tests/conformance")
        ),
        builtins=builtins,
        effects=effects,
        chapters=len(list((root / "spec").glob("[0-9][0-9]-*.md"))),
        hooks=_hooks_by_stage(
            (root / ".pre-commit-config.yaml").read_text(encoding="utf-8")
        ),
        ci_jobs=ci_jobs,
        matrix_cells=matrix_cells,
        gate_scripts=len(list((root / "scripts").glob("check_*.py"))),
        skips=skips(root),
    )


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------


def _levels(manifest: list[dict[str, Any]]) -> str:
    counts: dict[str, int] = {}
    for entry in manifest:
        counts[entry["level"]] = counts.get(entry["level"], 0) + 1
    order = [*_LEVEL_ORDER, *sorted(set(counts) - set(_LEVEL_ORDER))]
    return ", ".join(f"{counts.get(lvl, 0):,} at `{lvl}`" for lvl in order)


def _status(tree: Tree) -> str:
    lines = sum(n for n, _summary in tree.test_files.values())
    negatives = sum(1 for e in tree.manifest if "expected_error" in e)
    hooks = sum(tree.hooks.values())
    stages = ", ".join(
        f"{n:,} at {stage}" for stage, n in sorted(tree.hooks.items())
    )
    cells = "; ".join(
        f"the `{job}` job's matrix has {n:,} cells"
        for job, n in sorted(tree.matrix_cells.items())
    )
    rows = [
        ("Tests", f"{tree.collection.total:,} collected across"
                  f" {len(tree.test_files):,} files, {lines:,} lines of test code"),
        ("Conformance programs", f"{len(tree.manifest):,} in"
                                 f" `tests/conformance/manifest.json`: {_levels(tree.manifest)};"
                                 f" {negatives:,} of them negative fixtures (`expected_error`)"),
        ("Example programs", f"{tree.examples:,} in `examples/`"),
        ("Corpus programs", f"{tree.corpus:,} `.vera` files under `examples/` and"
                            " `tests/conformance/`, recursively"),
        ("Built-in functions", f"{tree.builtins:,}, as `vera builtins` lists them"),
        ("Effects", f"{tree.effects:,}, as `vera effects` lists them"),
        ("Spec chapters", f"{tree.chapters:,} in `spec/`"),
        ("Pre-commit hooks", f"{hooks:,} in `.pre-commit-config.yaml`: {stages}"),
        ("CI jobs", f"{tree.ci_jobs:,} in `.github/workflows/ci.yml`"
                    + (f"; {cells}" if cells else "")),
        ("Gate scripts", f"{tree.gate_scripts:,} `scripts/check_*.py`"),
    ]
    table = ["| Metric | Value |", "|--------|-------|"]
    table += [f"| **{name}** | {value} |" for name, value in rows]
    return "\n".join([
        *table,
        "",
        "Written by `scripts/render_status.py` from the tree.  The tests are"
        " counted by a collection, `pytest --collect-only -o addopts="
        " --matrix=full`, which includes the stress tests and every"
        " class-instrument cell, not by a run, so a run's passed, skipped"
        " and xfailed split is not recorded here.",
        "",
    ])


def _test_files(tree: Tree) -> str:
    table = ["| File | Tests | Lines | What it covers |",
             "|------|------:|------:|----------------|"]
    for name, (lines, summary) in tree.test_files.items():
        tests = tree.collection.per_file.get(name, 0)
        table.append(f"| `{name}` | {tests:,} | {lines:,} | {summary} |")
    return "\n".join([*table, ""])


def _skipped_tests(tree: Tree) -> str:
    out = [
        f"The suite skips {len(tree.skips):,} conformance-stage tests:",
        "",
        "| Test | Program | Declared level | Message | What the program is |",
        "|------|---------|----------------|---------|---------------------|",
    ]
    for skip in tree.skips:
        out.append(
            f"| `{skip.test}` | `{skip.program}` | `{skip.level}` |"
            f" {skip.message} | {skip.about.replace('|', chr(92) + '|')} |"
        )
    return "\n".join([*out, ""])


def render(tree: Tree) -> dict[str, str]:
    """Each block's text, as it belongs between its markers."""
    return {
        "status": _status(tree),
        "test-files": _test_files(tree),
        "skipped-tests": _skipped_tests(tree),
    }


# ---------------------------------------------------------------------------
# The document
# ---------------------------------------------------------------------------


def _spans(text: str) -> dict[str, tuple[int, int]] | str:
    """Where each block's content lies: from the line after its begin marker
    to the start of its end marker, or why the markers cannot be read.  A
    marker is a whole line, and each must appear exactly once, begin first."""
    lines = text.splitlines(keepends=True)
    offsets = list(itertools.accumulate((len(line) for line in lines), initial=0))
    spans: dict[str, tuple[int, int]] = {}
    for name in BLOCKS:
        found = {}
        for marker in (begin_marker(name), end_marker(name)):
            at = [i for i, line in enumerate(lines) if line.strip() == marker]
            if len(at) != 1:
                return (
                    f"`{marker}` appears {len(at)} times; each generated block"
                    " has one begin and one end marker, each on its own line"
                )
            found[marker] = at[0]
        begin, end = found[begin_marker(name)], found[end_marker(name)]
        if end < begin:
            return f"the `{name}` block's end marker comes before its begin marker"
        spans[name] = (offsets[begin + 1], offsets[end])
    return spans


def blocks_in(text: str) -> dict[str, str] | str:
    """Each generated block's current content, or why it cannot be read."""
    spans = _spans(text)
    if isinstance(spans, str):
        return spans
    return {name: text[start:end] for name, (start, end) in spans.items()}


def splice(text: str, rendered: Mapping[str, str]) -> str:
    """`text` with each block's content replaced by `rendered`'s.  Raises
    `ValueError` when the markers cannot be read."""
    spans = _spans(text)
    if isinstance(spans, str):
        raise ValueError(spans)
    out = text
    for name, (start, end) in sorted(spans.items(), key=lambda kv: -kv[1][0]):
        out = out[:start] + rendered[name] + out[end:]
    return out


def stale_blocks(
    root: Path, *, measure: Callable[[Path], Tree | str] = measure
) -> list[str]:
    """Why TESTING.md's generated blocks are not what this script would
    write now: one line per stale block, or the reason the tree or the
    markers cannot be read; ``[]`` when every block is current."""
    text = (root / DOCUMENT).read_text(encoding="utf-8")
    current = blocks_in(text)
    if isinstance(current, str):
        return [f"{DOCUMENT}: {current}"]
    tree = measure(root)
    if isinstance(tree, str):
        return [f"{DOCUMENT}: the tree could not be measured: {tree}"]
    errors: list[str] = []
    for name, now in render(tree).items():
        if current[name] == now:
            continue
        pairs = itertools.zip_longest(
            current[name].splitlines(), now.splitlines(), fillvalue="(nothing)"
        )
        doc, tree_line = next((a, b) for a, b in pairs if a != b)
        errors.append(
            f"{DOCUMENT}: the generated `{name}` block is not what"
            " scripts/render_status.py writes now; run it and commit the"
            f" result.  First difference: the document has {doc[:160]!r},"
            f" the tree gives {tree_line[:160]!r}"
        )
    return errors


def main(argv: list[str] | None = None) -> int:
    argparse.ArgumentParser(description=__doc__).parse_args(argv)
    # `vera.introspect` and the conformance tests import `vera`: from this
    # checkout, whatever editable install the interpreter would find first.
    sys.path.insert(0, str(ROOT))
    tree = measure(ROOT)
    if isinstance(tree, str):
        print(f"ERROR: {tree}", file=sys.stderr)
        return 1
    path = ROOT / DOCUMENT
    text = path.read_text(encoding="utf-8")
    try:
        new = splice(text, render(tree))
    except ValueError as exc:
        print(f"ERROR: {DOCUMENT}: {exc}", file=sys.stderr)
        return 1
    if new == text:
        print(f"{DOCUMENT}'s generated status is current.")
    else:
        path.write_text(new, encoding="utf-8")
        print(f"Rewrote {DOCUMENT}'s generated status.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
