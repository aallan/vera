#!/usr/bin/env python
"""The scorecard: the audit's measures, measured again, for TESTING.md.

The audit of v0.2.0 measured the repository on 2026-10-06, at 6508cc32, and
ROADMAP.md's Stage 29 holds v0.3.0 to a target on each of its measures.
``scripts/render_status.py`` writes the rows this module measures between
the `scorecard` markers in TESTING.md, and the release PR runs it, so every
release measures the scorecard again without hand work.  A row states one
measure, the audit's value at v0.2.0, held here as data (`MEASURES`), and
the value now.

A row is measured from one of three sources:

- The tree.  Each measurer reproduces the command the audit counted its row
  with, so the two columns count the same thing: on an export of the audit's
  tree (``VERA_AUDIT_TREE``, read by ``tests/test_scorecard.py``) each reads
  the audit's own value.  ``check_doc_counts.py --release`` measures these
  rows again and compares them with the document.
- The network, with ``--github``: the open issues, the pull-request runs of
  ``ci.yml`` and the pull requests merged since the last release, from the
  GitHub API (``GH_TOKEN`` or ``GITHUB_TOKEN`` is sent when set), and the
  statement coverage of the last post-merge coverage run, from Codecov's
  public API.
- A junit file, with ``--junit PATH``: the worker-seconds of one sample-mode
  run of the suite, and the share of them that the tests which started a
  process took, which ``tests/subprocess_census.py`` records on a run that
  loads it.

The network's rows and the junit file's change between any two moments, so
the freshness check does not measure them again: it asks that each is
present and states the window it was measured over.

The measures that need judgment are not generated: the obligation kinds with
one record both sides read, the modules that resolve a name or decide an
owner, and the facts mirrored by hand.  ROADMAP.md's Stage 29 states their
targets.
"""

from __future__ import annotations

import ast
import itertools
import json
import os
import re
import statistics
import xml.etree.ElementTree as ET
from collections.abc import Callable, Iterator, Mapping, Sequence
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, NamedTuple
from urllib.parse import urlencode
from urllib.request import Request, urlopen

AUDIT_DATE = "2026-10-06"
AUDIT_COMMIT = "6508cc32"

TREE = "tree"
GITHUB = "github"
JUNIT = "junit"

#: What render_status.py takes to measure a row of each source but the tree.
FLAGS = {GITHUB: "`--github`", JUNIT: "`--junit PATH`"}

#: The "Measured over" cell of a row that a render did not measure.
NOT_MEASURED = "not measured in this render"

REPO = "aallan/vera"
GITHUB_API = "https://api.github.com"
CODECOV_API = "https://api.codecov.io/api/v2/github/aallan/repos/vera"
#: The Codecov flag the post-merge coverage job uploads `vera/`'s coverage
#: under (codecov.yml).
CODECOV_FLAG = "python"

#: The junit property `tests/subprocess_census.py` gives every test: the
#: number of processes it started.
CENSUS = "subprocesses"

#: The collection that counts the pull-request gate's suite: the stress
#: tests deselected as pyproject's `addopts` deselects them, and each
#: class-instrument matrix sampled with a fixed seed, so the count is a
#: function of the tree and not of the week (tests/matrix_sample.py).
GATE_SEED = "scorecard"
GATE_COLLECT_ARGS = (
    "--collect-only", "-q", "--matrix=sample", f"--matrix-seed={GATE_SEED}",
)

#: The audit's gate scripts that exist only to keep hand-copied facts in step
#: (its appendix A2): its classification, held as data.  A script counts
#: while it exists.  The audit named eight, these six and `ALIGNMENT_GATES`.
MIRROR_GATES = (
    "check_doc_counts", "check_version_sync", "check_limitations_sync",
    "check_editor_grammars", "check_site_assets", "check_diagnostic_examples",
)

#: Two of the audit's eight, reclassified as alignment gates on 2026-10-12:
#: spec chapter 10 and examples/README.md stay hand-written, and each gate
#: holds its document to its source, so neither counts as a copy kept in step.
ALIGNMENT_GATES = ("check_grammar_alignment", "check_examples_readme")

#: A function this long or shorter is not long.
LONG = 500

#: The pull-request runs the CI-time rows take the median over.
RUNS = 20

#: The conclusions of a run that reached a verdict: a cancelled run was
#: replaced by a newer push and says nothing about how long a push waits.
VERDICTS = frozenset({"success", "failure"})

#: How a workflow step that runs the program generator names it.
GENERATOR = re.compile(r"\bprogram[_-]generator\b")


class Measure(NamedTuple):
    key: str
    label: str
    audit: str
    source: str
    counts: str


MEASURES: tuple[Measure, ...] = (
    Measure("soundness_bugs", "Open `soundness` bugs", "14 (≥17 by definition)", GITHUB,
            "the open issues labelled both `bug` and `soundness`"),
    Measure("open_bugs", "Open bugs", "82", GITHUB, "the open issues labelled `bug`"),
    Measure("infer_functions", "Backend `_infer_*` functions", "32", TREE,
            "the functions named `_infer_*` anywhere in `vera/`"),
    Measure("nat_int_twins",
            "Same-named `Nat`/`Int` helpers in `vera/verifier.py` and `vera/wasm/`",
            "12", TREE,
            "the function names both define, a `vera/wasm/` name read without its"
            " `codegen` word, that carry the word `nat`, `int`, `overflow` or"
            " `underflow`, or a word that begins `widen`"),
    Measure("guarded_claims", "Explicit `guarded=` claims by the verifier", "38", TREE,
            "the calls in `vera/verifier.py` to a `_record_*_tier3` recorder that pass"
            " `guarded`, by keyword or by position"),
    Measure("expr_dispatchers", "Hand-rolled `isinstance` dispatchers over `Expr`",
            "191", TREE,
            "the functions outside `vera/ast.py` whose own body, its nested functions"
            " apart, tests a value with `isinstance` against a subclass of"
            " `vera.ast.Expr`"),
    Measure("long_functions", "Functions over 500 lines", "17", TREE,
            "the functions in `vera/` more than 500 lines long, from the `def` line to"
            " the last"),
    Measure("host_mirrored", "Host built-ins hand-mirrored across hosts",
            "53 × 2, plus WASI", TREE,
            "the built-ins whose record in the built-in registry,"
            " `vera/builtins.py`, lowers through a host import (`Host`; before the"
            " registry, the host-import family sets of"
            " `vera/codegen/compilability.py`), each written by hand in the Python"
            " host and in `vera/browser/runtime.mjs`, and the ones"
            " `vera/codegen/wasi.py` writes again for a WASI world: the entries of"
            " its `_MAP_OPS` while it had one, and since `Map` and `Set` moved into"
            " generated code (#1676) the built-ins whose registry row names a WASI"
            " world"),
    Measure("sync_gates", "Gate scripts that exist only to sync copies", "8 of 23", TREE,
            "the scripts of the audit's eight still classed as such ("
            + ", ".join(f"`{g}`" for g in MIRROR_GATES)
            + ") that exist, of the `scripts/check_*.py`; the other two, "
            + " and ".join(f"`{g}`" for g in ALIGNMENT_GATES)
            + ", were reclassified as alignment gates on 2026-10-12"),
    Measure("ci_wall", "CI wall time per pull-request push", "57 min", GITHUB,
            f"the median, over the last {RUNS} pull-request runs of `ci.yml` that"
            " reached a verdict, of the time from a run's start to its last job's end"),
    Measure("runner_minutes", "Runner-minutes per pull-request push", "375", GITHUB,
            "the median, over the same runs, of the sum of a run's job durations"),
    Measure("fix_pr_runs", "Fix pull requests, median: CI runs", "6", GITHUB,
            "the pull-request runs of `ci.yml` of each pull request merged since the"
            " last release, Dependabot's and the `prep/` release branches' apart"),
    Measure("fix_pr_hours", "Fix pull requests, median: hours to merge", "11.0", GITHUB,
            "the hours from opening to merge of the same pull requests"),
    Measure("gate_tests", "Suite in the pull-request gate: tests", "30,095", TREE,
            "the tests a sample-mode collection keeps, the stress tests deselected as"
            f" the gate deselects them (`pytest --collect-only --matrix=sample"
            f" --matrix-seed={GATE_SEED}`)"),
    Measure("gate_worker_seconds", "Suite in the pull-request gate: worker-seconds",
            "9,037", JUNIT,
            "the sum of the test times in the junit file of one sample-mode run"),
    Measure("subprocess_share", "Subprocess share of suite time", "52%", JUNIT,
            "the share of those seconds taken by the tests that started a process, as"
            " `tests/subprocess_census.py` counts them"),
    Measure("golden_outputs", "Conformance entries with golden output", "0 of 256", TREE,
            "the entries of `tests/conformance/manifest.json` that pin their"
            " `expected_stdout`, of all of them; then the run-level entries, the"
            " only ones whose program runs, that pin their run"),
    Measure("program_generator", "Program generator with differentials", "none", TREE,
            "when the workflows run a step that names `program_generator`"),
    Measure("distrust", "`vera test` executes proved functions", "no", TREE,
            "whether `vera/tester.py`'s `test` takes `distrust`, a test under `tests/`"
            " passes `distrust=True`, and a job in `ci.yml` runs the suite"),
    Measure("statement_coverage", "Statement coverage", "96.2%", GITHUB,
            f"Codecov's `{CODECOV_FLAG}` flag for the last post-merge coverage run"
            " that uploaded it"),
    Measure("spec_words", "Spec words", "86,558", TREE,
            "the whitespace-separated words of `spec/*.md`"),
    Measure("spec_issue_links", "Issue links in the spec", "175", TREE,
            "the `https://github.com/aallan/vera/issues/N` links in `spec/*.md`"),
)


class MeasureError(Exception):
    """A row could not be measured: its source moved, or could not be read."""


# ---------------------------------------------------------------------------
# The tree
# ---------------------------------------------------------------------------


def _parse(path: Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def _functions(tree: ast.AST) -> Iterator[ast.FunctionDef | ast.AsyncFunctionDef]:
    """Every function and method, nested ones included."""
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node


def _sources(root: Path, *parts: str) -> list[Path]:
    return sorted(root.joinpath(*parts).rglob("*.py"))


def _callee(call: ast.Call) -> str | None:
    if isinstance(call.func, ast.Attribute):
        return call.func.attr
    if isinstance(call.func, ast.Name):
        return call.func.id
    return None


def infer_functions(root: Path) -> int:
    """The functions named `_infer_*` anywhere in `vera/`: the backend's own
    type inference, which the audit counted at 23 in `vera/wasm/`, 6 in
    `vera/monomorphize.py` and 3 in `vera/checker/`."""
    return sum(
        1 for path in _sources(root, "vera") for fn in _functions(_parse(path))
        if fn.name.startswith("_infer_")
    )


_NAT_INT_WORDS = frozenset({"nat", "int", "overflow", "underflow"})


def _without_codegen(name: str) -> str:
    """`name` without its `codegen` word: the backend's copy of a verifier
    helper says where it lives (`_has_nat_origin_codegen`)."""
    words = name.split("_")
    return "_".join(word for word in words if word != "codegen")


def _names_nat_or_int(name: str) -> bool:
    return any(
        word in _NAT_INT_WORDS or word.startswith("widen")
        for word in name.split("_") if word
    )


def nat_int_twins(root: Path) -> list[str]:
    """The `Nat`/`Int` helpers `vera/verifier.py` and `vera/wasm/` each
    define under one name, read as the audit read them: a `vera/wasm/` name
    without its `codegen` word, and a name about `Nat` or `Int` by its words."""
    verifier = {fn.name for fn in _functions(_parse(root / "vera" / "verifier.py"))}
    backend = {
        _without_codegen(fn.name)
        for path in _sources(root, "vera", "wasm") for fn in _functions(_parse(path))
    }
    return sorted(name for name in verifier & backend if _names_nat_or_int(name))


def guarded_claims(root: Path) -> int:
    """The verifier's explicit claims that code generation guards an
    obligation: the calls in `vera/verifier.py` to a Tier 3 recorder, a
    `_record_*_tier3` function, that pass its `guarded` parameter, by
    keyword or by position.  A call that leaves it to its default makes no
    claim."""
    tree = _parse(root / "vera" / "verifier.py")
    position: dict[str, int | None] = {}
    for fn in _functions(tree):
        if fn.name.startswith("_record_") and fn.name.endswith("_tier3"):
            params = [arg.arg for arg in (*fn.args.posonlyargs, *fn.args.args)]
            if params[:1] == ["self"]:
                params = params[1:]
            position[fn.name] = params.index("guarded") if "guarded" in params else None
    claims = 0
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        name = _callee(node)
        if name not in position:
            continue
        at = position[name]
        by_keyword = any(keyword.arg == "guarded" for keyword in node.keywords)
        by_position = (
            at is not None and len(node.args) > at
            and not any(isinstance(arg, ast.Starred) for arg in node.args[: at + 1])
        )
        claims += by_keyword or by_position
    return claims


def _expr_classes(root: Path) -> frozenset[str]:
    """The classes `vera/ast.py` derives from `Expr`, at any depth."""
    bases: dict[str, list[str]] = {}
    for node in _parse(root / "vera" / "ast.py").body:
        if isinstance(node, ast.ClassDef):
            bases[node.name] = [
                base.id if isinstance(base, ast.Name)
                else base.attr if isinstance(base, ast.Attribute) else ""
                for base in node.bases
            ]

    def derives(name: str, seen: frozenset[str]) -> bool:
        return any(
            base == "Expr" or (base not in seen and derives(base, seen | {base}))
            for base in bases.get(name, ())
        )

    found = frozenset(name for name in bases if name != "Expr" and derives(name, frozenset({name})))
    if not found:
        raise MeasureError("vera/ast.py defines no subclass of `Expr`")
    return found


def _own_nodes(fn: ast.AST) -> Iterator[ast.AST]:
    """The nodes of `fn`'s own body: a nested function or class is its own."""
    stack = list(ast.iter_child_nodes(fn))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))


def _isinstance_classes(call: ast.Call) -> set[str]:
    """The class names an `isinstance(x, C)` or `isinstance(x, (C, D))` names."""
    if not (isinstance(call.func, ast.Name) and call.func.id == "isinstance"
            and len(call.args) == 2):
        return set()
    second = call.args[1]
    targets = second.elts if isinstance(second, ast.Tuple) else [second]
    return {
        target.attr if isinstance(target, ast.Attribute) else target.id
        for target in targets if isinstance(target, (ast.Attribute, ast.Name))
    }


def expr_dispatchers(root: Path) -> int:
    """The functions that dispatch on `Expr` subclasses by hand: each function
    or method outside `vera/ast.py` whose own body tests a value with
    `isinstance` against a subclass of `vera.ast.Expr`.  A nested function
    counts as itself, and a test against the `Expr` base dispatches on none
    of its subclasses."""
    classes = _expr_classes(root)
    count = 0
    for path in _sources(root, "vera"):
        if path.relative_to(root).as_posix() == "vera/ast.py":
            continue
        for fn in _functions(_parse(path)):
            count += any(
                isinstance(node, ast.Call) and bool(classes & _isinstance_classes(node))
                for node in _own_nodes(fn)
            )
    return count


def long_functions(root: Path) -> int:
    """The functions in `vera/` longer than `LONG` lines, from the `def` line
    to the last, nested ones counted in their own right."""
    return sum(
        1 for path in _sources(root, "vera") for fn in _functions(_parse(path))
        if (fn.end_lineno or fn.lineno) - fn.lineno + 1 > LONG
    )


_FAMILY = re.compile(r"^_[A-Z][A-Z0-9]*_BUILTINS$")


def _assignments(tree: ast.AST) -> Iterator[tuple[str, ast.expr]]:
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    yield target.id, node.value
        elif (isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name)
              and node.value is not None):
            yield node.target.id, node.value


def _string_set(name: str, value: ast.expr) -> set[str]:
    """The strings of a `frozenset({...})`, `frozenset([...])` or `{...}`."""
    literal = value.args[0] if isinstance(value, ast.Call) and value.args else value
    if isinstance(literal, (ast.Set, ast.List, ast.Tuple)):
        strings = {
            element.value for element in literal.elts
            if isinstance(element, ast.Constant) and isinstance(element.value, str)
        }
        if strings:
            return strings
    raise MeasureError(
        f"vera/codegen/compilability.py's `{name}` is not a literal set of names,"
        " which the host-built-ins row reads"
    )


def _hosted_records(registry: Path) -> set[str]:
    """The built-ins whose record in the registry lowers through a host
    import: each `_fn("name", ..., lowering=Host(...))` of `vera/builtins.py`."""
    names: set[str] = set()
    for node in ast.walk(_parse(registry)):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "_fn" and node.args
                and isinstance(node.args[0], ast.Constant)):
            continue
        lowering = next((k.value for k in node.keywords if k.arg == "lowering"), None)
        if (isinstance(lowering, ast.Call) and isinstance(lowering.func, ast.Name)
                and lowering.func.id == "Host"):
            names.add(node.args[0].value)
    return names


def _wasi_written_records(registry: Path, hosted: set[str]) -> int | None:
    """The built-ins among *hosted* whose `HOST_IMPORTS` row in the registry
    names a WASI world (``wasi=``), which `vera/codegen/wasi.py`'s adapter
    implements again, or None when the registry has no such table."""
    for name, value in _assignments(_parse(registry)):
        if name != "HOST_IMPORTS" or not isinstance(value, ast.Tuple):
            continue
        written: set[str] = set()
        for row in value.elts:
            if not isinstance(row, ast.Call):
                continue
            worlds = next((k.value for k in row.keywords if k.arg == "wasi"), None)
            if worlds is None or (isinstance(worlds, ast.Tuple) and not worlds.elts):
                continue
            served = next((k.value for k in row.keywords if k.arg == "serves"), None)
            names = [a.value for a in (*row.args, *([served] if served else []))
                     if isinstance(a, ast.Constant) and isinstance(a.value, str)]
            written |= hosted.intersection(names)
        return len(written)
    return None


def host_mirrored(root: Path) -> tuple[int, int]:
    """The built-ins a host implements, and the ones WASI writes again.

    The built-ins are those whose record in the built-in registry,
    `vera/builtins.py`, lowers through a host import (`Host`), each written
    by hand in the Python host and in `vera/browser/runtime.mjs`; in a tree
    from before the registry, the members of the host-import family sets of
    `vera/codegen/compilability.py` (`_MD_BUILTINS` and the rest, which the
    audit's 53 were exactly).  The WASI ones are the entries of
    `vera/codegen/wasi.py`'s `_MAP_OPS`, which the WASI server world wrote
    again, in a tree that has the table; in a registry tree without it
    (since #1676 moved `Map` and `Set` into generated code), the hosted
    built-ins whose registry row names a WASI world.  A tree with neither
    is an error, not a zero: zero is the target, and the row must not read
    as met because its source moved.
    """
    registry = root / "vera" / "builtins.py"
    if registry.exists():
        hosted = _hosted_records(registry)
        if not hosted:
            raise MeasureError(
                "vera/builtins.py has no record lowered through a host import"
                " (`lowering=Host(...)`), the source the host-built-ins row"
                " reads; scripts/scorecard.py's `host_mirrored` needs the"
                " source that replaced them"
            )
        families = [hosted]
    else:
        compilability = root / "vera" / "codegen" / "compilability.py"
        families = [
            _string_set(name, value)
            for name, value in _assignments(_parse(compilability))
            if _FAMILY.match(name)
        ]
        if not families:
            raise MeasureError(
                "vera/codegen/compilability.py has no `_*_BUILTINS` host-import"
                " family set, the source the host-built-ins row reads;"
                " scripts/scorecard.py's `host_mirrored` needs the source that"
                " replaced them"
            )
    tables = [
        value for name, value in _assignments(_parse(root / "vera" / "codegen" / "wasi.py"))
        if name == "_MAP_OPS"
    ]
    if len(tables) == 1 and isinstance(tables[0], ast.Dict):
        return len(set().union(*families)), len(tables[0].keys)
    written = (_wasi_written_records(registry, set().union(*families))
               if registry.exists() else None)
    if written is None:
        raise MeasureError(
            "vera/codegen/wasi.py has no `_MAP_OPS` table and vera/builtins.py"
            " no `HOST_IMPORTS` rows with their WASI worlds, the sources of the"
            " host-built-ins row's WASI operations"
        )
    return len(set().union(*families)), written


def host_mirrored_text(built_ins: int, wasi: int) -> str:
    """The host-mirrored row as the scorecard prints it: the hosted
    built-ins, twice, and WASI's own copies of them, "none" at zero."""
    rest = "none" if wasi == 0 else f"WASI's {wasi:,}"
    return f"{built_ins:,} × 2, plus {rest}"


def sync_gates(root: Path) -> tuple[int, int]:
    """The audit's copy-syncing gate scripts that still exist, and the gate
    scripts, `scripts/check_*.py`."""
    scripts = root / "scripts"
    existing = sum((scripts / f"{name}.py").is_file() for name in MIRROR_GATES)
    return existing, len(list(scripts.glob("check_*.py")))


class Golden(NamedTuple):
    """What the conformance manifest pins of its programs' runs."""

    stdout: int       # entries that pin their stdout
    entries: int      # every entry, the audit's denominator
    run_level: int    # the entries at level `run`, the only ones that run
    run_pinned: int   # run-level entries that pin their stdout or their exit
    exit_only: int    # run-level entries that pin their exit status alone


def golden_outputs(root: Path) -> Golden:
    """Of the conformance manifest's entries: those that pin their stdout,
    out of all of them, as the audit counted; and of the run-level entries,
    the only ones whose program runs, those that pin their run at all and
    those that pin its exit status alone."""
    manifest = json.loads(
        (root / "tests" / "conformance" / "manifest.json").read_text(encoding="utf-8")
    )
    run = [entry for entry in manifest if entry.get("level") == "run"]
    return Golden(
        stdout=sum(1 for entry in manifest if "expected_stdout" in entry),
        entries=len(manifest),
        run_level=len(run),
        run_pinned=sum(1 for e in run if "expected_stdout" in e or "expected_exit" in e),
        exit_only=sum(1 for e in run if "expected_exit" in e and "expected_stdout" not in e),
    )


def _yaml(path: Path) -> dict[str, Any]:
    import yaml

    loaded = yaml.safe_load(path.read_text(encoding="utf-8"))
    return loaded if isinstance(loaded, dict) else {}


def _triggers(workflow: Mapping[Any, Any]) -> dict[str, Any]:
    # YAML 1.1, which PyYAML reads, takes a bare `on` key for `true`.
    on = workflow.get("on", workflow.get(True))
    if isinstance(on, str):
        return {on: None}
    if isinstance(on, list):
        return {str(event): None for event in on}
    return {str(event): value for event, value in (on or {}).items()}


def _jobs(workflow: Mapping[Any, Any]) -> Iterator[Mapping[str, Any]]:
    for job in (workflow.get("jobs") or {}).values():
        if isinstance(job, Mapping):
            yield job


def _runs(job: Mapping[str, Any]) -> Iterator[str]:
    for step in job.get("steps") or []:
        if isinstance(step, Mapping) and isinstance(step.get("run"), str):
            yield step["run"]


def _daily(schedule: Any) -> bool:
    for entry in schedule or []:
        fields = str((entry or {}).get("cron", "")).split()
        if len(fields) == 5 and fields[2:] == ["*", "*", "*"]:
            return True
    return False


_WHEN = ("every pull request", "after a merge", "nightly", "on a schedule", "by hand")


def program_generator(root: Path) -> str:
    """When the workflows run the program generator: on every pull request,
    after a merge, nightly, on a schedule or by hand, or `none`.  A step
    runs it when its command names `program_generator` (`GENERATOR`), and a
    job runs on the events its `if:` names with `github.event_name ==`, or
    on every event that triggers its workflow."""
    when: set[str] = set()
    for path in sorted((root / ".github" / "workflows").glob("*.y*ml")):
        workflow = _yaml(path)
        triggers = _triggers(workflow)
        for job in _jobs(workflow):
            if not any(GENERATOR.search(run) for run in _runs(job)):
                continue
            named = set(re.findall(r"github\.event_name\s*==\s*'(\w+)'", str(job.get("if", ""))))
            events = {event for event in triggers if not named or event in named}
            if "pull_request" in events:
                when.add("every pull request")
            if "push" in events:
                when.add("after a merge")
            if "schedule" in events:
                when.add("nightly" if _daily(triggers["schedule"]) else "on a schedule")
            if not events & {"pull_request", "push", "schedule"}:
                when.add("by hand")
    return ", ".join(word for word in _WHEN if word in when) or "none"


def _tester_distrusts(root: Path) -> bool:
    for node in _parse(root / "vera" / "tester.py").body:
        if isinstance(node, ast.FunctionDef) and node.name == "test":
            args = node.args
            return "distrust" in {a.arg for a in (*args.posonlyargs, *args.args, *args.kwonlyargs)}
    return False


def _suite_distrusts(root: Path) -> bool:
    """Whether a test under `tests/` passes `distrust=True` to anything."""
    for path in sorted((root / "tests").glob("test_*.py")):
        if "distrust" not in path.read_text(encoding="utf-8"):
            continue
        for node in ast.walk(_parse(path)):
            if isinstance(node, ast.Call) and any(
                keyword.arg == "distrust" and isinstance(keyword.value, ast.Constant)
                and keyword.value.value is True
                for keyword in node.keywords
            ):
                return True
    return False


_EXPRESSION = re.compile(r"\$\{\{.*?\}\}", re.S)
_ASSIGNMENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")


def _commands(run: str) -> Iterator[list[str]]:
    """The words of each command a step's `run` text runs, its `${{ }}`
    expressions and environment assignments aside."""
    text = _EXPRESSION.sub("X", run).replace("\\\n", " ")
    for line in text.splitlines():
        for command in re.split(r"&&|\|\||;|\|", line):
            words = command.split()
            while words and _ASSIGNMENT.match(words[0]):
                words = words[1:]
            if words[:2] == ["uv", "run"]:
                words = words[2:]
            if words[:1] in (["python"], ["python3"]) and words[1:2] == ["-m"]:
                words = words[2:]
            if words:
                yield words


def _runs_the_suite(run: str) -> bool:
    """Whether `run` runs pytest over the whole suite: with no test path, or
    with `tests` alone."""
    for words in _commands(run):
        if Path(words[0]).name != "pytest":
            continue
        paths = [
            word for word in words[1:]
            if not word.startswith("-")
            and ("/" in word or word.endswith(".py") or ".py::" in word or word == "tests")
        ]
        if all(path.rstrip("/") == "tests" for path in paths):
            return True
    return False


def distrust_in_ci(root: Path) -> str:
    """Whether `vera test` executes proved functions, and whether CI makes it:
    `no` when the tester has no distrust mode; `yes, in CI` when a test
    under `tests/` runs it (`distrust=True`) and a job in `ci.yml` runs the
    suite; `yes, not in CI` otherwise."""
    if not _tester_distrusts(root):
        return "no"
    ci = root / ".github" / "workflows" / "ci.yml"
    in_ci = ci.is_file() and any(
        _runs_the_suite(run) for job in _jobs(_yaml(ci)) for run in _runs(job)
    )
    return "yes, in CI" if in_ci and _suite_distrusts(root) else "yes, not in CI"


def _spec(root: Path) -> list[str]:
    return [path.read_text(encoding="utf-8") for path in sorted((root / "spec").glob("*.md"))]


_ISSUE_LINK = re.compile(r"https://github\.com/aallan/vera/issues/\d+")


def spec_words(root: Path) -> int:
    """The whitespace-separated words of `spec/*.md`, as `wc -w` counts them."""
    return sum(len(text.split()) for text in _spec(root))


def spec_issue_links(root: Path) -> int:
    """The links to an issue of the repository in `spec/*.md`."""
    return sum(len(_ISSUE_LINK.findall(text)) for text in _spec(root))


_WORDS = ("no", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine")


def _few(count: int) -> str:
    return _WORDS[count] if count < len(_WORDS) else f"{count:,}"


def _golden(golden: Golden) -> str:
    """`175 of 256; every run-level entry, one of them by exit status only`:
    the audit's denominator first, then the run-level entries, the only ones
    that can carry an output."""
    if golden.run_level and golden.run_pinned == golden.run_level:
        run = "every run-level entry"
    elif golden.run_pinned:
        run = f"{golden.run_pinned:,} of the {golden.run_level:,} run-level entries"
    else:
        run = "no run-level entry"
    if golden.exit_only:
        run += f", {_few(golden.exit_only)} of them by exit status only"
    return f"{golden.stdout:,} of {golden.entries:,}; {run}"


def tree_values(
    root: Path, *, gate_tests: Callable[[Path], int | str]
) -> dict[str, tuple[str, str]] | str:
    """Each tree row's value now and what it was measured over, by key, or
    why the tree could not be measured.  `gate_tests` counts the
    pull-request gate's collection (`GATE_COLLECT_ARGS`), or says why it
    could not."""
    try:
        tests = gate_tests(root)
        if isinstance(tests, str):
            return tests
        built_ins, wasi_copies = host_mirrored(root)
        existing, gates = sync_gates(root)
        now = {
            "infer_functions": f"{infer_functions(root):,}",
            "nat_int_twins": f"{len(nat_int_twins(root)):,}",
            "guarded_claims": f"{guarded_claims(root):,}",
            "expr_dispatchers": f"{expr_dispatchers(root):,}",
            "long_functions": f"{long_functions(root):,}",
            "host_mirrored": host_mirrored_text(built_ins, wasi_copies),
            "sync_gates": f"{existing:,} of {gates:,}",
            "gate_tests": f"{tests:,}",
            "golden_outputs": _golden(golden_outputs(root)),
            "program_generator": program_generator(root),
            "distrust": distrust_in_ci(root),
            "spec_words": f"{spec_words(root):,}",
            "spec_issue_links": f"{spec_issue_links(root):,}",
        }
    except (MeasureError, OSError, SyntaxError, ValueError, KeyError) as exc:
        return f"the scorecard could not be measured: {exc}"
    return {key: (value, "the tree") for key, value in now.items()}


# ---------------------------------------------------------------------------
# The network
# ---------------------------------------------------------------------------

Get = Callable[[str], Any]

#: At most this many pages of a listing are read.
_PAGES = 10


def _url(base: str, path: str, params: Sequence[tuple[str, object]] = ()) -> str:
    query = urlencode(list(params), safe=",/")
    return f"{base}/{path}" + (f"?{query}" if query else "")


def _github(path: str, *params: tuple[str, object]) -> str:
    return _url(f"{GITHUB_API}/repos/{REPO}", path, params)


def _codecov(path: str, *params: tuple[str, object]) -> str:
    return _url(CODECOV_API, path, params)


def fetch_json(url: str, *, token: str | None = None) -> Any:
    """The decoded JSON at `url`, or a `MeasureError` saying why not."""
    request = Request(url, headers={
        "User-Agent": "vera-scorecard/1", "Accept": "application/json",
    })
    if token:
        request.add_header("Authorization", f"Bearer {token}")
    try:
        # The URL is built here, from this module's constants.
        with urlopen(request, timeout=30) as response:
            return json.load(response)
    except (OSError, ValueError) as exc:
        # URLError and HTTPError are OSError, as a socket timeout is, and a
        # body that is not JSON raises JSONDecodeError, a ValueError.
        raise MeasureError(f"could not read {url}: {exc}") from exc


def github_get(url: str) -> Any:
    return fetch_json(url, token=os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN"))


def codecov_get(url: str) -> Any:
    return fetch_json(url)


def _time(text: str) -> datetime:
    return datetime.fromisoformat(text.replace("Z", "+00:00"))


def _listing(payload: Any, what: str) -> list[Mapping[str, Any]]:
    """`payload` as the list of objects a GitHub listing is.  An error body
    is an object, and an object read as a listing yields its keys, which a
    reader can count without failing: it is refused here instead."""
    if isinstance(payload, list) and all(isinstance(item, Mapping) for item in payload):
        return payload
    raise MeasureError(f"the listing of {what} is not a list of objects: {payload!r:.160}")


def open_issues(get: Get, labels: str) -> int:
    """The open issues carrying every label in `labels` (comma-separated)."""
    count = 0
    for page in range(1, _PAGES + 1):
        items = _listing(get(_github(
            "issues", ("labels", labels), ("state", "open"), ("per_page", 100), ("page", page),
        )), f"the open issues labelled {labels}")
        count += sum(1 for item in items if "pull_request" not in item)
        if len(items) < 100:
            return count
    raise MeasureError(f"more than {_PAGES * 100} open issues are labelled {labels}")


class RunTiming(NamedTuple):
    created: datetime
    wall_minutes: float
    runner_minutes: float


def _run_jobs(get: Get, run_id: int) -> list[dict[str, Any]]:
    jobs: list[dict[str, Any]] = []
    for page in range(1, _PAGES + 1):
        payload = get(_github(f"actions/runs/{run_id}/jobs", ("per_page", 100), ("page", page)))
        jobs += payload["jobs"]
        if not payload["jobs"] or len(jobs) >= payload["total_count"]:
            break
    return jobs


def pr_runs(get: Get, count: int = RUNS) -> list[RunTiming]:
    """The last `count` pull-request runs of `ci.yml` that reached a verdict:
    each one's wall time, from its start to its last job's end, and its
    runner-minutes, the sum of its jobs' durations."""
    found: list[RunTiming] = []
    for page in range(1, _PAGES + 1):
        runs = get(_github(
            "actions/workflows/ci.yml/runs", ("event", "pull_request"),
            ("status", "completed"), ("per_page", 100), ("page", page),
        ))["workflow_runs"]
        for run in runs:
            if run["conclusion"] not in VERDICTS:
                continue
            jobs = [
                job for job in _run_jobs(get, run["id"])
                if job.get("started_at") and job.get("completed_at")
            ]
            if not jobs:
                continue
            end = max(_time(job["completed_at"]) for job in jobs)
            runner = sum(
                (_time(job["completed_at"]) - _time(job["started_at"])).total_seconds()
                for job in jobs
            )
            found.append(RunTiming(
                created=_time(run["created_at"]),
                wall_minutes=(end - _time(run["run_started_at"])).total_seconds() / 60,
                runner_minutes=runner / 60,
            ))
            if len(found) == count:
                return found
        if len(runs) < 100:
            break
    return found


class FixPr(NamedTuple):
    number: int
    runs: int
    hours: float


def latest_release(get: Get) -> tuple[str, datetime]:
    """The last published release's tag, and when it was published."""
    payload = get(_github("releases/latest"))
    return str(payload["tag_name"]), _time(payload["published_at"])


def _ci_runs(get: Get, pr: Mapping[str, Any]) -> int:
    """The pull-request runs of `ci.yml` on `pr`'s branch while it was open."""
    opened, merged = _time(pr["created_at"]), _time(pr["merged_at"])
    repository = (pr["head"].get("repo") or {}).get("full_name")
    count = 0
    for page in range(1, _PAGES + 1):
        runs = get(_github(
            "actions/workflows/ci.yml/runs", ("event", "pull_request"),
            ("branch", pr["head"]["ref"]), ("per_page", 100), ("page", page),
        ))["workflow_runs"]
        count += sum(
            1 for run in runs
            if opened <= _time(run["created_at"]) <= merged
            and (run.get("head_repository") or {}).get("full_name") == repository
        )
        if len(runs) < 100:
            break
    return count


def fix_prs(get: Get, since: datetime) -> list[FixPr]:
    """The pull requests merged into `main` since `since`, Dependabot's and
    the `prep/` release branches' apart: each one's CI runs and the hours
    from opening to merge."""
    merged: list[Mapping[str, Any]] = []
    for page in range(1, _PAGES + 1):
        items = _listing(get(_github(
            "pulls", ("state", "closed"), ("base", "main"), ("sort", "updated"),
            ("direction", "desc"), ("per_page", 100), ("page", page),
        )), "the closed pull requests")
        for pr in items:
            if pr.get("merged_at") is None or _time(pr["merged_at"]) < since:
                continue
            if pr["user"]["type"] == "Bot" or pr["head"]["ref"].startswith("prep/"):
                continue
            merged.append(pr)
        # Sorted by update, newest first, and a merge is an update: once a
        # page reaches before `since`, no later page holds a merge after it.
        if len(items) < 100 or _time(items[-1]["updated_at"]) < since:
            break
    return [
        FixPr(
            number=pr["number"], runs=_ci_runs(get, pr),
            hours=(_time(pr["merged_at"]) - _time(pr["created_at"])).total_seconds() / 3600,
        )
        for pr in sorted(merged, key=lambda pr: pr["number"])
    ]


class Coverage(NamedTuple):
    percent: float
    commit: str
    uploaded: str


def post_merge_coverage(get: Get) -> Coverage:
    """Codecov's `CODECOV_FLAG` coverage for the last commit of `main` whose
    post-merge coverage run uploaded it, rather than carried an earlier
    upload forward."""
    commits = get(_codecov("commits/", ("branch", "main"), ("page_size", 20)))["results"]
    for commit in commits:
        sha = str(commit["commitid"])
        uploads = get(_codecov(f"commits/{sha}/uploads/"))["results"]
        own = [
            upload for upload in uploads
            if CODECOV_FLAG in (upload.get("flags") or [])
            and upload.get("upload_type") == "uploaded"
        ]
        if own:
            totals = get(_codecov("totals/", ("flag", CODECOV_FLAG), ("sha", sha)))["totals"]
            return Coverage(float(totals["coverage"]), sha, str(own[0]["created_at"])[:10])
    raise MeasureError(
        f"none of main's last {len(commits)} commits has a `{CODECOV_FLAG}` upload"
        " of its own on Codecov"
    )


def github_values(
    get: Get = github_get, codecov: Get = codecov_get, *, now: datetime | None = None,
) -> dict[str, tuple[str, str]]:
    """The network's rows: each one's value now and the window it was
    measured over, by key.  Raises `MeasureError` when a source cannot be
    read, or answers in a shape these readers do not know."""
    try:
        return _github_values(get, codecov, now or datetime.now(timezone.utc))
    except (KeyError, IndexError, TypeError, ValueError, AttributeError) as exc:
        raise MeasureError(
            f"a response is not in the shape scripts/scorecard.py reads: {exc!r}"
        ) from exc


def _github_values(get: Get, codecov: Get, now: datetime) -> dict[str, tuple[str, str]]:
    tracker = f"the tracker, {now:%Y-%m-%d %H:%M} UTC"
    values = {
        "soundness_bugs": (f"{open_issues(get, 'bug,soundness'):,}", tracker),
        "open_bugs": (f"{open_issues(get, 'bug'):,}", tracker),
    }
    runs = pr_runs(get)
    if not runs:
        raise MeasureError("no pull-request run of ci.yml has reached a verdict")
    created = sorted(run.created for run in runs)
    window = (
        f"{len(runs)} pull-request runs, {created[0]:%Y-%m-%d} to {created[-1]:%Y-%m-%d}"
    )
    values["ci_wall"] = (f"{statistics.median(r.wall_minutes for r in runs):.1f} min", window)
    values["runner_minutes"] = (f"{statistics.median(r.runner_minutes for r in runs):,.0f}", window)
    tag, published = latest_release(get)
    prs = fix_prs(get, published)
    window = (
        f"{len(prs)} pull requests merged since {tag} ({published:%Y-%m-%d}),"
        f" to {now:%Y-%m-%d}"
    )
    if prs:
        values["fix_pr_runs"] = (f"{statistics.median(p.runs for p in prs):g}", window)
        values["fix_pr_hours"] = (f"{statistics.median(p.hours for p in prs):.1f}", window)
    else:
        values["fix_pr_runs"] = values["fix_pr_hours"] = ("none merged", window)
    coverage = post_merge_coverage(codecov)
    values["statement_coverage"] = (
        f"{coverage.percent:.2f}%",
        f"Codecov, the post-merge run of `{coverage.commit[:7]}` ({coverage.uploaded})",
    )
    return values


# ---------------------------------------------------------------------------
# A junit file
# ---------------------------------------------------------------------------


class JunitRun(NamedTuple):
    started: datetime
    tests: int
    seconds: float
    spawning_seconds: float
    census: bool


def read_junit(path: Path) -> JunitRun:
    """What a junit file says of its run: when it started, its tests, their
    seconds, the seconds of the tests that started a process, and whether
    the file carries the subprocess census at all."""
    try:
        # The suite's own junit output, read from a local path: expat
        # resolves no external entity and refuses entity amplification.
        document = ET.parse(path).getroot()
    except (OSError, ET.ParseError) as exc:
        raise MeasureError(f"{path}: {exc}") from exc
    suites = [document] if document.tag == "testsuite" else list(document.iter("testsuite"))
    stamps = [suite.get("timestamp") for suite in suites if suite.get("timestamp")]
    if not stamps:
        raise MeasureError(f"{path} holds no junit testsuite with a timestamp")
    tests, seconds, spawning, census = 0, 0.0, 0.0, False
    try:
        for case in document.iter("testcase"):
            time = float(case.get("time") or 0)
            tests += 1
            seconds += time
            for prop in case.iter("property"):
                if prop.get("name") == CENSUS:
                    census = True
                    if int(prop.get("value") or 0) > 0:
                        spawning += time
        started = min(_time(str(stamp)) for stamp in stamps)
    except ValueError as exc:
        raise MeasureError(f"{path} is not a junit file pytest wrote: {exc}") from exc
    return JunitRun(started, tests, seconds, spawning, census)


def junit_values(path: Path) -> dict[str, tuple[str, str]]:
    """The junit file's rows: each one's value and the run it was measured
    over, by key.  Raises `MeasureError` for a file that cannot give them."""
    run = read_junit(path)
    if not run.tests or run.seconds <= 0:
        raise MeasureError(f"{path} holds no test that took any time")
    if not run.census:
        raise MeasureError(
            f"{path} carries no subprocess census: write it with `python -m pytest"
            f" -n auto -p tests.subprocess_census --junitxml={path}`"
        )
    window = f"a run of {run.tests:,} tests, {run.started.astimezone(timezone.utc):%Y-%m-%d %H:%M} UTC"
    return {
        "gate_worker_seconds": (f"{run.seconds:,.0f}", window),
        "subprocess_share": (f"{100 * run.spawning_seconds / run.seconds:.1f}%", window),
    }


# ---------------------------------------------------------------------------
# The block
# ---------------------------------------------------------------------------


class Row(NamedTuple):
    measure: str
    audit: str
    now: str
    over: str


HEADER = f"| Measure | v0.2.0, the audit ({AUDIT_DATE}) | Now | Measured over |"
_RULE = "|---------|---------------------------|-----|---------------|"


def rows(
    tree: Mapping[str, tuple[str, str]], measured: Mapping[str, tuple[str, str]],
) -> list[Row]:
    """One row per measure, in `MEASURES` order: the tree's from `tree`, the
    others from `measured`, and a row neither holds says it was not
    measured and which flag measures it."""
    out = []
    for measure in MEASURES:
        if measure.source == TREE:
            now, over = tree[measure.key]
        elif measure.key in measured:
            now, over = measured[measure.key]
        else:
            now, over = "not measured", f"{NOT_MEASURED}: {FLAGS[measure.source]} measures it"
        out.append(Row(measure.label, measure.audit, now, over))
    return out


def _cell(text: str) -> str:
    return text.replace("|", "\\|")


def render(table: Sequence[Row], version: str) -> str:
    """The block's text, as it belongs between its markers."""
    lines = [HEADER, _RULE]
    lines += [
        f"| {_cell(r.measure)} | {_cell(r.audit)} | {_cell(r.now)} | {_cell(r.over)} |"
        for r in table
    ]
    return "\n".join([
        *lines,
        "",
        "What each row counts, as the v0.2.0 column counted it:",
        "",
        *(f"- **{measure.label}**: {measure.counts}." for measure in MEASURES),
        "",
        f"Measured for v{version} by `scripts/render_status.py`.  The v0.2.0"
        f" column is the audit's measurement of {AUDIT_COMMIT}, taken on"
        f" {AUDIT_DATE} and held in `scripts/scorecard.py`.  `scripts/"
        "check_doc_counts.py --release` measures the tree's rows again; the"
        " others change from one moment to the next, so it asks of each only"
        " that it states the window it was measured over.",
        "",
    ])


_SPLIT = re.compile(r"(?<!\\)\|")


def parse(block: str) -> list[Row] | str:
    """The rows of a block's table, or why they cannot be read."""
    lines = block.splitlines()
    if HEADER not in lines:
        return "the `scorecard` block has no table under the header scripts/scorecard.py writes"
    out = []
    for line in lines[lines.index(HEADER) + 2:]:
        if not line.startswith("|"):
            break
        cells = [cell.strip().replace("\\|", "|") for cell in _SPLIT.split(line.strip())[1:-1]]
        if len(cells) != 4:
            return f"a row of the `scorecard` block does not have four cells: {line[:160]!r}"
        out.append(Row(*cells))
    return out


def stamped(over: str) -> bool:
    """Whether a "Measured over" cell states a window: a row a render
    measured carries a date, and one it did not says so."""
    return not over.startswith(NOT_MEASURED) and re.search(r"\d{4}-\d{2}-\d{2}", over) is not None


def stale(block: str, fresh: Sequence[Row], version: str) -> list[str]:
    """Why the block is not current, `[]` when it is.

    The tree's rows, the caption and the counting notes must be what a
    render writes now (`fresh`, for `version`).  A network or junit row is
    not measured again: it must be present and state the window it was
    measured over, and its value and window are taken as the document has
    them."""
    current = parse(block)
    if isinstance(current, str):
        return [current]
    in_document = {row.measure: row for row in reversed(current)}
    errors = []
    expected = []
    for measure, row in zip(MEASURES, fresh, strict=True):
        found = in_document.get(measure.label)
        if measure.source == TREE:
            expected.append(row)
        elif found is None:
            errors.append(f"the `scorecard` block has no `{measure.label}` row")
            expected.append(row)
        elif not stamped(found.over):
            errors.append(
                f"the `scorecard` block's `{measure.label}` row states no window it was"
                f" measured over: scripts/render_status.py measures it with"
                f" {FLAGS[measure.source]}"
            )
            expected.append(row)
        else:
            expected.append(row._replace(now=found.now, over=found.over))
    want = render(expected, version)
    if want != block:
        pairs = itertools.zip_longest(
            block.splitlines(), want.splitlines(), fillvalue="(nothing)"
        )
        document, tree = next(
            ((a, b) for a, b in pairs if a != b), ("(the same lines)", "(other line ends)")
        )
        errors.append(
            "the generated `scorecard` block is not what scripts/render_status.py"
            " writes now; run it and commit the result.  First difference: the"
            f" document has {document[:160]!r}, the tree gives {tree[:160]!r}"
        )
    return errors
