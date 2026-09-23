#!/usr/bin/env python
"""The documentation example gate: every Vera block an agent-facing document
teaches passes the toolchain, or carries a marker saying why not (#1481).

One checker holds every document in ``DOC_GATES`` to the same four stages, in
order:

1. **parse** — the block parses.
2. **check** — ``vera check`` accepts it, and it names nothing it does not
   define.  ``vera check`` only warns on a call to an undefined function or
   an unknown constructor (``UNDEFINED_NAME_CODES``), so that the program
   still reaches code generation, which refuses it; a block that draws one
   of those warnings leans on another block's definitions, and says so with
   an ``INCOMPLETE`` marker rather than passing as a complete program.
3. **verify** — ``vera verify`` accepts it.
4. **run** — for each ``vera:run`` marker on the block, ``vera run --fn``
   with the marker's arguments exits 0 and prints exactly the marker's
   ``stdout``.  A block without one does not run: only the document can say
   which invocation it teaches and what that invocation prints.

A block that is deliberately wrong or partial carries a skip marker naming
the stage it fails, with a category and a reason (``scripts/doc_annotations.py``
defines the grammar and the category vocabulary).  The gate still runs a
marked stage and requires it to fail there: a marked block that passes carries
a stale marker, and the gate fails until the marker is removed.  An unmarked
block that fails a stage fails the gate.

Which blocks are Vera
---------------------
A fence tagged ``vera`` always is: the author declared the language, so the
block is held to the gate however it looks, and a fragment says so with a
marker rather than being passed over by a guess.  An untagged fence, and an
HTML ``<pre>`` block, is Vera when it opens with a top-level declaration
(``fn``, ``data``, ``effect``, ``type``, ``forall<``, ``module``, ``import``,
optionally after ``public``/``private`` and leading ``--`` comments) — the
spec writes most of its programs in untagged fences, and the landing page's
``<pre>`` blocks carry no language at all.  Any other language tag is not
Vera, and a marker on such a block is a problem.

A ``vera:diagnostic`` pair (``scripts/check_diagnostic_examples.py``) marks
its program as the expected failure at the pair's ``stage``: the program is
held to fail there, and nowhere earlier, exactly as a skip marker would hold
it, and the replay gate pins the diagnostic's text.

Fidelity to the toolchain
-------------------------
The check and verify stages call the CLI's own ``cmd_check`` and
``cmd_verify`` with ``--json`` output, in process, on a file written to a
scratch directory: the same parse, the same import resolution and the same
type-checker artifacts ``vera verify`` hands the verifier.  A block whose
reader would run ``vera verify`` gets that command's verdict, not an
approximation of it.  The run stage starts ``python -m vera.cli run`` in a
subprocess, the command a reader types, with this checkout's compiler first
on ``PYTHONPATH``, the environment variables that change what a program does
neutralised (the list ``scripts/check_examples_run.py`` keeps), stdin closed
and a time budget.

The scratch directory holds a ``vera/`` copy of ``examples/vera/``, the stub
modules the repository keeps for cross-module examples, so a block that
imports ``vera.math`` or ``vera.collections`` resolves them the way the
module chapter says an import resolves: to ``vera/math.vera`` beside the
importing file.

The coverage rule
-----------------
Every tracked document with a block the gate would read as Vera is in exactly
one of ``DOC_GATES`` (the gate reads it) and ``NOT_GATED`` (with the reason it
does not).  A document added later with Vera blocks and no entry fails the
gate, and so does an entry that no longer matches a document, so neither list
can drift from the tree.  The rule runs whenever the gate checks every
document, which is how pre-commit and CI run it.

Usage::

    python scripts/check_doc_examples.py              # every document
    python scripts/check_doc_examples.py SKILL.md     # named documents only
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from collections.abc import Callable
from pathlib import Path
from typing import Any, NamedTuple

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_examples_run import NEUTRALISED_ENV
from doc_annotations import (
    CATEGORIES,
    Annotation,
    CodeBlock,
    RunMarker,
    StageOutcome,
    evaluate_block,
    scan_diagnostic_examples,
    scan_html,
    scan_markdown,
)

ROOT = Path(__file__).resolve().parent.parent


# ---------------------------------------------------------------------------
# The documents
# ---------------------------------------------------------------------------


# Every agent-facing document whose Vera blocks the gate holds, as
# repo-relative POSIX paths or globs.  A pattern that matches no file is an
# error: a renamed document must fail the gate rather than drop out of it.
DOC_GATES: tuple[str, ...] = (
    "SKILL.md",
    "README.md",
    "FAQ.md",
    "EXAMPLES.md",
    "DE_BRUIJN.md",
    "PYPI_README.md",
    "spec/*.md",
    "docs/index.html",
    "docs/index.md",
)

# Tracked documents with Vera blocks the gate deliberately does not read,
# each with the reason.  Printed by the report, so a reader of a gate run
# sees what is not covered and why.
NOT_GATED: dict[str, str] = {
    "docs/SKILL.md": (
        "generated from SKILL.md by scripts/build_site.py with the markers "
        "stripped; check_site_assets.py holds it equal to that gated source"
    ),
    "docs/llms-full.txt": (
        "generated by scripts/build_site.py with the markers stripped; its "
        "Vera blocks come from SKILL.md and FAQ.md, and check_site_assets.py "
        "holds it equal to them"
    ),
    ".github/ISSUE_TEMPLATE/bug_report.md": (
        "an issue template: its vera fence is an empty slot for the "
        "reporter's program"
    ),
    ".github/ISSUE_TEMPLATE/spec_issue.md": (
        "an issue template: its vera fence is an empty slot for the "
        "reporter's example"
    ),
}

# The file types the coverage rule reads for Vera blocks.
DOCUMENT_SUFFIXES: tuple[str, ...] = (".md", ".html", ".txt")

# The stub modules a block's `vera.*` imports resolve against.
IMPORT_ROOT = "examples/vera"

# Per-invocation wall-clock budget for the run stage.  A documentation
# example finishes in about a second; this only fires on a hang.
RUN_TIMEOUT_SECONDS = 120

# The stages in pipeline order, for the report.
STAGE_ORDER: tuple[str, ...] = ("parse", "check", "verify", "run")

# The warnings `vera check` gives a name the program does not define — a
# bare call (E200), a constructor (E210), a qualified call (E220), a module
# member (E233), a nullary constructor in a pattern (E322).  The command
# only warns so the program still reaches code generation, which refuses
# it; the check stage fails on them, because a block that draws one is not
# the complete program it would otherwise pass as.
UNDEFINED_NAME_CODES: frozenset[str] = frozenset(
    {"E200", "E210", "E220", "E233", "E322"}
)


# ---------------------------------------------------------------------------
# Which blocks are Vera
# ---------------------------------------------------------------------------


_DECLARATION_RE = re.compile(
    r"\A\s*(?:--.*\n\s*)*"  # optional leading line comments
    r"(?:public\s+|private\s+)?"  # optional visibility
    r"(?:fn\s|data\s|effect\s|type\s|forall\s*<|module\s|import\s)"
)


def selects(block: CodeBlock) -> bool:
    """Whether the gate reads *block* as Vera (see the module docstring)."""
    lang = block.lang.lower()
    if lang == "vera":
        return True
    if lang == "":
        return bool(_DECLARATION_RE.search(block.content.strip()))
    return False


def scan_document(path: Path) -> tuple[list[CodeBlock], list[str]]:
    """The code blocks of one document, with its marker problems."""
    if path.suffix == ".html":
        return scan_html(path)
    return scan_markdown(path)


def diagnostic_markers(path: Path) -> dict[int, Annotation]:
    """The expected failure each ``vera:diagnostic`` pair declares, keyed by
    the line of the program's opening fence (the line after the pair's open
    annotation).  Malformed pairs are reported by
    ``check_diagnostic_examples.py``; a program this cannot read is gated as
    an ordinary block, so it cannot escape by being malformed."""
    if path.suffix == ".html":
        return {}
    examples, _problems = scan_diagnostic_examples(path)
    return {
        ex.line + 1: Annotation(
            ex.line,
            ex.stage,
            "WRONG",
            f"vera:diagnostic example of {ex.error_code or 'its diagnostic'}; "
            f"check_diagnostic_examples.py replays the rendered text",
        )
        for ex in examples
    }


# ---------------------------------------------------------------------------
# The stages
# ---------------------------------------------------------------------------


def _first_line(text: str, limit: int = 240) -> str:
    stripped = text.strip()
    return stripped.splitlines()[0][:limit] if stripped else ""


def parse_error(content: str) -> str | None:
    """The parse stage: an error message, or None when the block parses."""
    from vera.errors import VeraError
    from vera.parser import parse

    try:
        parse(content, file="<doc>")
    except VeraError as exc:
        d = exc.diagnostic
        return f"[{d.error_code}] block line {d.location.line}: {_first_line(d.description)}"
    except Exception as exc:  # noqa: BLE001 — any parser crash is this block's parse failure, reported
        return f"{type(exc).__name__}: {_first_line(str(exc))}"
    return None


def _cli_json(command: Callable[..., int], path: Path) -> tuple[int, Any, str]:
    """Run one CLI command function in process with ``--json`` output."""
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = command(str(path), as_json=True)
    text = out.getvalue()
    try:
        return code, json.loads(text), text
    except json.JSONDecodeError:
        return code, None, text + err.getvalue()


def _diagnostic_text(diagnostic: dict[str, Any]) -> str:
    line = (diagnostic.get("location") or {}).get("line")
    return (
        f"[{diagnostic.get('error_code')}] block line {line}: "
        f"{_first_line(diagnostic.get('description') or '')}"
    )


def cli_stage_error(
    command: Callable[..., int],
    path: Path,
    failing_warnings: frozenset[str] = frozenset(),
) -> str | None:
    """A check or verify stage: the command's first error, or None.

    Both signals must agree before a block passes — the exit code and the
    envelope's ``ok`` — so a command that exits 0 on an envelope saying
    otherwise (or the reverse) fails the stage instead of picking a side.
    A warning whose code is in *failing_warnings* fails the stage too.
    """
    code, data, raw = _cli_json(command, path)
    if not isinstance(data, dict):
        return f"the command's --json output did not parse: {_first_line(raw)!r}"
    ok = data.get("ok")
    if code == 0 and ok is True:
        for warning in data.get("warnings") or []:
            if warning.get("error_code") in failing_warnings:
                return (
                    f"{_diagnostic_text(warning)} — the command only warns, "
                    f"but a block that names something it does not define "
                    f"is partial"
                )
        return None
    if code == 0 or ok is True:
        return f"exit code {code} disagrees with the envelope's ok={ok!r}"
    diagnostics = data.get("diagnostics") or []
    if not diagnostics:
        return f"exited {code} with no diagnostic"
    return _diagnostic_text(diagnostics[0])


def check_error(path: Path) -> str | None:
    """The check stage: ``vera check --json`` on *path*, failing on the
    undefined-name warnings as well as on errors."""
    from vera.cli import cmd_check

    return cli_stage_error(cmd_check, path, UNDEFINED_NAME_CODES)


def verify_error(path: Path) -> str | None:
    """The verify stage: ``vera verify --json`` on *path*."""
    from vera.cli import cmd_verify

    return cli_stage_error(cmd_verify, path)


def expected_stdout(run: RunMarker) -> str:
    """What ``vera run`` prints for a marker's ``stdout``.

    ``vera run`` ends non-empty output with a newline, adding one when the
    program's own output did not, so a marker writes the output without it.
    """
    if run.stdout == "" or run.stdout.endswith("\n"):
        return run.stdout
    return run.stdout + "\n"


def run_command(path: Path, run: RunMarker) -> list[str]:
    """The ``vera run`` argv for one marker.  ``--fn`` is always passed, so a
    missing or private function is an error rather than `vera run`'s
    first-export fallback running something else."""
    cmd = [sys.executable, "-m", "vera.cli", "run", str(path), "--fn", run.fn]
    if run.args:
        cmd += ["--", *run.args]
    return cmd


def shown_invocation(run: RunMarker) -> str:
    """The invocation as a reader would type it, for messages."""
    text = f"vera run --fn {run.fn}"
    if run.args:
        text += " -- " + " ".join(shlex.quote(a) for a in run.args)
    return text


def run_env(root: Path) -> dict[str, str]:
    """The run stage's environment: inherited, minus the variables that
    change what a program does, with *root*'s compiler first on the path."""
    env = dict(os.environ)
    for name in NEUTRALISED_ENV:
        env.pop(name, None)
    existing = env.get("PYTHONPATH")
    env["PYTHONPATH"] = str(root) + (os.pathsep + existing if existing else "")
    return env


def run_error(
    root: Path, path: Path, run: RunMarker, cwd: Path,
    timeout: int = RUN_TIMEOUT_SECONDS,
) -> str | None:
    """The run stage for one marker: an error message, or None."""
    try:
        result = subprocess.run(
            run_command(path, run),
            capture_output=True,
            text=True,
            encoding="utf-8",
            cwd=str(cwd),
            stdin=subprocess.DEVNULL,
            env=run_env(root),
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return f"`{shown_invocation(run)}` exceeded the {timeout}s budget"
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip() or "no output"
        return (
            f"`{shown_invocation(run)}` exited {result.returncode}: "
            f"{_first_line(detail)}"
        )
    want = expected_stdout(run)
    if result.stdout != want:
        return (
            f"`{shown_invocation(run)}` printed {result.stdout!r}; the "
            f"marker expects {want!r}"
        )
    return None


# ---------------------------------------------------------------------------
# Gating one document
# ---------------------------------------------------------------------------


class Workspace:
    """The scratch directory the check, verify and run stages read from.

    Each block is written to its own file, named for its document and line,
    beside a ``vera/`` copy of the import root.  Runs start in a separate
    empty directory, so a program that writes a file writes it there, and
    nothing on the working directory can shadow the compiler.
    """

    def __init__(self, root: Path, scratch: Path) -> None:
        self.blocks = scratch / "blocks"
        self.blocks.mkdir()
        shutil.copytree(root / IMPORT_ROOT, self.blocks / "vera")
        self.cwd = scratch / "cwd"
        self.cwd.mkdir()

    def write(self, doc: str, block: CodeBlock) -> Path:
        slug = re.sub(r"[^A-Za-z0-9]+", "_", doc).strip("_")
        path = self.blocks / f"{slug}_L{block.line}.vera"
        path.write_text(block.content + "\n", encoding="utf-8")
        return path


def on_file(
    stage: Callable[[Path], str | None], path: Path,
) -> Callable[[str], str | None]:
    """Adapt a stage that reads the block's file on disk to the
    content-taking runner ``evaluate_block`` calls."""
    return lambda _content: stage(path)


class BlockResult(NamedTuple):
    """What the gate found for one Vera block."""

    doc: str
    block: CodeBlock
    outcomes: tuple[StageOutcome, ...]
    run_errors: tuple[tuple[RunMarker, str | None], ...]


class DocReport(NamedTuple):
    """The gate's findings for one document."""

    doc: str
    total_blocks: int
    results: tuple[BlockResult, ...]
    problems: tuple[str, ...]


def gate_document(
    root: Path, doc: str, workspace: Workspace,
) -> DocReport:
    """Run every Vera block of one gated document through the stages."""
    return gate_file(root, root / doc, doc, workspace)


def gate_file(
    root: Path, path: Path, doc: str, workspace: Workspace,
) -> DocReport:
    """Run every Vera block of the document at *path*, reported as *doc*,
    through the stages, with *root*'s compiler for the run stage."""
    blocks, scan_problems = scan_document(path)
    problems = [f"{doc} {p}" for p in scan_problems]
    implied = diagnostic_markers(path)
    results: list[BlockResult] = []

    for block in blocks:
        if block.line in implied:
            block = block._replace(
                annotations=(*block.annotations, implied[block.line])
            )
        if not selects(block):
            if block.annotations or block.runs:
                problems.append(
                    f"{doc} line {block.line}: a vera marker on a block the "
                    f"gate does not read as Vera (language "
                    f"{block.lang!r}) — remove it"
                )
            continue
        if block.runs and block.annotations:
            problems.append(
                f"{doc} line {block.line}: vera:run on a block with a "
                f"vera:skip marker — the gate stops at the marked stage, so "
                f"the invocation would never run"
            )

        path_on_disk = workspace.write(doc, block)
        outcomes = evaluate_block(
            block,
            [
                ("parse", parse_error),
                ("check", on_file(check_error, path_on_disk)),
                ("verify", on_file(verify_error, path_on_disk)),
            ],
        )
        run_errors: list[tuple[RunMarker, str | None]] = []
        if (
            block.runs
            and not block.annotations
            and all(o.status == "ok" for o in outcomes)
        ):
            for run in block.runs:
                run_errors.append(
                    (run, run_error(root, path_on_disk, run, workspace.cwd))
                )
        results.append(
            BlockResult(doc, block, tuple(outcomes), tuple(run_errors))
        )
    return DocReport(doc, len(blocks), tuple(results), tuple(problems))


# ---------------------------------------------------------------------------
# The coverage rule
# ---------------------------------------------------------------------------


def expand_gates(
    root: Path, patterns: tuple[str, ...] = DOC_GATES,
) -> tuple[list[str], list[str]]:
    """The gated documents as repo-relative POSIX paths, and any pattern
    that matches no file (an error: a rename must not drop a document)."""
    docs: list[str] = []
    errors: list[str] = []
    for pattern in patterns:
        matches = sorted(
            p.relative_to(root).as_posix()
            for p in root.glob(pattern)
            if p.is_file()
        )
        if not matches:
            errors.append(
                f"DOC_GATES names {pattern!r}, which matches no file — a "
                f"renamed or deleted document must be re-pointed or removed, "
                f"not left to cover nothing"
            )
        docs.extend(m for m in matches if m not in docs)
    return docs, errors


def tracked_documents(root: Path) -> list[str]:
    """Every tracked file the coverage rule reads, as repo-relative POSIX
    paths.  Tracked rather than on disk, so a scratch file in a working
    tree is not asked to justify itself."""
    listing = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=str(root),
        capture_output=True,
        check=True,
    )
    names = listing.stdout.decode("utf-8").split("\0")
    return sorted(
        n for n in names if n and n.endswith(DOCUMENT_SUFFIXES)
    )


def has_vera_blocks(path: Path) -> bool:
    """Whether *path* holds a block the gate would read as Vera."""
    blocks, _problems = scan_document(path)
    return any(selects(b) for b in blocks)


def check_coverage(
    root: Path,
    gated: list[str],
    not_gated: dict[str, str],
    tracked: list[str],
) -> list[str]:
    """Every tracked document with Vera blocks is classified exactly once,
    and every classification names a real document."""
    bearing = {doc for doc in tracked if has_vera_blocks(root / doc)}
    errors: list[str] = []
    if not bearing:
        errors.append(
            "no tracked document has a Vera block — the discovery matched "
            "nothing.  This is an error rather than a pass: a coverage rule "
            "over nothing holds every document to nothing."
        )
    for doc in sorted(bearing - set(gated) - set(not_gated)):
        errors.append(
            f"{doc} has Vera blocks the gate does not read — add it to "
            f"DOC_GATES, or to NOT_GATED with the reason it is exempt"
        )
    for doc in sorted(set(gated) & set(not_gated)):
        errors.append(
            f"{doc} is in both DOC_GATES and NOT_GATED — a document is "
            f"gated or exempt, never both"
        )
    for doc in sorted(set(not_gated) - bearing):
        errors.append(
            f"NOT_GATED names {doc}, which is not a tracked document with "
            f"Vera blocks — remove the stale entry"
        )
    return errors


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


class Findings(NamedTuple):
    """Everything the gate reports, split by kind."""

    failures: list[str]
    stale: list[str]
    problems: list[str]


def collect(reports: list[DocReport]) -> Findings:
    failures: list[str] = []
    stale: list[str] = []
    problems: list[str] = []
    for report in reports:
        problems.extend(report.problems)
        for r in report.results:
            last = r.outcomes[-1]
            where = f"{r.doc} line {r.block.line}"
            if last.status == "failed":
                failures.append(f"{where} [{last.stage}]: {last.error}")
            elif last.status == "stale":
                ann = last.annotation
                if ann is None:
                    raise RuntimeError("stale outcome missing its marker")
                stale.append(
                    f"{where} [vera:skip-{ann.stage} {ann.category}]: "
                    f"{ann.reason} — the block passes {ann.stage}"
                )
            for run, error in r.run_errors:
                if error is not None:
                    failures.append(f"{where} [run, marker line {run.line}]: {error}")
    return Findings(failures, stale, problems)


def summary_lines(report: DocReport) -> list[str]:
    """One document's counts: blocks that pass each stage, and the marked
    blocks by the stage they fail and their category."""
    passed = Counter(
        o.stage for r in report.results for o in r.outcomes if o.status == "ok"
    )
    marked: dict[str, Counter[str]] = {}
    for r in report.results:
        last = r.outcomes[-1]
        if last.status == "skipped" and last.annotation is not None:
            marked.setdefault(last.stage, Counter())[last.annotation.category] += 1
    runs = sum(1 for r in report.results for _run, err in r.run_errors if err is None)
    lines = [
        f"{report.doc}: {len(report.results)} Vera block(s) "
        f"of {report.total_blocks} code block(s)"
    ]
    if report.results:
        lines.append(
            f"  pass parse {passed['parse']}, check {passed['check']}, "
            f"verify {passed['verify']}; run invocations passing: {runs}"
        )
    for stage in STAGE_ORDER:
        if stage in marked:
            cats = ", ".join(f"{c} {n}" for c, n in sorted(marked[stage].items()))
            lines.append(
                f"  marked to fail {stage}: {sum(marked[stage].values())} ({cats})"
            )
    return lines


def report(
    reports: list[DocReport],
    findings: Findings,
    coverage: list[str],
    *,
    every_document: bool,
) -> int:
    """Print the report; return the exit code.  *every_document* says the
    run covered the whole registry, which is when the coverage rule ran and
    the exemptions are worth listing."""
    for doc_report in reports:
        for line in summary_lines(doc_report):
            print(line)
    used = sorted({
        r.outcomes[-1].annotation.category
        for d in reports for r in d.results
        if r.outcomes[-1].annotation is not None
    })
    if used:
        print("\nCategories:")
        for category in used:
            print(f"  {category}: {CATEGORIES.get(category, '(not in the vocabulary)')}")
    if every_document:
        print("\nNot gated:")
        for doc, reason in sorted(NOT_GATED.items()):
            print(f"  {doc}: {reason}")

    sections = [
        ("COVERAGE ERRORS", coverage),
        ("MARKER PROBLEMS", findings.problems),
        (
            "STALE MARKERS (the block passes the stage its marker says it "
            "fails — remove the marker)",
            findings.stale,
        ),
        ("FAILURES", findings.failures),
    ]
    failed = False
    for title, items in sections:
        if items:
            failed = True
            print(f"\n{title} ({len(items)}):", file=sys.stderr)
            for item in items:
                print(f"  {item}", file=sys.stderr)
    if findings.failures:
        print(
            "\nA block the document teaches must pass every stage.  Fix the "
            "block, or, when it is deliberately wrong or partial, mark the "
            'stage it fails: <!-- vera:skip-<stage> category="..." '
            'reason="..." --> on the line before its fence (categories: '
            f"{', '.join(CATEGORIES)}; see scripts/doc_annotations.py).  A "
            "failing vera:run marker means the document states an output "
            "the program does not print.",
            file=sys.stderr,
        )
    if failed:
        return 1
    print("\nEvery documentation Vera block passes its gate.")
    return 0


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def run_gate(root: Path, docs: list[str]) -> list[DocReport]:
    """Gate *docs* (repo-relative paths under *root*)."""
    with tempfile.TemporaryDirectory(prefix="vera-doc-examples-") as scratch:
        workspace = Workspace(root, Path(scratch))
        return [gate_document(root, doc, workspace) for doc in docs]


def compiler_canary(root: Path) -> str | None:
    """An error when the in-process stages would use another checkout's
    compiler — the gate must measure the tree it lives in."""
    import vera

    location = Path(vera.__file__).resolve()
    if root.resolve() not in location.parents:
        return (
            f"the in-process stages imported vera from {location}, not from "
            f"{root} — run the gate with this checkout's interpreter"
        )
    return None


def main(argv: list[str] | None = None) -> int:
    requested = sys.argv[1:] if argv is None else argv
    gated, coverage = expand_gates(ROOT)
    canary = compiler_canary(ROOT)
    if canary is not None:
        print(f"ERROR: {canary}", file=sys.stderr)
        return 1

    if requested:
        unknown = [d for d in requested if d not in gated]
        if unknown:
            print(
                f"ERROR: not a gated document: {', '.join(unknown)} (gated: "
                f"{', '.join(gated)})",
                file=sys.stderr,
            )
            return 1
        docs = requested
        coverage = []
    else:
        docs = gated
        try:
            coverage += check_coverage(
                ROOT, gated, NOT_GATED, tracked_documents(ROOT)
            )
        except (OSError, subprocess.CalledProcessError) as exc:
            coverage.append(
                f"could not list the tracked documents with git ({exc}) — the "
                f"coverage rule needs a git checkout"
            )

    reports = run_gate(ROOT, docs)
    return report(
        reports, collect(reports), coverage, every_document=not requested
    )


if __name__ == "__main__":
    sys.exit(main())
