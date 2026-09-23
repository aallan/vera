#!/usr/bin/env python
"""The documentation example gate: every Vera block an agent-facing document
teaches passes the toolchain, or carries a marker saying why not (#1481).

One checker holds every document in ``DOC_GATES`` to the same four stages, in
order:

1. **parse** — the block parses.
2. **check** — ``vera check`` accepts it, and it draws no warning outside
   ``BENIGN_CHECK_WARNINGS``.  ``vera check`` only warns on a name the block
   does not define — a function, a constructor, a module — so that the
   program still reaches code generation, which refuses it; the gate fails
   every warning except the ones it names as harmless, so a warning the
   checker gains later fails here until someone classifies it.
3. **verify** — ``vera verify`` accepts it.
4. **run** — for each ``vera:run`` marker, ``vera run --fn`` with the
   marker's arguments exits 0 and prints exactly the marker's ``stdout``.
   A block that reaches this stage and exports a public function must name
   at least one invocation, or carry a ``vera:no-run`` marker whose property
   (``NO_RUN_PROPERTIES``) keeps it from running, so no block skips the run
   decision silently.

A block that is deliberately wrong or partial carries a skip marker naming
the stage it fails, with a category, a reason and — at the check and verify
stages, and for a WRONG example — the codes the failure carries
(``scripts/doc_annotations.py`` defines the grammar and the vocabularies).
The gate still runs a marked stage and requires it to fail there, with those
codes and no others: a marked block that passes carries a stale marker, and
one that fails some other way fails the gate.  An unmarked block that fails
a stage fails the gate.

Every ``vera run examples/<name>.vera`` invocation a gated document names is
run too, unless ``scripts/check_examples_run.py`` already runs that exact
invocation or skips that example by property.

Which blocks are Vera
---------------------
A fence tagged ``vera`` always is: the author declared the language, so the
block is held to the gate however it looks, and a fragment says so with a
marker rather than being passed over by a guess.  An untagged fence, and an
HTML ``<pre>`` block, is Vera when it opens a program: its first word, after
comments, is one of the keywords in FIRST(``start``) of the compiler's own
grammar, and the compiler's own parser accepts its first two tokens as the
start of a program — so a top-level form the grammar gains is recognised
without an edit here, and a closure such as ``fn(@Int -> @Int)`` is not
mistaken for a declaration.  Any other language tag is not Vera, and a
marker on such a block is a problem.

A ``vera:diagnostic`` pair (``scripts/check_diagnostic_examples.py``) marks
its program as the expected failure at the pair's ``stage``, with the pair's
``error_code``.  The replay gate scans every gated Markdown document and
replays only ``REPLAYED_STAGES``, so the example gate honours a pair only at
a replayed stage and only with a code; any other pair is a marker problem.

Fidelity to the toolchain
-------------------------
The check and verify stages call the CLI's own ``cmd_check`` and
``cmd_verify`` with ``--json`` output, in process, on a file written to a
scratch directory: the same parse, the same import resolution and the same
type-checker artifacts ``vera verify`` hands the verifier.  The run stage
starts ``python -m vera.cli run`` in a subprocess, the command a reader
types, with this checkout's compiler first on ``PYTHONPATH``, the
environment variables that change what a program does neutralised (the list
``scripts/check_examples_run.py`` keeps), stdin closed and a time budget.

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
import functools
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
from collections.abc import Callable, Iterable
from pathlib import Path
from typing import Any, NamedTuple

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_examples_run import (
    NEUTRALISED_ENV,
    RUN_SPECS,
    SKIP_PROPERTIES,
    SKIPS,
)
from doc_annotations import (
    CATEGORIES,
    REPLAYED_STAGES,
    Annotation,
    CodeBlock,
    NoRunMarker,
    RunMarker,
    StageFailure,
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
    "CHANGELOG.md": (
        "the change record: its blocks show what a release changed, in the "
        "syntax of that release, and are not examples to copy"
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

# The warnings `vera check` may give a block the check stage still passes,
# each with why it is harmless there.  Every other warning fails the stage:
# the rest of the checker's warnings name something the block does not
# define — a function, a constructor, a module — which `vera check` only
# warns on so the program still reaches code generation, where it is an
# error.  A warning the checker gains later fails the stage until it is
# classified here.
BENIGN_CHECK_WARNINGS: dict[str, str] = {
    "W001": (
        "a typed hole: the hole examples exist to show the report "
        "`vera check` gives for one"
    ),
    "W002": (
        "an async argument that evaluates eagerly: the program compiles and "
        "runs, in program order"
    ),
    "E310": (
        "an unreachable match arm: the program compiles and runs, and the "
        "arm is dead code"
    ),
}

# The properties a `vera:no-run` marker may name.  Where a property is the
# one `check_examples_run.py` skips an example for, the definition is that
# script's own.
NO_RUN_PROPERTIES: dict[str, str] = {
    "network": SKIP_PROPERTIES["network"],
    "api-key": SKIP_PROPERTIES["api-key"],
    "stdin": SKIP_PROPERTIES["stdin"],
    "long-running": SKIP_PROPERTIES["long-running"],
    "non-scalar-entry": (
        "every function it exports takes a parameter `vera run` cannot build "
        "from command-line arguments: an ADT, an array, a type variable or a "
        "request"
    ),
    "typed-hole": (
        "it holds a typed hole `?`, which `vera run` refuses (E614); the "
        "block shows the report `vera check` gives for one"
    ),
    "fixture": (
        "it reads a file or a database table it does not create, so a run "
        "reaches only the arm that reports the fixture missing"
    ),
}

# The parameter types `vera run` builds from command-line arguments.
_CLI_SCALARS: frozenset[str] = frozenset(
    {"Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit"}
)


# ---------------------------------------------------------------------------
# Which blocks are Vera
# ---------------------------------------------------------------------------


@functools.lru_cache(maxsize=1)
def program_keywords() -> frozenset[str]:
    """The words a Vera program can start with: FIRST(``start``) over the
    compiler's own grammar, every one of them a keyword.

    Raises when the grammar lets a program start with a token that is not a
    literal keyword, because the selector's premise — that a program opens
    with one of a fixed set of words — would no longer hold.
    """
    from lark.grammar import NonTerminal, Terminal
    from lark.lexer import PatternStr

    from vera.parser import _get_parser

    parser = _get_parser()
    first: dict[str, set[str]] = {r.origin.name: set() for r in parser.rules}
    nullable: set[str] = set()
    changed = True
    while changed:
        changed = False
        for rule in parser.rules:
            origin = rule.origin.name
            empty_so_far = True
            for sym in rule.expansion:
                if isinstance(sym, Terminal):
                    if sym.name not in first[origin]:
                        first[origin].add(sym.name)
                        changed = True
                    empty_so_far = False
                    break
                if isinstance(sym, NonTerminal):
                    before = len(first[origin])
                    first[origin] |= first[sym.name]
                    changed |= len(first[origin]) != before
                    if sym.name not in nullable:
                        empty_so_far = False
                        break
            if empty_so_far and origin not in nullable:
                nullable.add(origin)
                changed = True
    terminals = {t.name: t for t in parser.terminals}
    words: set[str] = set()
    for name in first["start"]:
        pattern = terminals[name].pattern
        if not isinstance(pattern, PatternStr):
            raise RuntimeError(
                f"the grammar lets a program start with {name}, which is not "
                f"a keyword; the untagged-block selector assumes a program "
                f"opens with one"
            )
        words.add(pattern.value)
    return frozenset(words)


_FIRST_WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

# How many tokens of a block the compiler's parser must accept before the
# block counts as opening a program.  One is the keyword; the second tells a
# declaration (`fn name`, `type Name`) from a closure or a function type
# (`fn(...)`) and from prose that starts with a keyword (`type the ...`).
_PREFIX_TOKENS = 2


def opens_a_program(text: str) -> bool:
    """Whether *text*, after comments, starts the way a program does: its
    first word is in :func:`program_keywords`, and the compiler's own LALR
    parser accepts its first two tokens as the start of a program."""
    from lark.exceptions import UnexpectedInput

    from vera.lexical import blank_comments
    from vera.parser import _get_parser

    blanked = blank_comments(text)
    m = _FIRST_WORD_RE.match(blanked.lstrip())
    if m is None or m.group(0) not in program_keywords():
        return False
    fed = 0
    try:
        for _token in _get_parser().parse_interactive(blanked).iter_parse():
            fed += 1  # yielded; it is fed to the parser on the next step
            if fed > _PREFIX_TOKENS:
                return True
    except UnexpectedInput:
        return fed - 1 >= _PREFIX_TOKENS
    return fed >= _PREFIX_TOKENS


def selects(block: CodeBlock) -> bool:
    """Whether the gate reads *block* as Vera (see the module docstring)."""
    lang = block.lang.lower()
    if lang == "vera":
        return True
    if lang != "":
        return False
    return opens_a_program(block.content)


def scan_document(path: Path) -> tuple[list[CodeBlock], list[str]]:
    """The code blocks of one document, with its marker problems."""
    if path.suffix == ".html":
        return scan_html(path)
    return scan_markdown(path)


def diagnostic_markers(path: Path) -> tuple[dict[int, Annotation], list[str]]:
    """The expected failure each honoured ``vera:diagnostic`` pair declares,
    keyed by the line of the program's opening fence, and the problems of
    the pairs the gate does not honour.

    A pair is honoured only at a stage the replay gate replays and only with
    an ``error_code``, because then the failure is both replayed against
    live output and held to one code.  Malformed pairs are reported by
    ``check_diagnostic_examples.py``; a program the scanner cannot read is
    gated as an ordinary block, so it cannot escape by being malformed.
    """
    if path.suffix == ".html":
        return {}, []
    examples, _problems = scan_diagnostic_examples(path)
    implied: dict[int, Annotation] = {}
    problems: list[str] = []
    for ex in examples:
        if ex.stage not in REPLAYED_STAGES:
            problems.append(
                f"line {ex.line}: a vera:diagnostic pair at stage "
                f"{ex.stage!r} is not replayed (check_diagnostic_examples.py "
                f"replays {', '.join(REPLAYED_STAGES)}), so it cannot excuse "
                f"a failure — use a vera:skip marker with a reason"
            )
            continue
        if not ex.error_code:
            problems.append(
                f"line {ex.line}: a vera:diagnostic pair with no error_code "
                f"cannot excuse a failure, because the failure it excuses "
                f"would be held to no code — name the code"
            )
            continue
        implied[ex.line + 1] = Annotation(
            ex.line,
            ex.stage,
            "WRONG",
            f"vera:diagnostic example of {ex.error_code}; "
            f"check_diagnostic_examples.py replays the rendered text",
            (ex.error_code,),
        )
    return implied, problems


def diagnostic_documents(root: Path) -> list[str]:
    """The documents ``check_diagnostic_examples.py`` replays: every gated
    document that is not HTML.  One list, so a pair the example gate honours
    is always a pair the replay gate checks."""
    docs, _errors = expand_gates(root)
    return [d for d in docs if not d.endswith(".html")]


# ---------------------------------------------------------------------------
# The stages
# ---------------------------------------------------------------------------


def _first_line(text: str, limit: int = 240) -> str:
    stripped = text.strip()
    return stripped.splitlines()[0][:limit] if stripped else ""


def parse_error(content: str) -> StageFailure | None:
    """The parse stage: the failure, or None when the block parses."""
    from vera.errors import VeraError
    from vera.parser import parse

    try:
        parse(content, file="<doc>")
    except VeraError as exc:
        d = exc.diagnostic
        return StageFailure(
            f"[{d.error_code}] block line {d.location.line}: "
            f"{_first_line(d.description)}",
            frozenset({d.error_code or "none"}),
        )
    except Exception as exc:  # noqa: BLE001 — any parser crash is this block's parse failure, reported
        return StageFailure(f"{type(exc).__name__}: {_first_line(str(exc))}")
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


def _code(diagnostic: dict[str, Any]) -> str:
    return str(diagnostic.get("error_code") or "none")


def _diagnostic_text(diagnostic: dict[str, Any]) -> str:
    line = (diagnostic.get("location") or {}).get("line")
    return (
        f"[{diagnostic.get('error_code')}] block line {line}: "
        f"{_first_line(diagnostic.get('description') or '')}"
    )


def cli_stage_error(
    command: Callable[..., int],
    path: Path,
    benign_warnings: Iterable[str] | None = None,
) -> StageFailure | None:
    """A check or verify stage: the failure, or None.

    Both signals must agree before a block passes — the exit code and the
    envelope's ``ok`` — so a command that exits 0 on an envelope saying
    otherwise (or the reverse) fails the stage instead of picking a side.
    When *benign_warnings* is given, every warning whose code it does not
    name fails the stage too.  The failure carries the code of every error
    and every failing warning, so a marker naming codes is held to all of
    them.
    """
    code, data, raw = _cli_json(command, path)
    if not isinstance(data, dict):
        return StageFailure(
            f"the command's --json output did not parse: {_first_line(raw)!r}"
        )
    ok = data.get("ok")
    if (code == 0) != (ok is True):
        return StageFailure(
            f"exit code {code} disagrees with the envelope's ok={ok!r}"
        )
    errors = list(data.get("diagnostics") or [])
    failing = []
    if benign_warnings is not None:
        benign = set(benign_warnings)
        failing = [
            w for w in data.get("warnings") or [] if _code(w) not in benign
        ]
    if code == 0 and not failing:
        return None
    if code != 0 and not errors:
        return StageFailure(f"exited {code} with no diagnostic")
    codes = frozenset(_code(d) for d in [*errors, *failing])
    if errors:
        return StageFailure(_diagnostic_text(errors[0]), codes)
    return StageFailure(
        f"{_diagnostic_text(failing[0])} — the command only warns, but "
        f"{_code(failing[0])} is not a warning the gate lets a block through "
        f"with (BENIGN_CHECK_WARNINGS)",
        codes,
    )


def check_error(path: Path) -> StageFailure | None:
    """The check stage: ``vera check --json`` on *path*, failing on every
    warning outside ``BENIGN_CHECK_WARNINGS`` as well as on errors."""
    from vera.cli import cmd_check

    return cli_stage_error(cmd_check, path, BENIGN_CHECK_WARNINGS)


def verify_error(path: Path) -> StageFailure | None:
    """The verify stage: ``vera verify --json`` on *path*."""
    from vera.cli import cmd_verify

    return cli_stage_error(cmd_verify, path)


def expected_stdout(run: RunMarker) -> str | None:
    """What ``vera run`` prints for a marker's ``stdout``, or None when the
    marker does not pin its output.

    ``vera run`` ends non-empty output with a newline, adding one when the
    program's own output did not, so a marker writes the output without it.
    """
    if run.stdout is None:
        return None
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


def _run(
    root: Path, argv: list[str], cwd: Path, timeout: int,
) -> subprocess.CompletedProcess[str] | None:
    """One ``vera run``, or None when it exceeds *timeout*."""
    try:
        return subprocess.run(
            argv,
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
        return None


def run_error(
    root: Path, path: Path, run: RunMarker, cwd: Path,
    timeout: int = RUN_TIMEOUT_SECONDS,
) -> str | None:
    """The run stage for one marker: an error message, or None."""
    result = _run(root, run_command(path, run), cwd, timeout)
    if result is None:
        return f"`{shown_invocation(run)}` exceeded the {timeout}s budget"
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip() or "no output"
        return (
            f"`{shown_invocation(run)}` exited {result.returncode}: "
            f"{_first_line(detail)}"
        )
    want = expected_stdout(run)
    if want is not None and result.stdout != want:
        return (
            f"`{shown_invocation(run)}` printed {result.stdout!r}; the "
            f"marker expects {want!r}"
        )
    return None


# ---------------------------------------------------------------------------
# What a block exports, and what keeps it from running
# ---------------------------------------------------------------------------


def _program(content: str) -> Any:
    from vera.parser import parse_to_ast

    return parse_to_ast(content, file="<doc>")


def exported_functions(program: Any) -> list[Any]:
    """The public top-level functions of a parsed block: what `vera run`
    can call."""
    from vera import ast

    return [
        top.decl
        for top in program.declarations
        if isinstance(top.decl, ast.FnDecl) and top.visibility == "public"
    ]


def _aliases(program: Any) -> dict[str, Any]:
    from vera import ast

    return {
        top.decl.name: top.decl.type_expr
        for top in program.declarations
        if isinstance(top.decl, ast.TypeAliasDecl)
    }


def cli_constructible(type_expr: Any, aliases: dict[str, Any], depth: int = 0) -> bool:
    """Whether `vera run` can build a parameter of this type from a
    command-line argument: a scalar, a refinement of one, or an alias of
    either."""
    from vera import ast

    if depth > 16:
        return False
    if isinstance(type_expr, ast.RefinementType):
        return cli_constructible(type_expr.base_type, aliases, depth + 1)
    if isinstance(type_expr, ast.NamedType) and not type_expr.type_args:
        if type_expr.name in _CLI_SCALARS:
            return True
        if type_expr.name in aliases:
            return cli_constructible(aliases[type_expr.name], aliases, depth + 1)
    return False


def _signals(program: Any) -> tuple[set[str], set[tuple[str, str]], bool]:
    """Every effect a block's functions declare, every qualified call it
    makes, and whether it holds a typed hole."""
    from vera import ast
    from vera.obligations.cache import walk_nodes

    effects: set[str] = set()
    calls: set[tuple[str, str]] = set()
    hole = False
    for node in walk_nodes(program):
        if isinstance(node, ast.FnDecl) and isinstance(node.effect, ast.EffectSet):
            effects |= {
                ref.name for ref in node.effect.effects
                if isinstance(ref, ast.EffectRef)
            }
        elif isinstance(node, ast.QualifiedCall):
            calls.add((node.qualifier, node.name))
        elif isinstance(node, ast.HoleExpr):
            hole = True
    return effects, calls, hole


def no_run_property_holds(category: str, program: Any) -> bool | None:
    """Whether a no-run property holds of the block, or None when the gate
    cannot tell.  A property that does not hold is a stale marker."""
    effects, calls, hole = _signals(program)
    if category == "network":
        return "Http" in effects
    if category == "api-key":
        return "Inference" in effects
    if category == "stdin":
        return bool({("IO", "read_line"), ("IO", "read_char")} & calls)
    if category == "long-running":
        return ("IO", "sleep") in calls
    if category == "typed-hole":
        return hole
    if category == "fixture":
        return "DB" in effects or ("IO", "read_file") in calls
    if category == "non-scalar-entry":
        aliases = _aliases(program)
        return all(
            any(not cli_constructible(p, aliases) for p in fn.params)
            for fn in exported_functions(program)
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
    stage: Callable[[Path], StageFailure | None], path: Path,
) -> Callable[[str], StageFailure | None]:
    """Adapt a stage that reads the block's file on disk to the
    content-taking runner ``evaluate_block`` calls."""
    return lambda _content: stage(path)


class BlockResult(NamedTuple):
    """What the gate found for one Vera block."""

    doc: str
    block: CodeBlock
    outcomes: tuple[StageOutcome, ...]
    run_errors: tuple[tuple[RunMarker, str | None], ...]
    run_coverage: str | None = None  # why the run decision is missing


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


def _run_decision(
    doc: str, block: CodeBlock, problems: list[str],
) -> str | None:
    """Hold a block that reached the run stage to a run decision: at least
    one invocation, or one no-run marker whose property holds.  Returns the
    coverage failure, if any; marker problems go to *problems*."""
    where = f"{doc} line {block.line}"
    program = _program(block.content)
    exports = exported_functions(program)
    if block.no_runs:
        marker: NoRunMarker = block.no_runs[0]
        if block.runs:
            problems.append(
                f"{where}: vera:no-run beside vera:run — a block either names "
                f"its invocations or says why it names none"
            )
        elif not exports:
            problems.append(
                f"{where}: vera:no-run on a block that exports no public "
                f"function, so there is nothing to run — remove it"
            )
        elif marker.category not in NO_RUN_PROPERTIES:
            problems.append(
                f"{where}: vera:no-run has the unknown category "
                f"{marker.category!r} (one of {', '.join(NO_RUN_PROPERTIES)})"
            )
        elif no_run_property_holds(marker.category, program) is False:
            problems.append(
                f"{where}: vera:no-run category={marker.category!r} does not "
                f"hold of this block ({NO_RUN_PROPERTIES[marker.category]}) — "
                f"the marker is stale; run the block instead"
            )
        return None
    if exports and not block.runs:
        names = ", ".join(fn.name for fn in exports)
        return (
            f"exports {names} but names no invocation — add a vera:run "
            f"marker, or vera:no-run with the property that keeps the block "
            f"from running ({', '.join(NO_RUN_PROPERTIES)})"
        )
    return None


def gate_file(
    root: Path, path: Path, doc: str, workspace: Workspace,
) -> DocReport:
    """Run every Vera block of the document at *path*, reported as *doc*,
    through the stages, with *root*'s compiler for the run stage."""
    blocks, scan_problems = scan_document(path)
    problems = [f"{doc} {p}" for p in scan_problems]
    implied, pair_problems = diagnostic_markers(path)
    problems += [f"{doc} {p}" for p in pair_problems]
    results: list[BlockResult] = []

    for block in blocks:
        if block.line in implied:
            block = block._replace(
                annotations=(*block.annotations, implied[block.line])
            )
        if not selects(block):
            if block.annotations or block.runs or block.no_runs:
                problems.append(
                    f"{doc} line {block.line}: a vera marker on a block the "
                    f"gate does not read as Vera (language "
                    f"{block.lang!r}) — remove it"
                )
            continue
        if (block.runs or block.no_runs) and block.annotations:
            problems.append(
                f"{doc} line {block.line}: a run decision on a block with a "
                f"vera:skip marker — the gate stops at the marked stage, so "
                f"the block never reaches the run stage"
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
        coverage: str | None = None
        reached_run = (
            not block.annotations
            and len(outcomes) == 3
            and all(o.status == "ok" for o in outcomes)
        )
        if reached_run:
            coverage = _run_decision(doc, block, problems)
            for run in block.runs:
                run_errors.append(
                    (run, run_error(root, path_on_disk, run, workspace.cwd))
                )
        results.append(
            BlockResult(doc, block, tuple(outcomes), tuple(run_errors), coverage)
        )
    return DocReport(doc, len(blocks), tuple(results), tuple(problems))


# ---------------------------------------------------------------------------
# The invocations a document names
# ---------------------------------------------------------------------------


_INVOCATION_RE = re.compile(
    r"vera run(?P<flags>(?:\s+--[\w-]+)*)\s+examples/(?P<name>[\w/]+)\.vera"
    r"(?P<rest>[^`|<\n#]*)"
)


class Invocation(NamedTuple):
    """A ``vera run examples/<name>.vera`` a document names."""

    doc: str
    line: int
    name: str  # the example, by stem
    fn: str | None  # None when the invocation gives no --fn
    args: tuple[str, ...]

    def argv(self, root: Path) -> list[str]:
        cmd = [sys.executable, "-m", "vera.cli", "run",
               str(root / "examples" / f"{self.name}.vera")]
        if self.fn is not None:
            cmd += ["--fn", self.fn]
        if self.args:
            cmd += ["--", *self.args]
        return cmd

    def shown(self) -> str:
        text = f"vera run examples/{self.name}.vera"
        if self.fn is not None:
            text += f" --fn {self.fn}"
        if self.args:
            text += " -- " + " ".join(shlex.quote(a) for a in self.args)
        return text


def documented_invocations(
    path: Path, doc: str,
) -> tuple[list[Invocation], list[str]]:
    """Every ``vera run examples/<name>.vera`` invocation in a document,
    and the ones the gate cannot read (a problem, not a skip)."""
    found: list[Invocation] = []
    problems: list[str] = []
    for lineno, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        for m in _INVOCATION_RE.finditer(line):
            where = f"{doc} line {lineno}"
            if m.group("flags").strip():
                problems.append(
                    f"{where}: the gate does not run `vera run` with "
                    f"{m.group('flags').strip()} — name the invocation in a "
                    f"form it runs, or extend it"
                )
                continue
            try:
                words = shlex.split(m.group("rest"), posix=True)
            except ValueError as exc:
                problems.append(f"{where}: the invocation does not split: {exc}")
                continue
            fn: str | None = None
            args: tuple[str, ...] = ()
            i = 0
            ok = True
            while i < len(words):
                if words[i] == "--fn" and i + 1 < len(words):
                    fn = words[i + 1]
                    i += 2
                elif words[i] == "--":
                    args = tuple(words[i + 1:])
                    break
                else:
                    problems.append(
                        f"{where}: the gate cannot read {words[i]!r} in "
                        f"`vera run examples/{m.group('name')}.vera"
                        f"{m.group('rest').rstrip()}`"
                    )
                    ok = False
                    break
            if ok:
                found.append(Invocation(doc, lineno, m.group("name"), fn, args))
    return found, problems


def invocation_owner(inv: Invocation) -> str | None:
    """Which gate already covers an invocation, or None when this one must
    run it: ``check_examples_run.py`` runs one invocation per example and
    skips some examples by property."""
    if inv.name in SKIPS:
        return f"check_examples_run.py skips it ({SKIPS[inv.name]})"
    spec = RUN_SPECS.get(inv.name)
    if spec is not None and (inv.fn or "main") == spec.fn and inv.args == spec.args:
        return "check_examples_run.py runs it"
    return None


def run_invocations(
    root: Path, invocations: list[Invocation], cwd: Path,
    timeout: int = RUN_TIMEOUT_SECONDS,
) -> list[str]:
    """Run every invocation no other gate covers; one failure line each."""
    failures: list[str] = []
    verdicts: dict[tuple[str, str | None, tuple[str, ...]], str | None] = {}
    for inv in invocations:
        where = f"{inv.doc} line {inv.line} [invocation]"
        if not (root / "examples" / f"{inv.name}.vera").is_file():
            failures.append(f"{where}: examples/{inv.name}.vera does not exist")
            continue
        if invocation_owner(inv) is not None:
            continue
        key = (inv.name, inv.fn, inv.args)
        if key not in verdicts:
            result = _run(root, inv.argv(root), cwd, timeout)
            if result is None:
                verdicts[key] = f"exceeded the {timeout}s budget"
            elif result.returncode != 0:
                detail = result.stderr.strip() or result.stdout.strip() or "no output"
                verdicts[key] = f"exited {result.returncode}: {_first_line(detail)}"
            else:
                verdicts[key] = None
        if verdicts[key] is not None:
            failures.append(f"{where}: `{inv.shown()}` {verdicts[key]}")
    return failures


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
            if r.run_coverage is not None:
                failures.append(f"{where} [run]: {r.run_coverage}")
            for run, error in r.run_errors:
                if error is not None:
                    failures.append(f"{where} [run, marker line {run.line}]: {error}")
    return Findings(failures, stale, problems)


def summary_lines(report: DocReport) -> list[str]:
    """One document's counts: blocks that pass each stage, the run
    decisions, and the marked blocks by the stage they fail and their
    category."""
    passed = Counter(
        o.stage for r in report.results for o in r.outcomes if o.status == "ok"
    )
    marked: dict[str, Counter[str]] = {}
    for r in report.results:
        last = r.outcomes[-1]
        if last.status == "skipped" and last.annotation is not None:
            marked.setdefault(last.stage, Counter())[last.annotation.category] += 1
    runs = sum(1 for r in report.results for _run, err in r.run_errors if err is None)
    no_runs = Counter(
        r.block.no_runs[0].category
        for r in report.results
        if r.block.no_runs and len(r.outcomes) == 3
        and all(o.status == "ok" for o in r.outcomes)
    )
    lines = [
        f"{report.doc}: {len(report.results)} Vera block(s) "
        f"of {report.total_blocks} code block(s)"
    ]
    if report.results:
        lines.append(
            f"  pass parse {passed['parse']}, check {passed['check']}, "
            f"verify {passed['verify']}; run invocations passing: {runs}"
        )
    if no_runs:
        cats = ", ".join(f"{c} {n}" for c, n in sorted(no_runs.items()))
        lines.append(f"  marked not to run: {sum(no_runs.values())} ({cats})")
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
    no_run_used = sorted({
        r.block.no_runs[0].category
        for d in reports for r in d.results if r.block.no_runs
    })
    if no_run_used:
        print("\nNot run:")
        for category in no_run_used:
            print(f"  {category}: {NO_RUN_PROPERTIES.get(category, '(not in the vocabulary)')}")
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
            'code="..." reason="..." --> on the line before its fence '
            f"(categories: {', '.join(CATEGORIES)}; see "
            "scripts/doc_annotations.py).  A block that exports a function "
            "names an invocation (vera:run) or says why it cannot run "
            "(vera:no-run).  A failing vera:run marker means the document "
            "states an output the program does not print.",
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
    """Gate *docs* (repo-relative paths under *root*), their blocks and the
    example invocations they name."""
    with tempfile.TemporaryDirectory(prefix="vera-doc-examples-") as scratch:
        workspace = Workspace(root, Path(scratch))
        reports = [gate_document(root, doc, workspace) for doc in docs]
        invocations: list[Invocation] = []
        extra: dict[str, list[str]] = {}
        for doc in docs:
            found, problems = documented_invocations(root / doc, doc)
            invocations += found
            extra.setdefault(doc, []).extend(problems)
        for failure in run_invocations(root, invocations, workspace.cwd):
            extra.setdefault(failure.split(" line ", 1)[0], []).append(failure)
    return [
        r._replace(problems=(*r.problems, *extra.get(r.doc, ())))
        for r in reports
    ]


def compiler_canary(root: Path, location: Path | None = None) -> str | None:
    """An error when the in-process stages would use another checkout's
    compiler — the gate must measure the tree it lives in.  *location* is
    the compiler package to test, by default the one imported."""
    if location is None:
        import vera

        location = Path(vera.__file__).resolve()
    if root.resolve() not in location.resolve().parents:
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
