#!/usr/bin/env python
r"""Inline fence markers for the documentation example gate (#538, #1481).

A documentation code block carries its gate instructions as HTML comments on
the lines immediately before its opening fence (or its ``<pre>`` tag)::

    <!-- vera:skip-parse category="FRAGMENT" reason="bare type expression" -->
    ```vera
    List<Result<User, Error>>
    ```

There are two kinds of marker, read by ``scripts/check_doc_examples.py``:

- **Skip markers** — ``vera:skip-parse``, ``vera:skip-check``,
  ``vera:skip-verify`` — say the block is expected to FAIL that stage, and
  why.  ``category`` is one of :data:`CATEGORIES`, a closed vocabulary, so a
  typo'd category is a problem rather than a new label; ``reason`` is free
  text.  Neither value may contain a double quote.  A block carries at most
  one skip marker per stage, and the gate stops at the first marked stage.
- **Run markers** — ``vera:run`` — name an invocation and the output it must
  print::

      <!-- vera:run fn="sum_with_state" args="5" stdout="15" -->

  ``fn`` is the function ``vera run --fn`` calls, ``args`` (optional) its
  arguments, split the way a POSIX shell splits a command line, and
  ``stdout`` exactly what the run prints (``\n`` for a line break, ``\"``
  for a double quote, ``\\`` for a backslash).  A block may carry several,
  one invocation each, and none together with a skip marker: a block the
  gate stops early never reaches the run.

The markers travel with their fence through document edits, so there are no
line numbers to maintain.  This replaced the line-number-keyed ``ALLOWLIST``
dicts in the check scripts and ``scripts/fix_allowlists.py`` (whose bulk-shift
renumbering heuristic was itself buggy — #606).

Stale detection: the gate still RUNS a skip-marked stage.  A marked block that
*passes* the stage carries a stale marker and fails the gate — the marker must
be removed.  This mirrors ``check_e602_clean.py``'s stale-entry treatment, so
the skip surface shrinks as parser/checker features land.  Malformed,
dangling, and duplicate markers are hard failures too, and so is any
``<!-- vera:...`` comment that is not a marker this module knows, so a
misspelt directive cannot quietly do nothing.

Rendering safety: HTML comments are invisible in rendered markdown, and the
language tag stays plain ``vera`` so GitHub syntax highlighting is unaffected
(the rationale for preferring this form over an info-string variant is in
issue #538).  ``build_site.py`` uses :func:`strip_annotations` so markers
never leak into the generated site assets (docs/SKILL.md, docs/llms-full.txt).

A second, unrelated annotation pair lives here too — ``vera:diagnostic`` /
``vera:diagnostic``'s closing tag ``/vera:diagnostic`` (#1291) — replaying a
```text fence carrying RENDERED COMPILER OUTPUT against a live re-run,
the same "replay, don't trust" shape as the ```vera fence markers above,
for content the example gate never touches (it runs Vera source; this diffs
diagnostic TEXT).  See :func:`scan_diagnostic_examples` and
:func:`replay_diagnostic_examples`.
"""

from __future__ import annotations

import html
import re
import shlex
import sys
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import NamedTuple

# `replay_diagnostic_examples` below, and `scripts/check_doc_examples.py`,
# which imports this module, both import from `vera` — pin that to the
# checkout THIS FILE lives in before either runs, ahead of whichever venv's
# editable-install finder would otherwise answer first (pinned to whatever
# checkout `pip install -e` last ran in, possibly a different worktree
# entirely — plan-file S13).  See TESTING.md's "Running against ANOTHER
# checkout" section for the sibling pytest-rootdir trap this is NOT — a
# different mechanism with a different remedy.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

# The stages a skip marker can name, in pipeline order.  The gate's fourth
# stage, `run`, is driven by `vera:run` markers instead: a block runs only
# when it names an invocation, so there is nothing for a `skip-run` to skip.
STAGES = ("parse", "check", "verify")

# The closed category vocabulary for skip markers.  Each entry says what kind
# of block the marker describes; the gate prints the definitions beside its
# per-category counts, so a reader of a gate run sees what was skipped and
# why without opening this file.
CATEGORIES: dict[str, str] = {
    "FRAGMENT": (
        "not a complete program: an expression, a statement, a clause, a "
        "signature or a template"
    ),
    "INCOMPLETE": (
        "complete declarations that use a function, type or module the "
        "block does not define"
    ),
    "FUTURE": (
        "syntax or a feature the spec describes and the reference compiler "
        "does not implement yet"
    ),
    "ILLUSTRATIVE": (
        "a construct shown in a form the toolchain does not accept as "
        "written: a contract left deliberately loose, or a declaration "
        "shown the way the compiler injects it"
    ),
    "WRONG": (
        "a deliberate mistake the prose labels as one; the marked stage is "
        "where the toolchain rejects it"
    ),
}

# A full, well-formed skip-marker line.
ANNOTATION_RE = re.compile(
    r'^\s*<!--\s*vera:skip-(parse|check|verify)\s+'
    r'category="([^"]+)"\s+reason="([^"]+)"\s*-->\s*$'
)

# A run-marker line; its attribute list is parsed by `parse_run_marker`.
RUN_MARKER_RE = re.compile(r"^\s*<!--\s*vera:run\b(.*?)-->\s*$")
_RUN_ATTR_RE = re.compile(r'\s*([A-Za-z_]+)="((?:[^"\\]|\\.)*)"')
_RUN_ESCAPES = {"n": "\n", "t": "\t", '"': '"', "\\": "\\"}
_RUN_ESCAPE_RE = re.compile(r"\\(.)")
_FN_NAME_RE = re.compile(r"^[a-z_][A-Za-z0-9_]*$")

# Anything that *looks* like a marker attempt: a comment opening on a
# `vera:` directive other than the `vera:diagnostic` pair (which
# `scan_diagnostic_examples` owns), or naming `vera:skip` / `vera:run`
# anywhere inside it.  A line matching this but neither marker regex is
# reported as malformed rather than silently ignored — a typo'd marker must
# not quietly un-skip (or fail to skip) a block, and a misspelt directive
# such as `vera:rn` must not quietly run nothing.
ANNOTATION_HINT_RE = re.compile(
    r"<!--(?:\s*vera:(?!diagnostic\b)|.*\bvera:(?:skip|run))", re.IGNORECASE
)

# Used by build_site.py to keep markers out of generated site assets.
_ANNOTATION_LINE_RE = re.compile(
    r"^[ \t]*<!--\s*vera:(?:skip-|run\b)[^\n]*-->[ \t]*\n", re.MULTILINE
)

_FENCE_OPEN_RE = re.compile(r"^```(\w*)$")
_FENCE_CLOSE_RE = re.compile(r"^```$")

# `vera:diagnostic` — rendered-diagnostic replay (#1291).  A ```text fence
# carrying compiler output (a diagnostic block, a fix text) is otherwise
# validated by nothing: DE_BRUIJN.md §6.2's E130 example went stale the
# moment #1262 extended E130's fix text, and every ```vera-fence gate above
# stayed green throughout (their remit is parsing Vera source, not checking
# rendered TEXT against it).  The annotation pair below travels with the
# fence it documents (no line numbers to maintain, matching `vera:skip-*`)
# and is invisible in rendered markdown, like every other HTML-comment
# annotation here — the fence's rendered appearance is unchanged; only a
# gate can tell the difference.
#
#     <!-- vera:diagnostic file="main.vera" stage="check" error_code="E130" -->
#     ```vera
#     type Meters = Int;
#     ...
#     ```
#     <!-- /vera:diagnostic -->
#     ```text
#     [E130] Error at main.vera, line 9, column 3:
#     ...
#     ```
#
# The program is wrapped in its own ```vera fence — not left bare between
# the two annotation comments — so the documentation example gate
# (`scripts/check_doc_examples.py`, which only collects FENCED blocks) also
# gates it: the fence carries no skip marker (the open annotation already
# sits on the line before it), and the example gate reads the pair as the
# expected failure at `stage`, so the program is held to fail there and
# nowhere earlier.  `scan_diagnostic_examples` strips the fence's opening
# and closing lines before handing the body to the replay, so both gates
# cover the same source with neither seeing the other's markers.
#
# `error_code` is optional: when given, the replay selects the one
# diagnostic with that code (and fails if that is not unique); when
# omitted, the replay requires the program to produce EXACTLY one
# diagnostic in total, so the example stays unambiguous about which
# diagnostic it illustrates either way.  `stage` currently supports only
# `"check"` — the shape #1291 asks to widen later.
_DIAGNOSTIC_OPEN_RE = re.compile(
    r'^\s*<!--\s*vera:diagnostic\s+file="([^"]*)"'
    r'(?:\s+stage="([^"]*)")?'
    r'(?:\s+error_code="([^"]*)")?'
    r'\s*-->\s*$'
)
_DIAGNOSTIC_CLOSE_RE = re.compile(r"^\s*<!--\s*/vera:diagnostic\s*-->\s*$")
_DIAGNOSTIC_HINT_RE = re.compile(r"<!--\s*/?vera:diagnostic")


class DiagnosticExample(NamedTuple):
    """One `vera:diagnostic`-annotated program paired with the ```text
    fence immediately following it that claims to be its rendered
    output."""

    line: int  # 1-based line of the opening annotation comment
    file: str
    stage: str  # defaults to "check" when the attribute is omitted
    error_code: str | None
    program: str  # the inline Vera source between the two comments
    fence_line: int  # 1-based line of the opening ``` of the ```text fence
    fence_content: str


def scan_diagnostic_examples(path: Path) -> tuple[list[DiagnosticExample], list[str]]:
    """Extract `vera:diagnostic`-annotated (program, expected-output) pairs
    from a Markdown file.  Returns ``(examples, problems)`` in the same
    shape :func:`scan_markdown` uses: a dangling open with no close, a
    close with no preceding open, a program not wrapped in its own
    ```vera fence, and a program not immediately followed (blank lines
    aside) by a ```text fence are all reported as problems rather than
    silently skipped.  The returned :class:`DiagnosticExample`'s
    ``program`` field holds the de-fenced source (the ```vera / ```
    marker lines are stripped, not just skipped over) so it can be
    handed to the parser exactly as the example gate hands a fence body.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    examples: list[DiagnosticExample] = []
    problems: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        open_match = _DIAGNOSTIC_OPEN_RE.match(line)
        if open_match:
            start_line = i + 1
            file_attr, stage_attr, code_attr = open_match.groups()
            stage = stage_attr or "check"
            i += 1
            program_lines: list[str] = []
            closed = False
            while i < len(lines):
                if _DIAGNOSTIC_CLOSE_RE.match(lines[i]):
                    closed = True
                    i += 1
                    break
                if _DIAGNOSTIC_OPEN_RE.match(lines[i]):
                    break  # a second open before this one closed
                program_lines.append(lines[i])
                i += 1
            if not closed:
                problems.append(
                    f"line {start_line}: vera:diagnostic annotation has no "
                    f"matching <!-- /vera:diagnostic --> before the next "
                    f"annotation or end of file"
                )
                continue
            program_open = _FENCE_OPEN_RE.match(program_lines[0]) if program_lines else None
            malformed_fence = (
                not program_lines
                or program_open is None
                or program_open.group(1).lower() != "vera"
                or not _FENCE_CLOSE_RE.match(program_lines[-1])
            )
            if malformed_fence:
                problems.append(
                    f"line {start_line}: vera:diagnostic annotation body "
                    f"must be wrapped in its own ```vera fence (so the "
                    f"documentation example gate also covers it), not left bare "
                    f"between the two annotation comments"
                )
                continue
            program_lines = program_lines[1:-1]
            while i < len(lines) and lines[i].strip() == "":
                i += 1
            if i >= len(lines) or not _FENCE_OPEN_RE.match(lines[i]):
                problems.append(
                    f"line {start_line}: vera:diagnostic annotation is not "
                    f"immediately followed by a code fence"
                )
                continue
            fence_lang = _FENCE_OPEN_RE.match(lines[i]).group(1)  # type: ignore[union-attr]
            if fence_lang.lower() != "text":
                problems.append(
                    f"line {start_line}: vera:diagnostic annotation is "
                    f"followed by a ```{fence_lang} fence, not ```text"
                )
                continue
            fence_line = i + 1
            i += 1
            fence_lines: list[str] = []
            while i < len(lines) and not _FENCE_CLOSE_RE.match(lines[i]):
                fence_lines.append(lines[i])
                i += 1
            if i >= len(lines):
                problems.append(
                    f"line {fence_line}: unterminated code fence "
                    f"(no closing ``` before end of file)"
                )
                continue
            i += 1
            examples.append(DiagnosticExample(
                start_line, file_attr, stage, code_attr,
                "\n".join(program_lines), fence_line, "\n".join(fence_lines),
            ))
            continue
        if _DIAGNOSTIC_CLOSE_RE.match(line):
            problems.append(
                f"line {i + 1}: <!-- /vera:diagnostic --> with no "
                f"preceding <!-- vera:diagnostic ... -->"
            )
            i += 1
            continue
        if _DIAGNOSTIC_HINT_RE.search(line):
            problems.append(
                f"line {i + 1}: malformed vera:diagnostic annotation: "
                f"{line.strip()!r} (expected "
                '<!-- vera:diagnostic file="..." [stage="..."] '
                '[error_code="..."] -->)'
            )
        i += 1
    return examples, problems


def replay_diagnostic_examples(
    examples: list[DiagnosticExample],
) -> list[str]:
    """Re-run each example's program and diff its rendered diagnostic
    against the ```text fence that claims to be its output.  Returns a
    list of human-readable problem strings (empty = every example's
    fence is live-accurate)."""
    from vera.checker import typecheck
    from vera.parser import parse_to_ast

    errors: list[str] = []
    for ex in examples:
        if ex.stage != "check":
            errors.append(
                f"line {ex.line}: vera:diagnostic stage={ex.stage!r} is not "
                f"replayed yet (only \"check\" is currently supported)"
            )
            continue
        try:
            program = parse_to_ast(ex.program)
            diags = typecheck(program, source=ex.program, file=ex.file)
        except Exception as exc:  # noqa: BLE001 — a bad replay is reported, not raised
            errors.append(
                f"line {ex.line}: replaying the annotated program raised "
                f"{type(exc).__name__}: {exc}"
            )
            continue
        if ex.error_code:
            matches = [d for d in diags if d.error_code == ex.error_code]
            if len(matches) != 1:
                errors.append(
                    f"line {ex.line}: expected exactly one diagnostic with "
                    f"error_code {ex.error_code!r}, found {len(matches)} "
                    f"(of {len(diags)} total)"
                )
                continue
        else:
            if len(diags) != 1:
                errors.append(
                    f"line {ex.line}: expected exactly one diagnostic "
                    f"(no error_code attribute to disambiguate), found "
                    f"{len(diags)}"
                )
                continue
            matches = diags
        live = matches[0].format()
        if live != ex.fence_content:
            errors.append(
                f"line {ex.fence_line}: ```text fence does not match live "
                f"output.\n--- fence ---\n{ex.fence_content}\n--- live ---\n"
                f"{live}"
            )
    return errors


class Annotation(NamedTuple):
    """One vera:skip marker: which stage a block is expected to fail, and why."""

    line: int  # 1-based line of the marker comment
    stage: str  # "parse" | "check" | "verify"
    category: str
    reason: str


class RunMarker(NamedTuple):
    """One vera:run marker: an invocation and the output it must print."""

    line: int  # 1-based line of the marker comment
    fn: str  # the function `vera run --fn` calls
    args: tuple[str, ...]  # its arguments, after `--`
    stdout: str  # the exact output, escapes decoded


class CodeBlock(NamedTuple):
    """A code block plus the markers attached to it."""

    line: int  # 1-based line of the opening fence / <pre> tag
    lang: str  # fence language tag ("" for HTML <pre> blocks)
    content: str
    annotations: tuple[Annotation, ...]
    runs: tuple[RunMarker, ...] = ()


class StageOutcome(NamedTuple):
    """Result of running one pipeline stage on one block."""

    stage: str
    status: str  # "ok" | "failed" | "skipped" | "stale"
    error: str | None  # the stage error for "failed" / "skipped"
    annotation: Annotation | None  # set for "skipped" / "stale"


class _Pending:
    """The markers read since the last block, waiting for the next fence."""

    def __init__(self) -> None:
        self.skips: list[Annotation] = []
        self.runs: list[RunMarker] = []
        self.first_line: int | None = None

    def __bool__(self) -> bool:
        return bool(self.skips or self.runs)

    def note(self, lineno: int) -> None:
        if self.first_line is None:
            self.first_line = lineno

    def take(self) -> tuple[tuple[Annotation, ...], tuple[RunMarker, ...]]:
        taken = (tuple(self.skips), tuple(self.runs))
        self.clear()
        return taken

    def clear(self) -> None:
        self.skips.clear()
        self.runs.clear()
        self.first_line = None


def _flush_pending(pending: _Pending, problems: list[str], where: str) -> None:
    """Report markers that are not immediately followed by a block."""
    if pending:
        problems.append(
            f"line {pending.first_line}: dangling vera marker — "
            f"not immediately followed by {where}"
        )
        pending.clear()


def _decode_run_value(raw: str) -> str | None:
    """Decode a run-marker attribute's backslash escapes, or None when it
    holds one this grammar does not define."""
    unknown = False

    def one(m: re.Match[str]) -> str:
        nonlocal unknown
        if m.group(1) not in _RUN_ESCAPES:
            unknown = True
            return ""
        return _RUN_ESCAPES[m.group(1)]

    decoded = _RUN_ESCAPE_RE.sub(one, raw)
    return None if unknown else decoded


def parse_run_marker(line: str, lineno: int) -> RunMarker | str | None:
    """Read *line* as a ``vera:run`` marker.

    Returns the :class:`RunMarker`, a problem string when the line is a run
    marker that does not follow the grammar, or ``None`` when the line is
    not a run marker at all.  Every attribute is ``name="value"``; ``fn`` and
    ``stdout`` are required and ``args`` is optional, and any other name, a
    repeated name, an unknown escape or text outside the attributes is a
    problem rather than something to ignore.
    """
    m = RUN_MARKER_RE.match(line)
    if m is None:
        return None
    expected = (
        '(expected <!-- vera:run fn="..." [args="..."] stdout="..." -->)'
    )
    body = m.group(1)
    attrs: dict[str, str] = {}
    pos = 0
    while True:
        am = _RUN_ATTR_RE.match(body, pos)
        if am is None:
            break
        name, raw = am.group(1), am.group(2)
        if name not in ("fn", "args", "stdout"):
            return f"line {lineno}: vera:run has an unknown attribute {name!r} {expected}"
        if name in attrs:
            return f"line {lineno}: vera:run repeats the attribute {name!r}"
        value = _decode_run_value(raw)
        if value is None:
            return (
                f"line {lineno}: vera:run attribute {name!r} holds an escape "
                f"other than \\n, \\t, \\\" or \\\\"
            )
        attrs[name] = value
        pos = am.end()
    if body[pos:].strip():
        return f"line {lineno}: malformed vera:run marker: {line.strip()!r} {expected}"
    missing = [a for a in ("fn", "stdout") if a not in attrs]
    if missing:
        return (
            f"line {lineno}: vera:run is missing "
            f"{' and '.join(repr(a) for a in missing)} {expected}"
        )
    if not _FN_NAME_RE.match(attrs["fn"]):
        return (
            f"line {lineno}: vera:run fn={attrs['fn']!r} is not a function "
            f"name"
        )
    try:
        args = tuple(shlex.split(attrs.get("args", ""), posix=True))
    except ValueError as exc:
        return f"line {lineno}: vera:run args do not split: {exc}"
    return RunMarker(lineno, attrs["fn"], args, attrs["stdout"])


def _take_annotation(
    line: str, lineno: int, pending: _Pending, problems: list[str]
) -> bool:
    """Consume *line* as a marker (or a malformed attempt at one).

    Returns True when the line was marker-shaped and has been handled.
    """
    m = ANNOTATION_RE.match(line)
    if m:
        ann = Annotation(lineno, m.group(1), m.group(2), m.group(3))
        pending.note(lineno)
        if ann.category not in CATEGORIES:
            problems.append(
                f"line {lineno}: vera:skip-{ann.stage} has the unknown "
                f"category {ann.category!r} (one of "
                f"{', '.join(CATEGORIES)})"
            )
        if any(p.stage == ann.stage for p in pending.skips):
            problems.append(
                f"line {lineno}: duplicate vera:skip-{ann.stage} annotation "
                f"for the same block"
            )
        else:
            pending.skips.append(ann)
        return True
    run = parse_run_marker(line, lineno)
    if run is not None:
        pending.note(lineno)
        if isinstance(run, str):
            problems.append(run)
        else:
            pending.runs.append(run)
        return True
    if ANNOTATION_HINT_RE.search(line):
        problems.append(
            f"line {lineno}: malformed vera marker: {line.strip()!r} "
            f'(expected <!-- vera:skip-<stage> category="..." reason="..." -->'
            f' or <!-- vera:run fn="..." [args="..."] stdout="..." -->)'
        )
        return True
    return False


def scan_markdown(path: Path) -> tuple[list[CodeBlock], list[str]]:
    """Extract fenced code blocks (with markers) from a Markdown file.

    Returns ``(blocks, problems)``.  ``problems`` lists malformed, dangling,
    and duplicate markers — the gate treats a non-empty list as failure.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    blocks: list[CodeBlock] = []
    problems: list[str] = []
    pending = _Pending()
    i = 0
    while i < len(lines):
        line = lines[i]
        if _take_annotation(line, i + 1, pending, problems):
            i += 1
            continue
        m = _FENCE_OPEN_RE.match(line)
        if m:
            lang = m.group(1)
            start_line = i + 1  # 1-based
            content_lines: list[str] = []
            i += 1
            while i < len(lines) and not _FENCE_CLOSE_RE.match(lines[i]):
                content_lines.append(lines[i])
                i += 1
            if i >= len(lines):
                # The fence ran to EOF — malformed markdown must fail
                # loudly, not be tested (or skip-annotated) as if
                # well-formed.
                problems.append(
                    f"line {start_line}: unterminated code fence "
                    f"(no closing ``` before end of file)"
                )
                pending.clear()
                break
            skips, runs = pending.take()
            blocks.append(
                CodeBlock(start_line, lang, "\n".join(content_lines), skips, runs)
            )
            i += 1
            continue
        _flush_pending(pending, problems, "a code fence")
        i += 1
    _flush_pending(pending, problems, "a code fence")
    return blocks, problems


def scan_html(path: Path) -> tuple[list[CodeBlock], list[str]]:
    """Extract ``<pre>`` code blocks (with markers) from an HTML file.

    Strips HTML tags and decodes entities to recover plain text content.
    A marker applies to the ``<pre>`` block opening on the line
    immediately after it.  Returns ``(blocks, problems)`` like
    :func:`scan_markdown`.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    blocks: list[CodeBlock] = []
    problems: list[str] = []
    pending = _Pending()
    i = 0
    while i < len(lines):
        line = lines[i]
        if _take_annotation(line, i + 1, pending, problems):
            i += 1
            continue
        if "<pre>" in line or "<pre " in line:
            start_line = i + 1  # 1-based
            pre_lines: list[str] = []
            while i < len(lines):
                pre_lines.append(lines[i])
                if "</pre>" in lines[i]:
                    break
                i += 1
            raw_html = "\n".join(pre_lines)
            m = re.search(r"<pre[^>]*>(.*?)</pre>", raw_html, re.DOTALL)
            if m:
                content = m.group(1)
                content = re.sub(r"<[^>]+>", "", content)
                content = html.unescape(content)
                skips, runs = pending.take()
                blocks.append(
                    CodeBlock(start_line, "", content.strip(), skips, runs)
                )
            else:
                # The collect loop only exits without a match when </pre>
                # never appeared — malformed HTML must fail loudly even
                # with no marker pending.
                problems.append(
                    f"line {start_line}: unterminated <pre> block "
                    f"(no closing </pre> before end of file)"
                )
                pending.clear()
            i += 1
            continue
        _flush_pending(pending, problems, "a <pre> block")
        i += 1
    _flush_pending(pending, problems, "a <pre> block")
    return blocks, problems


def evaluate_block(
    block: CodeBlock,
    stage_runners: Sequence[tuple[str, Callable[[str], str | None]]],
) -> list[StageOutcome]:
    """Run a block through ordered pipeline stages, honoring skip markers.

    Each runner takes the block content and returns an error message, or
    ``None`` on success.  For each stage in order:

    - marked ``skip-<stage>``: the runner still runs, and *failure* is the
      expected outcome (``"skipped"``); *success* means the marker is
      ``"stale"`` and the gate must fail so the marker gets removed.
      Either way the pipeline stops at a marked stage.
    - unmarked: success (``"ok"``) continues to the next stage; failure
      (``"failed"``) stops the pipeline.
    """
    by_stage = {a.stage: a for a in block.annotations}
    outcomes: list[StageOutcome] = []
    for stage, runner in stage_runners:
        annotation = by_stage.get(stage)
        error = runner(block.content)
        if annotation is not None:
            status = "stale" if error is None else "skipped"
            outcomes.append(StageOutcome(stage, status, error, annotation))
            break
        if error is not None:
            outcomes.append(StageOutcome(stage, "failed", error, None))
            break
        outcomes.append(StageOutcome(stage, "ok", None, None))
    return outcomes


def strip_annotations(text: str) -> str:
    """Remove vera:skip and vera:run marker lines (used by build_site.py so
    the markers never leak into generated site assets)."""
    return _ANNOTATION_LINE_RE.sub("", text)
