#!/usr/bin/env python
"""Inline fence-annotation support for the documentation code-block gates (#538).

Documentation code blocks that intentionally fail a compiler stage carry an
HTML-comment annotation on the line immediately before the opening fence::

    <!-- vera:skip-parse category="FRAGMENT" reason="bare type expression" -->
    ```vera
    List<Result<User, Error>>
    ```

Each pipeline stage has its own directive — ``vera:skip-parse``,
``vera:skip-check``, ``vera:skip-verify`` — and directives stack (one per
line) when a block is exempt from more than one stage.  ``category`` is one of
the conventional taxonomy labels (FRAGMENT, MISMATCH, FUTURE, INCOMPLETE,
ILLUSTRATIVE, SNIPPET, EXPECTED); ``reason`` is free text.  Neither value may
contain a double quote.

The annotation travels with its fence through document edits, so there are no
line numbers to maintain.  This replaced the line-number-keyed ``ALLOWLIST``
dicts in the check scripts and ``scripts/fix_allowlists.py`` (whose bulk-shift
renumbering heuristic was itself buggy — #606).

Stale detection: the gates still RUN the exempted stage.  An annotated block
that *passes* the stage is a stale annotation and fails the gate — the
annotation must be removed.  This mirrors ``check_e602_clean.py``'s
stale-entry treatment, so the skip surface shrinks as parser/checker features
land.  Malformed, dangling, and duplicate annotations are hard failures too.

Rendering safety: HTML comments are invisible in rendered markdown, and the
language tag stays plain ``vera`` so GitHub syntax highlighting is unaffected
(the rationale for preferring this form over an info-string variant is in
issue #538).  ``build_site.py`` uses :func:`strip_annotations` so annotations
never leak into the generated site assets (docs/SKILL.md, docs/llms-full.txt).
"""

from __future__ import annotations

import html
import re
from collections.abc import Callable, Collection, Sequence
from pathlib import Path
from typing import NamedTuple

STAGES = ("parse", "check", "verify")

# A full, well-formed annotation line.
ANNOTATION_RE = re.compile(
    r'^\s*<!--\s*vera:skip-(parse|check|verify)\s+'
    r'category="([^"]+)"\s+reason="([^"]+)"\s*-->\s*$'
)

# Anything that *looks* like an annotation attempt.  A line matching this but
# not ANNOTATION_RE is reported as malformed rather than silently ignored —
# a typo'd annotation must not quietly un-skip (or fail to skip) a block.
ANNOTATION_HINT_RE = re.compile(r"<!--.*vera:skip")

# Used by build_site.py to keep annotations out of generated site assets.
_ANNOTATION_LINE_RE = re.compile(
    r"^[ \t]*<!--\s*vera:skip-[^\n]*-->[ \t]*\n", re.MULTILINE
)

_FENCE_OPEN_RE = re.compile(r"^```(\w*)$")
_FENCE_CLOSE_RE = re.compile(r"^```$")


class Annotation(NamedTuple):
    """One vera:skip directive: which stage a block is exempt from, and why."""

    line: int  # 1-based line of the annotation comment
    stage: str  # "parse" | "check" | "verify"
    category: str
    reason: str


class CodeBlock(NamedTuple):
    """A code block plus the annotations attached to it."""

    line: int  # 1-based line of the opening fence / <pre> tag
    lang: str  # fence language tag ("" for HTML <pre> blocks)
    content: str
    annotations: tuple[Annotation, ...]


class StageOutcome(NamedTuple):
    """Result of running one pipeline stage on one block."""

    stage: str
    status: str  # "ok" | "failed" | "skipped" | "stale"
    error: str | None  # the stage error for "failed" / "skipped"
    annotation: Annotation | None  # set for "skipped" / "stale"


def _flush_pending(
    pending: list[Annotation], problems: list[str], where: str
) -> None:
    """Report annotations that are not immediately followed by a block."""
    if pending:
        problems.append(
            f"line {pending[0].line}: dangling vera:skip annotation — "
            f"not immediately followed by {where}"
        )
        pending.clear()


def _take_annotation(
    line: str, lineno: int, pending: list[Annotation], problems: list[str]
) -> bool:
    """Consume *line* as an annotation (or a malformed attempt at one).

    Returns True when the line was annotation-shaped and has been handled.
    """
    m = ANNOTATION_RE.match(line)
    if m:
        ann = Annotation(lineno, m.group(1), m.group(2), m.group(3))
        if any(p.stage == ann.stage for p in pending):
            problems.append(
                f"line {lineno}: duplicate vera:skip-{ann.stage} annotation "
                f"for the same block"
            )
        else:
            pending.append(ann)
        return True
    if ANNOTATION_HINT_RE.search(line):
        problems.append(
            f"line {lineno}: malformed vera:skip annotation: {line.strip()!r} "
            f'(expected <!-- vera:skip-<stage> category="..." reason="..." -->)'
        )
        return True
    return False


def scan_markdown(path: Path) -> tuple[list[CodeBlock], list[str]]:
    """Extract fenced code blocks (with annotations) from a Markdown file.

    Returns ``(blocks, problems)``.  ``problems`` lists malformed, dangling,
    and duplicate annotations — the gates treat a non-empty list as failure.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    blocks: list[CodeBlock] = []
    problems: list[str] = []
    pending: list[Annotation] = []
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
            blocks.append(
                CodeBlock(start_line, lang, "\n".join(content_lines), tuple(pending))
            )
            pending.clear()
            i += 1
            continue
        _flush_pending(pending, problems, "a code fence")
        i += 1
    _flush_pending(pending, problems, "a code fence")
    return blocks, problems


def scan_html(path: Path) -> tuple[list[CodeBlock], list[str]]:
    """Extract ``<pre>`` code blocks (with annotations) from an HTML file.

    Strips HTML tags and decodes entities to recover plain text content.
    An annotation applies to the ``<pre>`` block opening on the line
    immediately after it.  Returns ``(blocks, problems)`` like
    :func:`scan_markdown`.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    blocks: list[CodeBlock] = []
    problems: list[str] = []
    pending: list[Annotation] = []
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
                blocks.append(
                    CodeBlock(start_line, "", content.strip(), tuple(pending))
                )
                pending.clear()
            else:
                # The collect loop only exits without a match when </pre>
                # never appeared — malformed HTML must fail loudly even
                # with no annotation pending.
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
    """Run a block through ordered pipeline stages, honoring skip annotations.

    Each runner takes the block content and returns an error message, or
    ``None`` on success.  For each stage in order:

    - annotated ``skip-<stage>``: the runner still runs, and *failure* is the
      expected outcome (``"skipped"``); *success* means the annotation is
      ``"stale"`` and the gate must fail so the annotation gets removed.
      Either way the pipeline stops at an annotated stage.
    - unannotated: success (``"ok"``) continues to the next stage; failure
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


def unsupported_stage_annotations(
    block: CodeBlock, supported: Collection[str]
) -> list[Annotation]:
    """Annotations naming stages this gate does not run (e.g. ``skip-check``
    on a parse-only document) — the gate reports them as problems."""
    return [a for a in block.annotations if a.stage not in supported]


def strip_annotations(text: str) -> str:
    """Remove vera:skip annotation lines (used by build_site.py so the
    annotations never leak into generated site assets)."""
    return _ANNOTATION_LINE_RE.sub("", text)


def run_parse_only_gate(
    doc_path: Path,
    display_name: str,
    *,
    parse_label: str,
    hint_category: str = "FRAGMENT",
) -> int:
    """The shared parse-only doc gate (SKILL.md, FAQ.md, README.md, EXAMPLES.md).

    Extracts the ```vera fences from *doc_path*, parses each one, and reports
    failures, annotation problems, and stale annotations.  The per-document
    check scripts are thin wrappers over this — only the target file, the
    parser's ``file=`` label, and the fix-hint category differ.

    Returns the process exit code (0 = gate passes).
    """
    import sys

    from vera.parser import parse

    def try_parse(content: str) -> str | None:
        try:
            parse(content, file=parse_label)
            return None
        except Exception as exc:
            return str(exc).split("\n")[0][:200]

    if not doc_path.is_file():
        print(f"ERROR: {display_name} not found.", file=sys.stderr)
        return 1

    blocks, problems = scan_markdown(doc_path)

    total_blocks = 0
    vera_blocks = 0
    skipped_lang = 0
    skipped_annotated = 0
    passed = 0
    failures: list[tuple[int, str]] = []
    stale: list[tuple[int, str, str]] = []  # (line, category, reason)

    for block in blocks:
        total_blocks += 1

        # Only test vera-tagged blocks
        if block.lang.lower() != "vera":
            if block.annotations:
                problems.append(
                    f"line {block.line}: vera:skip annotation on a "
                    f"non-vera block (language {block.lang!r}) — remove it"
                )
            skipped_lang += 1
            continue

        vera_blocks += 1

        for ann in unsupported_stage_annotations(block, {"parse"}):
            problems.append(
                f"line {ann.line}: vera:skip-{ann.stage} is not supported "
                f"for {display_name} (parse-only gate)"
            )

        outcome = evaluate_block(block, [("parse", try_parse)])[-1]
        if outcome.status == "ok":
            passed += 1
        elif outcome.status == "skipped":
            skipped_annotated += 1
        elif outcome.status == "stale":
            assert outcome.annotation is not None
            stale.append(
                (block.line, outcome.annotation.category, outcome.annotation.reason)
            )
        else:
            failures.append((block.line, outcome.error or ""))

    # Report
    print(f"{display_name} code blocks: {total_blocks} total")
    print(f"  Skipped (non-Vera language): {skipped_lang}")
    print(f"  Vera blocks: {vera_blocks}")
    print(f"    Parsed OK: {passed}")
    print(f"    Annotated (vera:skip-parse): {skipped_annotated}")
    print(f"    FAILED: {len(failures)}")

    exit_code = 0

    if problems:
        print("\nANNOTATION PROBLEMS:", file=sys.stderr)
        for problem in problems:
            print(f"  {display_name} {problem}", file=sys.stderr)
        exit_code = 1

    if stale:
        print(
            "\nSTALE ANNOTATIONS (block parses fine — remove the annotation):",
            file=sys.stderr,
        )
        for line_no, category, reason in stale:
            print(
                f"  {display_name} line {line_no} [{category}]: {reason}",
                file=sys.stderr,
            )
        exit_code = 1

    if failures:
        print("\nFAILURES:", file=sys.stderr)
        for line_no, error in failures:
            print(f"\n  {display_name} line {line_no}:", file=sys.stderr)
            print(f"    {error}", file=sys.stderr)
        print(
            f"\n{len(failures)} {display_name} code block(s) failed to parse.",
            file=sys.stderr,
        )
        print(
            "If a block is intentionally unparseable, annotate the fence:",
            file=sys.stderr,
        )
        print(
            f'<!-- vera:skip-parse category="{hint_category}" reason="..." -->'
            " on the line before it (see scripts/doc_annotations.py).",
            file=sys.stderr,
        )
        exit_code = 1

    if exit_code == 0:
        print(f"\nAll {display_name} Vera code blocks parse successfully.")

    return exit_code
