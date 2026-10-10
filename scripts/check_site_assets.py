#!/usr/bin/env python3
"""Verify that docs/ site assets are up-to-date with source documentation.

Two independent checks, because they fail differently:

* **Staleness** — regenerate every site asset in memory and compare against
  the committed file.  Exits non-zero if any is stale, printing which ones
  need rebuilding.
* **Fact coherence** — compare the load-bearing facts stated in
  ``docs/index.html`` against the ones stated in ``docs/index.md``
  (:func:`check_fact_coherence`).  The staleness check cannot see this
  class of drift: ``docs/index.md`` is emitted by ``build_index_md()``,
  which holds the landing page's substance as a hand-maintained f-string,
  so the staleness comparison puts that generator on *both* sides.  When
  the generator misses an edit to the hand-designed HTML, the committed
  Markdown is stale in exactly the same way and the comparison is
  satisfied (#1154).

Usage:
    python scripts/check_site_assets.py

Fix stale assets by running:
    python scripts/build_site.py

Fix a coherence failure by hand, in ``build_index_md()`` — the Markdown
companion is what agents fetch via ``rel="alternate"`` and ``llms.txt``,
so a fact that has moved on in the HTML has to move on there too.
"""

from __future__ import annotations

import re
import sys
from html import unescape
from pathlib import Path
from typing import NamedTuple

# Add project root to path so we can import the build script
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from build_site import (  # noqa: E402
    DOCS,
    build_impl_status,
    build_index_md,
    build_llms_full_txt,
    build_llms_txt,
    build_robots_txt,
    build_sitemap_xml,
    build_skill_md,
    _without_lastmod,
)


def sitemap_stale_reason(sitemap_path: Path, expected: str) -> str | None:
    """Return why the committed sitemap is out of date, or ``None`` if current.

    Structure-only comparison: ``<lastmod>`` dates are blanked before comparing,
    because ``build_site`` preserves them when the URL set is unchanged (so they
    no longer churn per build) but they can still legitimately differ across
    machines/days — only a change to the URL structure means the file is stale.
    """
    if not sitemap_path.exists():
        return "missing (run: python scripts/build_site.py)"
    committed = _without_lastmod(sitemap_path.read_text(encoding="utf-8"))
    if committed != _without_lastmod(expected):
        return "stale (run: python scripts/build_site.py)"
    return None


# ---------------------------------------------------------------------------
# Landing-page fact coherence: docs/index.html vs docs/index.md
# ---------------------------------------------------------------------------
#
# Every fact below is stated in *both* files.  The two are written in
# deliberately different registers — the HTML is a designed page, the
# Markdown is a plain companion — so only facts are compared, never
# wording: benchmark version strings, counts, the benchmark table, the
# editor names.
#
# A pattern that matches *nothing* is an error in its own right.  Silently
# skipping a fact whose sentence was reworded would reinstate exactly the
# blind spot this check exists to close.


class _Fact(NamedTuple):
    """A single fact, and how to find it in each file.

    ``md_pattern`` defaults to ``html_pattern``: most facts read the same
    in both files, and one that does not says so.
    Each pattern must have exactly one capturing group — the value.
    """

    label: str
    html_pattern: str
    md_pattern: str | None = None


_PROSE_FACTS: tuple[_Fact, ...] = (
    _Fact("VeraBench version", r"VeraBench v(\d+\.\d+\.\d+)"),
    _Fact("tested Vera version", r"\bVera v(\d+\.\d+\.\d+)\b"),
    _Fact("benchmark problem count", r"\b(\d+)-problem benchmark\b"),
    _Fact("benchmark difficulty tiers", r"benchmark across (\d+) difficulty tiers"),
    _Fact("benchmark model count", r"\b(\w+) models, \w+ providers\b"),
    _Fact("benchmark provider count", r"\b\w+ models, (\w+) providers\b"),
    _Fact("models writing perfect Vera", r"\b(\w+) of \w+ frontier models\b"),
)

# Editor names, and every spelling each file uses for them.  Compared as a
# set: the page names the editors it supports, and the Markdown companion
# has to name the same ones.
_EDITORS: tuple[tuple[str, str], ...] = (
    ("VS Code", r"Visual Studio Code|VS Code"),
    ("Vim", r"\bVim\b"),
    ("TextMate", r"TextMate"),
)

_NUMBER_WORDS = {
    "one": "1", "two": "2", "three": "3", "four": "4", "five": "5",
    "six": "6", "seven": "7", "eight": "8", "nine": "9", "ten": "10",
    "eleven": "11", "twelve": "12", "thirteen": "13", "fourteen": "14",
    "fifteen": "15", "sixteen": "16", "seventeen": "17", "eighteen": "18",
    "nineteen": "19", "twenty": "20",
}

_HTML_BENCH_TABLE = re.compile(r'<table class="bench-table">(.*?)</table>', re.DOTALL)
_HTML_BENCH_ROW = re.compile(
    r'<td class="lang">(?P<model>.*?)\s*<span class="tag">(?P<tier>[^<]*)</span>'
    r"\s*</td>"
    r"\s*<td[^>]*>(?P<vera>[^<]*)</td>"
    r"\s*<td[^>]*>(?P<python>[^<]*)</td>"
    r"\s*<td[^>]*>(?P<typescript>[^<]*)</td>",
    re.DOTALL,
)
_MD_BENCH_HEADER = re.compile(
    r"^\|\s*Model\s*\|\s*Tier\s*\|\s*Vera\s*\|\s*Python\s*\|\s*TypeScript\s*\|\s*$"
)
_COLUMNS = ("tier", "Vera", "Python", "TypeScript")


def _normalize(raw: str) -> str:
    """Collapse whitespace and fold a number word onto its digits.

    The two files are allowed to differ in register, so "Nine models" and
    "9 models" are the same fact.  Percentages and version strings pass
    through untouched, and compare as strings.
    """
    value = " ".join(raw.split())
    return _NUMBER_WORDS.get(value.lower(), value)


def _text_of_html(raw: str) -> str:
    """Strip presentational markup from a table cell and normalize it."""
    return _normalize(unescape(re.sub(r"<[^>]+>", "", raw)))


def _text_of_md(raw: str) -> str:
    """Strip Markdown emphasis from a table cell and normalize it.

    ``**100%**`` and ``_97%_`` carry the same win/loss marking the HTML
    puts in a CSS class, so the emphasis is presentation, not fact.
    """
    return _normalize(re.sub(r"^[*_]+|[*_]+$", "", raw.strip()))


def _bench_rows_html(text: str, path: Path) -> tuple[list[tuple[str, ...]], list[str]]:
    """Parse the HTML benchmark table into ``(model, tier, …figures)`` rows."""
    table = _HTML_BENCH_TABLE.search(text)
    if table is None:
        return [], [
            f'benchmark table: no `<table class="bench-table">` found in'
            f" {path} — the table moved or was restructured, so it is no"
            f" longer gated"
        ]
    rows = [
        (
            _text_of_html(m.group("model")),
            _text_of_html(m.group("tier")),
            _text_of_html(m.group("vera")),
            _text_of_html(m.group("python")),
            _text_of_html(m.group("typescript")),
        )
        for m in _HTML_BENCH_ROW.finditer(table.group(1))
    ]
    if not rows:
        return [], [
            f"benchmark table: found in {path} but no rows parsed — the row"
            f" markup changed, so the figures are no longer gated"
        ]
    return rows, []


def _bench_rows_md(text: str, path: Path) -> tuple[list[tuple[str, ...]], list[str]]:
    """Parse the Markdown benchmark table into the same row shape."""
    lines = text.splitlines()
    start = next(
        (i for i, line in enumerate(lines) if _MD_BENCH_HEADER.match(line)), None
    )
    if start is None:
        return [], [
            f"benchmark table: no `| Model | Tier | Vera | Python |"
            f" TypeScript |` table found in {path} — the table moved or was"
            f" restructured, so it is no longer gated"
        ]
    rows: list[tuple[str, ...]] = []
    errors: list[str] = []
    for line in lines[start + 1 :]:
        if not line.startswith("|"):
            break
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if all(c and set(c) <= {"-", ":"} for c in cells):
            continue  # the |---|---| separator row
        if len(cells) != len(_COLUMNS) + 1:
            errors.append(
                f"benchmark table: {path} row {line.strip()!r} has"
                f" {len(cells)} cells, expected {len(_COLUMNS) + 1}"
            )
            continue
        rows.append(tuple(_text_of_md(c) for c in cells))
    if not rows and not errors:
        errors.append(
            f"benchmark table: header found in {path} but no rows follow it"
        )
    return rows, errors


def _index_rows(
    rows: list[tuple[str, ...]], path: Path
) -> tuple[dict[str, tuple[str, ...]], list[str]]:
    """Key rows by model name, reporting any model listed twice."""
    indexed: dict[str, tuple[str, ...]] = {}
    errors: list[str] = []
    for row in rows:
        if row[0] in indexed:
            errors.append(f"benchmark table: {path} lists model {row[0]!r} twice")
            continue
        indexed[row[0]] = row[1:]
    return indexed, errors


def _describe(figures: tuple[str, ...]) -> str:
    return ", ".join(f"{c}={v}" for c, v in zip(_COLUMNS, figures, strict=True))


def _compare_bench_tables(
    html_rows: list[tuple[str, ...]],
    md_rows: list[tuple[str, ...]],
    html_path: Path,
    md_path: Path,
) -> list[str]:
    """Compare the two tables by model-name set and per-model figures."""
    html_by, errors = _index_rows(html_rows, html_path)
    md_by, md_errors = _index_rows(md_rows, md_path)
    errors += md_errors

    only_html = sorted(set(html_by) - set(md_by))
    only_md = sorted(set(md_by) - set(html_by))
    if only_html or only_md:
        errors.append(
            f"benchmark table model set differs — in {html_path} only:"
            f" {only_html or 'none'}; in {md_path} only: {only_md or 'none'}"
        )
    for model in sorted(set(html_by) & set(md_by)):
        if html_by[model] != md_by[model]:
            errors.append(
                f"benchmark table row {model!r} differs: {html_path} says"
                f" ({_describe(html_by[model])}), {md_path} says"
                f" ({_describe(md_by[model])})"
            )
    return errors


def _read(path: Path) -> tuple[str | None, list[str]]:
    if not path.is_file():
        return None, [
            f"{path}: missing — cannot check landing-page fact coherence"
        ]
    return path.read_text(encoding="utf-8"), []


def check_fact_coherence(html_path: Path, md_path: Path) -> list[str]:
    """Compare the facts docs/index.html and docs/index.md both state.

    Returns one message per divergence, each naming the fact, both values
    and both file paths.  A fact that cannot be located in either file is
    reported the same way — an extraction failure is a gate failure, not a
    silent skip, because a reworded sentence would otherwise switch its own
    check off (#1154).
    """
    html, errors = _read(html_path)
    md, md_errors = _read(md_path)
    errors += md_errors
    if html is None or md is None:
        return errors

    # --- prose facts ------------------------------------------------------
    claimed: dict[str, dict[Path, str]] = {}
    for fact in _PROSE_FACTS:
        per_file: dict[Path, str] = {}
        for path, text, pattern in (
            (html_path, html, fact.html_pattern),
            (md_path, md, fact.md_pattern or fact.html_pattern),
        ):
            found = {_normalize(v) for v in re.findall(pattern, text)}
            if not found:
                errors.append(
                    f"{fact.label}: not found in {path} (pattern"
                    f" /{pattern}/) — the sentence moved or was reworded, so"
                    f" it is no longer gated"
                )
            elif len(found) > 1:
                errors.append(
                    f"{fact.label}: {path} states conflicting values"
                    f" {sorted(found)}"
                )
            else:
                per_file[path] = found.pop()
        if len(per_file) == 2 and per_file[html_path] != per_file[md_path]:
            errors.append(
                f"{fact.label} differs: {html_path} says"
                f" {per_file[html_path]!r}, {md_path} says"
                f" {per_file[md_path]!r}"
            )
        claimed[fact.label] = per_file

    # --- benchmark results table -----------------------------------------
    html_rows, row_errors = _bench_rows_html(html, html_path)
    errors += row_errors
    md_rows, row_errors = _bench_rows_md(md, md_path)
    errors += row_errors
    if html_rows and md_rows:
        errors += _compare_bench_tables(html_rows, md_rows, html_path, md_path)

    # Each file's own prose states how many models were benchmarked; the
    # table it sits next to has to have that many rows.  This is the half
    # the cross-file comparison cannot do — both files agreeing on nine
    # models says nothing about either table having nine rows.
    for path, rows in ((html_path, html_rows), (md_path, md_rows)):
        stated = claimed["benchmark model count"].get(path)
        if rows and stated is not None and stated != str(len(rows)):
            errors.append(
                f"benchmark table rows: {path} has {len(rows)} rows but its"
                f" prose states {stated} models"
            )

    # --- editor support ---------------------------------------------------
    editors: dict[Path, set[str]] = {}
    for path, text in ((html_path, html), (md_path, md)):
        editors[path] = {n for n, pattern in _EDITORS if re.search(pattern, text)}
        if not editors[path]:
            errors.append(
                f"editor support: no editor names found in {path} (looked"
                f" for {', '.join(n for n, _ in _EDITORS)}) — the claim moved"
                f" or was reworded, so it is no longer gated"
            )
    if all(editors.values()) and editors[html_path] != editors[md_path]:
        errors.append(
            f"editor support differs — in {html_path} only:"
            f" {sorted(editors[html_path] - editors[md_path]) or 'none'};"
            f" in {md_path} only:"
            f" {sorted(editors[md_path] - editors[html_path]) or 'none'}"
        )

    return errors


def main() -> int:
    expected = {
        "llms.txt": build_llms_txt(),
        "llms-full.txt": build_llms_full_txt(),
        "robots.txt": build_robots_txt(),
        # sitemap.xml contains today's date, so skip exact comparison
        "index.md": build_index_md(),
        "SKILL.md": build_skill_md(),
        "implementation-status.md": build_impl_status(),
    }

    stale: list[str] = []
    for name, content in expected.items():
        path = DOCS / name
        if not path.exists():
            stale.append(f"  {name}: missing (run: python scripts/build_site.py)")
        elif path.read_text(encoding="utf-8") != content:
            stale.append(f"  {name}: stale (run: python scripts/build_site.py)")

    # sitemap.xml: structure-only comparison (dates are allowed to differ).
    reason = sitemap_stale_reason(DOCS / "sitemap.xml", build_sitemap_xml())
    if reason is not None:
        stale.append(f"  sitemap.xml: {reason}")

    # The landing page and its Markdown companion state the same facts in
    # two hand-maintained places; the staleness loop above cannot see them
    # drift apart, because both its sides come from build_index_md().
    incoherent = check_fact_coherence(DOCS / "index.html", DOCS / "index.md")

    if stale or incoherent:
        if stale:
            print(f"ERROR: {len(stale)} site asset(s) out of date:")
            for s in stale:
                print(s)
        if incoherent:
            print(
                f"ERROR: {len(incoherent)} landing-page fact(s) diverge"
                f" between docs/index.html and docs/index.md"
                f" (fix build_index_md() in scripts/build_site.py):"
            )
            for i in incoherent:
                print(f"  {i}")
        return 1

    print("Site assets are up-to-date and landing-page facts are coherent.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
