"""Tests for the site-asset tooling: scripts/build_site.py and scripts/check_site_assets.py."""

from __future__ import annotations

import importlib.util
import re
from datetime import date
from pathlib import Path


# ---------------------------------------------------------------------------
# Import _abs_links from the script directly (it lives in scripts/, not in
# the vera package, so we use importlib rather than a regular import).
# ---------------------------------------------------------------------------

_SCRIPT = Path(__file__).parent.parent / "scripts" / "build_site.py"


def _load_build_site():
    spec = importlib.util.spec_from_file_location("build_site", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_mod = _load_build_site()
_abs_links = _mod._abs_links
REPO = _mod.REPO  # "https://github.com/aallan/vera"


_CHECK_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_site_assets.py"


def _load_check_site_assets():
    spec = importlib.util.spec_from_file_location("check_site_assets", _CHECK_SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_check = _load_check_site_assets()


# ---------------------------------------------------------------------------
# Helper
# ---------------------------------------------------------------------------

def _expected(path: str) -> str:
    """Return the expected absolute URL for a repo-relative path."""
    return f"{REPO}/blob/main/{path}"


# ---------------------------------------------------------------------------
# Basic rewriting
# ---------------------------------------------------------------------------


def test_relative_link_is_rewritten():
    text = "See [SKILL.md](SKILL.md) for details."
    result = _abs_links(text)
    assert f"[SKILL.md]({_expected('SKILL.md')})" in result


def test_nested_relative_path_is_rewritten():
    text = "See [spec](spec/03-slot-references.md)."
    result = _abs_links(text)
    assert f"[spec]({_expected('spec/03-slot-references.md')})" in result


def test_relative_link_with_anchor_is_rewritten():
    # The path component matches; the anchor (#) portion is part of the URL
    # but our regex only matches the file-path portion.  URLs like
    # "DE_BRUIJN.md#section" contain a '#' which IS in the allowed charset.
    text = "See [DE_BRUIJN.md](DE_BRUIJN.md#section)."
    result = _abs_links(text)
    assert f"[DE_BRUIJN.md]({_expected('DE_BRUIJN.md#section')})" in result


# ---------------------------------------------------------------------------
# Links that must NOT be rewritten
# ---------------------------------------------------------------------------


def test_https_link_is_unchanged():
    url = "https://example.com/page"
    text = f"See [example]({url})."
    assert _abs_links(text) == text


def test_http_link_is_unchanged():
    url = "http://example.com/page"
    text = f"See [example]({url})."
    assert _abs_links(text) == text


def test_fragment_only_link_is_unchanged():
    text = "See [section](#section-heading)."
    assert _abs_links(text) == text


def test_already_absolute_github_link_is_unchanged():
    url = f"{REPO}/blob/main/README.md"
    text = f"See [README]({url})."
    assert _abs_links(text) == text


# ---------------------------------------------------------------------------
# Fenced code blocks — content must be left untouched
# ---------------------------------------------------------------------------


def test_link_inside_backtick_fence_is_not_rewritten():
    text = (
        "Before.\n"
        "```\n"
        "[SKILL.md](SKILL.md)\n"
        "```\n"
        "After.\n"
    )
    result = _abs_links(text)
    # The link inside the fence must be unchanged
    assert "[SKILL.md](SKILL.md)" in result
    # The surrounding prose is not a link so nothing else changes
    assert result == text


def test_link_inside_tilde_fence_is_not_rewritten():
    text = (
        "Before.\n"
        "~~~\n"
        "[FAQ.md](FAQ.md)\n"
        "~~~\n"
        "After.\n"
    )
    result = _abs_links(text)
    assert "[FAQ.md](FAQ.md)" in result
    assert result == text


def test_link_after_fence_is_rewritten():
    text = (
        "```\n"
        "[SKILL.md](SKILL.md)\n"
        "```\n"
        "See [FAQ.md](FAQ.md).\n"
    )
    result = _abs_links(text)
    # Inside fence: unchanged
    assert "[SKILL.md](SKILL.md)" in result
    # Outside fence: rewritten
    assert f"[FAQ.md]({_expected('FAQ.md')})" in result


def test_inline_backticks_inside_fence_do_not_break_fence_detection():
    """The old regex-split approach broke when code inside a fence contained
    inline backticks.  The line-by-line scanner must handle this correctly."""
    text = (
        "```vera\n"
        "let x = `hello` in [README.md](README.md)\n"  # inline backtick inside fence
        "```\n"
        "See [SKILL.md](SKILL.md).\n"
    )
    result = _abs_links(text)
    # Inside fence: completely unchanged
    assert "[README.md](README.md)" in result
    # Outside fence: rewritten
    assert f"[SKILL.md]({_expected('SKILL.md')})" in result


def test_vera_effect_syntax_inside_fence_not_rewritten():
    """Vera handle[State<Int>](@Int = 0) syntax must not be mistaken for a
    Markdown link — both inside and outside fences."""
    text = (
        "```vera\n"
        "handle[State<Int>](@Int = 0) in { IO.print(\"hi\") }\n"
        "```\n"
    )
    result = _abs_links(text)
    assert result == text


def test_multiple_links_on_same_line():
    text = "See [A](a.md) and [B](b.md)."
    result = _abs_links(text)
    assert f"[A]({_expected('a.md')})" in result
    assert f"[B]({_expected('b.md')})" in result


def test_link_with_special_chars_in_url_not_rewritten():
    """URLs with characters outside [A-Za-z0-9_./#-] are left alone because
    they can't be repo-relative paths."""
    text = "See [example](some path with spaces.md)."
    # The space breaks the URL-ish pattern; the link regex won't match
    assert _abs_links(text) == text


def test_empty_string_returns_empty():
    assert _abs_links("") == ""


def test_text_with_no_links_unchanged():
    text = "Just some prose without any links at all."
    assert _abs_links(text) == text


def test_nested_fence_markers_handled():
    """A backtick fence opened with ``` is only closed by ```, not ~~~."""
    text = (
        "```\n"
        "[A](a.md)\n"
        "~~~\n"           # tilde inside backtick fence — still inside fence
        "[B](b.md)\n"
        "~~~\n"           # tilde close — NOT a backtick fence, still inside
        "[C](c.md)\n"
        "```\n"           # actual close
        "[D](d.md)\n"
    )
    result = _abs_links(text)
    # A, B, C all inside fence — unchanged
    assert "[A](a.md)" in result
    assert "[B](b.md)" in result
    assert "[C](c.md)" in result
    # D is outside fence — rewritten
    assert f"[D]({_expected('d.md')})" in result


# ---------------------------------------------------------------------------
# sitemap <lastmod> stability (no per-build date churn)
# ---------------------------------------------------------------------------

def test_without_lastmod_blanks_dates():
    s = "  <lastmod>2026-06-17</lastmod>\n  <lastmod>2020-01-01</lastmod>"
    assert _mod._without_lastmod(s) == "  <lastmod></lastmod>\n  <lastmod></lastmod>"


def test_sitemap_lastmod_preserved_when_structure_unchanged(tmp_path, monkeypatch):
    """A rebuild whose URL set matches the committed sitemap preserves the
    existing <lastmod> dates verbatim — no churn to today's date (which would
    trip the site-assets pre-commit hook on every unrelated source edit)."""
    monkeypatch.setattr(_mod, "DOCS", tmp_path)
    fresh = _mod.build_sitemap_xml()  # no existing file → today's date
    stale = _mod._without_lastmod(fresh).replace(
        "<lastmod></lastmod>", "<lastmod>2020-01-01</lastmod>"
    )
    (tmp_path / "sitemap.xml").write_text(stale, encoding="utf-8")
    rebuilt = _mod.build_sitemap_xml()
    assert rebuilt == stale
    assert "2020-01-01" in rebuilt
    assert date.today().isoformat() not in rebuilt


def test_sitemap_lastmod_refreshes_when_structure_changes(tmp_path, monkeypatch):
    """When the committed sitemap's URL set differs from the code's, the
    rebuild refreshes the dates to today — preservation applies only to an
    otherwise-identical sitemap."""
    monkeypatch.setattr(_mod, "DOCS", tmp_path)
    (tmp_path / "sitemap.xml").write_text(
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
        "  <url>\n"
        "    <loc>https://veralang.dev/gone.md</loc>\n"
        "    <lastmod>2020-01-01</lastmod>\n"
        "    <changefreq>weekly</changefreq>\n"
        "    <priority>0.1</priority>\n"
        "  </url>\n"
        "</urlset>\n",
        encoding="utf-8",
    )
    rebuilt = _mod.build_sitemap_xml()
    assert date.today().isoformat() in rebuilt
    assert "2020-01-01" not in rebuilt
    assert "gone.md" not in rebuilt


# ---------------------------------------------------------------------------
# vera:skip fence annotations (#538) must not leak into generated site assets
# ---------------------------------------------------------------------------


def test_skill_md_asset_strips_vera_skip_annotations():
    """SKILL.md carries inline <!-- vera:skip-... --> and <!-- vera:run ... -->
    fence markers for the doc gate (#538, #1481); the on-domain copy must not
    include either."""
    # Precondition: the source actually contains both kinds (otherwise this
    # test could pass vacuously with the strip deleted).
    source = (_SCRIPT.parent.parent / "SKILL.md").read_text(encoding="utf-8")
    assert "vera:skip-" in source
    assert "<!-- vera:run " in source
    asset = _mod.build_skill_md()
    assert "vera:skip" not in asset
    assert "vera:run" not in asset


def test_llms_full_txt_strips_vera_skip_annotations():
    """llms-full.txt inlines SKILL.md and FAQ.md; annotations must be
    stripped there too."""
    # Precondition: at least one inlined source actually carries annotations
    # (otherwise this test could pass vacuously with the strip deleted).
    skill = (_SCRIPT.parent.parent / "SKILL.md").read_text(encoding="utf-8")
    assert "vera:skip-" in skill
    assert "<!-- vera:run " in skill
    full = _mod.build_llms_full_txt("0.0.0")
    assert "vera:skip" not in full
    assert "vera:run" not in full


# ---------------------------------------------------------------------------
# check_site_assets.sitemap_stale_reason — the CI-gating staleness branch
# ---------------------------------------------------------------------------

_SITEMAP = (
    '<?xml version="1.0" encoding="UTF-8"?>\n'
    '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
    "  <url>\n"
    "    <loc>https://veralang.dev/index.md</loc>\n"
    "    <lastmod>2026-06-17</lastmod>\n"
    "  </url>\n"
    "</urlset>\n"
)


def test_sitemap_stale_reason_missing_file(tmp_path):
    """No committed sitemap on disk → reported as missing."""
    reason = _check.sitemap_stale_reason(tmp_path / "sitemap.xml", _SITEMAP)
    assert reason is not None
    assert "missing" in reason


def test_sitemap_stale_reason_date_only_diff_is_clean(tmp_path):
    """Same URL structure, older <lastmod> dates → not stale (returns None).

    This is the whole point of the structure-only check: a committed sitemap
    whose dates lag the freshly-built one must not trip the CI gate."""
    committed = _SITEMAP.replace("2026-06-17", "2020-01-01")
    (tmp_path / "sitemap.xml").write_text(committed, encoding="utf-8")
    assert _check.sitemap_stale_reason(tmp_path / "sitemap.xml", _SITEMAP) is None


def test_sitemap_stale_reason_structural_diff_is_stale(tmp_path):
    """A changed URL set → reported stale even after dates are blanked."""
    committed = _SITEMAP.replace("/index.md", "/gone.md")
    (tmp_path / "sitemap.xml").write_text(committed, encoding="utf-8")
    reason = _check.sitemap_stale_reason(tmp_path / "sitemap.xml", _SITEMAP)
    assert reason is not None
    assert "stale" in reason


# ---------------------------------------------------------------------------
# check_site_assets.check_fact_coherence — docs/index.html ↔ docs/index.md
#
# The staleness check above compares `build_index_md()` against the committed
# `docs/index.md`, i.e. the generator against itself; it cannot see the HTML.
# These tests drive the coherence gate that can (#1154).  Every case works on
# tmp_path copies — the committed pair is never mutated.
# ---------------------------------------------------------------------------

_DOCS = Path(__file__).parent.parent / "docs"


def _landing_pair(tmp_path):
    """Copy the committed landing-page pair into tmp_path.

    Returns ``(html_path, md_path)``.  Mutating a copy and re-running the
    check is how each drift class below is proved to be caught.
    """
    html = tmp_path / "index.html"
    md = tmp_path / "index.md"
    html.write_text(
        (_DOCS / "index.html").read_text(encoding="utf-8"), encoding="utf-8"
    )
    md.write_text((_DOCS / "index.md").read_text(encoding="utf-8"), encoding="utf-8")
    return html, md


def _edit(path, old, new):
    """Replace a *unique* anchor in ``path``, asserting it occurs exactly once.

    The uniqueness assertion is load-bearing: if the landing page is reworded
    so an anchor no longer matches, the mutation would silently become a
    no-op and the test would pass while proving nothing.
    """
    text = path.read_text(encoding="utf-8")
    assert text.count(old) == 1, f"anchor not unique ({text.count(old)}x): {old!r}"
    path.write_text(text.replace(old, new), encoding="utf-8")


def _sub(path, pattern, replacement, flags=0):
    """Regex-replace one occurrence in ``path``, asserting the edit landed."""
    text = path.read_text(encoding="utf-8")
    mutated, count = re.subn(pattern, replacement, text, count=1, flags=flags)
    assert count == 1, f"pattern matched {count} times: {pattern!r}"
    path.write_text(mutated, encoding="utf-8")


def _joined(errors):
    return "\n".join(errors)


def test_fact_coherence_committed_pair_is_clean():
    """The committed landing page and its Markdown companion agree today.

    Runs against the real files, not copies — this is the assertion the CI
    gate makes, and it must hold on a clean tree.
    """
    assert _check.check_fact_coherence(_DOCS / "index.html", _DOCS / "index.md") == []


def test_fact_coherence_html_percentage_bump_is_caught(tmp_path):
    """A single changed benchmark figure in the HTML names the model."""
    html, md = _landing_pair(tmp_path)
    _sub(
        html,
        r'(Claude Fable 5 <span class="tag">ceiling</span></td>\s*<td[^>]*>)100%',
        r"\g<1>42%",
    )
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a changed Vera figure must fail the gate"
    assert "Claude Fable 5" in joined
    assert "42%" in joined
    assert "100%" in joined
    assert str(html) in joined
    assert str(md) in joined


def test_fact_coherence_md_percentage_bump_is_caught(tmp_path):
    """The mirror case: the Markdown side drifts instead."""
    html, md = _landing_pair(tmp_path)
    _edit(
        md,
        "| Claude Fable 5 | ceiling | **100%** |",
        "| Claude Fable 5 | ceiling | **42%** |",
    )
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a changed Vera figure must fail the gate"
    assert "Claude Fable 5" in joined
    assert "42%" in joined
    assert str(html) in joined
    assert str(md) in joined


def test_fact_coherence_html_verabench_version_bump_is_caught(tmp_path):
    """The exact class that bit in #1153: the benchmark version string."""
    html, md = _landing_pair(tmp_path)
    _sub(html, r"VeraBench v\d+\.\d+\.\d+", "VeraBench v9.9.9")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a bumped VeraBench version must fail the gate"
    assert "VeraBench version" in joined
    assert "9.9.9" in joined
    assert str(html) in joined
    assert str(md) in joined


def test_fact_coherence_md_tested_vera_version_bump_is_caught(tmp_path):
    """The Vera release the sweep ran against is gated too."""
    html, md = _landing_pair(tmp_path)
    _sub(md, r"Vera v\d+\.\d+\.\d+\]", "Vera v9.9.9]")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a bumped tested-Vera version must fail the gate"
    assert "tested Vera version" in joined
    assert "9.9.9" in joined


def test_fact_coherence_version_badge_divergence_is_caught(tmp_path):
    """The headline version badge vs the Markdown "Current version" line.

    ``check_version_sync.py`` pins the HTML badge to pyproject.toml; nothing
    pinned it to ``index.md``, which states the same version in its own shape.
    """
    html, md = _landing_pair(tmp_path)
    _sub(md, r"\*\*Current version:\*\* \[\d+\.\d+\.\d+", "**Current version:** [9.9.9")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a diverged version badge must fail the gate"
    assert "version badge" in joined
    assert str(html) in joined
    assert str(md) in joined


def test_fact_coherence_md_problem_count_bump_is_caught(tmp_path):
    """The benchmark's problem count is a load-bearing fact."""
    html, md = _landing_pair(tmp_path)
    _sub(md, r"A \d+-problem benchmark", "A 61-problem benchmark")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a changed problem count must fail the gate"
    assert "problem count" in joined
    assert "61" in joined


def test_fact_coherence_html_model_count_bump_is_caught(tmp_path):
    """A prose model count that no longer matches its own table, or the pair.

    Bumping "Nine models" to "Ten models" in the HTML must trip both the
    HTML↔MD comparison and the within-file rows-vs-prose cross-check.
    """
    html, md = _landing_pair(tmp_path)
    _edit(html, "Nine models, three providers", "Ten models, three providers")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a changed model count must fail the gate"
    assert "model count" in joined
    assert any("rows" in e for e in errors), (
        f"prose count must be cross-checked against the table rows: {errors}"
    )


def test_fact_coherence_removed_html_table_row_is_caught(tmp_path):
    """Dropping a model from the HTML table names the missing model."""
    html, md = _landing_pair(tmp_path)
    _sub(
        html,
        r'\s*<tr>\s*<td class="lang">Kimi K3 .*?</tr>',
        "",
        flags=re.DOTALL,
    )
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a removed table row must fail the gate"
    assert "Kimi K3" in joined
    assert str(html) in joined
    assert str(md) in joined


def test_fact_coherence_removed_md_table_row_is_caught(tmp_path):
    """The mirror case: the Markdown table loses a row."""
    html, md = _landing_pair(tmp_path)
    _sub(md, r"\n\| Kimi K3 \|[^\n]*", "")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a removed table row must fail the gate"
    assert "Kimi K3" in joined


def test_fact_coherence_renamed_model_is_caught(tmp_path):
    """A model renamed on one side only shows up in both directions."""
    html, md = _landing_pair(tmp_path)
    _edit(md, "| Kimi K3 |", "| Kimi K4 |")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a renamed model must fail the gate"
    assert "Kimi K3" in joined
    assert "Kimi K4" in joined


def test_fact_coherence_tier_change_is_caught(tmp_path):
    """The per-model tier label is stated in both files, so it is gated."""
    html, md = _landing_pair(tmp_path)
    _edit(md, "| Kimi K3 | flagship |", "| Kimi K3 | workhorse |")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a changed tier must fail the gate"
    assert "Kimi K3" in joined
    assert "workhorse" in joined


def test_fact_coherence_dropped_editor_is_caught(tmp_path):
    """Editor support: three names on the page, three in the Markdown."""
    html, md = _landing_pair(tmp_path)
    _edit(
        md,
        "a [Vim package](https://github.com/aallan/vera/tree/main/editors/"
        "vim-veralang) for Vim 8+ and Neovim, and ",
        "",
    )
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "an editor dropped from one side must fail the gate"
    assert "editor support" in joined
    assert "Vim" in joined
    assert str(html) in joined
    assert str(md) in joined


# --- Extraction failure is gate failure ------------------------------------


def test_fact_coherence_missing_html_table_is_extraction_failure(tmp_path):
    """A restructured HTML table must fail loudly, not silently skip."""
    html, md = _landing_pair(tmp_path)
    _sub(html, r'<table class="bench-table">.*?</table>', "", flags=re.DOTALL)
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "an unlocatable benchmark table must fail the gate"
    assert "benchmark table" in joined
    assert str(html) in joined


def test_fact_coherence_missing_md_table_is_extraction_failure(tmp_path):
    """The Markdown table header is the anchor; losing it fails the gate."""
    html, md = _landing_pair(tmp_path)
    _edit(md, "| Model | Tier | Vera | Python | TypeScript |", "")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "an unlocatable benchmark table must fail the gate"
    assert "benchmark table" in joined
    assert str(md) in joined


def test_fact_coherence_missing_md_prose_fact_is_extraction_failure(tmp_path):
    """Deleting the results caveat removes two facts; both must be named."""
    html, md = _landing_pair(tmp_path)
    _sub(md, r"Results from \[VeraBench[^\n]*\n", "")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "an unlocatable fact must fail the gate"
    assert "VeraBench version" in joined
    assert "tested Vera version" in joined
    assert "not found" in joined
    assert str(md) in joined


def test_fact_coherence_missing_editor_claim_is_extraction_failure(tmp_path):
    """No editor names at all in a file is an extraction failure, not a pass."""
    html, md = _landing_pair(tmp_path)
    _sub(md, r"Editor support: [^\n]*\n", "")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "an unlocatable editor claim must fail the gate"
    assert "editor support" in joined
    assert str(md) in joined


def test_fact_coherence_missing_file_is_gate_failure(tmp_path):
    """A missing half of the pair fails loudly rather than passing vacuously."""
    html, md = _landing_pair(tmp_path)
    md.unlink()
    errors = _check.check_fact_coherence(html, md)
    assert errors, "a missing companion file must fail the gate"
    assert str(md) in _joined(errors)


def test_fact_coherence_conflicting_values_within_one_file_is_caught(tmp_path):
    """One file stating a fact twice, differently, is drift in its own right."""
    html, md = _landing_pair(tmp_path)
    _edit(
        md,
        "Full source and data:",
        "Results from [VeraBench v9.9.9](https://github.com/aallan/vera-bench"
        "#results).\n\nFull source and data:",
    )
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "conflicting values inside one file must fail the gate"
    assert "VeraBench version" in joined
    assert "9.9.9" in joined
    assert str(md) in joined
def _last_md_bench_row(md):
    """Locate the final data row of the Markdown benchmark table.

    Anchored on the same header regex the checker uses, so these tests
    mutate the benchmark table specifically — never some other table the
    companion may gain later.
    """
    lines = md.read_text(encoding="utf-8").splitlines()
    start = next(
        i for i, line in enumerate(lines) if _check._MD_BENCH_HEADER.match(line)
    )
    j = start + 1
    while j < len(lines) and lines[j].startswith("|"):
        j += 1
    return lines, j - 1


def test_fact_coherence_duplicate_md_model_row_is_caught(tmp_path):
    """``_index_rows``: one file listing a model twice is its own failure.

    The duplicate is dropped from the comparison, so without this branch a
    doubled row would silently shadow whichever copy came second.
    """
    html, md = _landing_pair(tmp_path)
    lines, last = _last_md_bench_row(md)
    model = _check._text_of_md(lines[last].strip().strip("|").split("|")[0])
    lines.insert(last + 1, lines[last])
    md.write_text("\n".join(lines) + "\n", encoding="utf-8")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a duplicated model row must fail the gate"
    assert "twice" in joined
    assert model in joined
    assert str(md) in joined


def test_fact_coherence_md_row_cell_count_is_caught(tmp_path):
    """``_bench_rows_md``: a row with the wrong cell count fails loudly.

    A malformed row cannot be compared, and skipping it silently would
    un-gate that model's figures — the same rule as a missing fact.
    """
    html, md = _landing_pair(tmp_path)
    lines, last = _last_md_bench_row(md)
    lines[last] = lines[last] + " 0% |"
    md.write_text("\n".join(lines) + "\n", encoding="utf-8")
    errors = _check.check_fact_coherence(html, md)
    joined = _joined(errors)
    assert errors, "a malformed table row must fail the gate"
    assert "cells" in joined
    assert str(md) in joined


# =====================================================================
# The generated implementation-status appendix (build_impl_status)
# =====================================================================


class TestImplementationStatusAppendix:
    """The shipped-versus-specified boundary, collected from the spec.

    The specification already marks every gap with a `Status:` callout;
    what it lacked was one page that carries all of them. The page is
    generated rather than written, so the property under test is not its
    prose but its COMPLETENESS: a callout added to a chapter has to reach
    the appendix without anyone remembering to copy it.
    """

    def _write_chapter(self, tmp_path: Path, name: str, text: str) -> Path:
        spec_dir = tmp_path / "spec"
        spec_dir.mkdir(exist_ok=True)
        path = spec_dir / name
        path.write_text(text, encoding="utf-8")
        return path

    def test_extracts_a_blockquote_callout_with_its_heading(
        self, tmp_path: Path,
    ) -> None:
        """The nearest preceding heading is what locates a callout for a reader."""
        chapter = self._write_chapter(tmp_path, "07-x.md", (
            "# Chapter 7\n\n"
            "## 7.1 Something Implemented\n\n"
            "Prose that is not a callout.\n\n"
            "### 7.1.2 The Gap\n\n"
            "> **Status: Not yet implemented.** The widget is specified here\n"
            "> but the compiler refuses it. Tracked in\n"
            "> [#999](https://github.com/aallan/vera/issues/999).\n\n"
            "More prose.\n"
        ))
        found = _mod._status_callouts(chapter)
        assert len(found) == 1
        heading, line, text = found[0]
        assert heading == "7.1.2 The Gap"
        assert line == 9
        # The blockquote markers are stripped and the lines rejoined…
        assert text.startswith("**Status: Not yet implemented.** The widget")
        # …and the issue link survives, which is the actionable half.
        assert "[#999](https://github.com/aallan/vera/issues/999)" in text
        assert ">" not in text

    def test_extracts_a_bare_paragraph_callout(self, tmp_path: Path) -> None:
        """Chapter 13 spells its callout without a blockquote.

        Matching only the `>` form would drop it silently — the one
        omission an appendix like this cannot afford, since a missing
        entry reads as "no gap here".
        """
        chapter = self._write_chapter(tmp_path, "13-y.md", (
            "## 13.1 Target\n\n"
            "**Status: experimental.**  Covers two host families\n"
            "and rejects the rest.\n\n"
            "Following prose.\n"
        ))
        found = _mod._status_callouts(chapter)
        assert len(found) == 1
        heading, _line, text = found[0]
        assert heading == "13.1 Target"
        assert text == (
            "**Status: experimental.**  Covers two host families "
            "and rejects the rest."
        )
        assert "Following prose" not in text

    def test_a_callout_without_an_issue_link_is_still_captured(
        self, tmp_path: Path,
    ) -> None:
        """Not every callout cites an issue; the scanner must not require one."""
        chapter = self._write_chapter(tmp_path, "05-z.md", (
            "## 5.2 Thing\n\n"
            "> **Status: Implemented.** Fully working.\n"
        ))
        found = _mod._status_callouts(chapter)
        assert len(found) == 1
        assert found[0][2] == "**Status: Implemented.** Fully working."

    def test_a_chapter_with_no_callouts_yields_nothing(
        self, tmp_path: Path,
    ) -> None:
        """The paired negative: prose mentioning status is not a callout."""
        chapter = self._write_chapter(tmp_path, "04-w.md", (
            "## 4.1 Thing\n\nThe status of this feature is good.\n"
        ))
        assert _mod._status_callouts(chapter) == []

    def test_output_carries_the_generated_header(self) -> None:
        """The page names its generator, so nobody edits it by hand."""
        out = _mod.build_impl_status()
        assert out.startswith("<!-- GENERATED FILE")
        assert "scripts/build_site.py (build_impl_status)" in out
        assert "python scripts/build_site.py" in out
        assert "# Implementation Status" in out

    def test_generation_is_idempotent(self) -> None:
        """Running the generator twice changes nothing.

        The appendix is gated by `check_site_assets.py`, which compares the
        file on disk against a fresh call; a generator that varied between
        calls would make that gate fail at random.
        """
        assert _mod.build_impl_status() == _mod.build_impl_status()

    def test_every_status_callout_in_the_spec_reaches_the_page(self) -> None:
        """Count parity against a LIVE scan of spec/, not a fixture.

        This is the property that matters: the appendix claims to be
        complete. Counting the callouts independently — by scanning the
        chapters for the marker directly — and comparing against the
        entries emitted catches a scanner that silently skips a spelling,
        which is how the bare-paragraph form in Chapter 13 would have been
        lost.
        """
        spec_dir = _mod.ROOT / "spec"
        live = 0
        for chapter in sorted(spec_dir.glob("*.md")):
            for raw in chapter.read_text(encoding="utf-8").splitlines():
                stripped = raw.lstrip()
                if stripped.startswith(">"):
                    stripped = stripped[1:].lstrip()
                if stripped.startswith("**Status:"):
                    live += 1
        assert live > 0, "no Status: callouts found — the scan is broken"
        out = _mod.build_impl_status()
        emitted = sum(1 for ln in out.splitlines() if ln.startswith("### "))
        assert emitted == live, (
            f"{live} Status: callouts in spec/ but {emitted} entries in the "
            f"appendix — the scanner is missing a spelling, or a chapter is "
            f"not being visited"
        )
        assert f"— {live} across " in out, (
            "the page's own header count must agree with the entries below it"
        )

    def test_chapters_are_referenced_by_posix_relative_path(self) -> None:
        """Paths in the output are POSIX-form, so Windows generates the same file."""
        out = _mod.build_impl_status()
        headings = [ln for ln in out.splitlines() if ln.startswith("## [")]
        assert headings, "no chapter sections emitted"
        for h in headings:
            assert "\\" not in h, f"backslash in a generated path: {h!r}"
            assert h.startswith("## [spec/"), h
