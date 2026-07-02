"""Tests for the site-asset tooling: scripts/build_site.py and scripts/check_site_assets.py."""

from __future__ import annotations

import importlib.util
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
    """SKILL.md carries inline <!-- vera:skip-... --> fence annotations for
    the doc gates; the on-domain copy must not include them."""
    # Precondition: the source actually contains annotations (otherwise this
    # test could pass vacuously with the strip deleted).
    source = (_SCRIPT.parent.parent / "SKILL.md").read_text(encoding="utf-8")
    assert "vera:skip-" in source
    assert "vera:skip" not in _mod.build_skill_md()


def test_llms_full_txt_strips_vera_skip_annotations():
    """llms-full.txt inlines SKILL.md and FAQ.md; annotations must be
    stripped there too."""
    # Precondition: at least one inlined source actually carries annotations
    # (otherwise this test could pass vacuously with the strip deleted).
    skill = (_SCRIPT.parent.parent / "SKILL.md").read_text(encoding="utf-8")
    assert "vera:skip-" in skill
    assert "vera:skip" not in _mod.build_llms_full_txt("0.0.0")


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
