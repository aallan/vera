"""Tests for scripts/build_site.py — focuses on _abs_links behaviour."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

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
