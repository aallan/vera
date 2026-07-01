"""Unit tests for `scripts/check_explicit_encoding.py` (#645).

The script enforces that every text-mode `open()` / `Path.read_text()` /
`Path.write_text()` under `vera/`, `scripts/`, `tests/` passes an explicit
`encoding=` — the durable fix for the cp1252-on-Windows class of bug (#641).

These tests pin the script's AST logic (so a future regex/AST tweak can't
silently weaken it) AND assert the repository is currently clean (so a new bare
call added anywhere in scope fails here as well as at the pre-commit / CI gate).

The script lives in `scripts/`, not a package, so it is loaded as a module.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT_PATH = ROOT / "scripts" / "check_explicit_encoding.py"


@pytest.fixture(scope="module")
def mod() -> object:
    """Import `check_explicit_encoding.py` as a module."""
    spec = importlib.util.spec_from_file_location(
        "check_explicit_encoding", SCRIPT_PATH)
    assert spec is not None and spec.loader is not None
    m = importlib.util.module_from_spec(spec)
    sys.modules["check_explicit_encoding"] = m
    spec.loader.exec_module(m)
    return m


def _reasons(mod: object, source: str) -> list[str]:
    return [v.reason for v in mod.check_source(source, "<test>.py")]


# ---------------------------------------------------------------------------
# Bare text-mode calls are flagged.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("src", [
    "p.read_text()",
    "p.write_text(data)",
    "open(path)",
    "open(path, 'w')",
    "open(path, mode='w')",
])
def test_bare_text_call_is_flagged(mod: object, src: str) -> None:
    assert len(mod.check_source(src, "<t>.py")) == 1


# ---------------------------------------------------------------------------
# An explicit UTF-8 literal (any common spelling, case-insensitive) satisfies
# the gate.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("src", [
    'p.read_text(encoding="utf-8")',
    'p.write_text(data, encoding="utf-8")',
    'open(path, encoding="utf-8")',
    'open(path, "w", encoding="utf-8")',
    'p.read_text(encoding="UTF-8")',   # case-insensitive
    'p.read_text(encoding="utf8")',    # hyphen-optional spelling
])
def test_utf8_literal_encoding_passes(mod: object, src: str) -> None:
    assert mod.check_source(src, "<t>.py") == []


# ---------------------------------------------------------------------------
# A non-UTF-8 codec or a non-literal encoding is rejected — the repo rule is
# UTF-8, and a deliberate exception must use `# encoding-exempt`, not a bare
# `encoding=` of any value (#645 CR).
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("src", [
    'p.read_text(encoding="latin-1")',   # wrong codec
    'open(path, encoding="ascii")',
    "p.read_text(encoding=enc)",         # non-literal — unverifiable
    "p.write_text(data, encoding=ENC)",
])
def test_non_utf8_or_nonliteral_encoding_is_flagged(mod: object, src: str) -> None:
    assert len(mod.check_source(src, "<t>.py")) == 1


# ---------------------------------------------------------------------------
# Binary I/O is not text — never flagged.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("src", [
    "open(path, 'rb')",
    "open(path, 'wb')",
    "open(path, mode='rb')",
    "open(path, 'r+b')",
    "p.read_bytes()",
    "p.write_bytes(data)",
])
def test_binary_is_not_flagged(mod: object, src: str) -> None:
    assert mod.check_source(src, "<t>.py") == []


def test_non_literal_open_mode_is_flagged(mod: object) -> None:
    # A dynamic mode we can't resolve statically is flagged (conservative):
    # the author must pass encoding= or open in binary explicitly.
    reasons = _reasons(mod, "open(path, mode)")
    assert len(reasons) == 1
    assert "non-literal mode" in reasons[0]


# ---------------------------------------------------------------------------
# `# encoding-exempt` opt-out — reason mandatory.
# ---------------------------------------------------------------------------

def test_optout_with_reason_suppresses(mod: object) -> None:
    src = "p.read_text()  # encoding-exempt: reads a latin-1 legacy fixture"
    assert mod.check_source(src, "<t>.py") == []


def test_optout_without_reason_is_itself_a_violation(mod: object) -> None:
    reasons = _reasons(mod, "p.read_text()  # encoding-exempt")
    assert len(reasons) == 1
    assert "without a reason" in reasons[0]


def test_marker_inside_a_string_does_not_suppress(mod: object) -> None:
    # The marker only counts as a real COMMENT token — a string that merely
    # contains the text must not exempt a sibling bare call.
    src = 'x = "# encoding-exempt: not a real marker"\np.read_text()'
    assert len(mod.check_source(src, "<t>.py")) == 1


# ---------------------------------------------------------------------------
# `.open()` method calls are out of scope (would collide with unrelated
# `.open()` methods, e.g. the LSP document store).
# ---------------------------------------------------------------------------

def test_dot_open_method_is_out_of_scope(mod: object) -> None:
    assert mod.check_source("store.open(uri, text, version)", "<t>.py") == []


# ---------------------------------------------------------------------------
# subprocess text captures (text=True / universal_newlines) decode with the
# locale codec, so they need an explicit encoding="utf-8" too (#645 AC3).
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("src", [
    "subprocess.run(cmd, capture_output=True, text=True)",
    "subprocess.check_output(cmd, text=True)",
    "subprocess.Popen(cmd, stdout=subprocess.PIPE, text=True)",
    "subprocess.run(cmd, capture_output=True, universal_newlines=True)",
    'subprocess.run(cmd, text=True, encoding="latin-1")',  # wrong codec
])
def test_subprocess_text_without_utf8_is_flagged(mod: object, src: str) -> None:
    assert len(mod.check_source(src, "<t>.py")) == 1


@pytest.mark.parametrize("src", [
    'subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")',
    'subprocess.check_output(cmd, text=True, encoding="utf-8")',
    "subprocess.run(cmd, capture_output=True)",   # bytes mode — no locale decode
    "subprocess.check_output(cmd)",               # bytes mode
    "subprocess.run(cmd, check=True)",            # no capture at all
])
def test_subprocess_bytes_or_utf8_is_ok(mod: object, src: str) -> None:
    assert mod.check_source(src, "<t>.py") == []


# ---------------------------------------------------------------------------
# tempfile.NamedTemporaryFile / TemporaryFile / SpooledTemporaryFile default to
# BINARY ("w+b"), but an explicit text mode is a locale-encoded write just like
# open(..., "w") — the idiom test helpers use to stage `.vera` source, and the
# blind spot that reddened the Windows matrix when PYTHONUTF8 was dropped (#645).
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("src", [
    'tempfile.NamedTemporaryFile(mode="w", suffix=".vera", delete=False)',
    'tempfile.NamedTemporaryFile("w")',              # positional text mode
    'tempfile.NamedTemporaryFile(mode="w+", delete=False)',
    'NamedTemporaryFile(mode="a")',                  # bare (from-imported) name
    'tempfile.TemporaryFile(mode="w")',
    'tempfile.SpooledTemporaryFile(mode="wt")',
    'tempfile.NamedTemporaryFile(mode="w", encoding="latin-1")',  # wrong codec
])
def test_tempfile_text_mode_without_utf8_is_flagged(mod: object, src: str) -> None:
    assert len(mod.check_source(src, "<t>.py")) == 1


@pytest.mark.parametrize("src", [
    "tempfile.NamedTemporaryFile()",                 # default "w+b" -> binary
    'tempfile.NamedTemporaryFile(mode="wb")',
    'tempfile.NamedTemporaryFile(mode="w+b", delete=False)',
    'tempfile.NamedTemporaryFile(mode="w", suffix=".vera", encoding="utf-8")',
    'tempfile.TemporaryFile(mode="w", encoding="utf-8")',
])
def test_tempfile_binary_or_utf8_is_ok(mod: object, src: str) -> None:
    assert mod.check_source(src, "<t>.py") == []


# ---------------------------------------------------------------------------
# Scope discovery is pinned independently of the clean-repo assertion below.
# `test_repository_has_no_bare_text_calls` only checks the files
# `iter_scope_files()` returns, so it would stay green if discovery silently
# stopped reaching a root (e.g. `SCOPE_DIRS` lost `tests`, or `rglob` broke) —
# fewer files checked still reads as "clean".  These pin the enumerator itself
# so such a regression fails loudly (#645 CR).
# ---------------------------------------------------------------------------

def test_iter_scope_files_reaches_every_scope_root(mod: object) -> None:
    files = mod.iter_scope_files()
    roots_hit = {p.relative_to(mod.ROOT).parts[0] for p in files}
    assert set(mod.SCOPE_DIRS) <= roots_hit, (
        f"iter_scope_files() must reach every scope root {mod.SCOPE_DIRS}; "
        f"reached {sorted(roots_hit)}")
    # A known real file under each scope root must be discovered — a stronger
    # guard than a count against discovery that returns a whole root as empty.
    found = {p.resolve() for p in files}
    sentinels = [
        mod.ROOT / "vera" / "cli.py",
        mod.ROOT / "scripts" / "check_explicit_encoding.py",
        Path(__file__).resolve(),  # tests/ — this very file
    ]
    missing = [s for s in sentinels if s.resolve() not in found]
    assert not missing, f"iter_scope_files() missed in-scope files: {missing}"


def test_in_scope_accepts_scope_roots_and_rejects_outsiders(mod: object) -> None:
    # Accept a real .py under each scope root (the `main FILE ...` filter path).
    assert mod._in_scope(mod.ROOT / "vera" / "cli.py")
    assert mod._in_scope(mod.ROOT / "scripts" / "check_explicit_encoding.py")
    assert mod._in_scope(Path(__file__))
    # Reject: a non-scope top-level dir, a non-.py file, a path outside ROOT.
    assert not mod._in_scope(mod.ROOT / "docs" / "foo.py")
    assert not mod._in_scope(mod.ROOT / "README.md")
    assert not mod._in_scope(mod.ROOT.parent / "outside_the_repo.py")


# ---------------------------------------------------------------------------
# The repository itself is clean (the production assertion).
# ---------------------------------------------------------------------------

def test_repository_has_no_bare_text_calls(mod: object) -> None:
    violations = mod.check_paths(mod.iter_scope_files())
    assert violations == [], (
        f"{len(violations)} bare text-mode file call(s) lack encoding='utf-8' "
        "(#645):\n" + "\n".join(
            f"  {v.file}:{v.line}: {v.reason}" for v in violations))
