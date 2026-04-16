"""Tests for scripts/check_changelog_updated.py.

Covers:
- ``is_substantive`` classification of file paths (pure function)
- ``_changelog_has_new_entry`` diff parsing (direct tests with stubbed
  subprocess calls)
- ``_has_skip_trailer`` commit-message parsing (direct tests with
  stubbed subprocess calls)
- End-to-end behaviour against a temporary git repository that
  actually exercises the script's subprocess-driven git commands.
"""

from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import textwrap
from pathlib import Path
from typing import Any

import pytest

# ---------------------------------------------------------------------------
# Load the script as a module (it's in scripts/, not a package).
# ---------------------------------------------------------------------------

_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_changelog_updated.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location(
        "check_changelog_updated", _SCRIPT,
    )
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_mod = _load()


# ---------------------------------------------------------------------------
# is_substantive — pure classification logic
# ---------------------------------------------------------------------------


class TestIsSubstantive:
    """Classification of file paths."""

    @pytest.mark.parametrize("path", [
        "vera/cli.py",
        "vera/wasm/calls.py",
        "vera/codegen/api.py",
        "spec/06-contracts.md",
        "SKILL.md",
    ])
    def test_substantive_paths(self, path: str) -> None:
        """Files under vera/, spec/, or SKILL.md are substantive."""
        assert _mod.is_substantive(path) is True

    @pytest.mark.parametrize("path", [
        # Test files
        "tests/test_codegen.py",
        "tests/conformance/ch03_slot_indexing.vera",
        # Scripts and CI
        "scripts/check_examples.py",
        ".github/workflows/ci.yml",
        # Docs
        "docs/index.html",
        "docs/llms.txt",
        # Examples
        "examples/hello_world.vera",
        # Root-level docs
        "CHANGELOG.md",
        "HISTORY.md",
        "README.md",
        "ROADMAP.md",
        "KNOWN_ISSUES.md",
        "FAQ.md",
        "CONTRIBUTING.md",
        "TESTING.md",
        "AGENTS.md",
        "CLAUDE.md",
        "DE_BRUIJN.md",
        "EXAMPLES.md",
        "LICENSE",
        # Build + config
        "pyproject.toml",
        "uv.lock",
        ".pre-commit-config.yaml",
        ".coderabbit.yaml",
        ".gitignore",
        # Editors + assets
        "editors/vscode/package.json",
        "assets/vera-social-preview.jpg",
    ])
    def test_exempt_paths(self, path: str) -> None:
        """Known exempt paths are not substantive."""
        assert _mod.is_substantive(path) is False

    @pytest.mark.parametrize("path", [
        "",
        "   ",
    ])
    def test_empty_paths(self, path: str) -> None:
        """Empty / whitespace paths are not substantive (can't be classified)."""
        assert _mod.is_substantive(path) is False

    def test_unknown_toplevel_is_substantive(self) -> None:
        """Conservative default: unknown top-level dirs trigger the check."""
        # A hypothetical future directory that we forgot to classify
        # should be treated as substantive, not silently skipped.
        assert _mod.is_substantive("stdlib/something.py") is True
        assert _mod.is_substantive("runtime/init.c") is True

    def test_path_prefix_matching_is_boundary_aware(self) -> None:
        """A file starting with the same letters as an exempt prefix is
        not automatically exempt (prefix must include the boundary)."""
        # "testsuite/" is not "tests/", so it should be substantive
        assert _mod.is_substantive("testsuite/foo.py") is True
        # "testing.md" is not "tests/" either
        assert _mod.is_substantive("testing.md") is True

    @pytest.mark.parametrize("path", [
        "README.md.bak",
        "README.md.orig",
        "CHANGELOG.md.old",
        "pyproject.toml.backup",
        ".gitignore.sample",
    ])
    def test_file_style_exemptions_require_exact_match(
        self, path: str,
    ) -> None:
        """File-style exempt entries (no trailing slash) must match
        exactly — a file whose name *starts with* an exempt filename
        is still substantive.

        Regression test: prior to the fix, ``path.startswith("README.md")``
        returned True for ``"README.md.bak"``, silently exempting a
        file that isn't actually README.md.
        """
        assert _mod.is_substantive(path) is True

    def test_directory_style_exemptions_match_prefix(self) -> None:
        """Directory-style entries (trailing slash) still match via prefix."""
        # tests/ matches anything under the tests/ directory
        assert _mod.is_substantive("tests/deeply/nested/test_foo.py") is False
        assert _mod.is_substantive("tests/conformance/manifest.json") is False


# ---------------------------------------------------------------------------
# _changelog_has_new_entry — diff parsing
# ---------------------------------------------------------------------------


class TestChangelogHasNewEntry:
    """Diff-parsing logic for CHANGELOG.md."""

    def test_detects_new_bullet(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """An added bullet line counts as a new entry."""
        diff = textwrap.dedent("""\
            diff --git a/CHANGELOG.md b/CHANGELOG.md
            @@ -7,6 +7,7 @@
             ## [Unreleased]
            +
            +- **New feature** — added the thing ([#999](https://...)).

             ## [0.0.111] - 2026-04-10
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: diff)
        assert _mod._changelog_has_new_entry("origin/main") is True

    def test_detects_new_version_heading(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """An added ``## [X.Y.Z]`` heading counts as a new entry."""
        diff = textwrap.dedent("""\
            diff --git a/CHANGELOG.md b/CHANGELOG.md
            @@ -7,6 +7,8 @@
             ## [Unreleased]

            +## [0.0.200] - 2026-05-01
            +
             ## [0.0.111] - 2026-04-10
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: diff)
        assert _mod._changelog_has_new_entry("origin/main") is True

    def test_bare_unreleased_heading_alone_does_not_count(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """An added ``+## [Unreleased]`` alone is structural scaffolding,
        not a new entry — require a bullet under it to count.

        Regression test: prior to the fix, the heading branch short-
        circuited on *any* added ``## [`` heading including
        ``[Unreleased]``, so reorganising a CHANGELOG to add the
        Unreleased section without any entries would have satisfied
        the check for any substantive change on the branch.
        """
        diff = textwrap.dedent("""\
            diff --git a/CHANGELOG.md b/CHANGELOG.md
            @@ -5,6 +5,8 @@
             The format is based on [Keep a Changelog]...

            +## [Unreleased]
            +
             ## [0.0.111] - 2026-04-10
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: diff)
        assert _mod._changelog_has_new_entry("origin/main") is False

    def test_added_unreleased_heading_with_bullet_counts(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``+## [Unreleased]`` plus a ``+- `` bullet underneath counts.

        The bullet-under-section branch must pick up the added bullet
        once the section tracker has recorded ``Unreleased``.
        """
        diff = textwrap.dedent("""\
            diff --git a/CHANGELOG.md b/CHANGELOG.md
            @@ -5,6 +5,10 @@
             The format is based on [Keep a Changelog]...

            +## [Unreleased]
            +### Added
            +- **Something new** — actually shipped.
            +
             ## [0.0.111] - 2026-04-10
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: diff)
        assert _mod._changelog_has_new_entry("origin/main") is True

    def test_ignores_file_header_lines(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``+++`` (file header) must not be confused with ``+`` (added line)."""
        diff = textwrap.dedent("""\
            diff --git a/CHANGELOG.md b/CHANGELOG.md
            --- a/CHANGELOG.md
            +++ b/CHANGELOG.md
            @@ -7,6 +7,6 @@
             ## [Unreleased]

             ## [0.0.111] - 2026-04-10
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: diff)
        # Only the +++ line was "added" — no real entry.
        assert _mod._changelog_has_new_entry("origin/main") is False

    def test_ignores_cosmetic_changes(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Whitespace-only or prose-only changes do not count as entries."""
        diff = textwrap.dedent("""\
            diff --git a/CHANGELOG.md b/CHANGELOG.md
            @@ -1,5 +1,5 @@
             # Changelog

            -All notable changes to this project will be documented in this file.
            +All notable changes to this project are documented in this file.

             The format is based on...
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: diff)
        assert _mod._changelog_has_new_entry("origin/main") is False

    def test_bullet_outside_unreleased_does_not_count(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Added bullets inside a *released* version entry are not new entries.

        A prose fix that inserts a bullet into an existing version's
        description isn't "adding a new entry" — only bullets under the
        [Unreleased] section (or a new ``## [X.Y.Z]`` heading) count.

        Regression test: prior to the fix, any added ``+- `` line
        counted, so editing v0.0.111's description would have satisfied
        the check for any substantive change on the branch.
        """
        diff = textwrap.dedent("""\
            diff --git a/CHANGELOG.md b/CHANGELOG.md
            @@ -5,7 +5,10 @@
             ## [Unreleased]

             ## [0.0.111] - 2026-04-10

             ### Fixed
            +
            +- Additional clarification bullet on an existing fix.
             - **SMT translator: String/Float64 parameters**...
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: diff)
        assert _mod._changelog_has_new_entry("origin/main") is False

    def test_bullet_under_unreleased_counts(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Added bullet inside [Unreleased] section counts as a new entry."""
        diff = textwrap.dedent("""\
            diff --git a/CHANGELOG.md b/CHANGELOG.md
            @@ -5,6 +5,9 @@
             ## [Unreleased]

            +### Added
            +- **New feature** — shipped the thing.
            +
             ## [0.0.111] - 2026-04-10
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: diff)
        assert _mod._changelog_has_new_entry("origin/main") is True

    def test_unreleased_section_tracking_survives_context(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Section tracker must use context lines, not only added lines.

        If the ``## [Unreleased]`` heading is a context line (pre-existing)
        and a ``+- `` is added immediately under it, the tracker should
        have recorded ``Unreleased`` from the context line.
        """
        diff = textwrap.dedent("""\
            diff --git a/CHANGELOG.md b/CHANGELOG.md
            @@ -6,6 +6,8 @@
             ## [Unreleased]

            +### Fixed
            +- Fixed a thing that was broken.

             ## [0.0.111] - 2026-04-10
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: diff)
        assert _mod._changelog_has_new_entry("origin/main") is True

    def test_no_diff_means_no_entry(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Empty diff (file untouched) returns False."""
        monkeypatch.setattr(_mod, "_run", lambda cmd: "")
        assert _mod._changelog_has_new_entry("origin/main") is False

    def test_git_failure_returns_false(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """If git fails (``_run`` returns None) we treat CHANGELOG as unchanged."""
        monkeypatch.setattr(_mod, "_run", lambda cmd: None)
        assert _mod._changelog_has_new_entry("origin/main") is False


# ---------------------------------------------------------------------------
# _has_skip_trailer — commit-message parsing
# ---------------------------------------------------------------------------


class TestHasSkipTrailer:
    """Detection of the ``Skip-changelog:`` trailer in commit messages."""

    def test_detects_trailer(self, monkeypatch: pytest.MonkeyPatch) -> None:
        log = textwrap.dedent("""\
            Fix some internal typo

            Skip-changelog: cosmetic comment update only

            Co-Authored-By: Claude <noreply@anthropic.invalid>
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: log)
        assert _mod._has_skip_trailer("origin/main") is True

    def test_absent_trailer(self, monkeypatch: pytest.MonkeyPatch) -> None:
        log = textwrap.dedent("""\
            Add feature X

            This does a thing.

            Co-Authored-By: Claude <noreply@anthropic.invalid>
            """)
        monkeypatch.setattr(_mod, "_run", lambda cmd: log)
        assert _mod._has_skip_trailer("origin/main") is False

    def test_must_be_line_start(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Mention of 'Skip-changelog:' in prose does not count."""
        log = (
            "Some commit\n"
            "\n"
            "I considered using Skip-changelog: but decided not to.\n"
        )
        monkeypatch.setattr(_mod, "_run", lambda cmd: log)
        assert _mod._has_skip_trailer("origin/main") is False

    def test_empty_log(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(_mod, "_run", lambda cmd: "")
        assert _mod._has_skip_trailer("origin/main") is False


# ---------------------------------------------------------------------------
# End-to-end: run the script against a real temporary git repo.
# ---------------------------------------------------------------------------


def _git(cwd: Path, *args: str) -> None:
    """Run ``git <args>`` in ``cwd``; raise if it fails."""
    subprocess.run(
        ["git", *args],
        cwd=cwd,
        check=True,
        capture_output=True,
    )


def _setup_repo(tmp_path: Path) -> Path:
    """Create a tiny git repo with one commit on ``main`` mirroring the
    project layout (so file classification works).

    The repo has:

    - ``CHANGELOG.md``  — minimal valid structure with ``[Unreleased]``
    - ``vera/cli.py``    — a substantive file
    - ``tests/t.py``     — an exempt file
    """
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-b", "main")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "Test User")
    _git(repo, "config", "commit.gpgsign", "false")

    (repo / "CHANGELOG.md").write_text(
        "# Changelog\n\n## [Unreleased]\n\n## [0.0.1] - 2026-01-01\n",
    )
    (repo / "vera").mkdir()
    (repo / "vera" / "cli.py").write_text("# placeholder\n")
    (repo / "tests").mkdir()
    (repo / "tests" / "t.py").write_text("# placeholder\n")

    _git(repo, "add", ".")
    _git(repo, "commit", "-m", "Initial")
    return repo


def _run_script(repo: Path, **env_overrides: str) -> subprocess.CompletedProcess[str]:
    """Run the check script inside ``repo``, diffing against local ``main``."""
    env = os.environ.copy()
    # Use local ``main`` instead of ``origin/main`` (no remote in the temp repo).
    env["CHANGELOG_CHECK_BASE"] = "main"
    # Strip out the repo-level env vars inherited from pre-commit, if any.
    for key in ("SKIP_CHANGELOG_LABEL",):
        env.pop(key, None)
    env.update(env_overrides)
    return subprocess.run(
        [sys.executable, str(_SCRIPT)],
        cwd=repo,
        env=env,
        capture_output=True,
        text=True,
    )


class TestEndToEnd:
    """Run the script against temporary git repos."""

    def test_passes_when_no_changes(self, tmp_path: Path) -> None:
        """No diff vs base → pass."""
        repo = _setup_repo(tmp_path)
        result = _run_script(repo)
        assert result.returncode == 0, result.stderr

    def test_passes_with_only_exempt_changes(self, tmp_path: Path) -> None:
        """Touching only exempt files doesn't require a CHANGELOG entry."""
        repo = _setup_repo(tmp_path)
        _git(repo, "checkout", "-b", "feature")
        (repo / "tests" / "t.py").write_text("# modified\n")
        _git(repo, "commit", "-am", "Tweak test")
        result = _run_script(repo)
        assert result.returncode == 0, result.stderr

    def test_fails_when_substantive_without_changelog(
        self, tmp_path: Path,
    ) -> None:
        """Touching vera/ without CHANGELOG → fail with helpful message."""
        repo = _setup_repo(tmp_path)
        _git(repo, "checkout", "-b", "feature")
        (repo / "vera" / "cli.py").write_text("# modified\n")
        _git(repo, "commit", "-am", "Tweak cli")
        result = _run_script(repo)
        assert result.returncode == 1
        assert "CHANGELOG.md" in result.stderr
        assert "vera/cli.py" in result.stderr

    def test_passes_when_substantive_with_changelog(
        self, tmp_path: Path,
    ) -> None:
        """Touching vera/ AND adding a CHANGELOG bullet → pass."""
        repo = _setup_repo(tmp_path)
        _git(repo, "checkout", "-b", "feature")
        (repo / "vera" / "cli.py").write_text("# modified\n")
        (repo / "CHANGELOG.md").write_text(
            "# Changelog\n\n"
            "## [Unreleased]\n\n"
            "- **Tweaked the CLI** — did a thing.\n\n"
            "## [0.0.1] - 2026-01-01\n",
        )
        _git(repo, "commit", "-am", "Tweak cli")
        result = _run_script(repo)
        assert result.returncode == 0, result.stderr

    def test_skip_trailer_bypasses_check(self, tmp_path: Path) -> None:
        """``Skip-changelog:`` trailer lets substantive changes pass."""
        repo = _setup_repo(tmp_path)
        _git(repo, "checkout", "-b", "feature")
        (repo / "vera" / "cli.py").write_text("# cosmetic\n")
        _git(
            repo, "commit", "-am",
            "Fix typo in comment\n\nSkip-changelog: cosmetic only",
        )
        result = _run_script(repo)
        assert result.returncode == 0, result.stderr

    def test_skip_label_env_var_bypasses_check(
        self, tmp_path: Path,
    ) -> None:
        """``SKIP_CHANGELOG_LABEL=1`` lets substantive changes pass."""
        repo = _setup_repo(tmp_path)
        _git(repo, "checkout", "-b", "feature")
        (repo / "vera" / "cli.py").write_text("# cosmetic\n")
        _git(repo, "commit", "-am", "Fix typo")
        result = _run_script(repo, SKIP_CHANGELOG_LABEL="1")
        assert result.returncode == 0, result.stderr

    def test_explicit_override_falls_back_to_main(
        self, tmp_path: Path,
    ) -> None:
        """An invalid ``CHANGELOG_CHECK_BASE`` falls through to ``main``.

        The fallback chain is ``$CHANGELOG_CHECK_BASE → origin/main → main``,
        so setting an invalid override doesn't break the check as long as
        ``main`` (or ``origin/main``) exists.
        """
        repo = _setup_repo(tmp_path)
        result = _run_script(repo, CHANGELOG_CHECK_BASE="nonexistent-ref")
        # Same behaviour as passing no override — no changes vs main → pass.
        assert result.returncode == 0

    def test_no_base_ref_at_all_skips_gracefully(
        self, tmp_path: Path,
    ) -> None:
        """No ``main``, no ``origin/main``, no override → skip with warning.

        This covers the edge case of running inside a repo that has
        neither ``main`` nor ``origin/main`` available (tarball extract,
        detached HEAD with no branch history fetched, etc.).  The script
        must exit 0 rather than crashing.
        """
        repo = tmp_path / "emptyrepo"
        repo.mkdir()
        _git(repo, "init", "-b", "feature")  # no ``main`` branch
        _git(repo, "config", "user.email", "t@e.invalid")
        _git(repo, "config", "user.name", "T")
        _git(repo, "config", "commit.gpgsign", "false")
        (repo / "f.txt").write_text("x\n")
        _git(repo, "add", "f.txt")
        _git(repo, "commit", "-m", "init on feature")

        result = _run_script(repo)
        assert result.returncode == 0
        assert "no base ref found" in result.stderr
