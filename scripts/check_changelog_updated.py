#!/usr/bin/env python
"""Verify that substantive PRs update CHANGELOG.md.

Runs at pre-push stage (locally) and in CI.  Compares the current
branch against the base ref (default ``origin/main``); if any
"substantive" files changed, requires ``CHANGELOG.md`` to also be
in the diff with a new entry.

File classification
-------------------

Substantive (requires a CHANGELOG entry when changed):

- ``vera/**``       compiler source
- ``spec/**``       language specification
- ``SKILL.md``      user-facing agent guide

Exempt (changing only these never triggers the check):

- ``tests/``, ``scripts/``, ``.github/``, ``docs/``, ``examples/``
- ``CHANGELOG.md``, ``HISTORY.md``, ``README.md``, ``ROADMAP.md``,
  ``KNOWN_ISSUES.md``, ``FAQ.md``, ``CONTRIBUTING.md``, ``TESTING.md``,
  ``AGENTS.md``, ``CLAUDE.md``, ``DE_BRUIJN.md``, ``EXAMPLES.md``,
  ``LICENSE``
- ``pyproject.toml``, ``uv.lock``
- ``.pre-commit-config.yaml``, ``.coderabbit.yaml``, ``.gitignore``

Any other path is treated as substantive (conservative default so a
new top-level directory doesn't accidentally bypass the check).

Escape hatches
--------------

- Commit trailer ``Skip-changelog: <reason>`` in any commit on the
  branch (git-native — works locally and in CI).
- Environment variable ``SKIP_CHANGELOG_LABEL=1`` (intended for CI
  runs where a ``skip-changelog`` PR label has been detected by an
  earlier workflow step).

Configuration
-------------

- ``CHANGELOG_CHECK_BASE`` — override the base ref (default
  ``origin/main``).  Mainly useful for release branches.

Exit codes
----------

- ``0`` — check passed, skipped, or not applicable (e.g. no diff).
- ``1`` — substantive changes detected without a matching CHANGELOG
  update and no escape hatch engaged.
"""

from __future__ import annotations

import os
import subprocess
import sys

# Prefixes / exact paths whose changes require a CHANGELOG entry.
# Anything not exempt is treated as substantive by default, but these
# are the "obviously substantive" paths used in error messages.
SUBSTANTIVE_PREFIXES: tuple[str, ...] = (
    "vera/",
    "spec/",
    "SKILL.md",
)

# Paths that are always exempt from the check.  Changing only files
# in this list never requires a CHANGELOG entry.
EXEMPT_PREFIXES: tuple[str, ...] = (
    # Directories (trailing slash intentional)
    "tests/",
    "scripts/",
    ".github/",
    "docs/",
    "examples/",
    "editors/",
    "assets/",
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
)

DEFAULT_BASE_REF = "origin/main"


def _run(cmd: list[str]) -> str | None:
    """Run a git command, returning stdout or ``None`` on failure."""
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, check=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None
    return result.stdout


def _resolve_base_ref() -> str | None:
    """Pick a base ref that actually exists in the local git repo.

    Falls back through ``origin/main``, ``main``, and any explicit
    override from ``$CHANGELOG_CHECK_BASE``.  Returns ``None`` if
    nothing usable exists (e.g. running outside a git worktree).
    """
    override = os.environ.get("CHANGELOG_CHECK_BASE")
    candidates = [c for c in (override, DEFAULT_BASE_REF, "main") if c]
    for ref in candidates:
        if _run(["git", "rev-parse", "--verify", ref]) is not None:
            return ref
    return None


def _changed_files(base: str) -> list[str]:
    """Files changed between ``base`` and ``HEAD``."""
    stdout = _run(["git", "diff", "--name-only", base, "HEAD"])
    if stdout is None:
        return []
    return [line for line in stdout.strip().split("\n") if line]


def _is_exempt(path: str) -> bool:
    """Return True iff ``path`` matches any entry in ``EXEMPT_PREFIXES``.

    Entries ending in ``/`` are treated as directory prefixes (matched
    with ``startswith``).  Entries without a trailing slash are treated
    as exact file paths (matched with equality).  This prevents
    accidental overmatching — e.g. ``README.md`` is exempt but
    ``README.md.bak`` is still treated as substantive.
    """
    for entry in EXEMPT_PREFIXES:
        if entry.endswith("/"):
            if path.startswith(entry):
                return True
        else:
            if path == entry:
                return True
    return False


def is_substantive(path: str) -> bool:
    """Return True iff ``path`` is substantive and needs a CHANGELOG entry.

    A path is substantive if it does NOT match any ``EXEMPT_PREFIXES``
    entry.  This is deliberately conservative — a brand-new top-level
    directory is treated as substantive until explicitly exempted.
    """
    # Normalise for robustness (no leading ``./`` etc).
    path = path.strip()
    if not path:
        return False
    return not _is_exempt(path)


def _changelog_has_new_entry(base: str) -> bool:
    """Return True if the CHANGELOG.md diff adds a new entry.

    A "new entry" is either:

    1. An added line introducing a new version heading (``+## [X.Y.Z]``
       or ``+## [Unreleased]``).
    2. An added bullet (``+- ...``) that appears *inside* the
       ``[Unreleased]`` section.

    Section-tracking is necessary because CHANGELOG.md commonly has
    prose edits (typo fixes, wording tweaks) inside released-version
    entries.  Those edits sometimes add bulleted lines, but they
    shouldn't count as "adding a new entry" for the purposes of this
    check — only bullets under ``[Unreleased]`` do.

    Pure whitespace or cosmetic changes to CHANGELOG.md don't count.
    """
    # ``--unified=9999`` forces git to include the whole file as context
    # rather than just a few lines around each hunk.  Without this, a new
    # bullet added more than 3 lines below the ``## [Unreleased]`` heading
    # would see the heading fall outside the diff window, and the
    # section tracker below would never have the chance to set
    # ``current_section = "Unreleased"``.  CHANGELOG.md is a few thousand
    # lines at worst, so running over the whole file is cheap.
    diff = _run([
        "git", "diff", "--unified=9999", base, "HEAD", "--", "CHANGELOG.md",
    ])
    if not diff:
        return False

    # Track which section header we're currently inside.  The diff
    # includes both context lines (prefixed with a space) and added
    # lines (prefixed with ``+``); we update current_section on both
    # so the tracker reflects the post-diff state of the file.
    current_section: str | None = None
    for line in diff.splitlines():
        if line.startswith("+++") or line.startswith("---"):
            # File headers — ignore entirely.
            continue

        # Extract the line content regardless of diff marker.  Strip
        # only the single-char diff prefix, NOT leading whitespace —
        # prose that mentions "## [X]" with indentation (e.g. a code
        # reference inside a bullet) must not be mistaken for a real
        # heading, which always starts at column 0.
        if line.startswith("+") or line.startswith(" "):
            content = line[1:] if len(line) > 1 else ""
        elif line.startswith("-"):
            # Removed context — doesn't tell us about the post-diff
            # section layout.
            continue
        else:
            # Hunk headers (``@@ ... @@``) and other metadata.
            continue

        if content.startswith("## ["):
            # Update section tracker — skip past ``## [`` (4 chars) to
            # the name, up to the closing ``]``.
            end = content.find("]", 4)
            if end > 4:
                current_section = content[4:end]
            # An *added* versioned heading (e.g. ``+## [0.0.114]``) is
            # itself a new entry — that's the release-cutting pattern.
            # But a bare ``+## [Unreleased]`` heading is just structural
            # scaffolding; don't short-circuit on it, let the loop
            # continue so the bullet-under-section check below can
            # decide whether there's any actual content.
            if line.startswith("+") and current_section != "Unreleased":
                return True
            continue

        # Added bullets only count inside the [Unreleased] section.
        if line.startswith("+") and content.startswith("- "):
            if current_section == "Unreleased":
                return True

    return False


def _has_skip_trailer(base: str) -> bool:
    """Return True if any commit on the branch has a ``Skip-changelog:`` trailer."""
    log = _run(["git", "log", f"{base}..HEAD", "--format=%B"])
    if not log:
        return False
    for line in log.splitlines():
        # Trailers appear at the start of a line, case-sensitive.
        if line.startswith("Skip-changelog:"):
            return True
    return False


def main() -> int:
    base = _resolve_base_ref()
    if base is None:
        # No base to diff against — likely running outside a git
        # worktree (e.g. inside a tarball) or during the very first
        # commit of a repo.  Skip without failing.
        print(
            "check_changelog_updated: no base ref found; skipping.",
            file=sys.stderr,
        )
        return 0

    changed = _changed_files(base)
    if not changed:
        return 0

    substantive = [f for f in changed if is_substantive(f)]
    if not substantive:
        return 0

    if _changelog_has_new_entry(base):
        return 0

    if _has_skip_trailer(base):
        return 0

    if os.environ.get("SKIP_CHANGELOG_LABEL") == "1":
        return 0

    print(
        "ERROR: Substantive changes detected but CHANGELOG.md "
        "is missing a new entry.",
        file=sys.stderr,
    )
    print("", file=sys.stderr)
    print("Files changed that require a CHANGELOG entry:", file=sys.stderr)
    for path in substantive[:10]:
        print(f"  {path}", file=sys.stderr)
    if len(substantive) > 10:
        print(f"  ... and {len(substantive) - 10} more", file=sys.stderr)
    print("", file=sys.stderr)
    print(
        "Add a bullet under [Unreleased] in CHANGELOG.md, or include",
        file=sys.stderr,
    )
    print(
        "'Skip-changelog: <reason>' in a commit message trailer.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
