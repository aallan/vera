"""The suite never acts on a repository it inherits (PR #1484).

Under pre-commit, git exports ``GIT_DIR`` and ``GIT_INDEX_FILE`` for the
repository being committed, and git honours them ahead of a subprocess's
``cwd`` or ``-C``.  A test that runs ``git init`` in a temporary directory
with them inherited re-initialises the repository being committed instead,
and from a linked worktree that marks the shared repository
``core.bare = true``.  ``tests/conftest.py`` clears every ``GIT_*``
variable at session start.  This module holds the suite to that: it runs
the tests that spawn git in a child session whose environment points at a
decoy repository, the way a hook's does, and requires the decoy unchanged.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).parent.parent

# Every test that runs git against a repository of its own, or reads one
# through a script's git reader.  Found by sweeping tests/ and scripts/ for
# git subprocesses; a new one belongs here.
GIT_SPAWNING_TESTS = (
    "tests/test_release.py",
    "tests/test_check_changelog_updated.py",
    "tests/test_check_corpus_differential.py::TestBaseCheckoutReuse",
    "tests/test_check_doc_counts.py::TestReleaseTags",
    "tests/test_check_doc_examples.py::TestLiveEnumeration",
    "tests/test_check_doc_examples.py::TestEnumerationIgnoresAnInheritedRepository",
    "tests/test_check_doc_examples.py::TestCoverage",
)


def _git(*args: str, cwd: Path) -> str:
    return subprocess.run(
        ["git", *args], cwd=cwd, check=True,
        capture_output=True, text=True, encoding="utf-8",
    ).stdout


def _decoy(path: Path) -> tuple[Path, dict[str, str]]:
    """A repository with a linked worktree, and the environment a hook in
    that worktree runs with: ``GIT_DIR`` names the worktree's gitdir, which
    does not end in ``.git``, and ``GIT_INDEX_FILE`` its index."""
    main = path / "main"
    main.mkdir(parents=True)
    _git("init", "-q", cwd=main)
    _git(
        "-c", "user.name=decoy", "-c", "user.email=decoy@example.invalid",
        "commit", "-q", "--allow-empty", "-m", "decoy", cwd=main,
    )
    _git("worktree", "add", "-q", str(path / "wt"), "-b", "wt", cwd=main)
    gitdir = main / ".git" / "worktrees" / "wt"
    return main, {"GIT_DIR": str(gitdir), "GIT_INDEX_FILE": str(gitdir / "index")}


def _state(main: Path) -> dict[str, bytes]:
    """What a stray git command could change: the shared config, the
    worktree's index and HEAD, and every ref."""
    gitdir = main / ".git"
    worktree = gitdir / "worktrees" / "wt"
    refs = subprocess.run(
        ["git", "for-each-ref"], cwd=main, check=True, capture_output=True,
    ).stdout
    return {
        "config": (gitdir / "config").read_bytes(),
        "index": (worktree / "index").read_bytes(),
        "HEAD": (worktree / "HEAD").read_bytes(),
        "refs": refs,
    }


class TestTheDecoy:
    def test_a_git_init_under_its_environment_damages_it(
        self, tmp_path: Path,
    ) -> None:
        """The positive control: the decoy registers the damage, so an
        unchanged decoy below means the suite did no damage, not that the
        decoy cannot show any."""
        main, env = _decoy(tmp_path / "decoy")
        before = _state(main)
        foreign = tmp_path / "foreign"
        foreign.mkdir()
        subprocess.run(
            ["git", "init", "-q"], cwd=foreign, env={**os.environ, **env},
            check=True, capture_output=True,
        )
        assert _state(main)["config"] != before["config"]
        assert not (foreign / ".git").exists()


class TestTheSuiteUnderAHooksEnvironment:
    def test_the_git_spawning_tests_leave_the_decoy_unchanged(
        self, tmp_path: Path,
    ) -> None:
        main, env = _decoy(tmp_path / "decoy")
        before = _state(main)
        result = subprocess.run(
            [
                sys.executable, "-m", "pytest", "-q",
                "-p", "no:randomly", "-p", "no:cacheprovider",
                *GIT_SPAWNING_TESTS,
            ],
            cwd=ROOT, env={**os.environ, **env},
            capture_output=True, text=True, encoding="utf-8", check=False,
        )
        after = _state(main)
        changed = sorted(k for k in before if before[k] != after[k])
        assert changed == [], (changed, result.stdout[-2000:])
        assert result.returncode == 0, result.stdout[-2000:]

    def test_every_listed_test_exists(self) -> None:
        for target in GIT_SPAWNING_TESTS:
            path, _sep, name = target.partition("::")
            assert (ROOT / path).is_file(), path
            if name:
                text = (ROOT / path).read_text(encoding="utf-8")
                assert f"class {name}" in text, target
