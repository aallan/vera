"""Tests for scripts/check_changelog_fragments.py (#1529).

A fragment is one pull request's CHANGELOG entry, a file of its own under
``changelog.d/``: its name says which issue or branch it belongs to and which
Keep a Changelog section it goes in, and its content is the bullets exactly
as ``CHANGELOG.md`` will carry them.  ``changelog.d/README.md`` is not a
fragment.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
from typing import Any

import pytest

_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_changelog_fragments.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("check_changelog_fragments", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


fragments = _load()

_BULLET = "- **A change.** What it does ([#1529](https://github.com/aallan/vera/issues/1529)).\n"


def _directory(tmp_path: Path, files: dict[str, str]) -> Path:
    directory = tmp_path / "changelog.d"
    directory.mkdir()
    for name, text in files.items():
        (directory / name).write_text(text, encoding="utf-8")
    return directory


def _problems(tmp_path: Path, files: dict[str, str]) -> list[str]:
    _found, problems = fragments.read_fragments(_directory(tmp_path, files))
    return list(problems)


class TestNames:
    @pytest.mark.parametrize(
        ("name", "issue", "slug", "section"),
        [
            ("1529.added.md", 1529, None, "added"),
            ("7.changed.md", 7, None, "changed"),
            ("1529.deprecated.md", 1529, None, "deprecated"),
            ("1529.removed.md", 1529, None, "removed"),
            ("1529.fixed.md", 1529, None, "fixed"),
            ("1529.security.md", 1529, None, "security"),
            ("+fast-lane.changed.md", None, "fast-lane", "changed"),
            ("+v0.2.1.fixed.md", None, "v0.2.1", "fixed"),
            ("+one_test_driver.added.md", None, "one_test_driver", "added"),
        ],
    )
    def test_a_fragment_name_gives_its_issue_or_slug_and_its_section(
        self,
        tmp_path: Path,
        name: str,
        issue: int | None,
        slug: str | None,
        section: str,
    ) -> None:
        found, problems = fragments.read_fragments(
            _directory(tmp_path, {name: _BULLET})
        )
        assert problems == []
        assert [(f.issue, f.slug, f.section) for f in found] == [(issue, slug, section)]

    @pytest.mark.parametrize(
        "name",
        [
            "1529.md",
            "1529.added",
            "1529.added.txt",
            "1529.added.md.bak",
            "01529.added.md",
            "0.added.md",
            "#1529.added.md",
            "fast-lane.changed.md",
            "+.changed.md",
            "+-lane.changed.md",
            "1529-fix.added.md",
            "notes.md",
        ],
    )
    def test_any_other_name_is_a_problem_naming_the_file(
        self, tmp_path: Path, name: str
    ) -> None:
        problems = _problems(tmp_path, {name: _BULLET})
        assert len(problems) == 1
        assert f"changelog.d/{name}" in problems[0]

    @pytest.mark.parametrize("name", ["1529.fix.md", "1529.Added.md", "+lane.bugfix.md"])
    def test_an_unknown_section_is_named_as_such(self, tmp_path: Path, name: str) -> None:
        problems = _problems(tmp_path, {name: _BULLET})
        assert len(problems) == 1
        assert f"changelog.d/{name}" in problems[0]
        assert "section" in problems[0]
        assert "added, changed, deprecated, removed, fixed, security" in problems[0]

    def test_the_readme_is_not_a_fragment(self, tmp_path: Path) -> None:
        found, problems = fragments.read_fragments(
            _directory(tmp_path, {"README.md": "# Not bullets\n\nProse.\n"})
        )
        assert (found, problems) == ([], [])

    @pytest.mark.parametrize("name", [".DS_Store", ".gitkeep", ".1529.added.md"])
    def test_a_dotfile_is_neither_a_fragment_nor_a_problem(
        self, tmp_path: Path, name: str
    ) -> None:
        """Finder writes `.DS_Store` into any folder it opens; a dotfile is
        never a fragment, so it fails neither the gate nor the assembly."""
        found, problems = fragments.read_fragments(
            _directory(tmp_path, {name: "\x00 not text", "1529.added.md": _BULLET})
        )
        assert problems == []
        assert [f.path.name for f in found] == ["1529.added.md"]

    def test_a_directory_is_a_problem(self, tmp_path: Path) -> None:
        directory = _directory(tmp_path, {})
        (directory / "1529.added.md").mkdir()
        _found, problems = fragments.read_fragments(directory)
        assert len(problems) == 1
        assert "changelog.d/1529.added.md" in problems[0]

    def test_a_missing_directory_holds_no_fragments(self, tmp_path: Path) -> None:
        assert fragments.read_fragments(tmp_path / "changelog.d") == ([], [])


class TestContent:
    @pytest.mark.parametrize(
        "text",
        [
            _BULLET,
            _BULLET + "- **Another change.** In the same section.\n",
            _BULLET
            + "  - A sub-bullet, indented two spaces.\n"
            + "  A continuation line, indented two spaces.\n"
            + "    Four spaces, as the oldest sections indent.\n",
        ],
    )
    def test_bullets_and_indented_continuations_are_well_formed(
        self, tmp_path: Path, text: str
    ) -> None:
        found, problems = fragments.read_fragments(
            _directory(tmp_path, {"1529.added.md": text})
        )
        assert problems == []
        assert [f.text for f in found] == [text]

    @pytest.mark.parametrize(
        ("text", "wanted"),
        [
            ("", "empty"),
            (_BULLET.rstrip("\n"), "newline"),
            (_BULLET + "\n", "newline"),
            (_BULLET + "\n- **Second.** After a blank line.\n", "line 2 is blank"),
            (_BULLET + "   \n- **Second.** After a line of spaces.\n", "line 2 is blank"),
            ("  - An indented first line.\n", "line 1"),
            ("* **A star bullet.**\n", "line 1"),
            ("Prose, not a bullet.\n", "line 1"),
            ("-No space after the dash.\n", "line 1"),
            ("- \n", "line 1"),
            ("### Fixed\n" + _BULLET, "line 1"),
            (_BULLET + "\t- A tab-indented sub-bullet.\n", "line 2"),
            (_BULLET + "Unindented prose after a bullet.\n", "line 2"),
        ],
    )
    def test_anything_else_is_a_problem_naming_the_file_and_the_line(
        self, tmp_path: Path, text: str, wanted: str
    ) -> None:
        problems = _problems(tmp_path, {"1529.added.md": text})
        assert len(problems) == 1, problems
        assert "changelog.d/1529.added.md" in problems[0]
        assert wanted in problems[0]

    def test_a_file_that_is_not_utf8_is_a_problem(self, tmp_path: Path) -> None:
        directory = _directory(tmp_path, {})
        (directory / "1529.added.md").write_bytes(b"- \xff\xfe not UTF-8.\n")
        _found, problems = fragments.read_fragments(directory)
        assert len(problems) == 1
        assert "changelog.d/1529.added.md" in problems[0]

    def test_every_problem_is_reported_not_only_the_first(self, tmp_path: Path) -> None:
        problems = _problems(
            tmp_path,
            {
                "1529.added.md": _BULLET,
                "1530.fix.md": _BULLET,
                "1531.fixed.md": "Prose.\n",
                "README.md": "Prose.\n",
            },
        )
        assert len(problems) == 2
        assert "changelog.d/1530.fix.md" in problems[0]
        assert "changelog.d/1531.fixed.md" in problems[1]


class TestMain:
    def test_a_well_formed_directory_passes(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ) -> None:
        directory = _directory(
            tmp_path, {"README.md": "Prose.\n", "1529.added.md": _BULLET}
        )
        assert fragments.main(["--directory", str(directory)]) == 0
        assert capsys.readouterr().err == ""

    def test_a_malformed_fragment_fails_naming_it(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ) -> None:
        directory = _directory(tmp_path, {"1529.added.md": "Prose.\n"})
        assert fragments.main(["--directory", str(directory)]) == 1
        assert "changelog.d/1529.added.md" in capsys.readouterr().err

    def test_the_repository_directory_is_the_default(self) -> None:
        assert fragments.DIRECTORY == Path(__file__).resolve().parent.parent / "changelog.d"
