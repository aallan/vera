"""Release-policy tests for ``scripts/release.py`` (#481)."""

from __future__ import annotations

import importlib.util
import os
import re
from pathlib import Path
import subprocess
import sys
from typing import Any

import pytest


_SCRIPT = Path(__file__).parent.parent / "scripts" / "release.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("release_helper", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


release = _load()


def _root(tmp_path: Path, version: str = "0.1.5") -> Path:
    (tmp_path / "pyproject.toml").write_text(
        f'[project]\nname = "veralang"\nversion = "{version}"\n',
        encoding="utf-8",
    )
    (tmp_path / "CHANGELOG.md").write_text(
        f"# Changelog\n\n## [{version}] - 2026-07-15\n\n"
        "### Added\n\n- Release machinery.\n\n"
        "## [0.1.4] - 2026-06-01\n\n- Previous.\n",
        encoding="utf-8",
    )
    return tmp_path


def _dist(tmp_path: Path) -> Path:
    dist = tmp_path / "dist"
    dist.mkdir()
    (dist / "veralang-0.1.5-py3-none-any.whl").write_bytes(b"wheel")
    (dist / "veralang-0.1.5.tar.gz").write_bytes(b"sdist")
    return dist


@pytest.fixture(autouse=True)
def _hermetic_git_env(monkeypatch: pytest.MonkeyPatch) -> None:
    """Scrub inherited ``GIT_*`` variables so every git subprocess in this
    module — the ``_git`` fixture helper AND the ``scripts/release.py`` helpers
    under test — is hermetic to the tmp repo its ``cwd`` names.

    When this suite runs inside a pre-commit hook, git exports ``GIT_DIR`` (and
    ``GIT_INDEX_FILE``) to the hook's environment.  Without the scrub, the
    exported gitdir overrode each call's ``cwd``: ``git init`` re-initialized
    the DEVELOPER'S repository instead of the tmp one — from a linked worktree
    the exported gitdir path doesn't end in ``.git``, so the re-init marked the
    shared repo ``core.bare=true`` — and ``git config user.*`` hijacked its
    committer identity, breaking every subsequent git operation in the outer
    repo while this test failed on ``git add`` (exit 128, "this operation must
    be run in a work tree").  ``release.py``'s own git calls read the wrong
    repo the same way, so the scrub lives here rather than in ``_git``."""
    for name in [k for k in os.environ if k.startswith("GIT_")]:
        monkeypatch.delenv(name, raising=False)


def _git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=True,
    )
    return result.stdout.strip()


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(root, "commit", "-m", message)
    return _git(root, "rev-parse", "HEAD")


class TestVersions:
    @pytest.mark.parametrize(
        ("value", "expected"),
        [("0.1.5", (0, 1, 5)), ("12.34.56", (12, 34, 56))],
    )
    def test_parse(self, value: str, expected: tuple[int, int, int]) -> None:
        assert release.parse_version(value) == expected

    @pytest.mark.parametrize(
        "value", ["v0.1.5", "0.1", "0.1.5rc1", "01.2.3", "1.02.3", ""]
    )
    def test_rejects_non_release_versions(self, value: str) -> None:
        with pytest.raises(release.ReleaseError, match="expected X.Y.Z"):
            release.parse_version(value)

    def test_project_version(self, tmp_path: Path) -> None:
        assert release.project_version(_root(tmp_path)) == "0.1.5"

    def test_project_name_must_be_veralang(self, tmp_path: Path) -> None:
        root = _root(tmp_path)
        (root / "pyproject.toml").write_text(
            '[project]\nname = "vera"\nversion = "0.1.5"\n', encoding="utf-8"
        )
        with pytest.raises(release.ReleaseError, match="expected 'veralang'"):
            release.project_version(root)


class TestChangelogNotes:
    def test_extracts_matching_section(self) -> None:
        text = (
            "## [Unreleased]\n\n- Future.\n\n"
            "## [0.1.5] - 2026-07-15\n\n### Fixed\n\n- One.\n- Two.\n\n"
            "## [0.1.4] - 2026-07-01\n\n- Old.\n"
        )
        assert release.changelog_notes(text, "0.1.5") == "### Fixed\n\n- One.\n- Two."

    def test_date_is_optional(self) -> None:
        assert (
            release.changelog_notes("## [0.1.5]\n\n- Notes.\n", "0.1.5") == "- Notes."
        )

    def test_missing_section_fails(self) -> None:
        with pytest.raises(release.ReleaseError, match="no ## \\[0.1.5\\]"):
            release.changelog_notes("## [0.1.4]\n\n- Old.\n", "0.1.5")

    @pytest.mark.parametrize(
        "body", ["", "\n### Added\n", "\nSome prose but no release bullet.\n"]
    )
    def test_section_requires_a_bullet(self, body: str) -> None:
        with pytest.raises(release.ReleaseError, match="at least one bullet"):
            release.changelog_notes(f"## [0.1.5]{body}", "0.1.5")

    def test_section_carries_the_heading_date(self) -> None:
        section = release.changelog_section("## [0.1.5] - 2026-07-15\n\n- One.\n", "0.1.5")
        assert (section.version, section.date, section.notes) == (
            "0.1.5",
            "2026-07-15",
            "- One.",
        )

    def test_section_without_a_date_reports_none(self) -> None:
        assert release.changelog_section("## [0.1.5]\n\n- One.\n", "0.1.5").date is None


def _section(bullets: str, *, version: str = "0.1.5") -> Any:
    return release.changelog_section(
        f"## [{version}] - 2026-07-15\n\n{bullets}\n", version
    )


# The closing line of every condensed body built from `_section`'s default
# version and date: the section in the CHANGELOG at its tag.
_CHANGELOG_LINK = (
    "Full release notes: [CHANGELOG.md]"
    "(https://github.com/aallan/vera/blob/v0.1.5/CHANGELOG.md#015---2026-07-15)"
)
# Words a body would need to talk about its own size or shortening.
_SIZE_WORDING = re.compile(r"budget|limit|characters|truncat|condens", re.IGNORECASE)


class TestReleaseBody:
    """#1288 — the GitHub Release body must always fit the 125,000 limit.

    The v0.1.10 failure landed *after* PyPI had accepted the immutable
    archives and after the tag was cut, so the notes builder is required to
    be total: it either passes the section through or condenses it, and the
    result never exceeds the limit.  A condensed body is the headline index
    and a closing link to the section in the CHANGELOG, and it says nothing
    about its own size.
    """

    def test_a_section_within_budget_passes_through_unchanged(self) -> None:
        section = _section("### Fixed\n\n- **One.** Detail.\n- **Two.** Detail.")
        assert release.release_body(section, repo="aallan/vera") == section.notes

    def test_an_oversized_section_is_condensed_to_fit(self) -> None:
        filler = "x" * 4000
        bullets = "### Fixed\n\n" + "\n".join(
            f"- **Lead-in {index}.** {filler}" for index in range(50)
        )
        section = _section(bullets)
        assert len(section.notes) > release.GITHUB_RELEASE_BODY_LIMIT

        body = release.release_body(section, repo="aallan/vera")
        assert len(body) <= release.GITHUB_RELEASE_BODY_LIMIT
        assert body != section.notes
        assert "### Fixed" in body
        assert "- Lead-in 0." in body
        assert "- Lead-in 49." in body
        assert filler not in body
        assert body.splitlines()[-1] == _CHANGELOG_LINK

    def test_the_condensed_body_leads_with_its_first_heading(self) -> None:
        """The index is the first thing a reader of the release sees.

        Nothing about the body itself comes before it: the first line is
        the section's first ``###`` heading, here the Highlights a release
        section opens with, and the next line is that heading's first entry.
        """
        section = _section(
            "### Highlights\n\n"
            f"- **Headline.** {'h' * 4000}\n\n"
            "### Fixed\n\n"
            + "\n".join(f"- **Lead {n}.** {'y' * 4000}" for n in range(50))
        )
        body = release.release_body(section, repo="aallan/vera")
        assert body != section.notes
        assert body.splitlines()[:2] == ["### Highlights", "- Headline."]

    def test_the_condensed_body_says_nothing_about_its_own_size(self) -> None:
        """Size is the builder's concern, not the reader's.

        Condensing starts at the budget, below GitHub's limit, so both bands
        are pinned: a section past the budget and under the limit, and one
        past the limit as well.  Both condense, and neither body states the
        section's length, the budget, the limit, or that it was shortened.
        """
        band = _section(
            "### Fixed\n\n"
            + "\n".join(f"- **Lead {n}.** {'z' * 2400}" for n in range(50))
        )
        over = _section(
            "### Fixed\n\n"
            + "\n".join(f"- **Lead {n}.** {'z' * 4000}" for n in range(50))
        )
        assert (
            release.RELEASE_BODY_BUDGET
            < len(band.notes)
            <= release.GITHUB_RELEASE_BODY_LIMIT
        )
        assert len(over.notes) > release.GITHUB_RELEASE_BODY_LIMIT

        for section in (band, over):
            body = release.release_body(section, repo="aallan/vera")
            assert body != section.notes, "both bands must condense"
            assert _SIZE_WORDING.search(body) is None, body.splitlines()[0]
            for figure in (
                len(section.notes),
                release.RELEASE_BODY_BUDGET,
                release.GITHUB_RELEASE_BODY_LIMIT,
            ):
                assert f"{figure:,}" not in body
                assert str(figure) not in body

    def test_the_index_reproduces_the_v0110_recovery_shape(self) -> None:
        """The lead-in carries the bullet's LAST issue/PR link, wrapped.

        Pinned because the v0.1.10 manual recovery attributed a bullet whose
        only reference sat mid-prose (``(PR [#1282](...) review)``), not
        immediately after the bold run.  The index lines come before the
        closing CHANGELOG link and the blank line that separates them.
        """
        section = _section(
            "### Changed\n\n"
            "- **Lead one.** Body citing "
            "([#1260](https://github.com/aallan/vera/issues/1260)) and then "
            "(PR [#1282](https://github.com/aallan/vera/pull/1282) review).\n"
            "- **Lead two.** No reference at all.\n"
        )
        assert release.condense_notes(section, repo="aallan/vera").splitlines() == [
            "### Changed",
            "- Lead one. ([#1282](https://github.com/aallan/vera/pull/1282))",
            "- Lead two.",
            "",
            _CHANGELOG_LINK,
        ]

    def test_a_bullet_without_a_bold_lead_in_still_reaches_the_index(self) -> None:
        section = _section("### Fixed\n\n- A plain bullet with no bold lead-in.")
        assert (
            "- A plain bullet with no bold lead-in."
            in release.condense_notes(section, repo="aallan/vera").splitlines()
        )

    def test_condensing_a_bullet_free_section_is_an_error(self) -> None:
        """An index that matches nothing is a failure, never a silent empty body."""
        section = release.ChangelogSection("0.1.5", "2026-07-15", "Prose only.")
        with pytest.raises(release.ReleaseError, match="no bullets"):
            release.condense_notes(section, repo="aallan/vera")

    def test_an_index_that_still_overflows_is_cut_at_a_line_and_keeps_the_link(
        self,
    ) -> None:
        """Even the index is past GitHub's limit: it is cut, the link stays.

        The cut falls after the last whole index line that fits beside the
        closing link.  Every line kept is a line of the full index, in order,
        and the first line dropped would not have fitted.
        """
        bullets = "### Fixed\n\n" + "\n".join(
            f"- **{'lead ' * 400}{index}.** detail" for index in range(400)
        )
        section = _section(bullets)
        full = release.condense_notes(section, repo="aallan/vera")
        assert len(full) > release.GITHUB_RELEASE_BODY_LIMIT

        body = release.release_body(section, repo="aallan/vera")
        assert len(body) <= release.GITHUB_RELEASE_BODY_LIMIT
        lines = body.splitlines()
        assert lines[-2:] == ["", _CHANGELOG_LINK]
        kept, full_lines = lines[:-2], full.splitlines()
        assert kept == full_lines[: len(kept)]
        assert kept[-1].startswith("- ")
        dropped = full_lines[len(kept)]
        assert len(body) + len(dropped) + 1 > release.GITHUB_RELEASE_BODY_LIMIT
        assert _SIZE_WORDING.search(body) is None

    def test_a_cut_at_the_limit_fills_it_exactly(self) -> None:
        """The cut's arithmetic, at the boundary itself.

        The long entries are sized so that they, the heading, the newline
        before each entry and the closing link come to exactly the limit.
        Every long entry is kept and every short one after them is dropped:
        a newline left out of the sum, or the closing link left out of it,
        would let a short entry in and take the body past the limit.
        """
        limit = release.GITHUB_RELEASE_BODY_LIMIT
        room = limit - len("\n\n" + _CHANGELOG_LINK + "\n")
        heading, count = "### Fixed", 60
        # Each long entry's index line is "- " plus its lead-in, `width` long.
        total = room - len(heading) - count
        widths = [total // count] * count
        widths[-1] += total - sum(widths)
        long = [f"- **{'a' * (width - 2)}** detail" for width in widths]
        short = [f"- **s{n}.** detail" for n in range(20)]
        section = _section(heading + "\n\n" + "\n".join(long + short))
        assert len(release.condense_notes(section, repo="aallan/vera")) > limit

        body = release.release_body(section, repo="aallan/vera")
        assert len(body) == limit
        lines = body.splitlines()
        assert lines[0] == heading
        assert lines[1:-2] == [f"- {'a' * (width - 2)}" for width in widths]
        assert lines[-2:] == ["", _CHANGELOG_LINK]

    def test_a_heading_cut_from_its_entries_is_dropped_with_them(self) -> None:
        """A cut never leaves a heading with nothing under it."""
        section = _section(
            "### Added\n\n- **Short.** Detail.\n\n"
            f"### Fixed\n\n- **{'x' * 130_000}.** Detail."
        )
        body = release.release_body(section, repo="aallan/vera")
        assert body.splitlines() == ["### Added", "- Short.", "", _CHANGELOG_LINK]

    def test_an_index_with_no_whole_line_that_fits_is_the_link_alone(self) -> None:
        """Total to the last case: when no index line fits, the link is the body."""
        section = _section(f"### Fixed\n\n- **{'x' * 130_000}.** Detail.")
        assert release.release_body(section, repo="aallan/vera") == (
            _CHANGELOG_LINK + "\n"
        )

    @pytest.mark.parametrize(
        ("version", "date", "expected"),
        [
            ("0.1.10", "2026-08-12", "#0110---2026-08-12"),
            ("0.1.5", None, "#015"),
        ],
    )
    def test_changelog_anchor(
        self, version: str, date: str | None, expected: str
    ) -> None:
        assert release.changelog_anchor(version, date) == expected

    def test_every_shipped_changelog_section_yields_a_body_that_fits(self) -> None:
        """The real artefact, not a fixture — and non-vacuously.

        v0.1.10's section is the one that 422'd, so at least one section here
        must exercise the condensing path; a suite where none did would pass
        with the limit check deleted.
        """
        root = Path(__file__).parent.parent
        text = (root / "CHANGELOG.md").read_text(encoding="utf-8")
        # The canonical heading grammar only; the oldest sections carry a
        # trailing PR reference the release extractor has never accepted.
        versions = re.findall(
            r"^## \[(\d+\.\d+\.\d+)\](?: - \d{4}-\d\d-\d\d)?[ \t]*$",
            text,
            re.MULTILINE,
        )
        assert len(versions) > 100, "CHANGELOG version headings no longer found"

        condensed = []
        for version in versions:
            section = release.changelog_section(text, version)
            body = release.release_body(section, repo="aallan/vera")
            assert len(body) <= release.GITHUB_RELEASE_BODY_LIMIT, version
            if body != section.notes:
                condensed.append(version)
                anchor = release.changelog_anchor(version, section.date)
                assert body.splitlines()[-1] == (
                    "Full release notes: [CHANGELOG.md](https://github.com/"
                    f"aallan/vera/blob/v{version}/CHANGELOG.md{anchor})"
                ), version
                assert body.splitlines()[0].startswith("### "), version
                assert _SIZE_WORDING.search(body.splitlines()[0]) is None, version
        assert "0.1.10" in condensed


class TestPlanning:
    def test_recovery_tracks_first_parent_bump_and_package_changes(
        self, tmp_path: Path
    ) -> None:
        root = _root(tmp_path, "0.1.4")
        (root / "vera").mkdir()
        (root / "vera" / "cli.py").write_text("OLD = True\n", encoding="utf-8")
        _git(root, "init", "-b", "main")
        _git(root, "config", "user.email", "release-test@example.invalid")
        _git(root, "config", "user.name", "Release Test")
        _commit(root, "initial")

        (root / "pyproject.toml").write_text(
            '[project]\nname = "veralang"\nversion = "0.1.5"\n',
            encoding="utf-8",
        )
        introduced = _commit(root, "bump version")
        (root / "README.md").write_text("Docs only.\n", encoding="utf-8")
        _commit(root, "docs after bump")

        assert release.version_introduction_commit("0.1.5", root) == introduced
        assert release.package_changes_since(introduced, root) == []

        (root / "vera" / "cli.py").write_text("NEW = True\n", encoding="utf-8")
        _commit(root, "package change")
        assert release.package_changes_since(introduced, root) == ["vera/cli.py"]

    def test_non_version_push_is_noop(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        root = _root(tmp_path)
        monkeypatch.setattr(release, "version_at_ref", lambda _ref, _root: "0.1.5")
        plan = release.plan_release(
            "push",
            before_ref="before",
            root=root,
        )
        assert plan == release.ReleasePlan(False, "none", "0.1.5")

    def test_increasing_push_plans_production(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        root = _root(tmp_path)
        monkeypatch.setattr(release, "version_at_ref", lambda _ref, _root: "0.1.4")
        monkeypatch.setattr(release, "tag_exists", lambda _version, _root: False)
        plan = release.plan_release(
            "push", before_ref="before", root=root
        )
        assert plan == release.ReleasePlan(True, "pypi", "0.1.5")

    def test_a_bump_is_planned_from_pyproject_alone(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """The version is written once, in `pyproject.toml`.  A tree whose
        package states some other version, and which has no script to
        compare copies with, plans its release from `pyproject.toml`; the
        CHANGELOG section is the one other thing a release needs."""
        root = _root(tmp_path)
        (root / "vera").mkdir()
        (root / "vera" / "__init__.py").write_text(
            '__version__ = "0.0.1"\n', encoding="utf-8"
        )
        monkeypatch.setattr(release, "version_at_ref", lambda _ref, _root: "0.1.4")
        monkeypatch.setattr(release, "tag_exists", lambda _version, _root: False)
        plan = release.plan_release("push", before_ref="before", root=root)
        assert plan == release.ReleasePlan(True, "pypi", "0.1.5")

    def test_a_bump_without_its_changelog_section_is_refused(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        root = _root(tmp_path)
        (root / "CHANGELOG.md").write_text(
            "# Changelog\n\n## [0.1.4] - 2026-06-01\n\n- Previous.\n",
            encoding="utf-8",
        )
        monkeypatch.setattr(release, "version_at_ref", lambda _ref, _root: "0.1.4")
        monkeypatch.setattr(release, "tag_exists", lambda _version, _root: False)
        with pytest.raises(release.ReleaseError, match=r"no ## \[0\.1\.5\]"):
            release.plan_release("push", before_ref="before", root=root)

    def test_decrease_is_rejected(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        root = _root(tmp_path, "0.1.4")
        monkeypatch.setattr(release, "version_at_ref", lambda _ref, _root: "0.1.5")
        with pytest.raises(release.ReleaseError, match="must increase"):
            release.plan_release(
                "push", before_ref="before", root=root
            )

    def test_push_requires_before_ref(self, tmp_path: Path) -> None:
        with pytest.raises(release.ReleaseError, match="requires --before-ref"):
            release.plan_release("push", root=_root(tmp_path))

    def test_testpypi_requires_exact_confirmation(self, tmp_path: Path) -> None:
        with pytest.raises(release.ReleaseError, match="does not match"):
            release.plan_release(
                "testpypi",
                confirm_version="0.1.4",
                root=_root(tmp_path),
            )

    def test_testpypi_allows_an_existing_production_tag(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setattr(release, "tag_exists", lambda _version, _root: True)
        plan = release.plan_release(
            "testpypi",
            confirm_version="0.1.5",
            root=_root(tmp_path),
        )
        assert plan.target == "testpypi"

    def test_production_recovery_requires_main(self, tmp_path: Path) -> None:
        with pytest.raises(release.ReleaseError, match="only from main"):
            release.plan_release(
                "production-recovery",
                ref_name="refs/heads/release/0.1.5",
                confirm_version="0.1.5",
                root=_root(tmp_path),
            )

    def test_production_recovery_rejects_later_package_changes(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setattr(
            release, "version_introduction_commit", lambda _version, _root: "abc"
        )
        monkeypatch.setattr(
            release, "package_changes_since", lambda _commit, _root: ["vera/cli.py"]
        )
        with pytest.raises(release.ReleaseError, match="vera/cli.py"):
            release.plan_release(
                "production-recovery",
                ref_name="refs/heads/main",
                confirm_version="0.1.5",
                root=_root(tmp_path),
            )

    def test_production_recovery_without_changes_is_allowed(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setattr(
            release, "version_introduction_commit", lambda _version, _root: "abc"
        )
        monkeypatch.setattr(release, "package_changes_since", lambda _commit, _root: [])
        monkeypatch.setattr(release, "tag_exists", lambda _version, _root: False)
        plan = release.plan_release(
            "production-recovery",
            ref_name="refs/heads/main",
            confirm_version="0.1.5",
            root=_root(tmp_path),
        )
        assert plan.target == "pypi"

    def test_production_rejects_existing_immutable_tag(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setattr(release, "version_at_ref", lambda _ref, _root: "0.1.4")
        monkeypatch.setattr(release, "tag_exists", lambda _version, _root: True)
        with pytest.raises(release.ReleaseError, match="already exists"):
            release.plan_release(
                "push",
                before_ref="before",
                root=_root(tmp_path),
            )


class TestArchivesAndRegistry:
    def test_distribution_hashes_and_manifest(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)
        assert set(hashes) == {
            "veralang-0.1.5-py3-none-any.whl",
            "veralang-0.1.5.tar.gz",
        }
        output = tmp_path / "release" / "SHA256SUMS"
        release.write_manifest(dist, output)
        assert output.read_text(encoding="utf-8").splitlines() == [
            f"{hashes[name]}  {name}" for name in sorted(hashes)
        ]

    def test_requires_exactly_one_wheel_and_sdist(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        (dist / "another.whl").write_bytes(b"extra")
        with pytest.raises(release.ReleaseError, match="exactly one"):
            release.distribution_hashes(dist)

    def test_registry_version_files(self) -> None:
        payload = {
            "releases": {
                "0.1.5": [
                    {"filename": "a.whl", "digests": {"sha256": "abc"}},
                    {"filename": "a.tar.gz", "digests": {"sha256": "def"}},
                ]
            }
        }
        assert release.registry_version_files(
            "pypi", "0.1.5", fetch=lambda _index: payload
        ) == {"a.whl": "abc", "a.tar.gz": "def"}

    def test_absent_project_or_version_returns_none(self) -> None:
        assert (
            release.registry_version_files("pypi", "0.1.5", fetch=lambda _index: None)
            is None
        )
        assert (
            release.registry_version_files(
                "pypi", "0.1.5", fetch=lambda _index: {"releases": {}}
            )
            is None
        )

    @pytest.mark.parametrize(
        ("payload", "message"),
        [
            ({"releases": []}, "no releases object"),
            ({"releases": {"0.1.5": ["bad"]}}, "malformed file data"),
            (
                {"releases": {"0.1.5": [{"digests": {"sha256": "abc"}}]}},
                "lacks filename/SHA-256 data",
            ),
            (
                {"releases": {"0.1.5": [{"filename": "a.whl"}]}},
                "lacks filename/SHA-256 data",
            ),
        ],
    )
    def test_registry_rejects_malformed_payloads(
        self, payload: dict[str, Any], message: str
    ) -> None:
        with pytest.raises(release.ReleaseError, match=message):
            release.registry_version_files(
                "pypi", "0.1.5", fetch=lambda _index: payload
            )

    def test_assert_absent_rejects_existing_version(self) -> None:
        payload = {
            "releases": {"0.1.5": [{"filename": "a", "digests": {"sha256": "b"}}]}
        }
        with pytest.raises(release.ReleaseError, match="already exists"):
            release.assert_version_absent("pypi", "0.1.5", fetch=lambda _index: payload)

    def test_verify_registry_matches_exact_files_and_hashes(
        self, tmp_path: Path
    ) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)
        payload = {
            "releases": {
                "0.1.5": [
                    {"filename": name, "digests": {"sha256": digest}}
                    for name, digest in hashes.items()
                ]
            }
        }
        release.verify_registry(
            "pypi", "0.1.5", dist, attempts=1, fetch=lambda _index: payload
        )

    def test_verify_registry_retries_propagation(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)
        payload = {
            "releases": {
                "0.1.5": [
                    {"filename": name, "digests": {"sha256": digest}}
                    for name, digest in hashes.items()
                ]
            }
        }
        responses = iter([None, payload])
        sleeps: list[float] = []
        release.verify_registry(
            "testpypi",
            "0.1.5",
            dist,
            attempts=2,
            delay=0.25,
            fetch=lambda _index: next(responses),
            sleep=sleeps.append,
        )
        assert sleeps == [0.25]

    def test_verify_registry_retries_stale_hashes(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)

        def payload(digests: dict[str, str]) -> dict[str, Any]:
            return {
                "releases": {
                    "0.1.5": [
                        {"filename": name, "digests": {"sha256": digest}}
                        for name, digest in digests.items()
                    ]
                }
            }

        responses = iter([payload(dict.fromkeys(hashes, "0" * 64)), payload(hashes)])
        sleeps: list[float] = []
        release.verify_registry(
            "pypi",
            "0.1.5",
            dist,
            attempts=2,
            delay=0.25,
            fetch=lambda _index: next(responses),
            sleep=sleeps.append,
        )
        assert sleeps == [0.25]

    def test_verify_registry_rejects_hash_mismatch(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)
        payload = {
            "releases": {
                "0.1.5": [
                    {"filename": name, "digests": {"sha256": "0" * 64}}
                    for name in hashes
                ]
            }
        }
        with pytest.raises(release.ReleaseError, match="SHA-256 mismatch"):
            release.verify_registry(
                "pypi", "0.1.5", dist, attempts=1, fetch=lambda _index: payload
            )

    def test_verify_registry_rejects_extra_filename(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        hashes = release.distribution_hashes(dist)
        files = [
            {"filename": name, "digests": {"sha256": digest}}
            for name, digest in hashes.items()
        ]
        files.append({"filename": "unexpected.zip", "digests": {"sha256": "x"}})
        payload = {"releases": {"0.1.5": files}}
        with pytest.raises(release.ReleaseError, match="filenames differ"):
            release.verify_registry(
                "pypi", "0.1.5", dist, attempts=1, fetch=lambda _index: payload
            )


class TestCLI:
    def test_write_github_outputs(self, tmp_path: Path) -> None:
        output = tmp_path / "github-output"
        release._write_github_outputs(
            output, release.ReleasePlan(False, "none", "0.1.5")
        )
        assert output.read_text(encoding="utf-8").splitlines() == [
            "publish=false",
            "target=none",
            "version=0.1.5",
            "artifact=veralang-0.1.5",
        ]

    def test_main_prepare_writes_github_outputs(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        def plan(mode: str, **kwargs: Any) -> Any:
            assert mode == "push"
            assert kwargs["before_ref"] == "before"
            return release.ReleasePlan(True, "pypi", "0.1.5")

        monkeypatch.setattr(release, "plan_release", plan)
        output = tmp_path / "github-output"
        assert (
            release.main(
                [
                    "prepare",
                    "--mode",
                    "push",
                    "--before-ref",
                    "before",
                    "--github-output",
                    str(output),
                ]
            )
            == 0
        )
        assert output.read_text(encoding="utf-8").splitlines() == [
            "publish=true",
            "target=pypi",
            "version=0.1.5",
            "artifact=veralang-0.1.5",
        ]

    def test_main_notes(self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(
            release,
            "section_for_version",
            lambda version: release.ChangelogSection(
                version, "2026-07-15", f"- Notes for {version}."
            ),
        )
        output = tmp_path / "release" / "notes.md"
        assert (
            release.main(["notes", "--version", "0.1.5", "--output", str(output)]) == 0
        )
        assert output.read_text(encoding="utf-8") == "- Notes for 0.1.5.\n"

    def test_main_notes_condenses_an_oversized_section(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        notes = "### Fixed\n\n" + "\n".join(
            f"- **Lead {index}.** {'z' * 4000}" for index in range(50)
        )
        monkeypatch.setattr(
            release,
            "section_for_version",
            lambda version: release.ChangelogSection(version, "2026-07-15", notes),
        )
        output = tmp_path / "release" / "notes.md"
        assert (
            release.main(
                [
                    "notes",
                    "--version",
                    "0.1.5",
                    "--output",
                    str(output),
                    "--repo",
                    "aallan/vera",
                ]
            )
            == 0
        )
        written = output.read_text(encoding="utf-8")
        assert len(written) <= release.GITHUB_RELEASE_BODY_LIMIT
        assert "- Lead 49." in written
        assert "z" * 4000 not in written
        assert written.splitlines()[0] == "### Fixed"
        assert written.splitlines()[-1] == _CHANGELOG_LINK

    def test_the_release_workflow_passes_the_repository_to_the_notes_step(self) -> None:
        """The fix is only real if ``release.yml`` consumes the fitted builder."""
        workflow = (
            Path(__file__).parent.parent / ".github" / "workflows" / "release.yml"
        ).read_text(encoding="utf-8")
        # The exact invocation, not a proximity window: a 400-character
        # slice can be satisfied by a `--repo` belonging to a LATER step,
        # and fails on a correct workflow whose `run:` block grows past
        # it.  This gate is the only thing tying the tested builder to the
        # shipped workflow (#1330 review).
        invocation = (
            'python scripts/release.py notes \\\n'
            '            --version "$VERSION" \\\n'
            '            --repo "$GITHUB_REPOSITORY" \\\n'
            "            --output release/RELEASE_NOTES.md"
        )
        assert invocation in workflow, (
            "release.yml no longer invokes the notes builder with --repo; "
            "found:\n"
            + workflow[workflow.find("release.py notes") - 40 :][:400]
        )

    def test_main_manifest(self, tmp_path: Path) -> None:
        dist = _dist(tmp_path)
        output = tmp_path / "release" / "SHA256SUMS"
        assert (
            release.main(["manifest", "--dist-dir", str(dist), "--output", str(output)])
            == 0
        )
        assert output.read_text(encoding="utf-8").splitlines() == [
            f"{digest}  {name}"
            for name, digest in sorted(release.distribution_hashes(dist).items())
        ]

    def test_main_assert_absent(self, monkeypatch: pytest.MonkeyPatch) -> None:
        calls: list[tuple[str, str]] = []
        monkeypatch.setattr(
            release,
            "assert_version_absent",
            lambda index, version: calls.append((index, version)),
        )
        assert (
            release.main(["assert-absent", "--index", "testpypi", "--version", "0.1.5"])
            == 0
        )
        assert calls == [("testpypi", "0.1.5")]

    def test_main_verify_registry(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        calls: list[tuple[str, str, Path]] = []
        monkeypatch.setattr(
            release,
            "verify_registry",
            lambda index, version, dist: calls.append((index, version, dist)),
        )
        dist = tmp_path / "dist"
        assert (
            release.main(
                [
                    "verify-registry",
                    "--index",
                    "pypi",
                    "--version",
                    "0.1.5",
                    "--dist-dir",
                    str(dist),
                ]
            )
            == 0
        )
        assert calls == [("pypi", "0.1.5", dist)]
