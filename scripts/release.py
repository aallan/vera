#!/usr/bin/env python
"""Plan, validate, and verify Vera package releases.

The GitHub Actions release workflow deliberately keeps policy in this tested
Python helper instead of embedding it in shell conditionals.  Nothing in this
module uploads files or mutates git state.
"""

from __future__ import annotations

import argparse
from collections.abc import Callable, Sequence
from dataclasses import dataclass
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib
from typing import Any
from urllib.error import HTTPError
from urllib.request import Request, urlopen


ROOT = Path(__file__).resolve().parent.parent
PROJECT = "veralang"
REPOSITORY = "aallan/vera"
INDEX_JSON_URLS = {
    "pypi": f"https://pypi.org/pypi/{PROJECT}/json",
    "testpypi": f"https://test.pypi.org/pypi/{PROJECT}/json",
}
PACKAGE_AFFECTING_PATHS = ("LICENSE", "PYPI_README.md", "pyproject.toml", "vera")
_VERSION_RE = re.compile(r"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$")

# GitHub refuses a release body over 125,000 characters with HTTP 422, and the
# release workflow reaches that step AFTER the immutable PyPI upload and AFTER
# the tag is cut (#1288).  The builder is therefore total: oversized notes are
# condensed rather than allowed to fail the step.
GITHUB_RELEASE_BODY_LIMIT = 125_000
RELEASE_BODY_BUDGET = 120_000
_SECTION_HEADING_RE = re.compile(r"^### .+$")
_BULLET_LEAD_RE = re.compile(r"^- \*\*(?P<lead>.+?)\*\*")
_BULLET_RE = re.compile(r"^-\s+(?P<text>\S.*)$")
_ISSUE_LINK_RE = re.compile(r"\[#\d+\]\(https://github\.com/[^\s)]+\)")


class ReleaseError(ValueError):
    """A release invariant was not satisfied."""


@dataclass(frozen=True)
class ReleasePlan:
    """The result consumed by the release workflow's downstream jobs."""

    publish: bool
    target: str
    version: str


def parse_version(value: str) -> tuple[int, int, int]:
    """Parse Vera's strict ``X.Y.Z`` release format."""
    match = _VERSION_RE.fullmatch(value)
    if match is None:
        raise ReleaseError(f"invalid release version {value!r}; expected X.Y.Z")
    return tuple(int(part) for part in match.groups())  # type: ignore[return-value]


def _project_from_pyproject(text: str, source: str) -> tuple[str, str]:
    try:
        data = tomllib.loads(text)
        name = data["project"]["name"]
        value = data["project"]["version"]
    except (KeyError, TypeError, tomllib.TOMLDecodeError) as exc:
        raise ReleaseError(f"{source}: cannot read project identity: {exc}") from exc
    if not isinstance(name, str) or not isinstance(value, str):
        raise ReleaseError(f"{source}: project name and version must be strings")
    parse_version(value)
    return name, value


def project_version(root: Path = ROOT) -> str:
    """Return the current checkout's project version."""
    path = root / "pyproject.toml"
    name, version = _project_from_pyproject(path.read_text(encoding="utf-8"), str(path))
    if name != PROJECT:
        raise ReleaseError(f"{path}: project name is {name!r}, expected {PROJECT!r}")
    return version


def _git(args: Sequence[str], root: Path = ROOT, *, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if check and result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip()
        raise ReleaseError(f"git {' '.join(args)} failed: {detail}")
    return result.stdout.strip()


def version_at_ref(ref: str, root: Path = ROOT) -> str:
    """Read ``[project].version`` from ``pyproject.toml`` at a git ref."""
    text = _git(["show", f"{ref}:pyproject.toml"], root)
    _name, version = _project_from_pyproject(text, f"{ref}:pyproject.toml")
    return version


@dataclass(frozen=True)
class ChangelogSection:
    """One release section of ``CHANGELOG.md``, with its heading date."""

    version: str
    date: str | None
    notes: str


def changelog_section(text: str, version: str) -> ChangelogSection:
    """Extract a non-empty, bullet-bearing release section and its date."""
    parse_version(version)
    heading = re.compile(
        rf"^## \[{re.escape(version)}\](?: - (?P<date>[0-9]{{4}}-[0-9]{{2}}-[0-9]{{2}}))?\s*$",
        re.MULTILINE,
    )
    match = heading.search(text)
    if match is None:
        raise ReleaseError(f"CHANGELOG.md has no ## [{version}] release section")
    next_heading = re.search(r"^## \[", text[match.end() :], re.MULTILINE)
    end = match.end() + next_heading.start() if next_heading else len(text)
    notes = text[match.end() : end].strip()
    if not notes or re.search(r"^-\s+\S", notes, re.MULTILINE) is None:
        raise ReleaseError(
            f"CHANGELOG.md section [{version}] must contain at least one bullet"
        )
    return ChangelogSection(version, match.group("date"), notes)


def changelog_notes(text: str, version: str) -> str:
    """Extract a non-empty, bullet-bearing release section."""
    return changelog_section(text, version).notes


def section_for_version(version: str, root: Path = ROOT) -> ChangelogSection:
    """Read one release section from the checkout's changelog."""
    return changelog_section(
        (root / "CHANGELOG.md").read_text(encoding="utf-8"), version
    )


def notes_for_version(version: str, root: Path = ROOT) -> str:
    """Extract release notes from the checkout's changelog."""
    return section_for_version(version, root).notes


def changelog_anchor(version: str, date: str | None) -> str:
    """Return GitHub's heading anchor for a ``## [version] - date`` line."""
    heading = f"[{version}]" + (f" - {date}" if date else "")
    slug = "".join(
        character
        for character in heading.lower()
        if character.isalnum() or character in "- "
    )
    return "#" + slug.replace(" ", "-")


def _index_line(bullet: str) -> str:
    """Condense one CHANGELOG bullet to its headline-index line.

    The lead-in is the bullet's bold run, de-emphasised, and the reference is
    the bullet's LAST issue or pull-request link — the rule that reproduces
    the v0.1.10 manual recovery, whose attribution for at least one bullet sat
    mid-prose rather than immediately after the bold run.  A bullet with no
    bold run keeps its own text, so no bullet is ever dropped from the index.
    """
    lead_match = _BULLET_LEAD_RE.match(bullet)
    if lead_match is not None:
        lead = lead_match.group("lead")
    else:
        plain = _BULLET_RE.match(bullet)
        if plain is None:  # pragma: no cover - callers filter on _BULLET_RE
            raise ReleaseError(f"not a changelog bullet: {bullet!r}")
        lead = plain.group("text")
    links = _ISSUE_LINK_RE.findall(bullet)
    return f"- {lead} ({links[-1]})" if links else f"- {lead}"


def condense_notes(
    section: ChangelogSection,
    *,
    repo: str = REPOSITORY,
    budget: int = RELEASE_BODY_BUDGET,
    limit: int = GITHUB_RELEASE_BODY_LIMIT,
) -> str:
    """Rewrite a release section as the headline index plus a CHANGELOG link.

    The shape is the one the v0.1.10 release was completed by hand with: the
    section's ``###`` subsection headers, one condensed line per bullet, and a
    link to the canonical section at the tag — the CHANGELOG being the release
    notes of record either way.
    """
    anchor = changelog_anchor(section.version, section.date)
    dated = f"[{section.version}]" + (f" - {section.date}" if section.date else "")
    # Worded against the threshold that actually fired.  Condensing starts
    # at the budget, not at the hard limit, so a section in the band
    # between them was published saying it was "past GitHub's
    # 125,000-character limit" while being comfortably under it — a
    # falsehood shipped verbatim in the release body (#1330 review).
    preamble = (
        f"The full release notes for this version are {len(section.notes):,} "
        f"characters, past the {budget:,}-character budget this project "
        f"publishes verbatim — GitHub's own limit is {limit:,} characters — so "
        "this body carries the headline index and the canonical notes live in the "
        f"CHANGELOG at the tag: **[CHANGELOG.md § {dated}]"
        f"(https://github.com/{repo}/blob/v{section.version}/CHANGELOG.md{anchor})**"
    )

    lines: list[str] = []
    bullets = 0
    for line in section.notes.splitlines():
        if _SECTION_HEADING_RE.match(line):
            lines.append("")
            lines.append(line)
        elif _BULLET_RE.match(line):
            lines.append(_index_line(line))
            bullets += 1
    if not bullets:
        raise ReleaseError(
            f"release section [{section.version}] condensed to no bullets"
        )
    return preamble + "\n" + "\n".join(lines).rstrip() + "\n"


def release_body(
    section: ChangelogSection,
    *,
    repo: str = REPOSITORY,
    budget: int = RELEASE_BODY_BUDGET,
    limit: int = GITHUB_RELEASE_BODY_LIMIT,
) -> str:
    """Return a release body that always fits GitHub's limit (#1288).

    Within budget the section is published verbatim.  Past it the section is
    condensed, and in the pathological case where even the index overflows the
    index is truncated — the step must never be the thing that fails after the
    immutable archives are already on PyPI.
    """
    if len(section.notes) <= budget:
        return section.notes
    condensed = condense_notes(section, repo=repo, budget=budget, limit=limit)
    if len(condensed) <= limit:
        return condensed
    notice = (
        f"\n\n_This index is truncated at {limit:,} characters; "
        "the CHANGELOG link above carries every entry._\n"
    )
    kept = condensed[: limit - len(notice)]
    cut = kept.rfind("\n")
    return (kept[:cut] if cut > 0 else kept.rstrip()) + notice


def tag_exists(version: str, root: Path = ROOT) -> bool:
    """Return whether the immutable release tag already exists locally."""
    parse_version(version)
    result = subprocess.run(
        ["git", "show-ref", "--verify", "--quiet", f"refs/tags/v{version}"],
        cwd=root,
        check=False,
    )
    return result.returncode == 0


def version_introduction_commit(version: str, root: Path = ROOT) -> str:
    """Find the first-parent commit that introduced ``version`` on main."""
    parse_version(version)
    commits = _git(["rev-list", "--first-parent", "HEAD"], root).splitlines()
    for commit in commits:
        if version_at_ref(commit, root) != version:
            continue
        parents = _git(["rev-list", "--parents", "-n", "1", commit], root).split()
        if len(parents) == 1 or version_at_ref(parents[1], root) != version:
            return commit
    raise ReleaseError(f"cannot find the commit that introduced version {version}")


def package_changes_since(commit: str, root: Path = ROOT) -> list[str]:
    """List changes that would alter package metadata or installed code."""
    output = _git(
        ["diff", "--name-only", f"{commit}..HEAD", "--", *PACKAGE_AFFECTING_PATHS],
        root,
    )
    return output.splitlines() if output else []


def plan_release(
    mode: str,
    *,
    before_ref: str | None = None,
    ref_name: str | None = None,
    confirm_version: str | None = None,
    root: Path = ROOT,
) -> ReleasePlan:
    """Validate an event and return the release workflow plan.

    The version is read from `pyproject.toml`, the one place it is
    written; a release also needs its `## [X.Y.Z]` CHANGELOG section.
    """
    current = project_version(root)

    if mode == "push":
        if not before_ref:
            raise ReleaseError("push planning requires --before-ref")
        previous = version_at_ref(before_ref, root)
        if current == previous:
            return ReleasePlan(False, "none", current)
        if parse_version(current) <= parse_version(previous):
            raise ReleaseError(
                f"version must increase on main: {previous} -> {current} is invalid"
            )
        target = "pypi"
    elif mode == "testpypi":
        if confirm_version != current:
            raise ReleaseError(
                f"confirmation {confirm_version!r} does not match version {current}"
            )
        target = "testpypi"
    elif mode == "production-recovery":
        if ref_name != "refs/heads/main":
            raise ReleaseError("production recovery is allowed only from main")
        if confirm_version != current:
            raise ReleaseError(
                f"confirmation {confirm_version!r} does not match version {current}"
            )
        introduced = version_introduction_commit(current, root)
        changes = package_changes_since(introduced, root)
        if changes:
            raise ReleaseError(
                "production recovery is blocked by package-affecting changes after "
                f"the version bump: {', '.join(changes)}"
            )
        target = "pypi"
    else:
        raise ReleaseError(f"unknown release mode {mode!r}")

    notes_for_version(current, root)
    if target == "pypi" and tag_exists(current, root):
        raise ReleaseError(f"immutable tag v{current} already exists")
    return ReleasePlan(True, target, current)


def distribution_hashes(dist_dir: Path) -> dict[str, str]:
    """Return SHA-256 hashes for exactly one wheel and one sdist."""
    files = sorted(
        path
        for path in dist_dir.iterdir()
        if path.suffix == ".whl" or path.name.endswith(".tar.gz")
    )
    wheels = [path for path in files if path.suffix == ".whl"]
    sdists = [path for path in files if path.name.endswith(".tar.gz")]
    if len(wheels) != 1 or len(sdists) != 1 or len(files) != 2:
        raise ReleaseError(
            f"{dist_dir}: expected exactly one wheel and one sdist; "
            f"found {[path.name for path in files]}"
        )
    return {path.name: sha256(path.read_bytes()).hexdigest() for path in files}


def write_manifest(dist_dir: Path, output: Path) -> None:
    """Write a deterministic SHA-256 manifest for the release archives."""
    hashes = distribution_hashes(dist_dir)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        "".join(f"{digest}  {name}\n" for name, digest in sorted(hashes.items())),
        encoding="utf-8",
    )


def _fetch_registry(index: str) -> dict[str, Any] | None:
    url = INDEX_JSON_URLS[index]
    request = Request(url, headers={"User-Agent": "vera-release-verifier/1"})
    try:
        # The URLs come from INDEX_JSON_URLS, not from input.
        with urlopen(request, timeout=30) as response:
            data = json.load(response)
    except HTTPError as exc:
        if exc.code == 404:
            return None
        raise ReleaseError(f"{index} returned HTTP {exc.code}") from exc
    if not isinstance(data, dict):
        raise ReleaseError(f"{index} returned a non-object JSON response")
    return data


def registry_version_files(
    index: str,
    version: str,
    *,
    fetch: Callable[[str], dict[str, Any] | None] = _fetch_registry,
) -> dict[str, str] | None:
    """Return registry filename-to-SHA mappings, or ``None`` if absent."""
    if index not in INDEX_JSON_URLS:
        raise ReleaseError(f"unknown package index {index!r}")
    parse_version(version)
    payload = fetch(index)
    if payload is None:
        return None
    releases = payload.get("releases")
    if not isinstance(releases, dict):
        raise ReleaseError(f"{index} JSON has no releases object")
    files = releases.get(version)
    if not files:
        return None
    result: dict[str, str] = {}
    for item in files:
        if not isinstance(item, dict):
            raise ReleaseError(f"{index} release {version} has malformed file data")
        filename = item.get("filename")
        digests = item.get("digests")
        digest = digests.get("sha256") if isinstance(digests, dict) else None
        if not isinstance(filename, str) or not isinstance(digest, str):
            raise ReleaseError(f"{index} release {version} lacks filename/SHA-256 data")
        result[filename] = digest
    return result


def assert_version_absent(
    index: str,
    version: str,
    *,
    fetch: Callable[[str], dict[str, Any] | None] = _fetch_registry,
) -> None:
    """Fail rather than overwriting or silently skipping an immutable version."""
    if registry_version_files(index, version, fetch=fetch) is not None:
        raise ReleaseError(f"{PROJECT} {version} already exists on {index}")


def verify_registry(
    index: str,
    version: str,
    dist_dir: Path,
    *,
    attempts: int = 12,
    delay: float = 5.0,
    fetch: Callable[[str], dict[str, Any] | None] = _fetch_registry,
    sleep: Callable[[float], None] = time.sleep,
) -> None:
    """Verify registry filenames and hashes, retrying index propagation."""
    expected = distribution_hashes(dist_dir)
    actual: dict[str, str] | None = None
    for attempt in range(1, attempts + 1):
        actual = registry_version_files(index, version, fetch=fetch)
        if actual == expected:
            break
        if attempt < attempts:
            sleep(delay)
    if actual is None:
        raise ReleaseError(f"{PROJECT} {version} did not appear on {index}")
    if set(actual) != set(expected):
        raise ReleaseError(
            f"{index} filenames differ: expected {sorted(expected)}, got {sorted(actual)}"
        )
    mismatches = [
        name for name, digest in expected.items() if actual.get(name) != digest
    ]
    if mismatches:
        raise ReleaseError(f"{index} SHA-256 mismatch for: {', '.join(mismatches)}")


def _write_github_outputs(path: Path, plan: ReleasePlan) -> None:
    with path.open("a", encoding="utf-8") as output:
        output.write(f"publish={'true' if plan.publish else 'false'}\n")
        output.write(f"target={plan.target}\n")
        output.write(f"version={plan.version}\n")
        output.write(f"artifact={PROJECT}-{plan.version}\n")


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)

    prepare = commands.add_parser("prepare", help="validate and plan a release event")
    prepare.add_argument(
        "--mode", choices=("push", "testpypi", "production-recovery"), required=True
    )
    prepare.add_argument("--before-ref")
    prepare.add_argument("--ref-name")
    prepare.add_argument("--confirm-version")
    prepare.add_argument("--github-output", type=Path, required=True)

    notes = commands.add_parser("notes", help="build a release body that fits")
    notes.add_argument("--version", required=True)
    notes.add_argument("--output", type=Path, required=True)
    notes.add_argument("--repo", default=REPOSITORY)

    manifest = commands.add_parser("manifest", help="write archive SHA-256 values")
    manifest.add_argument("--dist-dir", type=Path, default=Path("dist"))
    manifest.add_argument("--output", type=Path, required=True)

    absent = commands.add_parser("assert-absent", help="require an unpublished version")
    absent.add_argument("--index", choices=tuple(INDEX_JSON_URLS), required=True)
    absent.add_argument("--version", required=True)

    verify = commands.add_parser("verify-registry", help="verify uploaded archives")
    verify.add_argument("--index", choices=tuple(INDEX_JSON_URLS), required=True)
    verify.add_argument("--version", required=True)
    verify.add_argument("--dist-dir", type=Path, default=Path("dist"))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command == "prepare":
            plan = plan_release(
                args.mode,
                before_ref=args.before_ref,
                ref_name=args.ref_name,
                confirm_version=args.confirm_version,
            )
            _write_github_outputs(args.github_output, plan)
            action = f"publish to {plan.target}" if plan.publish else "no release"
            print(f"Release plan for {plan.version}: {action}.")
        elif args.command == "notes":
            section = section_for_version(args.version)
            body = release_body(section, repo=args.repo)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(body.rstrip("\n") + "\n", encoding="utf-8")
            # A pass-through returns the section itself, so length is the
            # signal a reader can check against the printed numbers.
            if len(body) != len(section.notes):
                print(
                    f"Release notes for {args.version} condensed from "
                    f"{len(section.notes):,} to {len(body):,} characters "
                    f"(GitHub's limit is {GITHUB_RELEASE_BODY_LIMIT:,})."
                )
        elif args.command == "manifest":
            write_manifest(args.dist_dir, args.output)
        elif args.command == "assert-absent":
            assert_version_absent(args.index, args.version)
            print(f"{PROJECT} {args.version} is absent from {args.index}.")
        elif args.command == "verify-registry":
            verify_registry(args.index, args.version, args.dist_dir)
            print(
                f"{PROJECT} {args.version} filenames and SHA-256 hashes match on "
                f"{args.index}."
            )
    except (OSError, ReleaseError, subprocess.SubprocessError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
