# CHANGELOG fragments

A pull request records its CHANGELOG entry here, in a file of its own, and not as a bullet under `[Unreleased]` in `CHANGELOG.md`. No two pull requests edit the same line, so they merge in either order. This README is not a fragment, and every tool ignores it.

## File name

- `changelog.d/<issue>.<section>.md` when the pull request closes an issue, `<issue>` being that issue's number: `changelog.d/1529.added.md`.
- `changelog.d/+<slug>.<section>.md` otherwise, `<slug>` being the last path component of the branch name: `changelog.d/+fast-lane.changed.md` for the branch `ci/fast-lane`.

`<section>` is one of `added`, `changed`, `deprecated`, `removed`, `fixed` and `security`, the Keep a Changelog sections. A pull request with bullets in two sections writes two files.

## Content

The bullets exactly as they will appear in `CHANGELOG.md`, in the style of its latest release section: each bullet a line starting with `- `, its sub-bullets and wrapped lines indented by spaces, issue and pull-request links written out as that section writes them, and every `@Type` in backticks. Nothing else: no heading and no blank line, and the file ends with one newline.

## Checks

`scripts/check_changelog_fragments.py` holds every file here to the name and content rules, in the commit hook and in CI's `lint` job. `scripts/check_changelog_updated.py` accepts a fragment the branch adds as the CHANGELOG entry a substantive change needs, and a `Skip-changelog: <reason>` trailer still bypasses it.

## Release

The release pull request runs `python scripts/release.py assemble --version X.Y.Z --date YYYY-MM-DD`. It writes the `## [X.Y.Z] - YYYY-MM-DD` section below a fresh, empty `## [Unreleased]`: the sections in the order above, any bullets still under `[Unreleased]` first in their section, and then the fragments, by issue number and then by slug. It adds the `[X.Y.Z]` compare link, points `[Unreleased]`'s at the new tag, and deletes the fragments it consumed. The release pull request then writes the section's `### Highlights` above its first section, and `scripts/release.py notes` reads the section as before.
