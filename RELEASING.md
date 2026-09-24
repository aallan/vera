# Releasing Vera

Vera publishes the Python distribution `veralang`; the installed command and
Python import package remain `vera`. Releases use GitHub Actions and PyPI
Trusted Publishing. No long-lived PyPI token or repository secret is involved.

The ordinary release signal is a strictly increasing `[project].version` merged
to `main`. The workflow builds and tests one wheel and one source archive,
passes those exact files to an approval-protected OIDC job, verifies their
registry hashes, and only then creates the tag and GitHub Release.

## One-time maintainer setup

Complete this only after `.github/workflows/release.yml` exists on `main`.

### Accounts

On both [PyPI](https://pypi.org/) and
[TestPyPI](https://test.pypi.org/):

1. Verify the maintainer email address.
2. Enable two-factor authentication.
3. Store current recovery codes somewhere independent of the password manager
   session used to perform the release.

### GitHub environments

In **Settings → Environments**, create:

- `testpypi`: allow deployments from `main` and `release/**`; it needs no
  reviewer gate.
- `pypi`: allow deployments from `main` only and require maintainer approval.
  A single-maintainer repository must leave **Prevent self-review** disabled or
  the maintainer who triggered the release cannot approve it.

Do not add registry tokens as environment secrets. The environment names are
part of the OIDC identities configured below.

### Trusted Publishers

TestPyPI and PyPI are separate services and each needs its own publisher. For a
project that does not exist yet, use the account-level **Publishing** page to
add a pending GitHub publisher with these exact fields:

| Field | TestPyPI | PyPI |
|---|---|---|
| PyPI project name | `veralang` | `veralang` |
| Owner | `aallan` | `aallan` |
| Repository | `vera` | `vera` |
| Workflow name | `release.yml` | `release.yml` |
| Environment | `testpypi` | `pypi` |

A pending publisher creates the project on its first successful upload and then
becomes a normal publisher. It does **not** reserve the name. Configure the
production pending publisher close to the first production release, after the
TestPyPI path has been proved.

## Stage the current version on TestPyPI

The manual TestPyPI path exercises the same build, archive inspection, installed
wheel smoke test, artifact handoff, attestations, and registry hash verification
as production. It never creates a production tag or GitHub Release.

1. Open **Actions → Release → Run workflow**.
2. Select `main` (or an allowed `release/**` branch).
3. Choose `testpypi` and type the exact current version into
   `confirm_version`.
4. Confirm that `publish-testpypi` and `verify-testpypi` pass.

For the initial staging run, publish `veralang==0.1.4`. Verify installation
without asking TestPyPI to supply Vera's third-party dependencies:

```bash
python -m venv /tmp/veralang-testpypi
source /tmp/veralang-testpypi/bin/activate
python -m pip download --no-deps \
  --index-url https://test.pypi.org/simple/ \
  --dest /tmp/veralang-testpypi-dist \
  veralang==0.1.4
python -m pip install /tmp/veralang-testpypi-dist/*.whl
vera version
```

TestPyPI versions are immutable too. A repeated dispatch for the same version
fails before upload instead of silently skipping files.

## Ordinary production release

The release-prep PR must:

1. Increase the version in every location gated by
   `scripts/check_version_sync.py` and regenerate `uv.lock`.
2. Turn the accumulated `[Unreleased]` notes into a dated `## [X.Y.Z]`
   section with at least one bullet and update the CHANGELOG compare links.
3. Add the release's one-line HISTORY entry and regenerate site assets.
4. Set the headline test totals to the live collection: the suite total and
   test-file count in `TESTING.md`'s overview row (with its passed /
   stress-deselected / skipped breakdown), `README.md`'s project-status line,
   `FAQ.md`'s by-the-numbers list, `ROADMAP.md`'s "Where we are" line and
   `vera/README.md`'s Test Suite paragraph.  Confirm with
   `python scripts/check_doc_counts.py --release`.  Fix PRs leave these
   alone, since every one of them moves them; CI runs this mode on the
   release PR (a pull request into `main`) and on pushes to `main`.
5. Reconcile `KNOWN_ISSUES.md`'s Bugs table with the tracker, by running
   `python scripts/check_doc_counts.py --check-bug-issues`.  The convention
   is one row per open `bug`-labelled issue, and the check needs the GitHub
   API — it sends `GH_TOKEN` or `GITHUB_TOKEN` when either is set, and is
   rate limited per IP when neither is, so export one before running it —
   so it is opt-in rather than part of the pre-commit hook: mid-cycle
   the two legitimately disagree, since a bug filed against an open PR's
   branch has an issue before it has a row.  At release time they should
   agree — that is the point at which the file is the published list.
6. Pass the ordinary protected-branch CI and review process.

After merge, `release.yml` detects the version increase on `main`. It then:

1. validates the version, CHANGELOG section, and absence of the version/tag;
2. builds, inspects, installs, and smoke-tests exactly one universal wheel and
   one source distribution in a job without OIDC permission;
3. stores those archives, release notes, and `SHA256SUMS` as one GitHub Actions
   artifact;
4. waits for approval on the `pypi` environment;
5. publishes only the downloaded archives through Trusted Publishing, with
   digital attestations enabled;
6. verifies PyPI exposes exactly those filenames and SHA-256 hashes; and
7. creates `vX.Y.Z` and the GitHub Release at the merge SHA, attaching the same
   archives and checksum manifest.

Approve the `pypi` deployment only after checking that the workflow SHA is the
intended release merge and the displayed version is correct.

## Failure and recovery

- Before PyPI accepts files, fix the cause and rerun failed jobs. If the whole
  run can no longer be resumed, **production-recovery** may be dispatched from
  `main` with the exact version. It refuses to run if the version, tag, or
  GitHub Release already exists, or if package-affecting files changed after
  the version-bump merge.
- After PyPI accepts files, do not rerun the whole workflow: the absence guard
  will reject it. Rerun only the failed verification or GitHub Release jobs so
  they continue using the retained, already-published artifact.
- If registry verification reports a filename or hash mismatch, stop. Do not
  create or move a tag while the registry and workflow artifacts disagree.

## Immutable-release policy

PyPI does not permit replacing a distribution file for an existing version.
Vera applies the same rule to every release surface:

- never move a published version tag;
- never replace release archives;
- never amend an already-released CHANGELOG section;
- yank a bad PyPI release rather than deleting or disguising it; and
- ship every post-release fix as a new patch version.

The pre-PyPI fold-in convention is retired. Once `veralang==X.Y.Z` exists, that
version describes one source state and one immutable set of archive hashes.
