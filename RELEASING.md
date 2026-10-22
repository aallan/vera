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

1. Increase `[project].version` in `pyproject.toml`, the one place the version
   is written, and regenerate `uv.lock` (`uv lock`); `uv lock --check`, in the
   push hook and in CI, holds the two together.
2. Assemble the dated `## [X.Y.Z]` section with
   `python scripts/release.py assemble --version X.Y.Z --date YYYY-MM-DD`.
   It writes the section from the `changelog.d/` fragments and any bullets
   still under `[Unreleased]`, updates the CHANGELOG compare links, and
   deletes the fragments it consumed; a malformed fragment stops it before
   anything is written.  Then write the section's `### Highlights` above its
   first subsection.
3. Add the release's one-line HISTORY entry and regenerate site assets.
4. Regenerate TESTING.md's status — the test totals, the per-file and
   skipped-tests tables, and the tree's counts — with
   `python scripts/render_status.py`, and commit it; confirm with
   `python scripts/check_doc_counts.py --release`.  The same run measures the
   scorecard when it is given `--github`, with `GH_TOKEN` exported, and
   `--junit PATH`, the junit file of one sample-mode run of the suite,
   `python -m pytest -n auto -p tests.subprocess_census --junitxml=PATH`.
   Fix PRs leave the status
   alone, since every one of them moves it.  CI runs that check on the change
   that raises `[project].version`, the same signal `release.yml` publishes on:
   a pull request whose version is higher than its base branch's, and the push
   event its merge produces on `main`, whose version is higher than the commit
   before it (`check_doc_counts.py --release-if-version-raised`).  The same
   answer runs that push's whole test matrix (ci.yml's `plan` job), which the
   push event of any other merge skips.  Every other pull request and push
   checks no count.
5. Reconcile `KNOWN_ISSUES.md`'s Bugs table with the tracker, by running
   `python scripts/check_doc_counts.py --check-bug-issues`.  The convention
   is one row per open `bug`-labelled issue, and the check needs the GitHub
   API — it sends `GH_TOKEN` or `GITHUB_TOKEN` when either is set, and is
   rate limited per IP when neither is, so export one before running it —
   so it is opt-in rather than part of the pre-commit hook: mid-cycle
   the two legitimately disagree, since a bug filed against an open PR's
   branch has an issue before it has a row.  At release time they must
   agree — that is the point at which the file is the published list.
6. Pass the ordinary protected-branch CI and review process.

The release PR merges by merge commit or squash, the only methods the
repository allows: the release reads the version rise against the merge
commit's first parent, which both methods make the pre-merge `main`.

After merge, CI's run on the merge commit runs the full test matrix, and
`release.yml` starts when that run completes. It then:

1. goes on only when that run succeeded, for the push event on `main`, and
   detects the version increase against the merge commit's first parent.
   Every later step reads the commit that run tested, which the first job's
   summary names beside the CI run. Two version-raising merges release one
   at a time, in the order their CI runs complete, which need not be the
   order of the merges, and step 8 marks a release Latest only when no
   higher version is tagged. On a version-raising pull request, re-run failed
   matrix jobs as a set, never one leg: `matrix-gate` reads each cell's latest
   run from the run's job listing, so it stays red while any blocking cell is
   still failed;
2. validates the version, CHANGELOG section, and absence of the version/tag;
3. builds, inspects, installs, and smoke-tests exactly one universal wheel and
   one source distribution in a job without OIDC permission;
4. stores those archives, release notes, and `SHA256SUMS` as one GitHub Actions
   artifact;
5. waits for approval on the `pypi` environment;
6. publishes only the downloaded archives through Trusted Publishing, with
   digital attestations enabled;
7. verifies PyPI exposes exactly those filenames and SHA-256 hashes; and
8. creates `vX.Y.Z` and the GitHub Release at the merge SHA, attaching the same
   archives and checksum manifest, and marks it Latest unless a higher
   `vX.Y.Z` tag exists.

Approve the `pypi` deployment only after checking that the commit the first
job's summary names is the intended release merge and the displayed version is
correct: the run's own commit is `main`'s tip when CI's run completed.

## Failure and recovery

- When CI's run on the release merge fails, re-run its failed jobs. A
  successful re-run completes that run again, and its completion starts the
  release: GitHub's `workflow_run` documentation excludes only the
  `requested` activity from a re-run, and the first live case confirms it.
  A re-run that starts no release, or a fix merged after the release merge,
  is recovered by dispatching **production-recovery**: the fix does not
  raise the version, so its own CI run starts no release, and the recovery
  waits for CI's run on the dispatched commit, at most 180 minutes. Releases
  have started from CI's completion since v0.2.6, whose cut is the first
  live run.
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
