#!/usr/bin/env python
"""Burndown instrument: compile every corpus program at two revisions
and report which ones MOVED.

    python scripts/check_corpus_differential.py --base-ref origin/main

**This is not a pre-commit hook and not a CI gate.**  It compiles the
whole corpus twice — once with the working tree's compiler, once with
the compiler at ``--base-ref`` — so a run costs minutes, not the
milliseconds a commit hook may spend.  It is deliberately absent from
``.pre-commit-config.yaml``, and `tests/test_check_corpus_differential.py`
asserts that absence so the claim cannot rot.  Run it by hand when the
question it answers is the one you have.

That question is: **did this change move any compiled output, and if so,
exactly which programs?**  It has two uses, and they are the same
measurement read in opposite directions:

- *Proving a change inert.*  A refactor, a rename, a whitelist
  reshuffle — the claim "codegen is unchanged" is otherwise an argument
  from reading the diff.  Zero movers over the whole corpus is evidence.
  PR #1323 made exactly this claim with an ad-hoc version of this
  script; promoting it means the next such claim is reproducible rather
  than re-improvised.
- *Enumerating what a change moved.*  When output is meant to change,
  the mover list is the scope of the change, program by program —
  including the programs nobody expected it to reach.

The comparison surface is the **WAT text** (`vera compile --wat`), which
is what "byte-identical WAT" meant in the PR #1323 record, compared by
SHA-256 digest.  Four verdicts per program, from two compiles:

| base      | head      | verdict                       |
|-----------|-----------|-------------------------------|
| same WAT  | same WAT  | not a mover                   |
| WAT A     | WAT B     | mover — `WAT differs`         |
| failed    | compiled  | mover — `compiles only at HEAD` |
| compiled  | failed    | mover — `compiles only at <base>` |
| failed    | failed    | not a mover, counted separately |

The two one-sided-failure rows are the reason this is not a `diff` over
saved WAT files.  A program whose compilability *reverses* has no WAT on
one side, and a comparison that only knows "same text / different text"
reports that as a text difference — which is the class the PR #1323
record called out as having been mis-described.  They are distinct
verdicts here, and each names the direction.

The both-failed row is counted and printed rather than folded into
agreement.  The corpus deliberately contains negative fixtures that fail
to compile at every revision; they agree vacuously, and a reader of a
green run is entitled to know how much of it was actually measured.

**How the two sides are built.**  The corpus is the *working tree's*
`.vera` files, and *both* sides compile those same files — only the
compiler differs.  That isolates a compiler change from a corpus change:
a program edited in the working tree is compiled from its edited text on
both sides, so it moves only if the compiler moved under it.  A program
using a feature the base compiler lacks shows up as `compiles only at
HEAD`, which is the true verdict.

The head side is the working tree as it stands, uncommitted edits
included.  The base side is materialised with ``git worktree add
--detach`` into ``--work-dir`` and driven through its *own* checkout: the
subprocess runs with ``cwd`` and ``PYTHONPATH`` set to that directory, so
``python -m vera.cli`` there resolves ``vera`` to the base revision's
package.  Each side is probed first (`canary_error`) to confirm it
imported the compiler it was supposed to: the venv may carry an editable
install of a *third* checkout, and a side that silently resolved to it
would compare a revision against itself and report zero movers —
a green verdict that measured nothing.

**The base checkout is left on disk.**  It is keyed by the base commit's
SHA and reused by later runs against the same revision, so repeated runs
pay for one checkout per revision rather than one per run.  Its path is
printed on every run.  Removing it is the caller's business:

    git worktree remove <printed path>   # or: git worktree prune

Requires the base revision's compiler to run under the *current* venv's
installed dependencies — the base checkout supplies `vera/`, not its own
site-packages.  Across a dependency bump this instrument compares what
the current environment can run, which is worth knowing before reading
its verdict.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path, PurePath
from typing import NamedTuple


# The corpus: everything `vera check` can reach under these roots, at any
# depth.  `examples/vera/` and `tests/conformance/vera/` hold the modules
# the top-level programs import — a non-recursive glob would compare a
# program while ignoring the source it is built from, the gap
# `scripts/check_corpus_canonical.py` records having had.
_CORPUS_DIRS = ("examples", "tests/conformance")

# The base checkout's default home.  Repository-local rather than under
# `tempfile.gettempdir()`: the path is fully predictable (a fixed directory
# name plus a public commit SHA), `base_checkout` reuses a pre-existing
# directory, and `_side_env` then puts it on PYTHONPATH — so on a shared
# machine another local user could plant a `vera` package there and the base
# side would import it.  The canary cannot object, because the planted
# package sits under the expected root (#1329 review).
_DEFAULT_WORK_DIR = Path(__file__).resolve().parent.parent / ".corpus-differential"


def _positive_seconds(value: str) -> int:
    """An `argparse` type for a budget that must be able to elapse.

    Zero or negative expires before any compile finishes, so both sides
    fail every program, `compare` counts them all as `both_failed`, and
    the run reports "No movers" over a corpus that never compiled.
    """
    seconds = int(value)
    if seconds <= 0:
        raise argparse.ArgumentTypeError(
            f"--timeout must be greater than zero, not {seconds}"
        )
    return seconds


# Per-file compile budget.  Generous — a corpus program compiles in well
# under a second — so this only fires on a genuine hang, and a hang on
# one side is reported as that side failing rather than blocking the run.
DEFAULT_TIMEOUT_SECONDS = 120

# The first line of a Vera error diagnostic: `[E154] Error at <file>,
# line N, column M:` — or the same without a code, which a few carry.
# Anchored so a warning's message body, which quotes neither, cannot
# match.
_ERROR_MARKER = re.compile(r"^(\[E\d+\]\s*)?Error\b")


# ---------------------------------------------------------------------------
# Data
# ---------------------------------------------------------------------------

# ``NamedTuple`` rather than ``@dataclass`` throughout: this module is
# loaded by its tests with the bare ``spec_from_file_location`` /
# ``exec_module`` recipe, which leaves the module unregistered in
# ``sys.modules`` — and ``@dataclass`` resolves its annotations through
# ``sys.modules[cls.__module__]``.  Same reason as
# `scripts/check_examples_run.py`.


class Artifact(NamedTuple):
    """One program's compiled output at one revision.

    ``digest`` is the SHA-256 of the WAT text and is ``None`` exactly
    when ``ok`` is False — there is no artifact to compare, and the
    reason lives in ``error``.
    """

    ok: bool
    digest: str | None
    size: int
    error: str


class Mover(NamedTuple):
    """A program whose compiled output changed between the revisions."""

    path: str
    kind: str
    reason: str


class Comparison(NamedTuple):
    """The whole corpus, classified.

    ``compared`` counts the programs both sides reported on, and
    partitions exactly into ``identical + both_failed + len(movers)``.
    ``unreported`` holds programs only one side reported on at all — a
    truncated run, which is a failure rather than a quiet shortfall.
    """

    movers: list[Mover]
    compared: int
    identical: int
    both_failed: int
    unreported: list[str]


class RunInfo(NamedTuple):
    """What the run compared, for the report and the JSON envelope."""

    base_ref: str
    base_sha: str
    base_root: str
    head_root: str


# ---------------------------------------------------------------------------
# The corpus
# ---------------------------------------------------------------------------


def corpus_files(root: Path) -> list[Path]:
    """Every corpus program under `root`, at any depth, in path order."""
    files: list[Path] = []
    for directory in _CORPUS_DIRS:
        files.extend(sorted((root / directory).rglob("*.vera")))
    return files


def corpus_guard(files: list[Path], root: Path) -> str | None:
    """Refuse to run on an empty corpus; ``None`` when there is one.

    A differential over zero programs finds zero movers, and zero movers
    is this instrument's success verdict — so an enumeration that stops
    matching would report "nothing moved" over nothing at all, which is
    the single failure mode most likely to be believed.
    """
    if files:
        return None
    return (
        f"could not find any .vera programs under {root} "
        f"({', '.join(_CORPUS_DIRS)}).  This is an error rather than a "
        f"clean run: a differential over an empty corpus reports zero "
        f"movers, which is indistinguishable from a change that moved "
        f"nothing."
    )


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------


def classify(
    base: Artifact, head: Artifact, base_label: str
) -> tuple[str, str] | None:
    """``(kind, reason)`` when this program moved, ``None`` when it did
    not.

    Compilability is checked before the digests, because a program that
    compiles at only one revision has no artifact to compare and must be
    named for the *direction* it moved in — reporting it as a text
    difference is the mis-description PR #1323's record calls out.
    """
    if base.ok and head.ok:
        if base.digest == head.digest:
            return None
        return (
            "wat-differs",
            f"WAT differs (at {base_label}: {_short(base.digest)}, "
            f"{base.size} bytes; at HEAD: {_short(head.digest)}, "
            f"{head.size} bytes)",
        )

    if head.ok and not base.ok:
        return (
            "head-only",
            f"compiles only at HEAD (at {base_label} it failed: "
            f"{base.error})",
        )

    if base.ok and not head.ok:
        return (
            "base-only",
            f"compiles only at {base_label} (at HEAD it failed: "
            f"{head.error})",
        )

    # Neither side produced an artifact — the negative conformance
    # fixtures live here.  Not a mover; counted separately by `compare`
    # so the agreement it contributes is never read as measurement.
    return None


def _short(digest: str | None) -> str:
    return "none" if digest is None else digest[:12]


def compare(
    base: dict[str, Artifact], head: dict[str, Artifact], base_label: str
) -> Comparison:
    """Classify every program both sides reported on."""
    movers: list[Mover] = []
    identical = 0
    both_failed = 0
    compared = 0

    for path in sorted(set(base) & set(head)):
        compared += 1
        verdict = classify(base[path], head[path], base_label)
        if verdict is not None:
            movers.append(Mover(path=path, kind=verdict[0], reason=verdict[1]))
        elif not base[path].ok and not head[path].ok:
            both_failed += 1
        else:
            identical += 1

    return Comparison(
        movers=movers,
        compared=compared,
        identical=identical,
        both_failed=both_failed,
        unreported=sorted(set(base) ^ set(head)),
    )


# ---------------------------------------------------------------------------
# Compiling one side
# ---------------------------------------------------------------------------


def canary_error(reported: str, root: Path, side: str) -> str | None:
    """The load-bearing guard: did this side import the compiler it was
    pointed at?

    Both sides run the same ``python -m vera.cli`` and differ only in
    ``PYTHONPATH``/``cwd``.  The venv also carries an editable install of
    whichever checkout was `pip install -e`'d, reachable through a
    finder on ``sys.meta_path``.  A side that resolved to *that* would
    compile with the wrong compiler, and the run would report zero
    movers no matter what the change did.
    """
    if not reported.strip():
        return (
            f"the {side} side could not import `vera` at all from {root} "
            f"— the differential cannot run.  Check that the checkout is "
            f"intact and that the current environment satisfies its "
            f"dependencies."
        )

    resolved = Path(reported.strip()).resolve()
    expected = root.resolve()
    if resolved == expected or expected in resolved.parents:
        return None

    return (
        f"the {side} side imported {reported.strip()}, which is not under "
        f"{root} — it is compiling with a different checkout's compiler, "
        f"so the differential would compare a revision against itself and "
        f"report zero movers.  Usually an editable install shadowing the "
        f"path, or a stale PYTHONPATH."
    )


def _side_env(root: Path) -> dict[str, str]:
    """The environment one side's compiles run under.

    ``PYTHONPATH`` is *replaced*, never extended: the caller's own
    ``PYTHONPATH`` frequently points at the head checkout (that is how
    this repo is driven), and inheriting it on the base side would put
    the head compiler first on the path — the exact vacuity
    `canary_error` exists to catch.
    """
    env = dict(os.environ)
    env["PYTHONPATH"] = str(root)
    # No .pyc into either checkout: the base one is a scratch worktree,
    # and stale bytecode across revisions has bitten this project before.
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env


def probe_compiler(python: str, root: Path) -> str:
    """Where this side's `vera` package actually resolves to, or ``""``."""
    result = subprocess.run(
        [python, "-c", "import vera, sys; sys.stdout.write(vera.__file__)"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        cwd=str(root),
        env=_side_env(root),
        check=False,
    )
    return result.stdout if result.returncode == 0 else ""


def _first_error(stderr: str, path: PurePath) -> str:
    """The compile's reason, in one line.

    A Vera diagnostic is a *block* — marker line, quoted source, caret,
    message — and only the first line carries the marker.  Skipping
    lines that start with ``warning:`` is therefore not enough to skip a
    warning: a real run against v0.1.9 reported a warning's quoted
    source line (``public fn read_some(@Unit -> @Int)``) as the reason a
    program failed to compile.  The error's own marker line is what to
    look for.

    With no marker anywhere the compile did not produce a diagnostic at
    all — it crashed.  The informative line of a traceback (and of an
    argparse usage error) is the last, not the first.

    The program's own path is stripped back to its name: the reason is
    already attached to a named program, and a corpus file's absolute
    path under a scratch checkout is long enough on its own to push the
    diagnostic past the truncation.

    Both spellings of that path are stripped.  Matching on ``str(path)``
    alone ties the strip to the host's separator, and a diagnostic is
    free to print the POSIX form on Windows — whereupon the strip
    matches nothing, silently, and the truncation eats the message
    instead of the path.  The parameter is a ``PurePath`` rather than a
    ``Path`` for the same reason: nothing here touches the filesystem,
    and the wider type lets a test render a Windows path on any host.
    """
    lines = [line.strip() for line in stderr.splitlines()]
    nonempty = [line for line in lines if line]

    for line in nonempty:
        if _ERROR_MARKER.match(line):
            reason = line
            break
    else:
        reason = nonempty[-1] if nonempty else "compile failed with no output"

    for rendering in (str(path), path.as_posix()):
        reason = reason.replace(rendering, path.name)
    return reason[:160]


def compile_one(
    python: str, compiler_root: Path, timeout: int, path: Path
) -> Artifact:
    """Compile one program with one side's compiler.

    Deliberately the CLI rather than the codegen API: ``vera compile
    --wat`` is the surface that holds its shape across revisions, and
    this script runs unchanged against a compiler whose internals it may
    predate.  A failure is *data* — the failure-direction verdicts are
    half of what the instrument measures — so nothing here raises.
    """
    try:
        result = subprocess.run(
            [python, "-m", "vera.cli", "compile", "--wat", str(path)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            # A compiler is free to emit a byte this codec cannot read, and
            # strict decoding would raise UnicodeDecodeError out of
            # `subprocess.run` — a ValueError that neither handler below
            # catches, aborting the whole corpus run through
            # `ThreadPoolExecutor.map`.  An undecodable diagnostic is data
            # like any other failure (#1329 review).
            errors="replace",
            cwd=str(compiler_root),
            env=_side_env(compiler_root),
            stdin=subprocess.DEVNULL,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return Artifact(
            ok=False, digest=None, size=0,
            error=f"compile exceeded the {timeout}s budget",
        )
    except OSError as exc:  # the interpreter or checkout is not usable
        return Artifact(
            ok=False, digest=None, size=0, error=f"could not run: {exc}",
        )

    if result.returncode != 0:
        return Artifact(
            ok=False, digest=None, size=0,
            error=_first_error(result.stderr, path),
        )

    wat = result.stdout
    digest = hashlib.sha256(wat.encode("utf-8")).hexdigest()
    return Artifact(ok=True, digest=digest, size=len(wat), error="")


def collect(
    files: list[Path],
    corpus_root: Path,
    compile_fn: Callable[[Path], Artifact],
    jobs: int = 1,
) -> dict[str, Artifact]:
    """Compile every file, keyed by its path relative to `corpus_root`.

    Both sides compile the *same* files — the working tree's — so both
    maps are keyed against the same root and line up by construction.
    An absolute key would not: the base compiler runs from a scratch
    checkout, and keying by anything side-specific would leave every
    program unreported.  POSIX form because the key is compared as a
    string (CLAUDE.md's cross-platform rule).
    """
    keys = [_key(path, corpus_root) for path in files]
    if jobs <= 1:
        results = [compile_fn(path) for path in files]
    else:
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            # `map` yields in input order, so the zip below cannot
            # misattribute a result to the wrong program.
            results = list(pool.map(compile_fn, files))
    return dict(zip(keys, results, strict=True))


def _key(path: Path, corpus_root: Path) -> str:
    try:
        return path.relative_to(corpus_root).as_posix()
    except ValueError:
        return path.as_posix()


# ---------------------------------------------------------------------------
# The base checkout
# ---------------------------------------------------------------------------


def resolve_ref(repo_root: Path, ref: str) -> str | None:
    """The commit SHA `ref` names, or ``None`` when git cannot resolve it."""
    result = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", "--verify", f"{ref}^{{commit}}"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )
    return result.stdout.strip() if result.returncode == 0 else None


def base_checkout(
    repo_root: Path, sha: str, work_dir: Path
) -> tuple[Path | None, str]:
    """A checkout of `sha`, materialised under `work_dir` if need be.

    Returns ``(path, "")`` or ``(None, error)``.  Named by SHA and reused
    when it is already there, so a session running the differential
    repeatedly against one base under ``--keep-base`` pays for one checkout.

    Removed by :func:`release_base_checkout` when the run ends, unless
    ``--keep-base`` (#1374): what it leaves behind is a full second copy of
    the repository INSIDE the repository, and the doc-surface walk in
    ``scripts/check_doc_builtin_shadowing.py`` read that copy's ``spec/`` as
    an authored surface of this one — so running the documented instrument
    turned ``pytest tests/`` red.  That walk now prunes nested checkouts as
    well; both halves are kept, because either alone leaves the other's
    failure mode reachable by a renamed ``--work-dir`` or by a `--keep-base`
    session.
    """
    dest = work_dir / f"vera-base-{sha[:12]}"

    if dest.exists():
        current = subprocess.run(
            ["git", "-C", str(dest), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=False,
        )
        status = subprocess.run(
            ["git", "-C", str(dest), "status", "--porcelain"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=False,
        )
        # The tree must be CLEAN, not merely at the right commit.  A
        # reused checkout is persistent by design, so an edit made under
        # it — a stray debug print, an abandoned bisect — survives to the
        # next run and silently becomes the base compiler.  `rev-parse`
        # cannot see that, and neither can the canary: it proves which
        # checkout was imported, and a modified one is still that
        # checkout.  A dirty base makes "0 movers" mean nothing and can
        # invent movers out of the edit, which is the one failure this
        # instrument must not have.  The message below has always
        # promised "a clean checkout"; this is what makes it true
        # (#1330 review).
        if (
            current.returncode == 0
            and current.stdout.strip() == sha
            and (dest / "vera" / "__init__.py").is_file()
            and status.returncode == 0
            and not status.stdout.strip()
        ):
            return dest, ""
        return None, (
            f"{dest} already exists but is not a clean checkout of {sha[:12]} "
            f"— this script never deletes it.  Move it aside, or pass a "
            f"different --work-dir."
        )

    work_dir.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(
        ["git", "-C", str(repo_root), "worktree", "add", "--detach",
         str(dest), sha],
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if result.returncode != 0:
        return None, (
            f"could not create a worktree for {sha[:12]} at {dest}: "
            f"{result.stderr.strip() or result.stdout.strip()}"
        )
    return dest, ""


def release_base_checkout(repo_root: Path, base_root: Path) -> None:
    """Remove the worktree :func:`base_checkout` created (#1374).

    Through ``git worktree remove``, not a directory delete: the checkout was
    created with ``git worktree add``, so the repository's worktree registry
    holds an entry for it, and removing the directory alone would leave that
    entry behind as a stale record the next run's cleanliness check cannot
    see.

    BEST EFFORT, deliberately.  The verdict this script exists to report is
    already computed by the time this runs, and losing it to a housekeeping
    error would be a worse failure than a leftover directory — which the
    doc-surface walk now prunes anyway.  A checkout this cannot remove is
    reported by the next run's own cleanliness check, which already refuses
    a dirty or mismatched reuse.
    """
    try:
        subprocess.run(
            ["git", "-C", str(repo_root), "worktree", "remove", "--force",
             str(base_root)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=False,
        )
    except OSError:
        # `check=False` suppresses a non-zero EXIT, not a failure to start the
        # process at all (PR #1372 review).  A missing `git`, an exhausted
        # descriptor table or a permission error raises here, and this runs
        # from a `finally` — so the exception would replace the verdict the
        # whole run exists to produce with a traceback.  Best effort means
        # best effort at the Python boundary too; a checkout this cannot
        # remove is caught by the next run's own cleanliness check.
        pass


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


def json_payload(info: RunInfo, comparison: Comparison) -> dict[str, object]:
    return {
        "ok": not comparison.movers and not comparison.unreported,
        "base_ref": info.base_ref,
        "base_sha": info.base_sha,
        "base_root": info.base_root,
        "head_root": info.head_root,
        "compared": comparison.compared,
        "identical": comparison.identical,
        "both_failed": comparison.both_failed,
        "movers": [m._asdict() for m in comparison.movers],
        "unreported": comparison.unreported,
    }


def summary_lines(info: RunInfo, comparison: Comparison) -> list[str]:
    """The stdout summary — what was compared, and how it partitioned."""
    return [
        f"Corpus differential: {comparison.compared} programs compiled at "
        f"both revisions.",
        f"  base: {info.base_ref} ({info.base_sha[:12]}) -> {info.base_root}",
        f"  head: working tree -> {info.head_root}",
        f"  identical WAT: {comparison.identical}",
        f"  compiled at neither revision: {comparison.both_failed} "
        f"(vacuous agreement — nothing was compared for these)",
        f"  movers: {len(comparison.movers)}",
    ]


def failure_lines(info: RunInfo, comparison: Comparison) -> list[str]:
    """The stderr report: every mover, then what to do about it."""
    lines: list[str] = []
    if comparison.movers:
        lines.append(f"MOVERS ({len(comparison.movers)}):")
        lines += [f"  {m.path}: {m.reason}" for m in comparison.movers]
        lines += [
            "",
            "Each line is a program whose compiled output changed between "
            f"{info.base_ref} and the working tree.  If the change under "
            "test was meant to be inert, these are its counter-examples; if "
            "it was meant to move output, this is the enumeration of what "
            "it moved.  Reproduce one with:",
            "",
            "  vera compile --wat <program>            # working tree",
            f"  (cd {info.base_root} && vera compile --wat "
            f"{info.head_root}/<program>)",
            "",
            "<program> is the mover's path above, and BOTH commands compile "
            "the working tree's copy of it — that is what the differential "
            "compared.  A relative path in the second command would compile "
            "the base checkout's own copy instead, which is a different "
            "input whenever the corpus source has changed.",
        ]
    if comparison.unreported:
        if lines:
            lines.append("")
        lines.append(f"UNREPORTED ({len(comparison.unreported)}):")
        lines += [f"  {path}" for path in comparison.unreported]
        lines += [
            "",
            "The two sides did not report on the same set of programs, so "
            "the run is truncated rather than clean — its verdict covers "
            "less than the corpus.  Usually a side that crashed partway.",
        ]
    return lines


def emit(info: RunInfo, comparison: Comparison, *, as_json: bool) -> int:
    """Print the verdict; return the exit code (0 clean, 1 moved)."""
    payload = json_payload(info, comparison)
    if as_json:
        print(json.dumps(payload, indent=2))
        return 0 if payload["ok"] else 1

    for line in summary_lines(info, comparison):
        print(line)

    lines = failure_lines(info, comparison)
    if lines:
        print("", file=sys.stderr)
        for line in lines:
            print(line, file=sys.stderr)
        return 1

    print(
        f"\nNo movers: the working tree's compiled output is identical to "
        f"{info.base_ref}'s across the corpus."
    )
    return 0


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Compile the corpus at two revisions and report which "
            "programs moved.  Burndown instrument — not a hook."
        ),
    )
    parser.add_argument(
        "--base-ref", default="origin/main",
        help="revision to compare the working tree against "
             "(default: origin/main)",
    )
    parser.add_argument(
        "--work-dir",
        default=str(_DEFAULT_WORK_DIR),
        help="where the base revision is checked out; the checkout is "
             "keyed by SHA and removed when the run ends "
             "(default: %(default)s)",
    )
    parser.add_argument(
        "--keep-base", action="store_true",
        help="leave the base checkout in place when the run ends, so a "
             "session comparing repeatedly against one base pays for one "
             "checkout (default: remove it)",
    )
    parser.add_argument(
        "--jobs", type=int, default=min(8, os.cpu_count() or 1),
        help="parallel compiles per side (default: %(default)s)",
    )
    parser.add_argument(
        "--timeout", type=_positive_seconds, default=DEFAULT_TIMEOUT_SECONDS,
        help="per-program compile budget in seconds (default: %(default)s)",
    )
    parser.add_argument(
        "--json", action="store_true", dest="as_json",
        help="emit the verdict as JSON on stdout",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    repo_root = Path(__file__).resolve().parent.parent

    files = corpus_files(repo_root)
    problem = corpus_guard(files, repo_root)
    if problem is not None:
        print(f"ERROR: {problem}", file=sys.stderr)
        return 1

    sha = resolve_ref(repo_root, args.base_ref)
    if sha is None:
        print(
            f"ERROR: git cannot resolve --base-ref {args.base_ref!r} to a "
            f"commit in {repo_root}.  Fetch it first (`git fetch origin`), "
            f"or name a revision that exists locally.",
            file=sys.stderr,
        )
        return 1

    base_root, problem = base_checkout(repo_root, sha, Path(args.work_dir))
    if base_root is None:
        print(f"ERROR: {problem}", file=sys.stderr)
        return 1
    disposition = "left in place" if args.keep_base else "removed at exit"
    print(f"Base checkout ({disposition}): {base_root}", file=sys.stderr)

    try:
        return _run(args, repo_root, files, sha, base_root)
    finally:
        # Every exit path, including the canary refusals below: a run that
        # bailed still materialised the checkout, and leaving it behind on
        # the failure paths only would make the leftover appear at random.
        if not args.keep_base:
            release_base_checkout(repo_root, base_root)


def _run(
    args: argparse.Namespace,
    repo_root: Path,
    files: list[Path],
    sha: str,
    base_root: Path,
) -> int:
    """The run itself, once the base checkout exists (#1374).

    Split from :func:`main` so the checkout's release is one ``finally``
    around every exit path rather than a call repeated at each ``return``.
    """
    # Both canaries before either side's corpus run: a side pointing at
    # the wrong compiler makes the whole differential vacuous, and that
    # must be a refusal rather than a green run.
    for side, root in (("head", repo_root), ("base", base_root)):
        problem = canary_error(probe_compiler(sys.executable, root), root, side)
        if problem is not None:
            print(f"ERROR: {problem}", file=sys.stderr)
            return 1

    info = RunInfo(
        base_ref=args.base_ref,
        base_sha=sha,
        base_root=str(base_root),
        head_root=str(repo_root),
    )

    sides: dict[str, dict[str, Artifact]] = {}
    for side, root in (("base", base_root), ("head", repo_root)):
        print(
            f"Compiling {len(files)} programs with the {side} compiler "
            f"({root})...",
            file=sys.stderr,
        )
        sides[side] = collect(
            files,
            repo_root,
            lambda path, root=root: compile_one(
                sys.executable, root, args.timeout, path
            ),
            jobs=args.jobs,
        )

    return emit(
        info,
        compare(sides["base"], sides["head"], args.base_ref),
        as_json=args.as_json,
    )


if __name__ == "__main__":
    sys.exit(main())
