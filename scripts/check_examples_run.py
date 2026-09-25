#!/usr/bin/env python
"""CI gate: every `examples/*.vera` program either RUNS
trap-free under the native runtime, or is matched to a documented
property that excludes it from harness execution.

`scripts/check_examples.py` type-checks and verifies every example and
`scripts/check_e602_clean.py` compiles them, so an example that fails to
parse, type-check, verify or compile is caught before this gate.  What
none of them does is *run* one.  A program can pass every static stage
and still trap the moment it executes — an out-of-bounds index behind a
Tier-3 obligation, a monomorphized clone that resolves to a missing
symbol, a host import nobody bound.  Until this gate, the only examples
protected against that were the ones some test happened to execute; the
rest could rot silently between releases.

The design's load-bearing part is the **coverage rule**, not the runs.
The script enumerates `examples/*.vera` from disk and requires every name
to appear in exactly one of two tables:

- ``RUN_SPECS`` — how to invoke it (entry point, arguments, fixtures).
- ``SKIPS`` — the property that excludes it, drawn from
  ``SKIP_PROPERTIES`` so every suppression carries a stated reason that
  the report prints.

An example in neither is an ERROR, so adding an example forces the author
to decide which it is; a table key with no file on disk is an ERROR too,
so a deleted example cannot leave a suppression behind to mask a later
re-add.  The classification is then cross-checked against the table in
TESTING.md (`check_testing_md`), on the `check_doc_counts.py` model: the
codebase is the oracle and the documentation must match it, so the
execution model stops living in maintainers' heads.

What this gate asserts is *runs green*, deliberately not *prints what it
used to*.  Output pinning belongs in the dedicated tests that already do
it — ``tests/test_db_runtime.py::TestDbOnDiskExample229`` pins
`sqlitedb.vera`'s rendered city table,
``tests/test_codegen_host_effects.py`` pins `inference_json.vera`'s
score line against a mocked provider, and ``tests/test_browser.py`` pins
examples against the browser runtime.  A gate that re-pinned stdout
would duplicate those and go red on every cosmetic edit to an example.

But *green* is two signals, not one, for the reason
`scripts/check_examples.py` gives where it asserts an exit code and an
``OK:`` sentinel together: either alone can be satisfied by the wrong
thing, and here both failures were measured rather than imagined.  A
`main` that is privatised or renamed sends `vera run` to its first-export
fallback, which runs a different function and exits 0 — so every spec
names its entry point and the CLI resolves it by name.  An example that
reaches outside the process answers a missing resource by printing a
message and completing normally — so the ones that do carry an
``expect`` substring only their success path prints, which is what makes
deleting `examples/sqlitedb.sqlite` fail the gate instead of passing on
the graceful in-memory arm.  Both signals, per run, always.

*Which* examples those are is derived rather than listed.
``check_sentinel_coverage`` reads each program's own declarations — the
`DB` effect in a function's effect row, the `IO.read_file` /
`IO.write_file` operations at a call site — and requires that set to
equal the set of specs carrying an ``expect``, in both directions.  A
list of filenames would be a snapshot of today's corpus that says
nothing about the next database or filesystem example, which is the only
case the rule exists for.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple


# ---------------------------------------------------------------------------
# Classification tables
# ---------------------------------------------------------------------------


class RunSpec(NamedTuple):
    """How to invoke one example under `vera run`, and what its success
    looks like.

    ``fn`` is always named, never left implicit.  With no ``--fn``,
    `vera run` falls back to the *first export*, and that fallback is a
    silent pass waiting to happen: privatise or rename `main` and the
    gate runs some other function, at exit 0.  Naming the entry point
    makes the CLI resolve it and exit 1 when it is gone.

    ``expect`` is a substring the success path prints.  It is set only
    for the examples that reach outside the process and answer a failure
    by printing a message and completing normally — for those, exit code
    alone cannot tell the success path from the graceful one.  It is
    deliberately not a full stdout pin; that belongs in the dedicated
    tests.

    Which examples those are is not left to judgement:
    ``check_sentinel_coverage`` derives the set from the resources each
    program declares and holds it equal to the specs carrying an
    ``expect``, so a missing sentinel and a spurious one are both
    errors.

    A ``NamedTuple`` rather than a frozen dataclass so the module can be
    loaded by the bare ``spec_from_file_location`` / ``exec_module``
    recipe the sibling script tests use: ``@dataclass`` resolves its
    annotations through ``sys.modules[cls.__module__]``, which that
    recipe leaves unregistered.
    """

    fn: str = "main"
    args: tuple[str, ...] = ()
    needs_db_fixture: bool = False
    expect: str | None = None


# The line `vera run` prints when it cannot use the entry point it was
# given and falls back to the first export.  Every spec names its entry
# point, so this note appearing at all means the resolution did not
# happen and some other function ran in its place.
FALLBACK_NOTE = "no 'main' declared"


# Every skip property, with the reason it excludes harness execution.
# Printed verbatim in the report, so a reader of a gate run sees what is
# not covered and why without opening this file.
SKIP_PROPERTIES: dict[str, str] = {
    "network": (
        "makes live outbound HTTP calls, so a gate run would depend on "
        "network reachability and on a third party's uptime"
    ),
    "api-key": (
        "calls an inference provider; with a key configured in the "
        "environment the gate would issue a real, billed API request, and "
        "without one it would only ever exercise the not-configured arm"
    ),
    "stdin": (
        "reads interactive input, so what it exercises is a property of "
        "the invoking terminal rather than of the program"
    ),
    "non-scalar-entry": (
        "exports no `main` and its only entry point takes an ADT "
        "parameter, which `vera run` cannot construct from CLI arguments"
    ),
    "long-running": (
        "its only entry point is a wall-clock animation loop whose "
        "duration is fixed by deliberate `IO.sleep` calls"
    ),
}


# The examples the harness runs.  Entry points and arguments follow
# the invocations documented in `examples/README.md`, which
# `scripts/check_examples_readme.py` independently holds to naming
# functions that exist.
RUN_SPECS: dict[str, RunSpec] = {
    "absolute_value": RunSpec(fn="absolute_value", args=("-5",)),
    "array_utilities": RunSpec(),
    "async_futures": RunSpec(),
    "base64": RunSpec(),
    "closures": RunSpec(fn="test_closure"),
    "collections": RunSpec(),
    # Reaches a real (in-memory) database and prints its error on the Err
    # arm before completing normally, so exit 0 alone does not mean the
    # round trip happened.
    "database": RunSpec(expect="database round-trip succeeded"),
    "effect_handler": RunSpec(),
    "ephemeris": RunSpec(),
    "factorial": RunSpec(fn="factorial", args=("10",)),
    # Writes then reads back a file; a failed write prints the error and
    # completes normally, so the sentinel is what proves the round trip.
    "file_io": RunSpec(expect="Hello from Vera!"),
    "fizzbuzz": RunSpec(),
    "gc_pressure": RunSpec(),
    "generics": RunSpec(fn="test_generics"),
    "hello_world": RunSpec(),
    "html": RunSpec(),
    "increment": RunSpec(fn="increment"),
    "json": RunSpec(),
    "list_ops": RunSpec(fn="test_list"),
    "markdown": RunSpec(),
    "maximum_syntax": RunSpec(),
    "modules": RunSpec(fn="clamp_to_range", args=("100", "0", "42")),
    "mutual_recursion": RunSpec(fn="is_even", args=("4",)),
    "nested_closures": RunSpec(fn="grid_sum"),
    "pattern_matching": RunSpec(fn="test_match"),
    "quantifiers": RunSpec(fn="test_process"),
    "refinement_types": RunSpec(fn="test_refine"),
    "regex": RunSpec(),
    "safe_divide": RunSpec(fn="safe_divide", args=("3", "10")),
    "scoreboard": RunSpec(),
    # The committed on-disk fixture, threaded the way
    # `tests/test_db_runtime.py::TestDbOnDiskExample229` threads it — without
    # it the example takes its graceful in-memory `Err` arm and the on-disk
    # read, which is the whole point of the example, never executes.  That
    # arm exits 0, so the sentinel is what makes deleting the fixture fail
    # the gate rather than pass it.
    "sqlitedb": RunSpec(
        needs_db_fixture=True,
        expect="read 4 cities from the on-disk database:",
    ),
    "string_ops": RunSpec(),
    "string_utilities": RunSpec(fn="padded_id"),
    "url_encoding": RunSpec(),
    "url_parsing": RunSpec(),
}


# The examples excluded by property.  Each is still type-checked,
# verified and compiled by the other gates; only execution is out of
# reach here.
SKIPS: dict[str, str] = {
    "async_http_fanout": "network",
    "http": "network",
    "inference": "api-key",
    "inference_json": "api-key",
    "io_operations": "stdin",
    "read_char": "stdin",
    "http_server": "non-scalar-entry",
    "life": "long-running",
}


# Environment variables that change what an example *does*.  The runner
# strips them from the inherited environment so a gate run measures the
# examples rather than the developer's shell — an ambient `VERA_DB_URL`
# would otherwise point `database.vera` at a real database, and an
# ambient provider key would turn a run into a billed API call.  A spec
# that needs one puts its own value back.
NEUTRALISED_ENV: tuple[str, ...] = (
    "VERA_DB_URL",
    "VERA_ANTHROPIC_API_KEY",
    "VERA_OPENAI_API_KEY",
    "VERA_MOONSHOT_API_KEY",
    "VERA_MISTRAL_API_KEY",
    "VERA_XAI_API_KEY",
    "VERA_DEEPSEEK_API_KEY",
)


# Per-example wall-clock budget.  Generous: the whole set runs
# in a few seconds, so this only ever fires on a genuine hang, which is
# reported as a failure rather than blocking the CI job indefinitely.
TIMEOUT_SECONDS = 300

# The committed on-disk database `sqlitedb.vera` reads.
DB_FIXTURE = "sqlitedb.sqlite"


# ---------------------------------------------------------------------------
# The coverage rule
# ---------------------------------------------------------------------------


def example_names(examples_dir: Path) -> list[str]:
    """Every standalone example program, by stem.

    Non-recursive by design: `examples/vera/` holds the modules
    `modules.vera` imports, which are libraries rather than programs and
    have no entry point of their own.
    """
    return sorted(p.stem for p in examples_dir.glob("*.vera"))


def check_coverage(
    names: list[str],
    run_specs: dict[str, RunSpec],
    skips: dict[str, str],
) -> list[str]:
    """Every name classified exactly once, every classification real.

    An empty corpus is an error rather than a vacuous pass: a glob that
    stops matching would otherwise switch the whole gate off silently,
    which is the failure this script is built to make impossible.
    """
    errors: list[str] = []
    if not names:
        errors.append(
            "no examples found — the corpus glob matched nothing.  This is "
            "an error rather than a pass: a gate with nothing to run "
            "reports success while covering zero programs."
        )
        return errors

    on_disk = set(names)
    classified = set(run_specs) | set(skips)

    for name in sorted(on_disk - classified):
        errors.append(
            f"{name}.vera is unclassified — add it to RUN_SPECS with an "
            f"entry point, or to SKIPS with a property from "
            f"SKIP_PROPERTIES explaining why the harness cannot run it."
        )

    for name in sorted(classified - on_disk):
        table = "RUN_SPECS" if name in run_specs else "SKIPS"
        errors.append(
            f"{name!r} is listed in {table} but no examples/{name}.vera "
            f"exists — remove the stale entry (a suppression outliving its "
            f"example would mask a later program of the same name)."
        )

    for name in sorted(set(run_specs) & set(skips)):
        errors.append(
            f"{name}.vera appears in both tables — an example is either "
            f"run or skipped, never both."
        )

    for name, prop in sorted(skips.items()):
        if prop not in SKIP_PROPERTIES:
            errors.append(
                f"{name}.vera is skipped for {prop!r}, which is not in "
                f"SKIP_PROPERTIES — every suppression must cite a "
                f"documented property so the report can state the reason."
            )

    return errors


# ---------------------------------------------------------------------------
# The derived sentinel rule
# ---------------------------------------------------------------------------


# The external resources an example can reach, as registry NAMES.  Which
# examples must pin a sentinel follows from these by reading what each
# program declares, so one added tomorrow is covered by being written
# rather than by being remembered here — the case a list of filenames
# cannot cover, since it is a snapshot of the corpus it was written
# against.
#
# Both halves are needed because the effect row alone does not
# discriminate.  `FileIO` and `Time` are not effects in Vera: file and
# clock operations live under `IO`, so `file_io.vera` declares exactly
# the bare `<IO>` that `hello_world.vera` does and only the operation it
# calls tells the two apart.  Measured over the corpus, `DB` appears in
# `database.vera` and `sqlitedb.vera` alone, and `IO.read_file` /
# `IO.write_file` in `file_io.vera` alone.
RESOURCE_EFFECTS: tuple[str, ...] = ("DB",)
RESOURCE_OPS: tuple[tuple[str, str], ...] = (
    ("IO", "read_file"),
    ("IO", "write_file"),
)


def resource_vocabulary() -> str:
    """The declared resource names, for the messages that cite them."""
    return ", ".join(
        [*RESOURCE_EFFECTS, *(f"{e}.{op}" for e, op in RESOURCE_OPS)]
    )


def resource_registry_errors() -> list[str]:
    """Every declared resource name, checked against the live registry.

    A name the compiler no longer has would match no example, and with
    nothing left requiring a sentinel the rule switches itself off while
    still reporting success.  Renaming the `DB` effect, or moving
    `read_file` out of `IO`, must therefore fail here rather than
    quietly empty the derivation — the same reason an empty corpus is an
    error in ``check_coverage``.

    The `vera` import is lazy, as `check_doc_counts.check_homepage_facts`
    does for the same registry: loading this module for its
    classification tables should not drag in the compiler.
    """
    from vera.introspect import builtin_effect_names, effects_payload

    live_effects = builtin_effect_names()
    live_ops = {
        str(item["name"]): {str(op) for op in item.get("ops", ())}
        for item in effects_payload()["items"]
        if item.get("kind") == "effect"
    }

    errors: list[str] = []
    for name in RESOURCE_EFFECTS:
        if name not in live_effects:
            errors.append(
                f"RESOURCE_EFFECTS names {name!r}, which the effect "
                f"registry does not have — could not find it among "
                f"{sorted(live_effects)}.  Re-point it at the current "
                f"name, so a renamed effect fails this gate instead of "
                f"silently matching no example."
            )
    for effect, op in RESOURCE_OPS:
        if effect not in live_ops:
            errors.append(
                f"RESOURCE_OPS names {effect}.{op}, but the effect "
                f"registry has no {effect!r} — could not find it among "
                f"{sorted(live_ops)}.  An operation is only meaningful "
                f"under an effect that exists."
            )
        elif op not in live_ops[effect]:
            errors.append(
                f"RESOURCE_OPS names {effect}.{op}, which {effect} does "
                f"not have — could not find {op!r} among "
                f"{sorted(live_ops[effect])}.  Re-point it at the "
                f"current operation, so a renamed one fails this gate "
                f"instead of silently matching no example."
            )
    return errors


def resource_signals(path: Path) -> frozenset[str]:
    """The external-resource signals one example declares.

    Two sources, since neither alone discriminates: the resource effects
    named in a function's effect row, and the resource operations the
    source calls.  Read off the parsed program rather than the text, so
    a comment naming `<DB>` is prose and not a declaration —
    `examples/sqlitedb.vera`'s first line is exactly such a comment, and
    a text scan would agree with the parse there by luck while
    disagreeing on the first example whose header describes what it
    deliberately does not do.

    Whatever the parse raises propagates; ``check_sentinel_coverage``
    turns it into an error line, because an example whose signals are
    *unknown* must not be spelled the same as one that has none.
    """
    from vera import ast
    from vera.obligations.cache import walk_nodes
    from vera.parser import parse_to_ast

    program = parse_to_ast(path.read_text(encoding="utf-8"), file=str(path))
    effects = set(RESOURCE_EFFECTS)
    ops = set(RESOURCE_OPS)

    signals: set[str] = set()
    for node in walk_nodes(program):
        if isinstance(node, ast.FnDecl):
            # `walk_nodes` is a generic dataclass-field walk, so a
            # `where` helper's row is reached alongside the outer one.
            row = node.effect
            if isinstance(row, ast.EffectSet):
                for ref in row.effects:
                    # Unqualified refs only: `Mod.DB` names a user
                    # effect in another module, not the built-in the
                    # registry check validated.
                    if isinstance(ref, ast.EffectRef) and ref.name in effects:
                        signals.add(ref.name)
        elif isinstance(node, ast.QualifiedCall):
            if (node.qualifier, node.name) in ops:
                signals.add(f"{node.qualifier}.{node.name}")
    return frozenset(signals)


def check_sentinel_coverage(
    examples_dir: Path,
    run_specs: dict[str, RunSpec],
) -> list[str]:
    """The examples that declare an external resource are exactly the
    specs that carry an ``expect``.

    Both directions are errors.  A resource-touching example with no
    sentinel passes on its graceful arm the day its fixture vanishes,
    which is the failure the sentinels exist to catch; a sentinel on an
    example with no resource re-pins stdout that the dedicated output
    tests own, and goes red on a cosmetic edit.

    An empty derived set is an error rather than a vacuous pass: with
    nothing required the two sides agree however broken the derivation
    is, which is the same failure mode ``check_coverage`` rules out for
    a glob that stops matching.
    """
    errors = resource_registry_errors()
    if errors:
        # Without a valid vocabulary the derivation below is
        # meaningless — it would match nothing and then report every
        # sentinel in the tables as spurious.
        return errors

    signals_by_name: dict[str, frozenset[str]] = {}
    inspected: set[str] = set()
    for name in sorted(run_specs):
        path = examples_dir / f"{name}.vera"
        if not path.is_file():
            # `check_coverage` and `run_corpus` both report this, each
            # naming the table the key came from; a third copy would
            # only repeat them.  It cannot hide the rule either — with
            # the files gone the derivation is empty, which is the
            # error below.
            continue
        inspected.add(name)
        try:
            signals = resource_signals(path)
        except Exception as exc:  # noqa: BLE001 — unknown signals are reported, never read as none
            errors.append(
                f"{name}.vera could not be parsed, so what it reaches "
                f"outside the process is unknown — read as 'declares no "
                f"resource' it would drop out of this rule silently, "
                f"and be diagnosed as carrying a sentinel for nothing: "
                f"{exc}"
            )
            continue
        if signals:
            signals_by_name[name] = signals

    if errors:
        return errors

    if not signals_by_name:
        return [
            f"no example in RUN_SPECS declares any of "
            f"[{resource_vocabulary()}] — the derivation matched "
            f"nothing, so the sentinel rule is no longer gated.  This "
            f"is an error rather than a pass: with the required set "
            f"empty both sides of the rule agree however broken the "
            f"derivation is, and every gate run reports success over "
            f"zero examples."
        ]

    # Only the specs whose `.vera` the loop above actually read.  Building
    # this from every entry in `run_specs` put a spec whose file is missing
    # into `pinned - signals_by_name`, where it drew the spurious-sentinel
    # diagnosis — "declares no external resource" — when the truth is that
    # the derivation never opened it.  `check_coverage` reports the missing
    # file first in `main`, but this is a public function tests call
    # directly (#1329 review).
    pinned = {
        name
        for name, spec in run_specs.items()
        if spec.expect and name in inspected
    }
    for name in sorted(set(signals_by_name) - pinned):
        errors.append(
            f"{name}.vera reaches outside the process "
            f"({', '.join(sorted(signals_by_name[name]))}) but its "
            f"RUN_SPECS entry sets no `expect` — a program like this "
            f"answers a missing resource by printing a message and "
            f"completing normally, so exit code alone cannot tell its "
            f"success path from that arm.  Pin a substring only the "
            f"success path prints."
        )
    for name in sorted(pinned - set(signals_by_name)):
        errors.append(
            f"{name}.vera declares no external resource "
            f"([{resource_vocabulary()}]) but its RUN_SPECS entry pins "
            f"the sentinel {run_specs[name].expect!r} — `expect` is for "
            f"programs that answer a missing resource by completing "
            f"normally.  On any other example it re-pins stdout that "
            f"the dedicated output tests own, and goes red on a "
            f"cosmetic edit."
        )
    return errors


# ---------------------------------------------------------------------------
# Invocation
# ---------------------------------------------------------------------------


def build_command(python: str, vera_file: Path, spec: RunSpec) -> list[str]:
    """The `vera run` argv for one example.

    ``--fn`` is always passed — see ``RunSpec`` for why the implicit
    first-export fallback is not safe to rely on.
    """
    cmd = [python, "-m", "vera.cli", "run", str(vera_file), "--fn", spec.fn]
    if spec.args:
        cmd += ["--", *spec.args]
    return cmd


def check_output(name: str, spec: RunSpec, output: str) -> str | None:
    """The second signal, beside the exit code: a failure line, or None.

    `scripts/check_examples.py` established the discipline — assert the
    exit code AND an output signal, because either alone can be satisfied
    by the wrong thing.  Two measured cases motivate it here, and both
    exit 0: a `main` that stops being callable, where `vera run` falls
    back to an arbitrary export, and an external fixture that vanishes,
    where the example takes its graceful arm.
    """
    # A backstop, not the live path.  `build_command` always passes
    # `--fn`, so `vera run` refuses a missing or private export outright
    # (non-zero, "not found in exports") and never reaches its
    # first-export fallback — the end-to-end cell in the tests pins that
    # refusal, and another pins that `--fn` is always passed, which is
    # what keeps this branch unreachable.  It stays as the tripwire for a
    # `build_command` that stops passing it (#1330 review).
    if FALLBACK_NOTE in output:
        return (
            f"{name}: `vera run` could not use the entry point "
            f"{spec.fn!r} and fell back to the first export — some other "
            f"function ran, at exit 0.  Usually the entry point was "
            f"renamed or made private."
        )
    if spec.expect is not None and spec.expect not in output:
        return (
            f"{name}: exited 0 but its output does not contain "
            f"{spec.expect!r} — the program completed down a graceful "
            f"failure arm rather than its success path.  Check whether "
            f"the fixture or resource it needs is still there."
        )
    return None


def missing_fixture(spec: RunSpec, examples_dir: Path) -> Path | None:
    """The committed fixture a spec needs but cannot find, if any.

    Checked *before* the run rather than left to fail inside it.
    `sqlite3` CREATES the database named by a `sqlite:///` URL when it is
    not there, so handing the example a URL for an absent fixture
    materialises an empty `examples/sqlitedb.sqlite` as a side effect.
    The sentinel would still fail the run — right verdict — but the gate
    would have written into the corpus it is checking, which is the very
    thing the per-run scratch directory exists to prevent.
    """
    if not spec.needs_db_fixture:
        return None
    fixture = examples_dir / DB_FIXTURE
    return None if fixture.is_file() else fixture


def spec_env(spec: RunSpec, examples_dir: Path) -> dict[str, str]:
    """The environment a spec adds on top of the inherited one."""
    if not spec.needs_db_fixture:
        return {}
    fixture = (examples_dir / DB_FIXTURE).resolve()
    # POSIX form so the URL is portable on Windows, matching
    # `tests/test_db_runtime.py`; `_open_connection` strips the prefix
    # back to the filesystem path.
    return {"VERA_DB_URL": f"sqlite:///{fixture.as_posix()}"}


def build_env(
    spec: RunSpec,
    examples_dir: Path,
    base: dict[str, str] | None = None,
) -> dict[str, str]:
    """The full environment for one run: inherited, minus the variables
    that would change the example's behaviour, plus the spec's own."""
    env = dict(os.environ if base is None else base)
    for name in NEUTRALISED_ENV:
        env.pop(name, None)
    env.update(spec_env(spec, examples_dir))
    return env


def run_corpus(
    examples_dir: Path,
    run_specs: dict[str, RunSpec],
    workdir_root: Path,
) -> list[str]:
    """Run every spec; return one formatted line per failure.

    Each example gets its own scratch working directory.  `file_io.vera`
    writes `hello.txt` relative to the process CWD, so running in place
    would drop artefacts beside the examples on every gate run.
    """
    failures: list[str] = []
    for name in sorted(run_specs):
        spec = run_specs[name]
        vera_file = examples_dir / f"{name}.vera"
        if not vera_file.is_file():
            failures.append(
                f"{name}: examples/{name}.vera does not exist, so the "
                f"RUN_SPECS entry covers nothing"
            )
            continue

        absent = missing_fixture(spec, examples_dir)
        if absent is not None:
            failures.append(
                f"{name}: the committed fixture {absent} does not exist, "
                f"so the run was not started — sqlite3 would have created "
                f"an empty database there rather than reading one"
            )
            continue

        workdir = workdir_root / f"run-{name}"
        workdir.mkdir(parents=True, exist_ok=True)
        try:
            result = subprocess.run(
                build_command(sys.executable, vera_file, spec),
                capture_output=True,
                text=True,
                encoding="utf-8",
                cwd=str(workdir),
                # Nothing reads the invoking terminal's stdin: an example
                # that tried would otherwise consume the user's keystrokes
                # mid-run.  DEVNULL is an immediate EOF, not a hang —
                # which is why terminal-dependence rather than hanging is
                # the reason the stdin examples are skipped.
                stdin=subprocess.DEVNULL,
                env=build_env(spec, examples_dir),
                timeout=TIMEOUT_SECONDS,
                check=False,
            )
        except subprocess.TimeoutExpired:
            failures.append(
                f"{name}: exceeded the {TIMEOUT_SECONDS}s budget — the "
                f"program hung rather than terminating"
            )
            continue

        if result.returncode != 0:
            detail = (result.stderr.strip() or result.stdout.strip()
                      or "no output")
            failures.append(
                f"{name}: `vera run` exited {result.returncode}: "
                f"{detail[:300]}"
            )
            continue

        # Exit code clean — now the second signal.  Both streams: the
        # fallback note goes to stderr, the sentinels to stdout.
        message = check_output(name, spec, result.stdout + result.stderr)
        if message is not None:
            failures.append(message)
    return failures


# ---------------------------------------------------------------------------
# The TESTING.md cross-check
# ---------------------------------------------------------------------------


_TABLE_HEADING = "Example execution coverage"
_ROW_RE = re.compile(r"^\|\s*`([A-Za-z0-9_]+)\.vera`\s*\|[^|]*\|\s*([^|]+?)\s*\|")


def parse_testing_table(text: str) -> dict[str, str] | None:
    """The example → harness-disposition map from TESTING.md's table.

    ``None`` when the heading is absent — distinct from an empty dict
    (heading present, no rows), because the two need different messages
    and neither may be reported as a pass.
    """
    lines = text.splitlines()

    # A `#` at column 0 inside a fenced block is a shell comment or a
    # heading in sample Markdown, not a heading of this document — and
    # TESTING.md has 32 such lines.  Tracking fences keeps one from
    # ending the subsection early, which would empty the table and fail
    # the gate on a document that is perfectly well formed.
    def _headings(seq: list[str]) -> list[bool]:
        out, in_fence = [], False
        for line in seq:
            if line.lstrip().startswith("```"):
                in_fence = not in_fence
                out.append(False)
                continue
            out.append(not in_fence and line.startswith("#"))
        return out

    is_heading = _headings(lines)
    start = None
    for i, line in enumerate(lines):
        if is_heading[i] and _TABLE_HEADING in line:
            start = i
            break
    if start is None:
        return None

    rows: dict[str, str] = {}
    for i in range(start + 1, len(lines)):
        if is_heading[i]:  # the next heading ends the subsection
            break
        m = _ROW_RE.match(lines[i])
        if m:
            rows[m.group(1)] = m.group(2).strip()
    return rows


def check_testing_md(
    text: str,
    run_specs: dict[str, RunSpec],
    skips: dict[str, str],
) -> list[str]:
    """TESTING.md's table must agree with this script's classification."""
    rows = parse_testing_table(text)
    if rows is None:
        return [
            f"TESTING.md: no heading containing {_TABLE_HEADING!r} — the "
            f"execution-model table is the documented form of this "
            f"script's classification, and a reworded heading must fail "
            f"the gate rather than leave nothing to compare."
        ]
    if not rows:
        return [
            f"TESTING.md: the {_TABLE_HEADING!r} section has no rows the "
            f"gate can read — expected one `| `<name>.vera` | ... | "
            f"<disposition> |` row per example."
        ]

    expected = {name: "runs" for name in run_specs}
    expected.update({name: f"skip: {prop}" for name, prop in skips.items()})

    errors: list[str] = []
    for name in sorted(set(expected) - set(rows)):
        errors.append(
            f"TESTING.md: no row for {name}.vera, which this script "
            f"classifies as {expected[name]!r}"
        )
    for name in sorted(set(rows) - set(expected)):
        errors.append(
            f"TESTING.md: row for {name}.vera, which this script does not "
            f"classify — the example was renamed or removed, or the row "
            f"was never real"
        )
    for name in sorted(set(rows) & set(expected)):
        if rows[name] != expected[name]:
            errors.append(
                f"TESTING.md: {name}.vera is documented as "
                f"{rows[name]!r} but this script classifies it as "
                f"{expected[name]!r}"
            )
    return errors


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


def _block(title: str, errors: list[str], footer: str = "") -> list[str]:
    if not errors:
        return []
    lines = [f"{title} ({len(errors)}):"]
    lines += [f"  {e}" for e in errors]
    if footer:
        lines += ["", footer]
    return lines


def error_blocks(
    coverage_errors: list[str],
    sentinel_errors: list[str],
    doc_errors: list[str],
    failures: list[str],
) -> list[str]:
    """The stderr report, as labelled blocks.

    Each kind gets its own header carrying its own count.  Filing one
    kind's lines under another's header misreports both — a reader who
    counts the lines beneath `COVERAGE ERRORS (n)` gets a number the
    header disagrees with.
    """
    return [
        *_block("COVERAGE ERRORS", coverage_errors),
        *_block(
            "SENTINEL COVERAGE", sentinel_errors,
            "Which examples must pin a success sentinel is derived from "
            "the resources each program declares, not from a list of "
            "names.  Fix the spec — or, if an example genuinely stopped "
            "reaching outside the process, drop its `expect`.",
        ),
        *_block(
            "DOCUMENTATION MISMATCH", doc_errors,
            "TESTING.md's execution-model table is the documented form of "
            "the classification in this script.  Update the table to "
            "match, so the model stays readable without reading the "
            "source.",
        ),
        *_block(
            "RUNTIME FAILURES", failures,
            "An example that no longer runs is a bug in the compiler or "
            "in the example, not something to suppress: SKIPS is for "
            "programs the harness structurally cannot drive, not for ones "
            "that are broken.",
        ),
    ]


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main() -> int:
    repo_root = Path(__file__).resolve().parent.parent
    examples_dir = repo_root / "examples"

    names = example_names(examples_dir)
    coverage_errors = check_coverage(names, RUN_SPECS, SKIPS)

    testing_md = repo_root / "TESTING.md"
    if testing_md.is_file():
        doc_errors = check_testing_md(
            testing_md.read_text(encoding="utf-8"), RUN_SPECS, SKIPS
        )
    else:
        doc_errors = [f"TESTING.md not found at {testing_md}"]

    # The coverage rule gates the run: with the tables out of sync with
    # disk, a green run would be reporting on the wrong set of programs.
    if coverage_errors:
        for line in error_blocks(coverage_errors, [], doc_errors, []):
            print(line, file=sys.stderr)
        return 1

    # Derived from the examples themselves, so it runs only once the
    # tables and disk agree: a spec whose file is missing is already
    # reported above, and would otherwise be reported twice.
    sentinel_errors = check_sentinel_coverage(examples_dir, RUN_SPECS)

    with tempfile.TemporaryDirectory(prefix="vera-examples-run-") as td:
        failures = run_corpus(examples_dir, RUN_SPECS, Path(td))

    print(
        f"Ran {len(RUN_SPECS)} of {len(names)} examples under the native "
        f"runtime ({len(SKIPS)} skipped by property)."
    )
    for prop in sorted(SKIP_PROPERTIES):
        skipped = sorted(n for n, p in SKIPS.items() if p == prop)
        if skipped:
            print(f"  skip [{prop}]: {', '.join(skipped)}")
            print(f"    {SKIP_PROPERTIES[prop]}")

    # With the rule holding, the specs carrying an `expect` ARE the
    # derived set, so printing them names it — a reader of a gate run
    # sees which examples the sentinel rule covers without opening this
    # file, as the skip properties above already do for the skips.
    if not sentinel_errors:
        pinned = sorted(n for n, s in RUN_SPECS.items() if s.expect)
        print(
            f"  sentinel required [{resource_vocabulary()}]: "
            f"{', '.join(pinned)}"
        )

    blocks = error_blocks([], sentinel_errors, doc_errors, failures)
    if blocks:
        print("", file=sys.stderr)
        for line in blocks:
            print(line, file=sys.stderr)
        return 1

    print("\nAll runnable examples execute trap-free.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
