"""The `matrix` marker: the pull-request gate samples the class-instrument matrices.

A test file that is a generated class instrument (TESTING.md § Class
Instruments) carries the marker at module level, naming the modules that
decide its class as paths from the repository root — the modules the fix
changed to close it::

    pytestmark = pytest.mark.matrix(decides=["vera/narrowing.py"])

Its cells are generated: one test function crossed with the dimensions the
class spans, hundreds or thousands of cells that drive the same code through
different shapes.  A pull request does not need every one of them on every
push, so by default a run keeps, of a marked file:

- every test that is not parametrised;
- every cell of a parametrised function of at most ``FLOOR`` cells, and of a
  function whose name carries the token ``repro``;
- and of every other parametrised function a stratified sample of at least
  ``max(FLOOR, ceil(FRACTION * cells))`` cells: the first and the last cell
  in collection order; every cell carrying an ``xfail`` mark, since a strict
  xfail pins an instance still open and a sampled-out one would let its fix
  pass unnoticed; every cell whose id carries a ``KEEP_TOKENS`` word; one
  cell for each value of every parametrize dimension with no more values
  than the sample has cells; and at least one cell from each of that many
  equal runs of the collection order, which spreads the sample across the
  outer loops the generators nest.

The cells every pull request must run — the reported instance, the red-first
pins and the mutant killers — are kept by three of those rules: write
each one as an unparametrised test (the corpus sweeps are written that
way too), in a function named for a ``repro``, or as a strict xfail.  The
keep words are a fourth way in, but no cell id of a marked file uses
``repro``, ``red`` or ``mutant`` as a word today (the one that carries
``named`` does so by accident), and they match whole words only: as a
substring, ``red`` would keep every ``declared`` and ``required`` cell.

A marked file runs in full, every cell, when the change under test touches
the file itself or a module its marker declares.  CI names the files a pull
request changes in ``VERA_MATRIX_CHANGED``, one path per line, from the plan
job's diff (.github/workflows/ci.yml); a run without the variable samples
every marked file.  Paths are compared whole, so a prefix of a declared path
is not that path.

Within those rules a cell is chosen by a hash of the seed and its node id,
so the sample is the same in every process, on every platform and every
Python version, and the seed is the ISO week: it rotates weekly and is
stable within a week.  ``--matrix-seed`` names another (a past week's, to
reproduce its sample).  ``--matrix=full`` runs every cell of every marked
file and ``--matrix=sample`` samples every one, whatever the variable says;
the coverage job, the release merge's push, the nightly run and the
pre-commit hook's run of a staged test file pass ``--matrix=full``.  A test
named on the command line below the file (``file.py::test_x``) always runs
in full, and the sample is drawn after ``-k`` and ``-m`` have selected, from
what they kept.

Cells left out are deselected, and the run's summary says how many: "N
matrix cells sampled out".  They are never reported as skipped.  The summary
also names each file run in full because the change touches it or a module
that decides it.

The hooks below are imported into ``tests/conftest.py``.  The selection is
``choose`` and which files run whole is ``decided_in_full``, both functions
of plain data, so their rules are tested without a pytest session.
"""

from __future__ import annotations

import datetime
import hashlib
import math
import os
import re
from collections.abc import Iterable, Sequence
from collections.abc import Set as AbstractSet
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

#: A parametrised function with at most this many cells keeps all of them,
#: and a sampled one keeps at least this many.
FLOOR = 20

#: The share of a sampled function's cells the sample keeps at least.
FRACTION = 0.10

#: A cell whose id carries one of these as a whole word is always kept.
#: Words, not substrings: `red` must not keep `declared` or `required`.
KEEP_TOKENS = frozenset({"repro", "red", "mutant", "named"})

#: A parametrised function whose name carries one of these keeps every cell.
FUNCTION_KEEP_TOKENS = frozenset({"repro"})

#: The variable CI sets on a pull request: the files the pull request
#: changes that a matrix can be decided by, one repository-relative path per
#: line (the plan job in .github/workflows/ci.yml).
CHANGED_ENV = "VERA_MATRIX_CHANGED"

_SEED_KEY = "vera_matrix_seed"
_SAMPLED_KEY = "vera_matrix_sampled_out"
_IN_FULL_KEY = "vera_matrix_in_full"


@dataclass(frozen=True)
class Cell:
    """What the sample reads of one parametrised test item."""

    nodeid: str
    cell_id: str
    # Each argname's index into its parametrize list.
    indices: tuple[tuple[str, int], ...] = ()
    xfail: bool = False


def iso_week(day: datetime.date | None = None) -> str:
    """The default seed: the ISO week of `day` (today, in UTC), as
    `2026-W41`."""
    day = day or datetime.datetime.now(datetime.timezone.utc).date()
    year, week, _ = day.isocalendar()
    return f"{year}-W{week:02d}"


def tokens(text: str) -> set[str]:
    """The lower-case words of `text`, split at every character that is not
    a letter or a digit."""
    return {word for word in re.split(r"[^0-9a-z]+", text.lower()) if word}


def target(cells: int) -> int:
    """How many cells a sampled function keeps at least."""
    return min(cells, max(FLOOR, math.ceil(cells * FRACTION)))


def _rank(seed: str, nodeid: str) -> str:
    return hashlib.sha256(f"{seed}\0{nodeid}".encode("utf-8")).hexdigest()


def _dimensions(cells: Sequence[Cell]) -> list[tuple[int, ...]]:
    """One value vector per parametrize dimension.  The argnames of one
    `parametrize` call move together, so argnames whose index vectors are
    equal are one dimension."""
    names = sorted({name for cell in cells for name, _ in cell.indices})
    vectors: dict[tuple[int, ...], str] = {}
    for name in names:
        vector = tuple(dict(cell.indices).get(name, -1) for cell in cells)
        vectors.setdefault(vector, name)
    return list(vectors)


def choose(cells: Sequence[Cell], function: str, seed: str) -> set[int]:
    """The positions of the cells of one parametrised function the sample
    keeps, `cells` being that function's cells in collection order."""
    count = len(cells)
    if count <= FLOOR or FUNCTION_KEEP_TOKENS & tokens(function):
        return set(range(count))
    want = target(count)
    rank = [_rank(seed, cell.nodeid) for cell in cells]
    by_rank = sorted(range(count), key=rank.__getitem__)
    kept = {0, count - 1}
    kept |= {
        position for position, cell in enumerate(cells)
        if cell.xfail or KEEP_TOKENS & tokens(cell.cell_id)
    }
    for dimension in _dimensions(cells):
        values = set(dimension)
        if len(values) > want:
            continue
        uncovered = values - {dimension[position] for position in kept}
        for position in by_rank:
            if not uncovered:
                break
            if dimension[position] in uncovered:
                kept.add(position)
                uncovered.discard(dimension[position])
    chosen = [position in kept for position in range(count)]
    for stratum in range(want):
        low, high = stratum * count // want, (stratum + 1) * count // want
        if not any(chosen[low:high]):
            pick = min(range(low, high), key=rank.__getitem__)
            chosen[pick] = True
            kept.add(pick)
    return kept


def changed_paths(value: str | None) -> frozenset[str]:
    """The paths a `VERA_MATRIX_CHANGED` value names: one per line, with
    surrounding space and blank lines dropped, and a Windows separator or a
    leading `./` normalised away."""
    paths: set[str] = set()
    for line in (value or "").splitlines():
        path = line.strip().replace("\\", "/")
        while path.startswith("./"):
            path = path[2:]
        if path:
            paths.add(path)
    return frozenset(paths)


def deciders(marker: pytest.Mark) -> tuple[str, ...]:
    """The modules a `matrix` marker declares as deciding its file's class,
    as paths from the repository root.  One path written as a string is
    one module, never its characters."""
    decides = marker.kwargs.get("decides", ())
    if isinstance(decides, str):
        return (decides,)
    return tuple(decides)


def decided_in_full(
    path: str, decides: Iterable[str], changed: AbstractSet[str]
) -> list[str]:
    """The changed paths that put the marked file `path` in full: the file
    itself and each module it declares, compared whole, so a prefix, a
    suffix or another spelling of a declared path is not that path."""
    return sorted({path, *decides} & changed)


def _cell(item: Any) -> Cell:
    callspec = item.callspec
    return Cell(
        nodeid=item.nodeid,
        cell_id=str(callspec.id),
        indices=tuple(sorted(callspec.indices.items())),
        xfail=item.get_closest_marker("xfail") is not None,
    )


def _seed(config: pytest.Config) -> str:
    seed = getattr(config, "_vera_matrix_seed", None)
    if seed is None:
        workerinput = getattr(config, "workerinput", None) or {}
        seed = (
            config.getoption("matrix_seed")
            or workerinput.get(_SEED_KEY)
            or iso_week()
        )
        config._vera_matrix_seed = seed  # type: ignore[attr-defined]
    return str(seed)


def _named_on_the_command_line(config: pytest.Config) -> tuple[str, ...]:
    """The node ids the command line names below the file level, relative to
    the rootdir as node ids are."""
    root = Path(str(config.rootpath)).resolve()
    here = Path(str(config.invocation_params.dir))
    named: list[str] = []
    for arg in config.args:
        path, separator, rest = str(arg).partition("::")
        if not separator:
            continue
        try:
            relative = (here / path).resolve().relative_to(root).as_posix()
        except ValueError:
            continue
        named.append(f"{relative}::{rest}")
    return tuple(named)


def _is_named(nodeid: str, named: tuple[str, ...]) -> bool:
    return any(
        nodeid == name or nodeid.startswith((f"{name}::", f"{name}["))
        for name in named
    )


def pytest_addoption(parser: pytest.Parser) -> None:
    group = parser.getgroup("matrix", "class-instrument matrices")
    group.addoption(
        "--matrix",
        choices=("sample", "full"),
        default=None,
        dest="matrix",
        help=(
            "full: run every cell of every file marked `matrix`; sample: run "
            "a stratified, weekly-seeded sample of each one's parametrised "
            "cells.  Default: the sample, but every cell of a file that "
            f"{CHANGED_ENV} names, or one of whose deciding modules it names "
            "(see tests/matrix_sample.py)"
        ),
    )
    group.addoption(
        "--matrix-seed",
        default=None,
        dest="matrix_seed",
        metavar="SEED",
        help="the sample's seed (default: this ISO week in UTC, e.g. 2026-W41)",
    )


@pytest.hookimpl(optionalhook=True)
def pytest_configure_node(node: Any) -> None:
    """pytest-xdist, on the controller: hand every worker the same seed, so
    a run that spans the turn of a week collects one sample everywhere."""
    node.workerinput[_SEED_KEY] = _seed(node.config)


# Last, so the sample is drawn from what `-k` and `-m` kept: their
# deselection runs in this hook too, and a conftest's implementation would
# otherwise run before it, leaving a selection fewer cells than the floor.
@pytest.hookimpl(trylast=True)
def pytest_collection_modifyitems(
    config: pytest.Config, items: list[pytest.Item]
) -> None:
    mode = config.getoption("matrix")
    if mode == "full":
        return
    # The deciding-module rule reads the variable only by default: an
    # explicit `--matrix=sample` samples every marked file whatever changed.
    changed = changed_paths(os.environ.get(CHANGED_ENV)) if mode is None else frozenset()
    named = _named_on_the_command_line(config)
    reasons: dict[str, list[str]] = {}
    functions: dict[str, list[int]] = {}
    for position, item in enumerate(items):
        marker = item.get_closest_marker("matrix")
        if marker is None:
            continue
        # A node id's file part is the path from the rootdir, which for this
        # repository is its root, as the deciders and the variable's are.
        path = item.nodeid.split("::", 1)[0]
        if path not in reasons:
            reasons[path] = decided_in_full(path, deciders(marker), changed)
        if reasons[path]:
            continue
        if getattr(item, "callspec", None) is None:
            continue
        if _is_named(item.nodeid, named):
            continue
        functions.setdefault(item.nodeid.split("[", 1)[0], []).append(position)
    in_full = {path: why for path, why in reasons.items() if why}
    seed = _seed(config)
    dropped: set[int] = set()
    for function, positions in functions.items():
        kept = choose([_cell(items[p]) for p in positions], function, seed)
        dropped |= {p for index, p in enumerate(positions) if index not in kept}
    if dropped:
        deselected = [items[p] for p in sorted(dropped)]
        items[:] = [item for p, item in enumerate(items) if p not in dropped]
        config.hook.pytest_deselected(items=deselected)
    config._vera_matrix_sampled_out = len(dropped)  # type: ignore[attr-defined]
    config._vera_matrix_in_full = in_full  # type: ignore[attr-defined]
    workeroutput = getattr(config, "workeroutput", None)
    if workeroutput is not None:
        workeroutput[_SAMPLED_KEY] = len(dropped)
        workeroutput[_IN_FULL_KEY] = in_full


@pytest.hookimpl(optionalhook=True)
def pytest_testnodedown(node: Any, error: object) -> None:
    """pytest-xdist, on the controller: the workers sampled, so the count
    comes back with them.  Every worker collects the same sample."""
    workeroutput = getattr(node, "workeroutput", {})
    config = node.config
    sampled = workeroutput.get(_SAMPLED_KEY)
    if sampled is not None:
        config._vera_matrix_sampled_out = max(
            sampled, getattr(config, "_vera_matrix_sampled_out", 0)
        )
    in_full = workeroutput.get(_IN_FULL_KEY)
    if in_full:
        config._vera_matrix_in_full = {
            **getattr(config, "_vera_matrix_in_full", {}), **in_full
        }


def pytest_terminal_summary(
    terminalreporter: Any, exitstatus: int, config: pytest.Config
) -> None:
    in_full: dict[str, list[str]] = getattr(config, "_vera_matrix_in_full", {})
    for path, why in sorted(in_full.items()):
        terminalreporter.write_line(
            f"{path} runs every matrix cell: the change touches {', '.join(why)}"
        )
    sampled = getattr(config, "_vera_matrix_sampled_out", 0)
    if sampled:
        terminalreporter.write_line(
            f"{sampled} matrix cells sampled out (seed {_seed(config)});"
            " --matrix=full runs every cell"
        )
