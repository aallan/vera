"""Sharding: ``--shard=K/N`` runs the K-th of N parts of the collection.

The pull-request lane runs the suite in shards, on Linux in three and on
Windows in two (the ``shard`` job in .github/workflows/ci.yml), so the
shards have to be the suite between them.  A test belongs to shard
``int(sha256(node id)) mod N + 1``: a function of its node id alone, so over
one collection every test lands in exactly one shard, and in the same shard
on every run, in every process, on every platform and Python version.  No
durations file is kept, so there is nothing to refresh as tests come and go;
the hash spreads the tests, and their time, evenly enough at the suite's
size, and each shard runs its part under its own xdist workers.

The shard is taken last, after every other selection: ``-k`` and ``-m``, and
the class-instrument matrices' sample (tests/matrix_sample.py), which is
drawn from the whole collection, so each shard runs its share of one sample
rather than a sample of its own share.  The tests of the other shards are
deselected, never skipped, and the run's summary names the shard.

``tests/conftest.py`` loads this module as a plugin (``pytest_plugins``);
``parse_shard`` and ``shard_of`` are functions of plain data, so the rule is
tested without a pytest session (tests/test_shard.py).
"""

from __future__ import annotations

import argparse
import hashlib
import re
from collections.abc import Generator
from typing import Any

import pytest

_SHARD = re.compile(r"([1-9][0-9]*)/([1-9][0-9]*)")

# What a shard kept of the tests selected before it, `(kept, selected)`.
_COUNTS_KEY = "vera_shard_counts"


def parse_shard(value: str) -> tuple[int, int]:
    """`K/N` as `(K, N)`, with `1 <= K <= N`; anything else is a ValueError."""
    match = _SHARD.fullmatch(value)
    if match is None:
        raise ValueError(f"{value!r} is not K/N")
    k, n = int(match.group(1)), int(match.group(2))
    if k > n:
        raise ValueError(f"shard {k} of {n} does not exist")
    return k, n


def shard_of(nodeid: str, count: int) -> int:
    """The shard, from 1 to `count`, that the test with this node id is in."""
    digest = hashlib.sha256(nodeid.encode("utf-8")).hexdigest()
    return int(digest, 16) % count + 1


def _option(value: str) -> tuple[int, int]:
    try:
        return parse_shard(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"{exc}: --shard takes K/N with 1 <= K <= N") from exc


def pytest_addoption(parser: pytest.Parser) -> None:
    parser.getgroup("shard", "sharding").addoption(
        "--shard",
        type=_option,
        default=None,
        dest="shard",
        metavar="K/N",
        help=(
            "run only the K-th of N parts of the collection: the tests whose "
            "node id hashes to it, after every other selection "
            "(see tests/shard.py)"
        ),
    )


# A wrapper, so the shard is taken after every implementation of the hook
# has run: `-k` and `-m`, and the matrix sample, which is `trylast`.
@pytest.hookimpl(wrapper=True)
def pytest_collection_modifyitems(
    config: pytest.Config, items: list[pytest.Item]
) -> Generator[None, Any, Any]:
    result = yield
    chosen = config.getoption("shard")
    if chosen is None:
        return result
    k, n = chosen
    kept = [item for item in items if shard_of(item.nodeid, n) == k]
    dropped = [item for item in items if shard_of(item.nodeid, n) != k]
    counts = (len(kept), len(items))
    if dropped:
        items[:] = kept
        config.hook.pytest_deselected(items=dropped)
    config._vera_shard_counts = counts  # type: ignore[attr-defined]
    workeroutput = getattr(config, "workeroutput", None)
    if workeroutput is not None:
        workeroutput[_COUNTS_KEY] = counts
    return result


@pytest.hookimpl(optionalhook=True)
def pytest_testnodedown(node: Any, error: object) -> None:
    """pytest-xdist, on the controller: the workers collected and sharded,
    so the counts come back with them.  Every worker keeps the same shard."""
    counts = getattr(node, "workeroutput", {}).get(_COUNTS_KEY)
    if counts is not None:
        node.config._vera_shard_counts = tuple(counts)


def pytest_terminal_summary(
    terminalreporter: Any, exitstatus: int, config: pytest.Config
) -> None:
    chosen = config.getoption("shard")
    if chosen is None:
        return
    k, n = chosen
    counts = getattr(config, "_vera_shard_counts", None)
    size = f" runs {counts[0]:,} of the {counts[1]:,} tests selected" if counts else ""
    terminalreporter.write_line(
        f"shard {k}/{n}{size}; the other shards' tests are deselected"
    )
