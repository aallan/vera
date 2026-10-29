"""Sharding (tests/shard.py): `--shard=K/N` runs the K-th of N parts of the
collection.

A pull request runs the suite on Linux in three shards and on Windows in
two, so the shards have to be the suite between them: over one collection
every test lands in exactly one shard, whatever else selected it, and in the
same shard on every run.  Three layers:

1. **The rule** — `parse_shard` reads `K/N` and refuses anything else, and
   `shard_of` puts a node id in one shard of `N` by a hash of the id alone,
   the same in any process whatever its hash seed, pinned on known ids.
2. **The plugin** — pytest run in a subprocess over synthetic files with the
   plugin and the matrix sample loaded by `-p`: the shards of a collection
   are disjoint and their union is the collection, for two and three shards,
   after a `-k` selection and after the matrix sample (which is drawn from
   the whole collection, so a shard holds its share of one sample); the same
   shards on a second run under another hash seed; under xdist a shard runs
   exactly the tests it collects; a malformed `--shard` is a usage error.
3. **The wiring** — the repository's conftest loads the plugin, and the
   pull-request lane's shard job runs every shard of each platform's count,
   each cell handing the suite its own `K/N` and the plan job's list of
   changed files.
"""

from __future__ import annotations

import os
import re
import shlex
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

import pytest
import yaml

from tests import shard

ROOT = Path(__file__).resolve().parent.parent
CI = ROOT / ".github" / "workflows" / "ci.yml"


# ---------------------------------------------------------------------------
# 1. The rule
# ---------------------------------------------------------------------------


class TestTheRule:
    @pytest.mark.parametrize(
        ("value", "want"), [("1/1", (1, 1)), ("1/3", (1, 3)), ("3/3", (3, 3)), ("2/2", (2, 2))],
    )
    def test_it_reads_k_of_n(self, value: str, want: tuple[int, int]) -> None:
        assert shard.parse_shard(value) == want

    @pytest.mark.parametrize(
        "value", ["0/3", "4/3", "1/0", "-1/3", "1", "a/b", "1/3/4", "", " 1/3", "1/ 3", "1.0/3"],
    )
    def test_it_refuses_anything_else(self, value: str) -> None:
        with pytest.raises(ValueError):
            shard.parse_shard(value)

    @pytest.mark.parametrize("count", [1, 2, 3, 5])
    def test_every_id_lands_in_one_shard_of_the_count(self, count: int) -> None:
        ids = [f"tests/test_x.py::test_{n}[{n % 7}]" for n in range(500)]
        shards = [shard.shard_of(nodeid, count) for nodeid in ids]
        assert set(shards) == set(range(1, count + 1))

    def test_the_shard_is_a_function_of_the_id_alone(self) -> None:
        """Pinned: a change of the hash would move every test, and a shard
        that depends on the process (Python's salted `hash`) would move them
        on every run."""
        ids = (
            "tests/test_parser.py::test_empty_module",
            "tests/test_conformance.py::TestConformance::test_run[ch03_slot_indexing]",
            "tests/test_shard.py::TestTheRule::test_it_reads_k_of_n[1/3-want1]",
        )
        assert [shard.shard_of(nodeid, 3) for nodeid in ids] == PINNED_OF_3
        assert [shard.shard_of(nodeid, 5) for nodeid in ids] == PINNED_OF_5

    def test_the_shard_does_not_depend_on_the_hash_seed(self) -> None:
        ids = [f"tests/test_y.py::test_{n}" for n in range(200)]
        program = (
            "import sys; from tests import shard; "
            "print([shard.shard_of(i, 3) for i in sys.argv[1:]])"
        )
        outputs = set()
        for seed in ("0", "1", "12345"):
            result = subprocess.run(
                [sys.executable, "-c", program, *ids],
                cwd=ROOT, env={**os.environ, "PYTHONHASHSEED": seed},
                capture_output=True, text=True, encoding="utf-8", check=True,
            )
            outputs.add(result.stdout)
        assert len(outputs) == 1, outputs


# The shards `shard_of` gives the three ids above, of three and of five.
PINNED_OF_3 = [3, 1, 1]
PINNED_OF_5 = [5, 4, 5]


# ---------------------------------------------------------------------------
# 2. The plugin, in a pytest of its own over synthetic files
# ---------------------------------------------------------------------------

_MARKED = '''
import pytest

pytestmark = pytest.mark.matrix(decides=["pkg/mod.py"])


def test_plain():
    pass


@pytest.mark.parametrize("a", range(10))
@pytest.mark.parametrize("b", range(30))
def test_grid(a, b):
    pass


@pytest.mark.parametrize("n", range(200))
def test_long(n):
    pass
'''

_UNMARKED = '''
import pytest


class TestThings:
    @pytest.mark.parametrize("n", range(120))
    def test_one(self, n):
        pass

    def test_two(self):
        pass


@pytest.mark.parametrize("word", ["alpha", "beta", "gamma", "delta"])
def test_words(word):
    pass
'''

# test_plain 1, test_grid 300, test_long 200; TestThings 121; test_words 4.
_WHOLE = 1 + 300 + 200 + 121 + 4


# The order the two plugins are registered in.  Hooks of one priority run
# last-registered first, so the shard must not depend on it.
_PLUGINS = ("tests.shard", "tests.matrix_sample")


def _pytest(
    tmp_path: Path, *args: str, hash_seed: str | None = None,
    plugins: tuple[str, ...] = _PLUGINS,
) -> subprocess.CompletedProcess[str]:
    """pytest over the synthetic files, with the shard plugin and the matrix
    sample loaded, and `VERA_MATRIX_CHANGED` absent: CI sets it for the suite
    itself, and a run under test must not inherit the pull request's list."""
    (tmp_path / "pytest.ini").write_text(
        "[pytest]\nmarkers =\n    matrix: a generated class-instrument matrix\n",
        encoding="utf-8",
    )
    (tmp_path / "test_marked.py").write_text(_MARKED, encoding="utf-8")
    (tmp_path / "test_unmarked.py").write_text(_UNMARKED, encoding="utf-8")
    env = {**os.environ, "PYTHONPATH": str(ROOT)}
    env.pop("PYTEST_ADDOPTS", None)
    env.pop("VERA_MATRIX_CHANGED", None)
    if hash_seed is not None:
        env["PYTHONHASHSEED"] = hash_seed
    return subprocess.run(
        [
            sys.executable, "-m", "pytest", *(arg for name in plugins for arg in ("-p", name)),
            "-p", "no:cacheprovider", "-c", str(tmp_path / "pytest.ini"),
            "--rootdir", str(tmp_path), *args,
        ],
        cwd=tmp_path, env=env, capture_output=True, text=True,
        encoding="utf-8", check=False,
    )


def _collected(result: subprocess.CompletedProcess[str]) -> list[str]:
    assert result.returncode == 0, result.stdout + result.stderr
    return [line for line in result.stdout.splitlines() if "::" in line]


def _assert_a_partition(whole: list[str], parts: list[list[str]]) -> None:
    """Pairwise disjoint, and their union is `whole`, item for item."""
    seen: dict[str, int] = {}
    for number, part in enumerate(parts, start=1):
        assert len(part) == len(set(part)), f"shard {number} collects a test twice"
        for nodeid in part:
            assert nodeid not in seen, f"{nodeid} is in shards {seen[nodeid]} and {number}"
            seen[nodeid] = number
    assert sorted(seen) == sorted(whole)
    assert all(part for part in parts), [len(part) for part in parts]


class TestThePlugin:
    _FULL = ("--collect-only", "-q", "--matrix=full")

    @pytest.mark.parametrize("count", [2, 3])
    def test_the_shards_are_the_collection(self, tmp_path: Path, count: int) -> None:
        whole = _collected(_pytest(tmp_path, *self._FULL))
        assert len(whole) == _WHOLE
        parts = [
            _collected(_pytest(tmp_path, *self._FULL, f"--shard={k}/{count}"))
            for k in range(1, count + 1)
        ]
        _assert_a_partition(whole, parts)

    def test_the_shards_divide_a_keyword_selection(self, tmp_path: Path) -> None:
        select = ("-k", "grid or words")
        whole = _collected(_pytest(tmp_path, *self._FULL, *select))
        assert len(whole) == 304
        parts = [
            _collected(_pytest(tmp_path, *self._FULL, *select, f"--shard={k}/3"))
            for k in (1, 2, 3)
        ]
        _assert_a_partition(whole, parts)

    @pytest.mark.parametrize("plugins", [_PLUGINS, _PLUGINS[::-1]], ids=["shard-first", "sample-first"])
    def test_the_shards_divide_one_matrix_sample(self, tmp_path: Path, plugins: tuple[str, ...]) -> None:
        """The sample is drawn from the whole collection and the shards then
        divide it, whichever plugin is registered first.  Drawn in each shard
        instead, from that shard's cells, the union would be another sample:
        each shard keeps its own first and last cell and its own floor."""
        seed = ("--collect-only", "-q", "--matrix-seed", "2026-W41")
        whole = _collected(_pytest(tmp_path, *seed, plugins=plugins))
        assert len(whole) < _WHOLE, "the synthetic matrix was not sampled"
        parts = [_collected(_pytest(tmp_path, *seed, f"--shard={k}/3", plugins=plugins)) for k in (1, 2, 3)]
        _assert_a_partition(whole, parts)

    def test_another_hash_seed_is_the_same_shards(self, tmp_path: Path) -> None:
        first = [_collected(_pytest(tmp_path, *self._FULL, f"--shard={k}/3", hash_seed="1")) for k in (1, 2, 3)]
        again = [_collected(_pytest(tmp_path, *self._FULL, f"--shard={k}/3", hash_seed="987")) for k in (1, 2, 3)]
        assert first == again

    def test_a_shard_under_xdist_runs_what_it_collects(self, tmp_path: Path) -> None:
        """Every worker collects and shards for itself, so they must agree
        (xdist stops on "Different tests were collected" otherwise), and the
        run executes exactly the shard's tests."""
        collected = _collected(_pytest(tmp_path, *self._FULL, "--shard=2/3"))
        result = _pytest(tmp_path, "-q", "-n", "2", "--matrix=full", "--shard=2/3", "-rA")
        assert result.returncode == 0, result.stdout + result.stderr
        ran = re.findall(r"^PASSED (\S+)$", result.stdout, re.MULTILINE)
        assert sorted(ran) == sorted(collected)
        assert f"shard 2/3 runs {len(collected)} of the {_WHOLE} tests selected" in result.stdout, result.stdout

    def test_the_run_says_which_shard_it_is(self, tmp_path: Path) -> None:
        result = _pytest(tmp_path, "--collect-only", "-q", "--matrix=full", "--shard=2/3")
        whole = _pytest(tmp_path, "--collect-only", "-q", "--matrix=full")
        assert f"shard 2/3 runs {len(_collected(result))} of the {_WHOLE} tests selected" in result.stdout, result.stdout
        assert "shard" not in whole.stdout.lower(), whole.stdout

    @pytest.mark.parametrize("value", ["0/3", "4/3", "two/three", "3"])
    def test_a_malformed_shard_is_a_usage_error(self, tmp_path: Path, value: str) -> None:
        result = _pytest(tmp_path, "--collect-only", "-q", f"--shard={value}")
        assert result.returncode == 4, result.stdout + result.stderr
        assert "--shard" in result.stderr, result.stderr


# ---------------------------------------------------------------------------
# 3. The wiring: the repository's conftest, and the pull-request lane
# ---------------------------------------------------------------------------


class TestTheWiring:
    def _collect(self, *args: str) -> list[str]:
        env = {**os.environ}
        env.pop("PYTEST_ADDOPTS", None)
        env.pop("VERA_MATRIX_CHANGED", None)
        result = subprocess.run(
            [sys.executable, "-m", "pytest", "tests/test_shard.py", "--collect-only", "-q", *args],
            cwd=ROOT, env=env, capture_output=True, text=True, encoding="utf-8", check=False,
        )
        return _collected(result)

    def test_the_repository_shards_its_own_collection(self) -> None:
        whole = self._collect()
        _assert_a_partition(whole, [self._collect(f"--shard={k}/2") for k in (1, 2)])

    def test_the_lane_runs_every_shard_of_each_platform(self) -> None:
        """Each platform's cells run shards 1 to N of one N, so the suite
        runs whole on each; a cell lost from the list, or two cells with one
        number, would drop a part of the suite from every pull request with
        nothing failing."""
        job = yaml.safe_load(CI.read_text(encoding="utf-8"))["jobs"]["shard"]
        assert set(job["strategy"]["matrix"]) == {"include"}, job["strategy"]["matrix"]
        cells = job["strategy"]["matrix"]["include"]
        by_platform: dict[str, list[tuple[int, int]]] = defaultdict(list)
        for cell in cells:
            by_platform[cell["os"]].append((int(cell["shard"]), int(cell["shards"])))
        # The images every gating job runs on (README § Supported
        # platforms), so a label GitHub moves never changes them.
        assert set(by_platform) == {"ubuntu-24.04", "windows-2025-vs2026"}, by_platform
        for platform, numbers in by_platform.items():
            counts = {count for _, count in numbers}
            assert len(counts) == 1, (platform, numbers)
            (count,) = counts
            assert sorted(k for k, _ in numbers) == list(range(1, count + 1)), (platform, numbers)
        from tests.test_gate_placement import render

        runs = [step for step in job["steps"] if re.match(r"pytest\b", str(step.get("run", "")))]
        assert len(runs) == 1, job["steps"]
        for cell in cells:
            command = render(str(runs[0]["run"]), {f"matrix.{k}": v for k, v in cell.items()},
                             runs[0].get("env"))
            assert f"--shard={cell['shard']}/{cell['shards']}" in shlex.split(command), (cell, command)
        assert (runs[0].get("env") or {}).get("VERA_MATRIX_CHANGED") == "${{ needs.plan.outputs.changed }}"
