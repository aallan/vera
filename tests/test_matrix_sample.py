"""The `matrix` marker's sample (tests/matrix_sample.py).

A pull request runs a sample of every class-instrument matrix, and the whole
of one whose file it changes or whose deciding module it changes; the
nightly run, the release merge and the coverage job run them all in full.
So the sample's rules carry the gate's coverage of those files.  Three
layers:

1. **The rules** — `choose` over plain cells: what is always kept (every cell
   of a small or `repro`-named function, the first and last cell, strict
   xfails, whole-word keep tokens and never a substring of a longer word),
   the floor of `max(20, 10%)`, a value of every small dimension, a cell in
   every run of the collection order, and the seed: the same sample for the
   same seed in any process, whatever its hash seed, and another for another
   week.  And the deciding-module rule over plain paths: `VERA_MATRIX_CHANGED`
   read one path per line, a file put in full by a change to itself or to a
   module it declares, paths compared whole.
2. **The plugin** — pytest run in a subprocess over a synthetic marked file
   with the hooks loaded by `-p`: the counts it collects with and without
   `--matrix=full`, an unmarked file left whole, a test named on the command
   line run in full, the "sampled out" summary line in place of any skip, and
   one sample across xdist workers.  Under `VERA_MATRIX_CHANGED`: a file run
   in full when it or a module it declares changed and sampled otherwise,
   per file, the flag overriding the variable either way, and the summary
   naming each file run whole and why, on xdist too.
3. **The wiring** — the repository's own conftest samples a real marked
   file by default, collects all of it under `--matrix=full`, and collects
   all of it when its deciding module changed; every marked file is on the
   list, names the modules that decide it, each a file in the tree, and
   every path a marker names is one the plan job's diff can list.
"""

from __future__ import annotations

import ast
import datetime
import fnmatch
import importlib
import itertools
import json
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

from tests import matrix_sample as ms
from tests.matrix_sample import Cell, choose

ROOT = Path(__file__).resolve().parent.parent

# The variable CI hands the suite on a pull request (the plan job's diff in
# .github/workflows/ci.yml).  Spelled out rather than read from the module
# under test: the name is the contract between the two.
CHANGED = "VERA_MATRIX_CHANGED"


def _grid(*sizes: int, prefix: str = "tests/test_g.py::test_g") -> list[Cell]:
    """The cells of a function with one stacked `parametrize` per size: the
    product of the dimensions, each argname indexing its own list."""
    names = [f"d{axis}" for axis in range(len(sizes))]
    combos: list[tuple[int, ...]] = [()]
    for size in sizes:
        combos = [(*combo, value) for value in range(size) for combo in combos]
    cells: list[Cell] = []
    for combo in combos:
        cell_id = "-".join(f"v{value}" for value in combo)
        cells.append(Cell(
            nodeid=f"{prefix}[{cell_id}]",
            cell_id=cell_id,
            indices=tuple(zip(names, combo, strict=True)),
        ))
    return cells


def _flat(count: int, ids: list[str] | None = None, prefix: str = "tests/test_f.py::test_f") -> list[Cell]:
    """The cells of a function with one `parametrize` over `count` values."""
    ids = ids or [f"c{index}" for index in range(count)]
    return [
        Cell(nodeid=f"{prefix}[{cell_id}]", cell_id=cell_id, indices=(("cell", index),))
        for index, cell_id in enumerate(ids)
    ]


# ---------------------------------------------------------------------------
# 1. The rules
# ---------------------------------------------------------------------------


class TestTheRules:
    @pytest.mark.parametrize("count", [1, 2, 19, 20])
    def test_a_function_at_or_under_the_floor_keeps_every_cell(self, count: int) -> None:
        assert choose(_flat(count), "test_f", "2026-W41") == set(range(count))

    @pytest.mark.parametrize("name", ["test_issue_repro", "test_repro_runs", "TestX::test_the_repro"])
    def test_a_repro_named_function_keeps_every_cell(self, name: str) -> None:
        assert choose(_flat(300), name, "2026-W41") == set(range(300))

    @pytest.mark.parametrize(("count", "floor"), [(21, 20), (150, 20), (200, 20), (201, 21), (3300, 330)])
    def test_the_sample_keeps_at_least_the_floor(self, count: int, floor: int) -> None:
        assert ms.target(count) == floor
        kept = choose(_flat(count), "test_f", "2026-W41")
        assert len(kept) >= floor
        assert len(kept) < count

    def test_the_first_and_the_last_cell_are_kept(self) -> None:
        for seed in ("2026-W41", "2026-W42", "2027-W01"):
            kept = choose(_flat(500), "test_f", seed)
            assert {0, 499} <= kept, seed

    def test_every_strict_xfail_is_kept(self) -> None:
        cells = _flat(400)
        pinned = {17, 233, 398}
        cells = [
            Cell(cell.nodeid, cell.cell_id, cell.indices, xfail=index in pinned)
            for index, cell in enumerate(cells)
        ]
        for seed in ("2026-W41", "2026-W42"):
            assert pinned <= choose(cells, "test_f", seed)

    @pytest.mark.parametrize("word", sorted(ms.KEEP_TOKENS))
    def test_a_keep_word_in_a_cell_id_keeps_the_cell(self, word: str) -> None:
        ids = [f"c{index}" for index in range(400)]
        ids[211] = f"shape|{word}|d2"
        ids[312] = f"{word.upper()}_first-x"
        kept = choose(_flat(400, ids), "test_f", "2026-W41")
        assert {211, 312} <= kept

    def test_a_keep_word_inside_a_longer_word_keeps_nothing(self) -> None:
        """`red` is in `declared`, `required` and `covered`, which 1,253 ids
        of the candidate files contain; a substring rule would keep them."""
        words = ("declared", "required", "unnamed")
        ids = [f"{words[index % 3]}-{index}" for index in range(400)]
        kept = choose(_flat(400, ids), "test_f", "2026-W41")
        assert len(kept) < 100

    @pytest.mark.parametrize("seed", ["2026-W41", "2026-W42", "2026-W43"])
    def test_every_value_of_every_small_dimension_appears(self, seed: str) -> None:
        """600 cells and a sample of 60, and the fast dimension's 50 values
        each sit in every 50th cell, so a run of the collection order holds
        ten of them and a pick per run misses about fourteen: only the cover
        reaches them all."""
        cells = _grid(50, 12)
        kept = choose(cells, "test_g", seed)
        assert ms.target(600) == 60
        for axis, size in enumerate((50, 12)):
            seen = {dict(cells[index].indices)[f"d{axis}"] for index in kept}
            assert seen == set(range(size)), (axis, sorted(set(range(size)) - seen))

    def test_one_large_dimension_is_not_covered_value_by_value(self) -> None:
        """A single `parametrize` over generated cells is one dimension with
        a value per cell; covering it would keep the whole matrix."""
        kept = choose(_flat(3300), "test_f", "2026-W41")
        assert len(kept) < 400

    def test_every_run_of_the_collection_order_has_a_kept_cell(self) -> None:
        count = 3300
        want = ms.target(count)
        kept = choose(_flat(count), "test_f", "2026-W41")
        for stratum in range(want):
            low, high = stratum * count // want, (stratum + 1) * count // want
            assert any(low <= index < high for index in kept), (low, high)

    def test_the_same_seed_is_the_same_sample(self) -> None:
        cells = _grid(6, 50)
        assert choose(cells, "test_g", "2026-W41") == choose(list(cells), "test_g", "2026-W41")

    def test_another_week_is_another_sample(self) -> None:
        cells = _grid(6, 50)
        assert choose(cells, "test_g", "2026-W41") != choose(cells, "test_g", "2026-W42")

    @pytest.mark.parametrize(
        ("day", "week"),
        [
            ("2026-10-05", "2026-W41"),
            ("2026-10-11", "2026-W41"),
            ("2026-10-12", "2026-W42"),
            ("2026-12-31", "2026-W53"),
            ("2027-01-01", "2026-W53"),
            ("2027-01-04", "2027-W01"),
        ],
    )
    def test_the_seed_is_the_iso_week(self, day: str, week: str) -> None:
        """Monday to Sunday is one week, across the turn of a year too, so a
        sample is stable within a week and rotates with it."""
        assert ms.iso_week(datetime.date.fromisoformat(day)) == week

    def test_the_sample_does_not_depend_on_the_hash_seed(self) -> None:
        """Each xdist worker is a process with its own string-hash seed, and
        workers that sampled differently would collect different tests."""
        program = (
            "import json\n"
            "from tests.matrix_sample import Cell, choose\n"
            "cells = [Cell(f'tests/test_f.py::test_f[c{i}]', f'c{i}', (('cell', i),))"
            " for i in range(1000)]\n"
            "print(json.dumps(sorted(choose(cells, 'test_f', '2026-W41'))))\n"
        )
        answers = []
        for hash_seed in ("0", "1", "4242"):
            env = {**os.environ, "PYTHONHASHSEED": hash_seed, "PYTHONPATH": str(ROOT)}
            result = subprocess.run(
                [sys.executable, "-c", program], cwd=ROOT, env=env,
                capture_output=True, text=True, encoding="utf-8", check=True,
            )
            answers.append(json.loads(result.stdout))
        assert answers[0] == answers[1] == answers[2]


class TestTheDecidingModuleRule:
    """A marked file runs whole when the change under test touches the file
    or a module its marker declares as deciding its class; CI names the
    files a pull request changes in `VERA_MATRIX_CHANGED`."""

    def test_the_variable_is_one_path_per_line(self) -> None:
        value = "vera/a.py\n\n  tests/test_b.py \r\nvera\\c.py\n./vera/d.py\n"
        assert ms.changed_paths(value) == {
            "vera/a.py", "tests/test_b.py", "vera/c.py", "vera/d.py",
        }

    @pytest.mark.parametrize("value", [None, "", "\n", "  \r\n"])
    def test_an_empty_or_absent_variable_names_nothing(self, value: str | None) -> None:
        assert ms.changed_paths(value) == frozenset()

    def test_a_changed_decider_puts_its_file_in_full(self) -> None:
        changed = frozenset({"README.md", "vera/b.py"})
        assert ms.decided_in_full("tests/test_x.py", ("vera/a.py", "vera/b.py"), changed) == ["vera/b.py"]

    def test_a_change_to_the_file_itself_puts_it_in_full(self) -> None:
        changed = frozenset({"tests/test_x.py"})
        assert ms.decided_in_full("tests/test_x.py", ("vera/a.py",), changed) == ["tests/test_x.py"]

    def test_every_reason_is_named(self) -> None:
        changed = frozenset({"vera/b.py", "tests/test_x.py", "vera/a.py", "vera/c.py"})
        assert ms.decided_in_full("tests/test_x.py", ("vera/b.py", "vera/a.py"), changed) == [
            "tests/test_x.py", "vera/a.py", "vera/b.py",
        ]

    @pytest.mark.parametrize(
        "path",
        ["vera/a.pyc", "vera/ab.py", "a.py", "vera", "vera/", "VERA/A.PY", "x/vera/a.py", "tests/test_x.py.orig"],
    )
    def test_paths_are_compared_whole(self, path: str) -> None:
        """Neither a prefix, a suffix nor another case of a declared path
        is that path."""
        assert ms.decided_in_full("tests/test_x.py", ("vera/a.py",), frozenset({path})) == []

    def test_no_change_puts_nothing_in_full(self) -> None:
        assert ms.decided_in_full("tests/test_x.py", ("vera/a.py",), frozenset()) == []

    def test_the_marker_names_its_deciders(self) -> None:
        """A list names one module per entry, and a single string is one
        module, never its characters."""
        assert ms.deciders(pytest.mark.matrix(decides=["vera/a.py", "vera/b.py"]).mark) == (
            "vera/a.py", "vera/b.py",
        )
        assert ms.deciders(pytest.mark.matrix(decides="vera/a.py").mark) == ("vera/a.py",)
        assert ms.deciders(pytest.mark.matrix.mark) == ()


# ---------------------------------------------------------------------------
# 2. The plugin, in a pytest of its own over a synthetic marked file
# ---------------------------------------------------------------------------

_MARKED = '''
import pytest

pytestmark = pytest.mark.matrix(decides=["pkg/mod.py", "pkg/other.py"])


def test_plain():
    pass


@pytest.mark.parametrize("a", range(10))
@pytest.mark.parametrize("b", range(30))
def test_grid(a, b):
    pass


@pytest.mark.parametrize("n", range(12))
def test_small(n):
    pass


@pytest.mark.parametrize("n", range(50))
def test_issue_repro(n):
    pass


@pytest.mark.parametrize(
    "n",
    [pytest.param(i, marks=pytest.mark.xfail(strict=True)) if i == 77 else i for i in range(200)],
)
def test_pinned(n):
    assert n != 77
'''

_UNMARKED = '''
import pytest


@pytest.mark.parametrize("n", range(300))
def test_unmarked(n):
    pass
'''

# A second marked file, decided by a module of its own, for the cells that
# show the rule is per file.  Written only where a test asks for it.
_MARKED_TOO = '''
import pytest

pytestmark = pytest.mark.matrix(decides=["pkg/third.py"])


@pytest.mark.parametrize("n", range(100))
def test_too(n):
    pass
'''

# test_plain 1, test_grid 300 (a sample of 30), test_small 12, test_issue_repro
# 50, test_pinned 200 (a sample of 20); and 300 unmarked.
_FULL = 1 + 300 + 12 + 50 + 200 + 300


def _pytest(
    tmp_path: Path, *args: str, changed: str | None = None, files: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    """pytest over the synthetic files, with `VERA_MATRIX_CHANGED` set to
    `changed` or, by default, absent: CI sets it for the suite itself, and a
    run under test must not inherit the pull request's own list."""
    (tmp_path / "pytest.ini").write_text(
        "[pytest]\nmarkers =\n    matrix: a generated class-instrument matrix\n",
        encoding="utf-8",
    )
    (tmp_path / "test_marked.py").write_text(_MARKED, encoding="utf-8")
    (tmp_path / "test_unmarked.py").write_text(_UNMARKED, encoding="utf-8")
    for name, text in (files or {}).items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    env = {**os.environ, "PYTHONPATH": str(ROOT)}
    env.pop("PYTEST_ADDOPTS", None)
    env.pop(CHANGED, None)
    if changed is not None:
        env[CHANGED] = changed
    return subprocess.run(
        [
            sys.executable, "-m", "pytest", "-p", "tests.matrix_sample",
            "-p", "no:cacheprovider", "-c", str(tmp_path / "pytest.ini"),
            "--rootdir", str(tmp_path), *args,
        ],
        cwd=tmp_path, env=env, capture_output=True, text=True,
        encoding="utf-8", check=False,
    )


def _collected(result: subprocess.CompletedProcess[str]) -> list[str]:
    return [line for line in result.stdout.splitlines() if "::" in line]


class TestThePlugin:
    def test_the_default_samples_and_full_collects_everything(self, tmp_path: Path) -> None:
        sampled = _pytest(tmp_path, "--collect-only", "-q", "--matrix-seed", "2026-W41")
        full = _pytest(tmp_path, "--collect-only", "-q", "--matrix=full")
        assert sampled.returncode == 0, sampled.stdout + sampled.stderr
        assert full.returncode == 0, full.stdout + full.stderr
        assert len(_collected(full)) == _FULL
        kept = _collected(sampled)
        by_function = {
            name: [line for line in kept if f"::{name}" in line]
            for name in ("test_plain", "test_grid", "test_small", "test_issue_repro", "test_pinned", "test_unmarked")
        }
        assert len(by_function["test_plain"]) == 1
        assert len(by_function["test_small"]) == 12
        assert len(by_function["test_issue_repro"]) == 50
        assert len(by_function["test_unmarked"]) == 300
        assert 30 <= len(by_function["test_grid"]) < 300
        assert 20 <= len(by_function["test_pinned"]) < 200
        assert any(line.endswith("test_pinned[77]") for line in kept)
        assert any(line.endswith("test_grid[0-0]") for line in kept)
        assert any(line.endswith("test_grid[29-9]") for line in kept)
        dropped = _FULL - len(kept)
        assert f"{len(kept)}/{_FULL} tests collected ({dropped} deselected)" in sampled.stdout

    def test_a_run_reports_the_sample_and_skips_nothing(self, tmp_path: Path) -> None:
        result = _pytest(tmp_path, "-q", "-rs", "--matrix-seed", "2026-W41")
        assert result.returncode == 0, result.stdout + result.stderr
        out = result.stdout
        match = re.search(r"(\d+) matrix cells sampled out \(seed 2026-W41\)", out)
        assert match is not None, out
        assert int(match.group(1)) > 0
        assert "skipped" not in out
        assert "1 xfailed" in out

    def test_full_reports_no_sample(self, tmp_path: Path) -> None:
        result = _pytest(tmp_path, "-q", "--matrix=full")
        assert result.returncode == 0, result.stdout + result.stderr
        assert "sampled out" not in result.stdout
        assert f"{_FULL - 1} passed, 1 xfailed" in result.stdout

    def test_a_test_named_on_the_command_line_runs_in_full(self, tmp_path: Path) -> None:
        result = _pytest(
            tmp_path, "--collect-only", "-q", "test_marked.py::test_grid",
            "--matrix-seed", "2026-W41",
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert len(_collected(result)) == 300

    def test_a_keyword_selection_is_sampled_after_it_selects(self, tmp_path: Path) -> None:
        """`-k` and `-m` deselect in the same hook as the sample, and the
        sample runs last, so it samples what they kept: a sampled function
        keeps at least the floor of its selected cells, and the first and
        the last of them.  Sampled first, the 200 cells' sample would lose
        to `-k` every kept cell whose id has no `1`."""
        result = _pytest(
            tmp_path, "--collect-only", "-q", "--matrix-seed", "2026-W41", "-k", "test_pinned and 1",
        )
        assert result.returncode == 0, result.stdout + result.stderr
        kept = _collected(result)
        selected = [n for n in range(200) if "1" in str(n)]
        assert len(selected) == 119
        assert all("::test_pinned[" in line for line in kept), kept
        assert ms.FLOOR <= len(kept) < len(selected), len(kept)
        assert kept[0].endswith("test_pinned[1]"), kept[0]
        assert kept[-1].endswith("test_pinned[199]"), kept[-1]

    def test_the_week_moves_the_sample(self, tmp_path: Path) -> None:
        one = _collected(_pytest(tmp_path, "--collect-only", "-q", "--matrix-seed", "2026-W41"))
        again = _collected(_pytest(tmp_path, "--collect-only", "-q", "--matrix-seed", "2026-W41"))
        other = _collected(_pytest(tmp_path, "--collect-only", "-q", "--matrix-seed", "2026-W42"))
        assert one == again
        assert one != other

    def test_xdist_workers_collect_one_sample(self, tmp_path: Path) -> None:
        """Two workers that sampled differently would stop the run with
        "Different tests were collected"; the controller also has to report
        the count its workers sampled out."""
        result = _pytest(tmp_path, "-q", "-n", "2", "--matrix-seed", "2026-W41")
        assert result.returncode == 0, result.stdout + result.stderr
        assert re.search(r"\d+ matrix cells sampled out \(seed 2026-W41\)", result.stdout), result.stdout


def _in_file(lines: list[str], name: str) -> list[str]:
    return [line for line in lines if line.startswith(f"{name}::")]


class TestTheDecidingModuleRuleInARun:
    """`VERA_MATRIX_CHANGED` in a pytest run: the synthetic marked file
    declares `pkg/mod.py` and `pkg/other.py` as deciding it."""

    _SEED = ("--matrix-seed", "2026-W41")

    def test_a_changed_decider_runs_its_file_in_full(self, tmp_path: Path) -> None:
        result = _pytest(tmp_path, "--collect-only", "-q", *self._SEED, changed="README.md\npkg/other.py\n")
        assert result.returncode == 0, result.stdout + result.stderr
        assert len(_collected(result)) == _FULL
        assert "deselected" not in result.stdout

    def test_a_change_to_the_file_itself_runs_it_in_full(self, tmp_path: Path) -> None:
        result = _pytest(tmp_path, "--collect-only", "-q", *self._SEED, changed="test_marked.py\n")
        assert result.returncode == 0, result.stdout + result.stderr
        assert len(_collected(result)) == _FULL

    def test_any_other_change_leaves_the_sample(self, tmp_path: Path) -> None:
        """A prefix, a neighbour and another file's decider are not this
        file's deciders, so the sample is the one no variable collects."""
        alone = _collected(_pytest(tmp_path, "--collect-only", "-q", *self._SEED))
        other = _collected(_pytest(
            tmp_path, "--collect-only", "-q", *self._SEED,
            changed="pkg/mod.pyc\npkg\npkg/third.py\ntest_unmarked.py\nREADME.md\n",
        ))
        assert len(alone) < _FULL
        assert other == alone

    def test_the_rule_is_per_file(self, tmp_path: Path) -> None:
        """A change to one file's decider runs that file whole and leaves
        the other marked file sampled."""
        alone = _collected(_pytest(
            tmp_path, "--collect-only", "-q", *self._SEED, files={"test_marked_too.py": _MARKED_TOO},
        ))
        changed = _collected(_pytest(
            tmp_path, "--collect-only", "-q", *self._SEED,
            changed="pkg/third.py\n", files={"test_marked_too.py": _MARKED_TOO},
        ))
        assert len(_in_file(alone, "test_marked_too.py")) < 100
        assert len(_in_file(changed, "test_marked_too.py")) == 100
        assert _in_file(changed, "test_marked.py") == _in_file(alone, "test_marked.py")

    def test_the_flag_overrides_the_variable_either_way(self, tmp_path: Path) -> None:
        alone = _collected(_pytest(tmp_path, "--collect-only", "-q", *self._SEED))
        sampled = _collected(_pytest(
            tmp_path, "--collect-only", "-q", "--matrix=sample", *self._SEED, changed="pkg/mod.py\n",
        ))
        full = _collected(_pytest(tmp_path, "--collect-only", "-q", "--matrix=full", changed="README.md\n"))
        assert sampled == alone
        assert len(full) == _FULL

    def test_the_summary_names_each_file_run_whole_and_why(self, tmp_path: Path) -> None:
        result = _pytest(tmp_path, "-q", *self._SEED, changed="pkg/other.py\ntest_marked.py\n")
        assert result.returncode == 0, result.stdout + result.stderr
        assert re.search(
            r"^test_marked\.py runs every matrix cell: the change touches pkg/other\.py, test_marked\.py$",
            result.stdout, re.MULTILINE,
        ), result.stdout
        assert "sampled out" not in result.stdout
        assert f"{_FULL - 1} passed, 1 xfailed" in result.stdout

    def test_xdist_workers_agree_and_the_controller_reports_it(self, tmp_path: Path) -> None:
        """Every worker reads the same variable, so they collect the same
        tests; the controller names the file its workers ran whole and
        counts what they sampled out of the other one."""
        result = _pytest(
            tmp_path, "-q", "-n", "2", *self._SEED,
            changed="pkg/mod.py\n", files={"test_marked_too.py": _MARKED_TOO},
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert re.search(
            r"^test_marked\.py runs every matrix cell: the change touches pkg/mod\.py$",
            result.stdout, re.MULTILINE,
        ), result.stdout
        assert re.search(r"\d+ matrix cells sampled out \(seed 2026-W41\)", result.stdout), result.stdout
        assert "test_marked_too.py runs every" not in result.stdout


# ---------------------------------------------------------------------------
# 3. The wiring: the repository's conftest, over a real marked file
# ---------------------------------------------------------------------------


def _matrix_mark(name: str) -> pytest.Mark:
    """The `matrix` mark a test file carries at module level, read from the
    module the way pytest reads it."""
    module = importlib.import_module(f"tests.{name.removesuffix('.py')}")
    declared = module.pytestmark if isinstance(module.pytestmark, list) else [module.pytestmark]
    found = [mark for mark in (getattr(m, "mark", m) for m in declared) if mark.name == "matrix"]
    assert len(found) == 1, f"{name} carries {len(found)} `matrix` marks at module level"
    return found[0]


def _carries_the_marker(path: Path) -> bool:
    """Whether a file assigns a `pytest.mark.matrix` to `pytestmark` at
    module level.  Read from the syntax tree: `test_matrix_sample.py`'s own
    synthetic files hold the same line inside a string."""
    for node in ast.parse(path.read_text(encoding="utf-8")).body:
        if not isinstance(node, ast.Assign):
            continue
        if not any(isinstance(target, ast.Name) and target.id == "pytestmark" for target in node.targets):
            continue
        for part in ast.walk(node.value):
            if (
                isinstance(part, ast.Attribute) and part.attr == "matrix"
                and isinstance(part.value, ast.Attribute) and part.value.attr == "mark"
            ):
                return True
    return False


def _plan_pathspec() -> list[str]:
    """The pathspec of the plan job's `git diff --name-only`: what a pull
    request's list of changed files can name at all."""
    workflow = yaml.safe_load((ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8"))
    step = next(s for s in workflow["jobs"]["plan"]["steps"] if s.get("id") == "changed")
    for line in str(step["run"]).splitlines():
        tokens = shlex.split(line)
        if tokens[:3] == ["git", "diff", "--name-only"]:
            spec = tokens[tokens.index("--") + 1:] if "--" in tokens else []
            return list(itertools.takewhile(lambda t: not t.startswith((">", "|")), spec))
    raise AssertionError("the plan job's `changed` step runs no `git diff --name-only`")


def _listable(path: str, spec: list[str]) -> bool:
    """Whether git lists `path` under `spec`: a directory names what is
    below it, and a glob's `*` matches across `/`, as in a git pathspec."""
    if not spec:
        return True
    for entry in spec:
        if any(ch in entry for ch in "*?["):
            if fnmatch.fnmatchcase(path, entry):
                return True
        elif path == entry.rstrip("/") or path.startswith(entry.rstrip("/") + "/"):
            return True
    return False


class TestTheWiring:
    _FILE = "tests/test_nested_container_guards.py"

    def _collect(self, *args: str, changed: str | None = None) -> str:
        env = {**os.environ}
        env.pop("PYTEST_ADDOPTS", None)
        env.pop(CHANGED, None)
        if changed is not None:
            env[CHANGED] = changed
        result = subprocess.run(
            [sys.executable, "-m", "pytest", self._FILE, "--collect-only", "-q", *args],
            cwd=ROOT, env=env, capture_output=True, text=True, encoding="utf-8",
            check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        return result.stdout.strip().splitlines()[-1]

    def test_a_marked_file_is_sampled_by_default_and_whole_under_full(self) -> None:
        full = self._collect("--matrix=full")
        sampled = self._collect("--matrix-seed", "2026-W41")
        total = int(re.match(r"(\d+) tests collected", full).group(1))  # type: ignore[union-attr]
        match = re.match(rf"(\d+)/{total} tests collected \((\d+) deselected\)", sampled)
        assert match is not None, sampled
        kept, dropped = int(match.group(1)), int(match.group(2))
        assert kept + dropped == total
        assert ms.FLOOR <= kept < total / 2

    def test_the_marked_files_are_marked(self) -> None:
        """Every file the gate samples carries the marker at module level,
        and the corpus differentials and hand-written files do not."""
        for name in MARKED_FILES:
            _matrix_mark(name)
        for name in UNMARKED_FILES:
            text = (ROOT / "tests" / name).read_text(encoding="utf-8")
            assert "pytest.mark.matrix" not in text, name

    def test_the_list_is_every_marked_file(self) -> None:
        """A file marked but missing from the list would escape the checks
        below, its deciders among them."""
        marked = {path.name for path in (ROOT / "tests").glob("test_*.py") if _carries_the_marker(path)}
        assert marked == set(MARKED_FILES)

    def test_every_marked_file_names_the_modules_that_decide_it(self) -> None:
        """At least one, each a repository-relative POSIX path to a file in
        the tree: a misspelt or moved module would never match a change, and
        the file would run its sample when its class's module changed."""
        for name in MARKED_FILES:
            decides = ms.deciders(_matrix_mark(name))
            assert decides, f"{name} names no module that decides its class"
            for path in decides:
                assert re.fullmatch(r"[\w.-]+(/[\w.-]+)+", path) and ".." not in path.split("/"), (name, path)
                assert (ROOT / path).is_file(), f"{name} names {path}, which is not a file in the tree"

    def test_a_changed_decider_runs_a_real_marked_file_in_full(self) -> None:
        decides = ms.deciders(_matrix_mark(Path(self._FILE).name))
        assert decides
        full = self._collect("--matrix=full")
        changed = self._collect("--matrix-seed", "2026-W41", changed=f"README.md\n{decides[-1]}\n")
        unrelated = self._collect("--matrix-seed", "2026-W41", changed="README.md\nvera/__main__.py\n")
        assert re.fullmatch(r"\d+ tests collected in .*", full), full
        assert changed.split(" in ")[0] == full.split(" in ")[0], (changed, full)
        assert "deselected" in unrelated, unrelated

    def test_every_path_a_marker_names_is_one_the_plan_job_can_list(self) -> None:
        """The plan job lists only the paths a matrix can be decided by, so
        the list stays far below the 32,767 characters an environment
        variable can hold on Windows; a decider outside that pathspec would
        never reach `VERA_MATRIX_CHANGED`."""
        spec = _plan_pathspec()
        for name in MARKED_FILES:
            for path in (f"tests/{name}", *ms.deciders(_matrix_mark(name))):
                assert _listable(path, spec), f"the plan job's diff ({spec}) never lists {path}, which {name} names"


# The generated class-instrument files the gate samples, and the large files
# that are not generated matrices and run whole: two corpus differentials and
# a file of hand-written cases with no parametrisation above sixteen cells.
MARKED_FILES = (
    "test_nested_container_guards.py",
    "test_literal_typing_from_context_1541_1565.py",
    "test_evaluated_position_obligations_1480.py",
    "test_check_implies_compile.py",
    "test_one_classifier_1503.py",
    "test_boundary_guard_correctness_1466.py",
    "test_termination_rule.py",
    "test_cross_namespace_ctor_1436.py",
    "test_named_traps_1479.py",
    "test_clone_decreases_1569.py",
    "test_self_qualified_calls_1558.py",
    "test_binder_position_generator.py",
)
UNMARKED_FILES = (
    "test_obligations.py",
    "test_int_overflow_differential.py",
    "test_name_resolution_spine_1316.py",
)
