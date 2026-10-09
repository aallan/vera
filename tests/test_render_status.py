"""scripts/render_status.py, which writes TESTING.md's generated status.

A count lives in one place, and that place is generated: the script
measures the tree and writes three blocks between markers in TESTING.md,
and `check_doc_counts.py --release` asks whether they are what it would
write now (`stale_blocks`).  Each measurement is checked on a synthetic
tree whose counts cannot coincide with one another, the collection against
a real pytest, the conformance skips against a test module whose skip rule
is not the level rule, and the splice and the freshness check in both
directions.
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

ROOT = Path(__file__).resolve().parent.parent
_SCRIPT = ROOT / "scripts" / "render_status.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("render_status_under_test", _SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


RS = _load()


# ---------------------------------------------------------------------------
# A synthetic tree, every count distinct so that no two can be confused
# ---------------------------------------------------------------------------

_PRECOMMIT = """\
repos:
  - repo: https://github.com/pre-commit/pre-commit-hooks
    rev: v5.0.0
    hooks:
      - id: trailing-whitespace
      - id: check-yaml
  - repo: local
    hooks:
      - id: ruff
        entry: ruff check .
        language: system
      - id: mypy
        entry: mypy vera/
        language: system
      - id: uv-lock-check
        entry: uv lock --check
        language: system
        stages: [pre-push]
"""

_CI = """\
name: CI
on:
  pull_request:
    branches: [main]
jobs:
  plan:
    runs-on: ubuntu-latest
    steps: []
  test:
    strategy:
      matrix:
        os: [a, b, c]
        python-version: ["3.11", "3.12"]
        include:
          - os: d
            python-version: "3.12"
          - os: a
            extra: yes
    runs-on: ${{ matrix.os }}
    steps: []
  lint:
    runs-on: ubuntu-latest
    steps: []
  typecheck:
    runs-on: ubuntu-latest
    steps: []
"""

_MANIFEST = """[
  {"id": "r1", "file": "r1.vera", "level": "run", "title": "R1"},
  {"id": "r2", "file": "r2.vera", "level": "run", "title": "R2"},
  {"id": "r3", "file": "r3.vera", "level": "run", "title": "R3"},
  {"id": "r4", "file": "r4.vera", "level": "run", "title": "R4"},
  {"id": "v1", "file": "v1.vera", "level": "verify", "title": "V1"},
  {"id": "v2", "file": "v2.vera", "level": "verify", "title": "V2"},
  {"id": "c1", "file": "c1.vera", "level": "check", "title": "C1",
   "expected_error": "E111"}
]
"""

_DOC = """\
# Testing

## Overview

{status}
Prose outside the blocks stays as written.

## Test Files

{files}
### Skipped tests

{skips}
## After
"""


def _block(name: str, body: str = "") -> str:
    return f"{RS.begin_marker(name)}\n{body}{RS.end_marker(name)}\n"


def _empty_doc() -> str:
    return _DOC.format(
        status=_block("status"), files=_block("test-files"),
        skips=_block("skipped-tests"),
    )


def _write(path: Path, text: str = "") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _synthetic(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    _write(root / "tests" / "test_alpha.py",
           '"""Alpha | covers   one\nthing.\n\nNot this paragraph."""\n\n\ndef test_a():\n    pass\n')
    _write(root / "tests" / "test_beta.py", "def test_b():\n    pass\n")
    # On disk but collected by nothing: a row with zero tests.
    _write(root / "tests" / "test_gamma.py", '"""Gamma."""\n')
    _write(root / "tests" / "conftest.py", "")
    _write(root / "tests" / "conformance" / "manifest.json", _MANIFEST)
    for name in ("r1", "r2", "v1"):
        _write(root / "tests" / "conformance" / f"{name}.vera")
    _write(root / "tests" / "conformance" / "vera" / "mod.vera")
    for name in ("a", "b", "c", "d", "e"):
        _write(root / "examples" / f"{name}.vera")
    _write(root / "examples" / "vera" / "lib.vera")
    _write(root / "examples" / "README.md")
    for name in ("00-intro.md", "01-lexical.md", "02-types.md", "03-slots.md",
                 "04-expressions.md", "05-functions.md"):
        _write(root / "spec" / name)
    _write(root / "spec" / "README.md")
    for name in ("check_one.py", "check_two.py", "check_three.py",
                 "check_four.py", "check_five.py", "check_six.py",
                 "check_seven.py", "build_site.py", "doc_annotations.py"):
        _write(root / "scripts" / name)
    _write(root / ".pre-commit-config.yaml", _PRECOMMIT)
    _write(root / ".github" / "workflows" / "ci.yml", _CI)
    _write(root / "TESTING.md", _empty_doc())
    return root


_COLLECTION = RS.Collection(
    total=1_234, per_file={"test_alpha.py": 1_200, "test_beta.py": 34},
)
_SKIPS = [
    RS.Skip("test_run[v1]", "v1.vera", "verify", "verify-only", "V1"),
]


def _measure(root: Path, **overrides: Any) -> Any:
    kwargs: dict[str, Any] = {
        "collect": lambda _root: _COLLECTION,
        "registry": lambda _root: (171, 9),
        "skips": lambda _root: list(_SKIPS),
    }
    kwargs.update(overrides)
    tree = RS.measure(root, **kwargs)
    assert not isinstance(tree, str), tree
    return tree


# ---------------------------------------------------------------------------
# The collection
# ---------------------------------------------------------------------------


class TestParseCollection:
    def test_it_counts_each_file_and_the_total(self) -> None:
        out = (
            "tests/test_a.py::TestX::test_one\n"
            "tests/test_a.py::test_two[x y]\n"
            "tests/test_b.py::test_three\n"
            "\n"
            "3 tests collected in 0.10s\n"
        )
        assert RS.parse_collection(out) == RS.Collection(
            3, {"test_a.py": 2, "test_b.py": 1}
        )

    def test_lines_after_the_node_ids_are_not_node_ids(self) -> None:
        """A warning summary after the blank line can name a node too."""
        out = (
            "tests/test_a.py::test_one\n"
            "\n"
            "tests/test_a.py::test_one\n"
            "  PytestWarning: something\n"
            "1 test collected in 0.01s\n"
        )
        assert RS.parse_collection(out) == RS.Collection(1, {"test_a.py": 1})

    def test_a_summary_that_disagrees_with_the_ids_is_a_reason(self) -> None:
        out = "tests/test_a.py::test_one\n\n2 tests collected in 0.01s\n"
        reason = RS.parse_collection(out)
        assert isinstance(reason, str) and "2" in reason and "1" in reason

    def test_no_summary_is_a_reason(self) -> None:
        assert isinstance(RS.parse_collection("tests/test_a.py::t\n"), str)


class TestCollect:
    def test_it_asks_for_every_test(self, tmp_path: Path) -> None:
        """The counts are each file's whole size: `-o addopts=` keeps the
        stress tests pyproject deselects, and `--matrix=full` every cell of
        a class-instrument matrix, which a default collection samples by
        the week.  Without it a release's counts would change from one
        week to the next with no change to the tree."""
        seen: list[list[str]] = []

        def run(command: list[str], **kwargs: Any) -> Any:
            seen.append(command)
            assert kwargs["cwd"] == str(tmp_path)
            return subprocess.CompletedProcess(
                command, 0, "tests/test_a.py::t\n\n1 test collected in 0.01s\n", ""
            )

        assert RS.collect(tmp_path, run=run) == RS.Collection(1, {"test_a.py": 1})
        (command,) = seen
        assert "--collect-only" in command
        assert "--matrix=full" in command
        at = command.index("-o")
        assert command[at + 1] == "addopts="

    def test_an_expired_collection_is_a_reason(self, tmp_path: Path) -> None:
        def run(command: list[str], **kwargs: Any) -> Any:
            raise subprocess.TimeoutExpired(command, kwargs["timeout"])

        reason = RS.collect(tmp_path, run=run)
        assert isinstance(reason, str)
        assert f"{RS.COLLECT_TIMEOUT_SECONDS} s" in reason

    def test_a_failed_collection_carries_its_output(self, tmp_path: Path) -> None:
        def run(command: list[str], **kwargs: Any) -> Any:
            return subprocess.CompletedProcess(
                command, 2, "", "ERROR: usage: unrecognized arguments: --bogus\n"
            )

        reason = RS.collect(tmp_path, run=run)
        assert isinstance(reason, str) and "unrecognized arguments" in reason

    def test_a_real_collection_includes_the_stress_tests(self, tmp_path: Path) -> None:
        """Against pytest itself: a tree whose pyproject deselects `stress`,
        with a conftest that accepts `--matrix`, collects all three tests."""
        root = tmp_path / "proj"
        _write(root / "pyproject.toml", (
            "[tool.pytest.ini_options]\n"
            "testpaths = ['tests']\n"
            "markers = ['stress: slow']\n"
            "addopts = \"-m 'not stress'\"\n"
        ))
        _write(root / "tests" / "conftest.py", (
            "def pytest_addoption(parser):\n"
            "    parser.addoption('--matrix', default='sample')\n"
        ))
        _write(root / "tests" / "test_one.py", (
            "import pytest\n\n"
            "def test_a():\n    pass\n\n"
            "@pytest.mark.parametrize('n', [1, 2])\n"
            "@pytest.mark.stress\n"
            "def test_b(n):\n    pass\n"
        ))
        assert RS.collect(root) == RS.Collection(3, {"test_one.py": 3})


# ---------------------------------------------------------------------------
# The other measurements
# ---------------------------------------------------------------------------


class TestSummaryOf:
    def test_the_first_paragraph_on_one_line(self) -> None:
        source = '"""First  line\n  continues.\n\nSecond paragraph."""\n'
        assert RS.summary_of(source) == "First line continues."

    def test_a_pipe_cannot_end_the_table_cell(self) -> None:
        assert RS.summary_of('"""a | b"""\n') == "a \\| b"

    def test_no_docstring_is_an_empty_cell(self) -> None:
        assert RS.summary_of("x = 1\n") == ""


class TestMatrixSize:
    @pytest.mark.parametrize(
        ("matrix", "cells"),
        [
            ({"os": ["a", "b"], "py": ["1", "2", "3"]}, 6),
            # An include that overwrites an axis value is a new cell...
            ({"os": ["a"], "py": ["1"], "include": [{"os": "z", "py": "1"}]}, 2),
            # ...and one that only adds a key extends the cells it fits.
            ({"os": ["a"], "py": ["1"], "include": [{"os": "a", "extra": 1}]}, 1),
            ({"os": ["a", "b"], "py": ["1", "2"], "exclude": [{"os": "b", "py": "2"}]}, 3),
            ({"include": [{"os": "a"}, {"os": "b"}]}, 2),
        ],
    )
    def test_it_counts_cells_as_github_does(self, matrix: dict[str, Any], cells: int) -> None:
        assert RS.matrix_size(matrix) == cells


class TestMeasure:
    def test_each_count_is_read_from_its_source(self, tmp_path: Path) -> None:
        tree = _measure(_synthetic(tmp_path))
        assert tree.collection == _COLLECTION
        assert list(tree.test_files) == ["test_alpha.py", "test_beta.py", "test_gamma.py"]
        assert tree.test_files["test_alpha.py"] == (8, "Alpha \\| covers one thing.")
        assert len(tree.manifest) == 7
        assert tree.examples == 5          # examples/*.vera, not examples/vera/
        assert tree.corpus == 10           # recursive: 6 + 4
        assert (tree.builtins, tree.effects) == (171, 9)
        assert tree.chapters == 6          # spec/NN-*.md, not spec/README.md
        assert tree.hooks == {"commit": 4, "push": 1}
        assert tree.ci_jobs == 4
        assert tree.matrix_cells == {"test": 7}
        assert tree.gate_scripts == 7      # scripts/check_*.py only
        assert tree.skips == _SKIPS

    def test_a_failed_collection_is_the_reason(self, tmp_path: Path) -> None:
        reason = RS.measure(
            _synthetic(tmp_path), collect=lambda _root: "no pytest",
            registry=lambda _root: (0, 0), skips=lambda _root: [],
        )
        assert reason == "no pytest"

    def test_the_real_tree_is_readable(self) -> None:
        """The real manifest, configuration files and registries, with the
        collection faked: what the release PR reads parses as the readers
        expect."""
        sys_path = list(sys.path)
        try:
            sys.path.insert(0, str(ROOT))
            tree = RS.measure(ROOT, collect=lambda _root: RS.Collection(
                1, {"test_render_status.py": 1}))
        finally:
            sys.path[:] = sys_path
        assert not isinstance(tree, str), tree
        assert tree.builtins > 0 and tree.effects > 0
        assert tree.hooks and tree.matrix_cells.get("test", 0) > 0
        assert tree.skips, "the conformance suite skips no stage at all"


# ---------------------------------------------------------------------------
# The conformance skips are the tests' own decision
# ---------------------------------------------------------------------------

_CONFORMANCE_MODULE = '''\
import pytest

MANIFEST = [
    {"id": "p_x", "file": "p_x.vera", "level": "run", "title": "Ends in x"},
    {"id": "q", "file": "q.vera", "level": "check", "title": "Negative",
     "expected_error": "E321", "expected_error_stage": "compile"},
]


def _vera(*args):
    raise AssertionError("the real CLI ran")


def parse_file(path):
    raise AssertionError("the real parser ran")


def format_source(source):
    raise AssertionError("the real formatter ran")


@pytest.mark.parametrize("entry", MANIFEST, ids=lambda e: "id-" + e["id"])
class TestConformance:
    def test_parse(self, entry):
        parse_file(entry["file"])

    def test_run(self, entry):
        # Not the level rule: a `run`-level entry skips here by its name.
        if entry["id"].endswith("_x"):
            pytest.skip("suffix-x")
        _vera("run", entry["file"])

    def test_check(self, entry):
        if entry["level"] == "check":
            pytest.skip("odd")
        _vera("check", entry["file"])
'''


class TestConformanceSkips:
    def test_the_rows_are_what_the_stage_methods_decide(self, tmp_path: Path) -> None:
        """The module's skip rule is not the level rule — the level rule
        would skip `q`'s run and nothing of `p_x` — so the rows can only
        come from calling the stages; the ids come from the parametrize
        mark, and no real work runs."""
        root = tmp_path / "repo"
        _write(root / "tests" / "test_conformance.py", _CONFORMANCE_MODULE)
        assert RS.conformance_skips(root) == [
            RS.Skip("test_run[id-p_x]", "p_x.vera", "run", "suffix-x", "Ends in x"),
            RS.Skip(
                "test_check[id-q]", "q.vera", "check", "odd",
                "Negative; negative: `expected_error: E321` at `compile`",
            ),
        ]

    def test_a_renamed_piece_of_work_is_an_error_not_a_real_run(
        self, tmp_path: Path
    ) -> None:
        root = tmp_path / "repo"
        _write(root / "tests" / "test_conformance.py",
               _CONFORMANCE_MODULE.replace("def _vera(", "def _run_cli("))
        with pytest.raises(RuntimeError, match="_vera"):
            RS.conformance_skips(root)

    def test_every_real_row_really_skips(self) -> None:
        """Against the real suite: each row's stage, called with nothing
        replaced, skips with the message the row states."""
        rows = RS.conformance_skips(ROOT)
        assert rows
        module = RS._conformance_module(ROOT / "tests" / "test_conformance.py")
        entries = {entry["file"]: entry for entry in module.MANIFEST}
        for row in rows:
            stage = row.test.split("[", 1)[0]
            with pytest.raises(pytest.skip.Exception) as raised:
                getattr(module.TestConformance(), stage)(entries[row.program])
            assert raised.value.msg == row.message, row


# ---------------------------------------------------------------------------
# Rendering, splicing and the freshness check
# ---------------------------------------------------------------------------


class TestRender:
    def test_the_status_block_states_every_count(self, tmp_path: Path) -> None:
        status = RS.render(_measure(_synthetic(tmp_path)))["status"]
        for fact in (
            "| **Tests** | 1,234 collected from 3 test files, which hold 11 lines |",
            "7 in `tests/conformance/manifest.json`: 0 at `parse`, 1 at `check`,"
            " 2 at `verify`, 4 at `run`; 1 of them negative fixtures",
            "| **Example programs** | 5 in `examples/` |",
            "| **Corpus programs** | 10 `.vera` files",
            "| **Built-in functions** | 171,",
            "| **Effects** | 9,",
            "| **Spec chapters** | 6 in `spec/` |",
            "5 in `.pre-commit-config.yaml`: 4 at commit, 1 at push |",
            "4 in `.github/workflows/ci.yml`; the `test` job's matrix has 7 cells |",
            "| **Gate scripts** | 7 `scripts/check_*.py` |",
        ):
            assert fact in status, fact
        assert "--matrix=full" in status, "the block says how the tests were counted"

    def test_the_file_table_has_a_row_per_file(self, tmp_path: Path) -> None:
        files = RS.render(_measure(_synthetic(tmp_path)))["test-files"]
        assert files.splitlines()[2:] == [
            "| `test_alpha.py` | 1,200 | 8 | Alpha \\| covers one thing. |",
            "| `test_beta.py` | 34 | 2 |  |",
            "| `test_gamma.py` | 0 | 1 | Gamma. |",
        ]

    def test_the_skip_block_counts_its_rows(self, tmp_path: Path) -> None:
        skips = RS.render(_measure(_synthetic(tmp_path)))["skipped-tests"]
        assert skips.startswith("The suite skips 1 conformance-stage tests")
        assert "| `test_run[v1]` | `v1.vera` | `verify` | verify-only | V1 |" in skips


class TestSplice:
    def test_only_the_blocks_change_and_a_second_splice_is_a_no_op(self) -> None:
        text = _empty_doc()
        blocks = {"status": "S\n", "test-files": "F\n", "skipped-tests": "K\n"}
        once = RS.splice(text, blocks)
        assert RS.blocks_in(once) == blocks
        assert RS.splice(once, blocks) == once
        outside = [line for line in once.splitlines() if line not in ("S", "F", "K")]
        assert outside == text.splitlines()

    @pytest.mark.parametrize(
        "edit",
        [
            lambda t: t.replace(RS.end_marker("status") + "\n", "", 1),
            lambda t: t.replace(RS.begin_marker("test-files"),
                                RS.begin_marker("test-files") + "\n" + RS.begin_marker("test-files"), 1),
            lambda t: t.replace(RS.begin_marker("skipped-tests"), "x " + RS.begin_marker("skipped-tests"), 1),
        ],
        ids=["missing end", "duplicate begin", "marker inside a line"],
    )
    def test_markers_it_cannot_read_are_refused(self, edit: Any) -> None:
        text = edit(_empty_doc())
        assert isinstance(RS.blocks_in(text), str)
        with pytest.raises(ValueError):
            RS.splice(text, {name: "" for name in RS.BLOCKS})

    def test_an_end_before_its_begin_is_refused(self) -> None:
        text = _empty_doc().replace(
            _block("status"), f"{RS.end_marker('status')}\n{RS.begin_marker('status')}\n"
        )
        assert "before" in RS.blocks_in(text)


class TestStaleBlocks:
    @staticmethod
    def _current(tmp_path: Path) -> tuple[Path, Any]:
        root = _synthetic(tmp_path)
        tree = _measure(root)
        doc = root / "TESTING.md"
        doc.write_text(RS.splice(doc.read_text(encoding="utf-8"), RS.render(tree)),
                       encoding="utf-8")
        return root, tree

    def test_a_current_document_is_fresh(self, tmp_path: Path) -> None:
        root, tree = self._current(tmp_path)
        assert RS.stale_blocks(root, measure=lambda _root: tree) == []

    @pytest.mark.parametrize(
        ("block", "old", "new"),
        [
            ("status", "| **Example programs** | 5 in", "| **Example programs** | 4 in"),
            ("test-files", "| `test_beta.py` | 34 |", "| `test_beta.py` | 33 |"),
            ("skipped-tests", "| verify-only |", "| check-only |"),
        ],
        ids=["status", "test-files", "skipped-tests"],
    )
    def test_each_block_is_checked(
        self, tmp_path: Path, block: str, old: str, new: str
    ) -> None:
        root, tree = self._current(tmp_path)
        doc = root / "TESTING.md"
        text = doc.read_text(encoding="utf-8")
        assert text.count(old) == 1
        doc.write_text(text.replace(old, new), encoding="utf-8")
        errors = RS.stale_blocks(root, measure=lambda _root: tree)
        assert len(errors) == 1, errors
        assert f"`{block}` block" in errors[0]
        assert new.strip("| ") in errors[0], "the first difference is named"

    def test_a_tree_that_moved_makes_the_document_stale(self, tmp_path: Path) -> None:
        root, tree = self._current(tmp_path)
        moved = tree._replace(examples=6)
        (error,) = RS.stale_blocks(root, measure=lambda _root: moved)
        assert "`status` block" in error

    def test_unreadable_markers_are_one_error(self, tmp_path: Path) -> None:
        root, tree = self._current(tmp_path)
        doc = root / "TESTING.md"
        doc.write_text(doc.read_text(encoding="utf-8").replace(
            RS.end_marker("skipped-tests"), ""), encoding="utf-8")
        (error,) = RS.stale_blocks(root, measure=lambda _root: tree)
        assert RS.end_marker("skipped-tests") in error


class TestMain:
    def test_it_writes_the_blocks_once(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        root = _synthetic(tmp_path)
        tree = _measure(root)
        monkeypatch.setattr(RS, "ROOT", root)
        monkeypatch.setattr(RS, "measure", lambda _root: tree)
        monkeypatch.setattr(sys, "path", list(sys.path))
        assert RS.main([]) == 0
        written = (root / "TESTING.md").read_text(encoding="utf-8")
        assert RS.blocks_in(written) == RS.render(tree)
        assert "Prose outside the blocks stays as written." in written
        assert "Rewrote" in capsys.readouterr().out
        assert RS.main([]) == 0
        assert (root / "TESTING.md").read_text(encoding="utf-8") == written
        assert "current" in capsys.readouterr().out

    def test_a_tree_it_cannot_measure_writes_nothing(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        root = _synthetic(tmp_path)
        before = (root / "TESTING.md").read_text(encoding="utf-8")
        monkeypatch.setattr(RS, "ROOT", root)
        monkeypatch.setattr(RS, "measure", lambda _root: "pytest collection failed")
        monkeypatch.setattr(sys, "path", list(sys.path))
        assert RS.main([]) == 1
        assert (root / "TESTING.md").read_text(encoding="utf-8") == before
        assert "pytest collection failed" in capsys.readouterr().err
