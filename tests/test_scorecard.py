"""scripts/scorecard.py, the scorecard rows of TESTING.md's generated status.

Each measurer reproduces the command the audit of v0.2.0 measured its row
with, so the two columns count the same thing.  Every one is checked on a
synthetic tree whose answer is known and is neither zero nor the audit's
value, and each fixture carries the decoy its likeliest mutant would count:
a nested function, a name that only looks like the measured one, a module
the count leaves out.  The GitHub, Codecov and junit readers are checked
against responses and a junit file recorded from the real services and a
real run (`tests/fixtures/scorecard/`), the subprocess census against a real
pytest run, and the freshness split, which re-measures the tree's rows and
asks of the others only that each carries its window, in both directions.
"""

from __future__ import annotations

import importlib.util
import json
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import pytest

ROOT = Path(__file__).resolve().parent.parent
_SCRIPT = ROOT / "scripts" / "scorecard.py"
_FIXTURES = Path(__file__).resolve().parent / "fixtures" / "scorecard"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("scorecard_under_test", _SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


SC = _load()


def _write(path: Path, text: str = "") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _body(lines: int) -> str:
    """A function body of `lines` lines, the `def` line among them."""
    return "".join("    x = 1\n" for _ in range(lines - 1))


# ---------------------------------------------------------------------------
# The tree's rows, each on a tree whose answer is known
# ---------------------------------------------------------------------------


class TestInferFunctions:
    def test_every_infer_function_in_vera_is_counted(self, tmp_path: Path) -> None:
        """Three, one nested and one outside `vera/wasm/`, as the audit's 32
        held 3 in `vera/checker/`; `_inferred` and `infer_type` are not
        `_infer_*` functions."""
        _write(tmp_path / "vera" / "wasm" / "inference.py", (
            "def _infer_expr(x):\n"
            "    def _infer_inner(y):\n"
            "        return y\n"
            "    return _infer_inner(x)\n"
            "def _inferred(x):\n    return x\n"
            "def infer_type(x):\n    return x\n"
        ))
        _write(tmp_path / "vera" / "checker" / "core.py", (
            "class Checker:\n"
            "    def _infer_call(self, x):\n        return x\n"
        ))
        assert SC.infer_functions(tmp_path) == 3


class TestNatIntTwins:
    def test_a_wasm_name_is_read_without_its_codegen_word(self, tmp_path: Path) -> None:
        """Four twins: `_result_is_nat` by name, `_has_nat_origin` and
        `_overflow_arith_type` through the `codegen` word the backend's
        copy carries, and `_register_widenings` by its `widen` word.  A
        same-named helper that is not about `Nat` or `Int` is not counted,
        nor is `_print_point`, whose words hold the letters of `int` but
        not the word."""
        _write(tmp_path / "vera" / "verifier.py", (
            "class V:\n"
            "    def _result_is_nat(self): ...\n"
            "    def _has_nat_origin(self): ...\n"
            "    def _overflow_arith_type(self): ...\n"
            "    def _register_widenings(self): ...\n"
            "    def _field_is_generic(self): ...\n"
            "    def _print_point(self): ...\n"
            "    def _only_here_nat(self): ...\n"
        ))
        _write(tmp_path / "vera" / "wasm" / "operators.py", (
            "class W:\n"
            "    def _result_is_nat(self): ...\n"
            "    def _has_nat_origin_codegen(self): ...\n"
            "    def _overflow_arith_codegen_type(self): ...\n"
            "    def _field_is_generic(self): ...\n"
            "    def _print_point(self): ...\n"
        ))
        _write(tmp_path / "vera" / "wasm" / "deep" / "more.py", (
            "def _register_widenings(): ...\n"
        ))
        assert SC.nat_int_twins(tmp_path) == [
            "_has_nat_origin", "_overflow_arith_type", "_register_widenings",
            "_result_is_nat",
        ]


class TestGuardedClaims:
    _VERIFIER = (
        "class V:\n"
        "    def _record_nat_bind_tier3(self, decl, node, site, status, guarded=None):\n"
        "        ...\n"
        "    def _record_refined_bind_tier3(self, decl, node, site, guarded=None):\n"
        "        ...\n"
        "    def _record_undecided_safety(self, decl, node):\n"
        "        ...\n"
        "    def _record_obligation(self, kind, guarded=None):\n"
        "        ...\n"
        "    def _check(self, guarded=None):\n"
        "        ...\n"
        "    def walk(self, d, n, s, st):\n"
        "        self._record_nat_bind_tier3(d, n, s, st, guarded=True)\n"
        "        self._record_nat_bind_tier3(d, n, s, st, guarded=self.g(n))\n"
        "        self._record_refined_bind_tier3(d, n, s, False)\n"
        "        self._record_nat_bind_tier3(d, n, s, st)\n"
        "        self._record_undecided_safety(d, n)\n"
        "        self._record_obligation('nat_bind', guarded=True)\n"
        "        self._check(guarded=True)\n"
        "        self._check(guarded=False)\n"
    )

    def test_a_claim_is_a_tier3_recorder_call_that_passes_guarded(
        self, tmp_path: Path
    ) -> None:
        """Three claims: two by keyword, one by position.  The recorder
        call that leaves `guarded` to its default makes no claim, and
        neither does a `guarded=` passed to anything but a `_record_*_tier3`
        recorder: not to another `_record_*` method, nor to a checker."""
        _write(tmp_path / "vera" / "verifier.py", self._VERIFIER)
        assert SC.guarded_claims(tmp_path) == 3


class TestExprDispatchers:
    _AST = (
        "class Node: ...\n"
        "class Expr(Node): ...\n"
        "class Literal(Expr): ...\n"
        "class IntLit(Literal): ...\n"
        "class BinaryExpr(Expr): ...\n"
        "class Stmt(Node): ...\n"
        "def format_expr(e):\n"
        "    if isinstance(e, IntLit):\n"
        "        return 'i'\n"
    )

    def test_a_function_dispatching_on_an_expr_subclass_is_counted(
        self, tmp_path: Path
    ) -> None:
        """Four dispatchers: by attribute, by a bare name in a tuple, a
        method, and a nested function, which counts as itself and not as
        its enclosing function.  A test against a statement class or the
        `Expr` base is not dispatch over the subclasses, and `vera/ast.py`,
        which defines them, is not counted."""
        _write(tmp_path / "vera" / "ast.py", self._AST)
        _write(tmp_path / "vera" / "walk.py", (
            "from vera import ast\n"
            "from vera.ast import IntLit, BinaryExpr\n"
            "def by_attribute(e):\n"
            "    return isinstance(e, ast.IntLit)\n"
            "def by_tuple(e):\n"
            "    return isinstance(e, (IntLit, BinaryExpr))\n"
            "def on_statements(s):\n"
            "    return isinstance(s, ast.Stmt)\n"
            "def on_the_base(e):\n"
            "    return isinstance(e, ast.Expr)\n"
            "def outer(e):\n"
            "    def inner(x):\n"
            "        return isinstance(x, ast.Literal)\n"
            "    return inner(e)\n"
            "class Walker:\n"
            "    def visit(self, e):\n"
            "        return isinstance(e, BinaryExpr)\n"
        ))
        assert SC.expr_dispatchers(tmp_path) == 4


class TestLongFunctions:
    def test_a_function_is_long_past_500_lines(self, tmp_path: Path) -> None:
        """Three: one of 501 lines, and a 610-line function with a 600-line
        one inside it, each counted.  Exactly 500 lines is not over."""
        _write(tmp_path / "vera" / "big.py", (
            "def f501():\n" + _body(501)
            + "def f500():\n" + _body(500)
            + "def outer():\n" + "    def inner():\n"
            + "".join("        y = 2\n" for _ in range(599))
            + "".join("    z = 3\n" for _ in range(9))
        ))
        assert SC.long_functions(tmp_path) == 3


class TestHostMirrored:
    # Five built-ins: `log` is in two families and is one built-in, and
    # `_KNOWN` is not a family set.
    _COMPILABILITY = (
        "class Scan:\n"
        "    _MD_BUILTINS = frozenset({'md_parse', 'md_render'})\n"
        "    _MATH_BUILTINS = frozenset({\n"
        "        'log', 'sin', 'cos',\n"
        "    })\n"
        "    _LOG_BUILTINS = frozenset({'log'})\n"
        "    _KNOWN = frozenset({'not_a_family'})\n"
    )
    _WASI = (
        "_MAP_OPS: dict[str, object] = {\n"
        "    'map_new': 1, 'map_get': 2, 'map_size': 3, 'map_keys': 4,\n"
        "}\n"
    )

    def test_the_family_sets_and_the_wasi_map_operations(self, tmp_path: Path) -> None:
        _write(tmp_path / "vera" / "codegen" / "compilability.py", self._COMPILABILITY)
        _write(tmp_path / "vera" / "codegen" / "wasi.py", self._WASI)
        assert SC.host_mirrored(tmp_path) == (5, 4)

    def test_no_family_set_is_an_error_not_a_zero(self, tmp_path: Path) -> None:
        """Zero is the target, so a module that moved its family sets must
        stop the measurement rather than read as the target met."""
        _write(tmp_path / "vera" / "codegen" / "compilability.py", "X = 1\n")
        _write(tmp_path / "vera" / "codegen" / "wasi.py", self._WASI)
        with pytest.raises(SC.MeasureError, match="_BUILTINS"):
            SC.host_mirrored(tmp_path)

    def test_no_wasi_map_table_is_an_error_not_a_zero(self, tmp_path: Path) -> None:
        _write(tmp_path / "vera" / "codegen" / "compilability.py", self._COMPILABILITY)
        _write(tmp_path / "vera" / "codegen" / "wasi.py", "Y = 2\n")
        with pytest.raises(SC.MeasureError, match="_MAP_OPS"):
            SC.host_mirrored(tmp_path)


class TestSyncGates:
    def test_the_audits_mirror_gates_that_still_exist(self, tmp_path: Path) -> None:
        """Two of the audit's eight are left, among five gate scripts: an
        alignment gate, a gate the audit classified otherwise, and a script
        that is not a gate, are not counted."""
        for name in ("check_doc_counts", "check_site_assets",
                     "check_examples_readme", "check_licenses", "check_e602_clean"):
            _write(tmp_path / "scripts" / f"{name}.py")
        _write(tmp_path / "scripts" / "render_status.py")
        assert SC.sync_gates(tmp_path) == (2, 5)

    def test_the_two_alignment_gates_are_reclassified(self, tmp_path: Path) -> None:
        """`check_grammar_alignment` and `check_examples_readme` hold a
        hand-written document to its source, and were reclassified as
        alignment gates on 2026-10-12: the audit's eight are the six counted
        and those two, the audit's own value stays 8 of 23, and the row's
        note says what moved and when."""
        assert SC.ALIGNMENT_GATES == ("check_grammar_alignment", "check_examples_readme")
        assert not set(SC.ALIGNMENT_GATES) & set(SC.MIRROR_GATES)
        assert len(SC.MIRROR_GATES) + len(SC.ALIGNMENT_GATES) == 8
        for name in SC.ALIGNMENT_GATES:
            _write(tmp_path / "scripts" / f"{name}.py")
        assert SC.sync_gates(tmp_path) == (0, 2)
        (row,) = [m for m in SC.MEASURES if m.key == "sync_gates"]
        assert row.audit == "8 of 23"
        assert "reclassified as alignment gates on 2026-10-12" in row.counts
        for name in SC.ALIGNMENT_GATES:
            assert f"`{name}`" in row.counts


class TestGoldenOutputs:
    def test_an_entry_with_its_stdout_has_golden_output(self, tmp_path: Path) -> None:
        manifest = [
            {"id": "a", "level": "run", "expected_exit": 0, "expected_stdout": "1\n"},
            {"id": "b", "level": "run", "expected_exit": 0, "expected_stdout": ""},
            {"id": "c", "level": "run", "expected_exit": 1, "expected_stdout": "x"},
            {"id": "d", "level": "run", "expected_exit": 0,
             "nondeterministic_stdout": "prints the clock"},
            {"id": "e", "level": "check"},
            {"id": "f", "level": "verify"},
        ]
        _write(tmp_path / "tests" / "conformance" / "manifest.json", json.dumps(manifest))
        golden = SC.golden_outputs(tmp_path)
        assert golden == SC.Golden(stdout=3, entries=6, run_level=4, run_pinned=4, exit_only=1)
        assert SC._golden(golden) == "3 of 6; every run-level entry, one of them by exit status only"

    def test_a_run_level_entry_that_pins_nothing(self, tmp_path: Path) -> None:
        """The audit's tree had no pinned run at all; a tree part of the way
        there says how far."""
        manifest = [
            {"id": "a", "level": "run", "expected_exit": 0, "expected_stdout": "1\n"},
            {"id": "b", "level": "run"},
            {"id": "c", "level": "run"},
            {"id": "d", "level": "check"},
        ]
        _write(tmp_path / "tests" / "conformance" / "manifest.json", json.dumps(manifest))
        assert SC._golden(SC.golden_outputs(tmp_path)) == (
            "1 of 4; 1 of the 3 run-level entries"
        )
        none = [{"id": "b", "level": "run"}, {"id": "d", "level": "check"}]
        _write(tmp_path / "tests" / "conformance" / "manifest.json", json.dumps(none))
        assert SC._golden(SC.golden_outputs(tmp_path)) == "0 of 2; no run-level entry"


class TestProgramGenerator:
    @staticmethod
    def _tree(tmp_path: Path, workflows: dict[str, str]) -> Path:
        for name, text in workflows.items():
            _write(tmp_path / ".github" / "workflows" / name, text)
        return tmp_path

    _PR = (
        "on:\n  pull_request:\n    branches: [main]\n"
        "jobs:\n  test:\n    runs-on: ubuntu-latest\n"
        "    steps:\n      - run: pytest -v -n auto\n"
    )

    def test_no_step_runs_a_generator(self, tmp_path: Path) -> None:
        assert SC.program_generator(self._tree(tmp_path, {"ci.yml": self._PR})) == "none"

    def test_a_daily_scheduled_step_is_nightly(self, tmp_path: Path) -> None:
        nightly = (
            "on:\n  schedule:\n    - cron: '0 4 * * *'\n"
            "jobs:\n  gen:\n    runs-on: ubuntu-latest\n    steps:\n"
            "      - name: Generate\n"
            "        run: |\n          python -m vera.program_generator --budget 600\n"
        )
        tree = self._tree(tmp_path, {"ci.yml": self._PR, "generate.yml": nightly})
        assert SC.program_generator(tree) == "nightly"

    def test_a_pull_request_step_runs_on_every_pull_request(self, tmp_path: Path) -> None:
        workflow = self._PR.replace("pytest -v -n auto", "python scripts/program_generator.py")
        assert SC.program_generator(self._tree(tmp_path, {"ci.yml": workflow})) == (
            "every pull request"
        )

    def test_a_weekly_schedule_is_not_nightly(self, tmp_path: Path) -> None:
        weekly = (
            "on:\n  schedule:\n    - cron: '0 6 * * 1'\n"
            "jobs:\n  gen:\n    runs-on: ubuntu-latest\n"
            "    steps:\n      - run: python -m vera.program_generator\n"
        )
        assert SC.program_generator(self._tree(tmp_path, {"weekly.yml": weekly})) == (
            "on a schedule"
        )

    def test_a_job_runs_on_the_events_its_condition_names(self, tmp_path: Path) -> None:
        """ci.yml is triggered by pull requests, merges and the nightly
        schedule; a job that names the schedule in its `if:` runs nightly
        only, whatever else triggers the workflow."""
        ci = (
            "on:\n  pull_request:\n    branches: [main]\n  push:\n    branches: [main]\n"
            "  schedule:\n    - cron: '0 3 * * *'\n"
            "jobs:\n  test:\n    runs-on: ubuntu-latest\n"
            "    steps:\n      - run: pytest -v -n auto\n"
            "  generate:\n    if: github.event_name == 'schedule'\n"
            "    runs-on: ubuntu-latest\n"
            "    steps:\n      - run: python -m vera.program_generator\n"
        )
        assert SC.program_generator(self._tree(tmp_path, {"ci.yml": ci})) == "nightly"


class TestDistrust:
    _TESTER = "def test(path, *, trials=100, distrust=False):\n    ...\n"
    _EXERCISED = (
        "from vera.tester import test\n"
        "def test_corpus():\n    test('x.vera', distrust=True)\n"
    )
    _CI = (
        "on:\n  pull_request:\n    branches: [main]\n"
        "jobs:\n  shard:\n    runs-on: ubuntu-latest\n"
        "    steps:\n"
        "      - run: pytest tests/test_browser.py -v\n"
        "      - run: pytest -v -n 4 --shard=${{ matrix.shard }}/${{ matrix.shards }}\n"
    )

    def _tree(self, tmp_path: Path, *, tester: str, test: str, ci: str) -> Path:
        _write(tmp_path / "vera" / "tester.py", tester)
        _write(tmp_path / "tests" / "test_corpus.py", test)
        _write(tmp_path / ".github" / "workflows" / "ci.yml", ci)
        return tmp_path

    def test_a_suite_that_distrusts_run_by_ci_is_in_ci(self, tmp_path: Path) -> None:
        """The shard step runs the whole suite: the slash inside its
        `${{ }}` expression is not a test path."""
        tree = self._tree(tmp_path, tester=self._TESTER, test=self._EXERCISED, ci=self._CI)
        assert SC.distrust_in_ci(tree) == "yes, in CI"

    def test_a_tester_without_the_mode_is_no(self, tmp_path: Path) -> None:
        tree = self._tree(
            tmp_path, tester="def test(path, *, trials=100):\n    ...\n",
            test=self._EXERCISED, ci=self._CI,
        )
        assert SC.distrust_in_ci(tree) == "no"

    def test_ci_running_only_named_files_is_not_in_ci(self, tmp_path: Path) -> None:
        ci = self._CI.replace(
            "pytest -v -n 4 --shard=${{ matrix.shard }}/${{ matrix.shards }}",
            "pytest tests/test_conformance.py -k run -n auto",
        )
        tree = self._tree(tmp_path, tester=self._TESTER, test=self._EXERCISED, ci=ci)
        assert SC.distrust_in_ci(tree) == "yes, not in CI"

    def test_a_suite_that_never_distrusts_is_not_in_ci(self, tmp_path: Path) -> None:
        tree = self._tree(
            tmp_path, tester=self._TESTER,
            test=self._EXERCISED.replace("distrust=True", "distrust=False"), ci=self._CI,
        )
        assert SC.distrust_in_ci(tree) == "yes, not in CI"


class TestSpec:
    def test_words_and_issue_links(self, tmp_path: Path) -> None:
        """Nine words in two chapters; two issue links, and neither a pull
        request's link nor a bare `#45` is an issue link."""
        _write(tmp_path / "spec" / "00-intro.md", "One two\nthree [#12](https://github.com/aallan/vera/issues/12)\n")
        _write(tmp_path / "spec" / "01-next.md",
               "see https://github.com/aallan/vera/issues/7 and https://github.com/aallan/vera/pull/3 #45\n")
        assert SC.spec_words(tmp_path) == 9
        assert SC.spec_issue_links(tmp_path) == 2


class TestAgainstTheAuditsTree:
    """The measurers against the tree the audit measured, when a copy of it
    is at hand (`VERA_AUDIT_TREE`, an export of 6508cc32): every row the
    tree gives must read the audit's own value, which is what makes the
    two columns commensurable."""

    def test_each_tree_row_reads_the_audits_value(self) -> None:
        import os

        tree = os.environ.get("VERA_AUDIT_TREE")
        if not tree:
            pytest.skip("VERA_AUDIT_TREE names no export of the audit's tree (6508cc32)")
        root = Path(tree)
        assert SC.infer_functions(root) == 32
        assert len(SC.nat_int_twins(root)) == 12
        assert SC.guarded_claims(root) == 38
        assert SC.expr_dispatchers(root) == 191
        assert SC.long_functions(root) == 17
        assert SC.host_mirrored(root)[0] == 53
        # The one row whose columns count different sets, as its note says:
        # the audit's eight, less the two reclassified since as alignment
        # gates.
        assert SC.sync_gates(root) == (8 - len(SC.ALIGNMENT_GATES), 23)
        assert SC.golden_outputs(root) == SC.Golden(0, 256, 176, 0, 0)
        assert SC.program_generator(root) == "none"
        assert SC.distrust_in_ci(root) == "no"
        assert SC.spec_words(root) == 86_558
        assert SC.spec_issue_links(root) == 175


class TestTheRealTree:
    def test_every_tree_measurer_reads_the_real_tree(self) -> None:
        """What the release PR reads parses as each measurer expects."""
        values = SC.tree_values(ROOT, gate_tests=lambda _root: 1)
        assert not isinstance(values, str), values
        assert set(values) == {m.key for m in SC.MEASURES if m.source == SC.TREE}


# ---------------------------------------------------------------------------
# The network's rows, against responses recorded from the real services
# ---------------------------------------------------------------------------

#: When tests/fixtures/scorecard/{github,codecov}.json were recorded.
_RECORDED_AT = datetime(2026, 10, 12, 8, 44, tzinfo=timezone.utc)


def _recorded(name: str) -> Any:
    """A `get` that answers from a recording, and fails on any request the
    recording does not hold: the measurer asks for exactly what it did."""
    store = json.loads((_FIXTURES / f"{name}.json").read_text(encoding="utf-8"))

    def get(url: str) -> Any:
        assert url in store, f"a request the recording does not hold: {url}"
        return store[url]

    return get


class TestTheNetworkRows:
    def test_the_open_issues(self) -> None:
        get = _recorded("github")
        assert SC.open_issues(get, "bug") == 89
        assert SC.open_issues(get, "bug,soundness") == 18

    def test_the_pull_request_runs_that_reached_a_verdict(self) -> None:
        """The recording's newest runs were cancelled by a newer push; the
        twenty taken are the ones that reached a verdict, and a cancelled
        run's jobs are never asked for."""
        import statistics

        runs = SC.pr_runs(_recorded("github"))
        assert len(runs) == 20
        assert round(statistics.median(r.wall_minutes for r in runs), 1) == 36.4
        assert round(statistics.median(r.runner_minutes for r in runs), 1) == 263.6
        assert min(r.created for r in runs).date().isoformat() == "2026-10-09"

    def test_the_pull_requests_merged_since_the_release(self) -> None:
        """Two since v0.2.1, which the release's own pull request
        (`prep/v0.2.1`, merged before it was published) is not one of."""
        get = _recorded("github")
        tag, published = SC.latest_release(get)
        assert (tag, published.isoformat()) == ("v0.2.1", "2026-10-11T05:16:57+00:00")
        prs = SC.fix_prs(get, published)
        assert [(pr.number, pr.runs, round(pr.hours, 2)) for pr in prs] == [
            (1652, 3, 0.84), (1653, 5, 1.55),
        ]

    def test_the_post_merge_coverage(self) -> None:
        assert SC.post_merge_coverage(_recorded("codecov")) == SC.Coverage(
            96.26, "d4488257af1db63358e42b775a4ae690bfdb2616", "2026-10-12",
        )

    def test_each_row_states_its_window(self) -> None:
        values = SC.github_values(
            _recorded("github"), _recorded("codecov"), now=_RECORDED_AT,
        )
        tracker = "the tracker, 2026-10-12 08:44 UTC"
        runs = "20 pull-request runs, 2026-10-09 to 2026-10-12"
        merged = "2 pull requests merged since v0.2.1 (2026-10-11), to 2026-10-12"
        assert values == {
            "soundness_bugs": ("18", tracker),
            "open_bugs": ("89", tracker),
            "ci_wall": ("36.4 min", runs),
            "runner_minutes": ("264", runs),
            "fix_pr_runs": ("4", merged),
            "fix_pr_hours": ("1.2", merged),
            "statement_coverage": (
                "96.26%", "Codecov, the post-merge run of `d448825` (2026-10-12)",
            ),
        }
        assert all(SC.stamped(over) for _now, over in values.values())


def _issues_url(labels: str, page: int) -> str:
    return (f"{SC.GITHUB_API}/repos/aallan/vera/issues?labels={labels}&state=open"
            f"&per_page=100&page={page}")


class TestTheIssueCount:
    def test_a_pull_request_is_not_an_issue(self) -> None:
        """The issues endpoint lists the pull requests that carry a label
        too; a full page asks for the next."""
        first = [{"number": n} for n in range(100)]
        first[3]["pull_request"] = {}
        store = {
            _issues_url("bug", 1): first,
            _issues_url("bug", 2): [{"number": 500}, {"number": 501, "pull_request": {}}],
        }
        assert SC.open_issues(store.__getitem__, "bug") == 100

    @pytest.mark.parametrize("payload", [
        {"message": "API rate limit exceeded", "documentation_url": "https://docs.github.com"},
        ["not an issue"],
    ], ids=["an error object", "a list of another thing"])
    def test_a_listing_that_is_not_a_list_of_issues_is_refused(self, payload: Any) -> None:
        """An error body is an object, and iterating an object yields its
        keys, strings that `"pull_request" not in` tests as substrings: the
        count would be a wrong number with a valid window."""
        with pytest.raises(SC.MeasureError, match="not a list of objects"):
            SC.open_issues(lambda _url: payload, "bug")

    def test_a_pull_request_listing_that_is_not_a_list_is_refused(self) -> None:
        with pytest.raises(SC.MeasureError, match="not a list of objects"):
            SC.fix_prs(lambda _url: {"message": "Not Found"}, datetime(2026, 10, 1, tzinfo=timezone.utc))


class TestTheFixPullRequests:
    """Synthetic responses for what the recording holds no instance of: a
    release branch and Dependabot merging after the release, and a run on a
    branch outside its pull request's lifetime."""

    _SINCE = datetime(2026, 10, 11, 5, 16, tzinfo=timezone.utc)

    @staticmethod
    def _pr(number: int, ref: str, opened: str, merged: str | None, kind: str = "User",
            repo: str = "aallan/vera") -> dict[str, Any]:
        return {"number": number, "created_at": opened, "merged_at": merged,
                "updated_at": merged or opened, "user": {"type": kind},
                "head": {"ref": ref, "repo": {"full_name": repo}}}

    @staticmethod
    def _runs_url(ref: str) -> str:
        return (f"{SC.GITHUB_API}/repos/aallan/vera/actions/workflows/ci.yml/runs"
                f"?event=pull_request&branch={ref}&per_page=100&page=1")

    def test_which_pull_requests_and_which_runs(self) -> None:
        pulls = (f"{SC.GITHUB_API}/repos/aallan/vera/pulls?state=closed&base=main"
                 "&sort=updated&direction=desc&per_page=100&page=1")
        run = lambda when, repo="aallan/vera": {  # noqa: E731
            "created_at": when, "head_repository": {"full_name": repo}}
        store = {
            pulls: [
                self._pr(30, "fix/b", "2026-10-11T08:00:00Z", "2026-10-11T14:00:00Z"),
                self._pr(31, "prep/v0.2.2", "2026-10-11T09:00:00Z", "2026-10-11T13:00:00Z"),
                self._pr(32, "dependabot/uv/x", "2026-10-11T09:00:00Z",
                         "2026-10-11T12:00:00Z", kind="Bot"),
                self._pr(33, "fix/closed", "2026-10-11T09:00:00Z", None),
                self._pr(20, "fix/a", "2026-10-10T20:00:00Z", "2026-10-11T06:00:00Z"),
                self._pr(10, "fix/old", "2026-10-09T08:00:00Z", "2026-10-10T08:00:00Z"),
            ],
            self._runs_url("fix/b"): {"workflow_runs": [
                run("2026-10-11T08:05:00Z"), run("2026-10-11T09:00:00Z"),
                run("2026-10-11T15:00:00Z"),  # after the merge: a later push
                run("2026-10-11T08:30:00Z", repo="someone/vera"),  # a fork's branch
            ]},
            self._runs_url("fix/a"): {"workflow_runs": [
                run("2026-10-10T20:01:00Z"), run("2026-10-11T02:00:00Z"),
                run("2026-10-11T05:00:00Z"),
            ]},
        }
        prs = SC.fix_prs(store.__getitem__, self._SINCE)
        assert [(pr.number, pr.runs, pr.hours) for pr in prs] == [(20, 3, 10.0), (30, 2, 6.0)]

    def test_the_last_commit_with_a_python_upload_of_its_own(self) -> None:
        """The newest commit's Python session was carried forward from the
        one before, and its JavaScript upload is its own: the row reads the
        commit whose post-merge run uploaded Python coverage."""
        base = SC.CODECOV_API
        store = {
            f"{base}/commits/?branch=main&page_size=20": {
                "results": [{"commitid": "a" * 40}, {"commitid": "b" * 40}],
            },
            f"{base}/commits/{'a' * 40}/uploads/": {"results": [
                {"flags": ["javascript"], "upload_type": "uploaded", "created_at": "2026-10-12 08:00:00"},
                {"flags": ["python"], "upload_type": "carriedforward", "created_at": "2026-10-12 08:00:01"},
            ]},
            f"{base}/commits/{'b' * 40}/uploads/": {"results": [
                {"flags": ["python"], "upload_type": "uploaded", "created_at": "2026-10-11 21:30:00"},
            ]},
            f"{base}/totals/?flag=python&sha={'b' * 40}": {"totals": {"coverage": 95.5}},
        }
        assert SC.post_merge_coverage(store.__getitem__) == SC.Coverage(
            95.5, "b" * 40, "2026-10-11",
        )

    def test_no_upload_of_its_own_is_an_error(self) -> None:
        base = SC.CODECOV_API
        store = {
            f"{base}/commits/?branch=main&page_size=20": {"results": [{"commitid": "c" * 40}]},
            f"{base}/commits/{'c' * 40}/uploads/": {"results": [
                {"flags": ["python"], "upload_type": "carriedforward", "created_at": "2026-10-12"},
            ]},
        }
        with pytest.raises(SC.MeasureError, match="upload of its own"):
            SC.post_merge_coverage(store.__getitem__)


class TestAFailedRequest:
    def test_an_unreachable_service_is_a_measure_error(self) -> None:
        with pytest.raises(SC.MeasureError, match="could not read"):
            SC.fetch_json("http://127.0.0.1:9/nothing")

    def test_a_response_of_another_shape_is_a_measure_error(self) -> None:
        """An answer without the fields the readers take, such as a listing
        with no `workflow_runs`, is a reason the render states, not a
        traceback."""
        def get(url: str) -> Any:
            return [] if "/issues?" in url else {}

        with pytest.raises(SC.MeasureError, match="not in the shape"):
            SC.github_values(get, lambda _url: {}, now=_RECORDED_AT)


# ---------------------------------------------------------------------------
# The junit file's rows
# ---------------------------------------------------------------------------


class TestTheJunitRows:
    def test_the_recorded_run(self) -> None:
        """Recorded from a real run of five tests under pytest-xdist with the
        census loaded: two of them started a process, one of them through
        a module-scoped fixture, and one replaced `Popen` with a stand-in."""
        run = SC.read_junit(_FIXTURES / "junit.xml")
        assert (run.tests, run.census) == (5, True)
        assert (round(run.seconds, 3), round(run.spawning_seconds, 3)) == (2.169, 1.56)
        assert run.started.isoformat() == "2026-10-12T09:43:53.233073+01:00"
        window = "a run of 5 tests, 2026-10-12 08:43 UTC"
        assert SC.junit_values(_FIXTURES / "junit.xml") == {
            "gate_worker_seconds": ("2", window),
            "subprocess_share": ("71.9%", window),
        }

    def test_a_file_without_the_census_is_refused(self, tmp_path: Path) -> None:
        """Without the plugin no test carries the property, and a share
        read from that file would be zero, which is under the target."""
        text = (_FIXTURES / "junit.xml").read_text(encoding="utf-8")
        bare = tmp_path / "bare.xml"
        bare.write_text(text.replace('name="subprocesses"', 'name="other"'), encoding="utf-8")
        with pytest.raises(SC.MeasureError, match="-p tests.subprocess_census"):
            SC.junit_values(bare)

    def test_a_file_that_is_not_junit_is_refused(self, tmp_path: Path) -> None:
        broken = tmp_path / "broken.xml"
        broken.write_text("<testsuites><testsuite", encoding="utf-8")
        with pytest.raises(SC.MeasureError):
            SC.junit_values(broken)

    def test_a_time_that_is_not_a_number_is_refused(self, tmp_path: Path) -> None:
        text = (_FIXTURES / "junit.xml").read_text(encoding="utf-8")
        odd = tmp_path / "odd.xml"
        odd.write_text(text.replace('time="1.235"', 'time="soon"'), encoding="utf-8")
        with pytest.raises(SC.MeasureError, match="not a junit file pytest wrote"):
            SC.junit_values(odd)


class TestTheCensus:
    """`tests/subprocess_census.py` in a real pytest run, loaded as the
    release PR loads it, from a project holding a copy of it."""

    _PROBE = (
        "import subprocess\nimport sys\n\nimport pytest\n\n"
        "@pytest.fixture(scope='module')\n"
        "def started():\n"
        "    subprocess.run([sys.executable, '-c', 'pass'], check=True)\n\n"
        "def test_starts_one():\n"
        "    subprocess.run([sys.executable, '-c', 'pass'], check=True)\n\n"
        "def test_starts_none():\n"
        "    assert True\n\n"
        "def test_its_fixture_starts_one(started):\n"
        "    assert True\n\n"
        "@pytest.fixture\n"
        "def cleaned_up():\n"
        "    yield\n"
        "    subprocess.run([sys.executable, '-c', 'pass'], check=True)\n\n"
        "def test_its_teardown_starts_one(cleaned_up):\n"
        "    assert True\n"
    )

    @pytest.mark.parametrize("workers", [[], ["-n", "2"]], ids=["one process", "xdist"])
    def test_every_test_carries_its_count(self, tmp_path: Path, workers: list[str]) -> None:
        project = tmp_path / "project"
        _write(project / "pyproject.toml", "[tool.pytest.ini_options]\ntestpaths = ['tests']\n")
        _write(project / "tests" / "__init__.py")
        shutil.copyfile(ROOT / "tests" / "subprocess_census.py",
                        project / "tests" / "subprocess_census.py")
        _write(project / "tests" / "test_probe.py", self._PROBE)
        junit = tmp_path / "junit.xml"
        result = subprocess.run(
            [sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider", *workers,
             "-p", "tests.subprocess_census", f"--junitxml={junit}"],
            cwd=project, capture_output=True, text=True, encoding="utf-8", check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        import xml.etree.ElementTree as ET

        counts = {
            case.get("name"): [p.get("value") for p in case.iter("property")
                               if p.get("name") == SC.CENSUS]
            for case in ET.parse(junit).getroot().iter("testcase")
        }
        assert counts == {"test_starts_one": ["1"], "test_starts_none": ["0"],
                          "test_its_fixture_starts_one": ["1"],
                          "test_its_teardown_starts_one": ["1"]}
        assert SC.read_junit(junit).census


# ---------------------------------------------------------------------------
# The block, and its freshness
# ---------------------------------------------------------------------------

_TREE = {
    measure.key: (f"{index + 1001:,}", "the tree")
    for index, measure in enumerate(SC.MEASURES) if measure.source == SC.TREE
}
_MEASURED = {
    **{key: (f"{index}", "the tracker, 2026-10-12 08:44 UTC")
       for index, key in enumerate(("soundness_bugs", "open_bugs"), start=7)},
    "ci_wall": ("31.5 min", "20 pull-request runs, 2026-10-09 to 2026-10-12"),
    "runner_minutes": ("244", "20 pull-request runs, 2026-10-09 to 2026-10-12"),
    "fix_pr_runs": ("3", "4 pull requests merged since v0.2.1 (2026-10-11), to 2026-10-12"),
    "fix_pr_hours": ("2.5", "4 pull requests merged since v0.2.1 (2026-10-11), to 2026-10-12"),
    "statement_coverage": ("96.30%", "Codecov, the post-merge run of `abcdef0` (2026-10-12)"),
    "gate_worker_seconds": ("2,345", "a run of 20,229 tests, 2026-10-12 09:00 UTC"),
    "subprocess_share": ("31.0%", "a run of 20,229 tests, 2026-10-12 09:00 UTC"),
}


class TestTheBlock:
    def test_one_row_per_measure_in_order(self) -> None:
        table = SC.rows(_TREE, _MEASURED)
        assert [row.measure for row in table] == [m.label for m in SC.MEASURES]
        assert {row.measure: row.audit for row in table}["Functions over 500 lines"] == "17"
        text = SC.render(table, "0.2.9")
        assert "| Functions over 500 lines | 17 | 1,007 | the tree |" in text
        assert "Measured for v0.2.9 by `scripts/render_status.py`." in text
        assert SC.parse(text) == table

    def test_an_unmeasured_row_says_which_flag_measures_it(self) -> None:
        table = SC.rows(_TREE, {})
        by_label = {row.measure: row for row in table}
        assert by_label["Open bugs"].now == "not measured"
        assert "`--github` measures it" in by_label["Open bugs"].over
        assert "`--junit PATH` measures it" in by_label["Subprocess share of suite time"].over
        assert not SC.stamped(by_label["Open bugs"].over)

    def test_a_pipe_in_a_cell_cannot_end_it(self) -> None:
        table = SC.rows({**_TREE, "program_generator": ("a | b", "the tree")}, _MEASURED)
        assert SC.parse(SC.render(table, "0.2.9")) == table


class TestFreshness:
    """`check_doc_counts.py --release` measures the tree's rows again and
    compares them; the network's and the junit file's are compared by their
    presence and their window alone."""

    _DOCUMENT = SC.render(SC.rows(_TREE, _MEASURED), "0.2.9")
    _FRESH = SC.rows(_TREE, {})

    def test_a_current_block_is_fresh(self) -> None:
        assert SC.stale(self._DOCUMENT, self._FRESH, "0.2.9") == []

    def test_a_measured_row_is_not_measured_again(self) -> None:
        """Other values and other windows than any render now would give:
        still fresh, since each states the window it was measured over."""
        moved = self._DOCUMENT.replace("| 31.5 min |", "| 58.0 min |").replace(
            "2026-10-09 to 2026-10-12", "2026-10-01 to 2026-10-02")
        assert moved != self._DOCUMENT
        assert SC.stale(moved, self._FRESH, "0.2.9") == []

    def test_a_row_the_tree_gives_is_measured_again(self) -> None:
        (error,) = SC.stale(self._DOCUMENT, SC.rows({**_TREE, "spec_words": ("9", "the tree")}, {}), "0.2.9")
        assert "`scorecard` block is not what" in error and "the tree gives '| Spec words | 86,558 | 9 |" in error

    def test_an_unmeasured_row_is_stale(self) -> None:
        document = SC.render(SC.rows(_TREE, {k: v for k, v in _MEASURED.items() if k != "ci_wall"}), "0.2.9")
        (error,) = SC.stale(document, self._FRESH, "0.2.9")
        assert "`CI wall time per pull-request push` row states no window" in error
        assert "`--github`" in error

    def test_a_missing_row_is_stale(self) -> None:
        document = "\n".join(
            line for line in self._DOCUMENT.splitlines()
            if not line.startswith("| Subprocess share")
        ) + "\n"
        errors = SC.stale(document, self._FRESH, "0.2.9")
        assert any("no `Subprocess share of suite time` row" in e for e in errors), errors

    def test_an_edited_audit_value_is_stale(self) -> None:
        document = self._DOCUMENT.replace("| Open bugs | 82 |", "| Open bugs | 80 |")
        (error,) = SC.stale(document, self._FRESH, "0.2.9")
        assert "| Open bugs | 82 |" in error

    def test_another_version_is_stale(self) -> None:
        (error,) = SC.stale(self._DOCUMENT, self._FRESH, "0.3.0")
        assert "Measured for v0.3.0" in error

    def test_an_unreadable_block_is_one_reason(self) -> None:
        (error,) = SC.stale("no table here\n", self._FRESH, "0.2.9")
        assert "no table" in error
