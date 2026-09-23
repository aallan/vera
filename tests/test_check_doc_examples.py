"""Tests for scripts/check_doc_examples.py — the documentation example gate
(#1481).

SKILL.md is the language reference agents read before writing Vera, and it
shipped two examples the toolchain refuses: a State loop whose `decreases`
measure traps on every input, and a block labelled CORRECT that `vera verify`
rejects with E500.  Nothing noticed, because SKILL.md's gate only parsed.  The
fix is one gate for every agent-facing document, at four stages — parse,
check, verify, run — and these tests hold each piece of it:

- **The two defects** (``TestTheIssueExamples``): the old CORRECT example
  fails the verify stage and the old State loop is refused when run, each in
  a synthetic document, so dropping either stage from the gate turns a cell
  red; the corrected forms pass, and SKILL.md carries the corrected forms.
- **Stage semantics** (``TestStages``): a marked stage must fail (a pass is
  a stale marker), the undefined-name warnings fail the check stage, a run
  marker compares exact output, and a run marker the gate could never reach
  is a problem.
- **Selection** (``TestSelection``): which blocks the gate reads as Vera.
- **The coverage rule** (``TestCoverage``, the wiring cell): every tracked
  document with Vera blocks is gated or exempt with a reason, and pre-commit
  and CI both run the gate over every document.
- **The real documents** (``TestRealDocuments``): every gated document
  passes, one cell per document.
"""

from __future__ import annotations

import importlib.util
import json
import re
from pathlib import Path
from typing import Any

import pytest

ROOT = Path(__file__).parent.parent
_SCRIPT = ROOT / "scripts" / "check_doc_examples.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("check_doc_examples", _SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_MOD = _load()


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _fence(program: str, *markers: str) -> str:
    """A ```vera fence around *program*, preceded by *markers*."""
    lead = "".join(m + "\n" for m in markers)
    return f"{lead}```vera\n{program}\n```\n"


def _gate(tmp_path: Path, text: str, name: str = "doc.md") -> Any:
    """Gate a synthetic document holding *text*."""
    doc = tmp_path / name
    doc.write_text(text, encoding="utf-8")
    scratch = tmp_path / "scratch"
    scratch.mkdir()
    workspace = _MOD.Workspace(ROOT, scratch)
    return _MOD.gate_file(ROOT, doc, name, workspace)


def _findings(report: Any) -> Any:
    return _MOD.collect([report])


def _write_block(tmp_path: Path, program: str) -> Path:
    scratch = tmp_path / "block-scratch"
    scratch.mkdir()
    workspace = _MOD.Workspace(ROOT, scratch)
    block = _MOD.CodeBlock(1, "vera", program, ())
    return workspace.write("probe.md", block)


# The CORRECT example as SKILL.md shipped it: `requires(true)` admits 0, and
# the body returns its argument, so `ensures(@Int.result > 0)` is refuted.
_OLD_CORRECT = """\
private fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  @Int.0
}"""

_FIXED_CORRECT = _OLD_CORRECT.replace("requires(true)", "requires(@Int.0 > 0)")

# The State loop as SKILL.md shipped it.  On the last call the counter is
# n + 1, so the measure's `@Nat.1 - @Nat.0` is `n - (n + 1)`.
_OLD_STATE_LOOP = """\
-- Sum 1..n using State<Int>
private fn add_value(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.1 + @Int.0)
  effects(pure)
{
  @Int.1 + @Int.0
}

public fn sum_with_state(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    sum_loop(@Nat.0, 1)
  }
}
where {
  fn sum_loop(@Nat, @Nat -> @Int)
    requires(true)
    ensures(true)
    decreases(@Nat.1 - @Nat.0 + 1)
    effects(<State<Int>>)
  {
    if @Nat.0 > @Nat.1 then {
      get(())
    } else {
      put(add_value(get(()), @Nat.0));
      sum_loop(@Nat.1, @Nat.0 + 1)
    }
  }
}"""

# The corrected loop: the invariant is stated, and the measure adds before it
# subtracts, so it stays non-negative on the last call.
_FIXED_STATE_LOOP = _OLD_STATE_LOOP.replace(
    "    requires(true)\n    ensures(true)\n    decreases(@Nat.1 - @Nat.0 + 1)",
    "    requires(@Nat.0 <= @Nat.1 + 1)\n    ensures(true)\n"
    "    decreases(@Nat.1 + 1 - @Nat.0)",
)

_SUM_RUNS = (
    '<!-- vera:run fn="sum_with_state" args="5" stdout="15" -->',
    '<!-- vera:run fn="sum_with_state" args="0" stdout="0" -->',
)

# A program that verifies and traps at run time for a negative argument: an
# `assert` is a runtime check by design, with no static obligation behind it.
_ASSERTING = """\
public fn pick(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  assert(@Int.0 > 0);
  @Int.0
}"""

_TWO = """\
public fn two(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 2)
  effects(pure)
{
  2
}"""


def _skill_block(predicate: Any) -> Any:
    """The one SKILL.md block *predicate* selects."""
    blocks, problems = _MOD.scan_document(ROOT / "SKILL.md")
    assert problems == []
    matches = [b for b in blocks if b.lang == "vera" and predicate(b)]
    assert len(matches) == 1, [b.line for b in matches]
    return matches[0]


# ---------------------------------------------------------------------------
# The two defects the issue names
# ---------------------------------------------------------------------------


class TestTheIssueExamples:
    def test_old_correct_example_fails_the_verify_stage(
        self, tmp_path: Path,
    ) -> None:
        """Red with the verify stage removed from the gate: the block parses
        and checks, so only `vera verify` refuses it."""
        findings = _findings(_gate(tmp_path, _fence(_OLD_CORRECT)))
        assert len(findings.failures) == 1
        assert "[verify]" in findings.failures[0]
        assert "[E500]" in findings.failures[0]

    def test_corrected_correct_example_passes(self, tmp_path: Path) -> None:
        findings = _findings(_gate(tmp_path, _fence(_FIXED_CORRECT)))
        assert findings == _MOD.Findings([], [], [])

    def test_old_state_loop_is_refused(self, tmp_path: Path) -> None:
        """The gate refuses the old loop at the first stage the toolchain
        does.  Until #1480 obligates a measure's arithmetic, `vera verify`
        passes it and both runs trap, so this is red with the run stage
        removed from the gate; once #1480 lands, `vera verify` refuses it
        with E502 and the runs never start.  Which of the two this compiler
        does is read from the verify stage itself, so each branch is
        asserted exactly rather than as a disjunction."""
        report = _gate(tmp_path, _fence(_OLD_STATE_LOOP, *_SUM_RUNS))
        failures = _findings(report).failures
        verdict = _MOD.verify_error(_write_block(tmp_path, _OLD_STATE_LOOP))
        if verdict is None:
            assert len(failures) == 2
            assert all("[run, marker line" in f and "exited" in f for f in failures)
        else:
            assert "[E502]" in verdict
            assert len(failures) == 1
            assert "[verify]" in failures[0] and "[E502]" in failures[0]

    def test_corrected_state_loop_prints_the_sums(self, tmp_path: Path) -> None:
        runs = (
            *_SUM_RUNS,
            '<!-- vera:run fn="sum_with_state" args="10" stdout="55" -->',
        )
        report = _gate(tmp_path, _fence(_FIXED_STATE_LOOP, *runs))
        assert _findings(report) == _MOD.Findings([], [], [])
        (result,) = report.results
        assert [error for _run, error in result.run_errors] == [None, None, None]

    def test_skill_md_state_loop_is_the_corrected_form_and_runs(
        self, tmp_path: Path,
    ) -> None:
        """SKILL.md's own block: it names its invocations, and they pass."""
        block = _skill_block(lambda b: "fn sum_with_state" in b.content)
        assert "decreases(@Nat.1 + 1 - @Nat.0)" in block.content
        assert "requires(@Nat.0 <= @Nat.1 + 1)" in block.content
        assert {(r.args, r.stdout) for r in block.runs} >= {
            (("5",), "15"), (("0",), "0"),
        }
        path = _write_block(tmp_path, block.content)
        assert _MOD.check_error(path) is None
        assert _MOD.verify_error(path) is None
        cwd = tmp_path / "cwd"
        cwd.mkdir()
        for run in block.runs:
            assert _MOD.run_error(ROOT, path, run, cwd) is None

    def test_skill_md_correct_result_example_verifies(
        self, tmp_path: Path,
    ) -> None:
        block = _skill_block(
            lambda b: "ensures(@Int.result > 0)" in b.content
            and "private fn f(" in b.content
        )
        assert "requires(@Int.0 > 0)" in block.content
        assert block.annotations == ()
        assert _MOD.verify_error(_write_block(tmp_path, block.content)) is None


# ---------------------------------------------------------------------------
# Stage semantics
# ---------------------------------------------------------------------------


class TestStages:
    def test_stages_in_order(self) -> None:
        assert _MOD.STAGE_ORDER == ("parse", "check", "verify", "run")

    def test_marked_failing_stage_is_skipped(self, tmp_path: Path) -> None:
        marker = '<!-- vera:skip-verify category="ILLUSTRATIVE" reason="loose" -->'
        report = _gate(tmp_path, _fence(_OLD_CORRECT, marker))
        assert _findings(report) == _MOD.Findings([], [], [])
        (result,) = report.results
        assert [o.status for o in result.outcomes] == ["ok", "ok", "skipped"]

    def test_marked_passing_stage_is_stale(self, tmp_path: Path) -> None:
        marker = '<!-- vera:skip-verify category="ILLUSTRATIVE" reason="loose" -->'
        findings = _findings(_gate(tmp_path, _fence(_FIXED_CORRECT, marker)))
        assert findings.failures == []
        assert len(findings.stale) == 1
        assert "vera:skip-verify ILLUSTRATIVE" in findings.stale[0]

    def test_marked_check_on_a_block_that_checks_is_stale(
        self, tmp_path: Path,
    ) -> None:
        marker = '<!-- vera:skip-check category="WRONG" reason="it does not" -->'
        findings = _findings(_gate(tmp_path, _fence(_FIXED_CORRECT, marker)))
        assert len(findings.stale) == 1

    def test_undefined_function_fails_the_check_stage(
        self, tmp_path: Path,
    ) -> None:
        """`vera check` only warns (E200) on a call to a function the block
        does not define; the gate reads that as a partial block."""
        program = _TWO.replace("{\n  2\n}", "{\n  helper(())\n}")
        findings = _findings(_gate(tmp_path, _fence(program)))
        assert len(findings.failures) == 1
        assert "[check]" in findings.failures[0]
        assert "[E200]" in findings.failures[0]

    def test_incomplete_marker_covers_an_undefined_function(
        self, tmp_path: Path,
    ) -> None:
        program = _TWO.replace("{\n  2\n}", "{\n  helper(())\n}")
        marker = '<!-- vera:skip-check category="INCOMPLETE" reason="helper is elsewhere" -->'
        findings = _findings(_gate(tmp_path, _fence(program, marker)))
        assert findings == _MOD.Findings([], [], [])

    def test_undefined_constructor_fails_the_check_stage(
        self, tmp_path: Path,
    ) -> None:
        program = """\
private fn to_int(@Color -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Color.0 {
    Red -> 0,
    Green -> 1
  }
}"""
        findings = _findings(_gate(tmp_path, _fence(program)))
        assert len(findings.failures) == 1
        assert "[check]" in findings.failures[0]
        assert "[E322]" in findings.failures[0]

    def test_typed_hole_warning_does_not_fail_check(
        self, tmp_path: Path,
    ) -> None:
        """Only the undefined-name warnings fail the stage: a typed hole's
        W001 is what a hole example exists to show."""
        program = _TWO.replace("{\n  2\n}", "{\n  ?\n}").replace(
            "ensures(@Int.result == 2)", "ensures(true)"
        )
        path = _write_block(tmp_path, program)
        assert _MOD.check_error(path) is None

    def test_run_output_mismatch_is_a_failure(self, tmp_path: Path) -> None:
        """Red with the run stage removed from the gate."""
        marker = '<!-- vera:run fn="two" stdout="3" -->'
        findings = _findings(_gate(tmp_path, _fence(_TWO, marker)))
        assert len(findings.failures) == 1
        assert "printed '2\\n'" in findings.failures[0]
        assert "expects '3\\n'" in findings.failures[0]

    def test_run_trap_is_a_failure_and_a_clean_run_passes(
        self, tmp_path: Path,
    ) -> None:
        markers = (
            '<!-- vera:run fn="pick" args="4" stdout="4" -->',
            '<!-- vera:run fn="pick" args="-1" stdout="-1" -->',
        )
        report = _gate(tmp_path, _fence(_ASSERTING, *markers))
        (result,) = report.results
        errors = [error for _run, error in result.run_errors]
        assert errors[0] is None
        assert errors[1] is not None and "exited 1" in errors[1]
        assert len(_findings(report).failures) == 1

    def test_run_of_a_missing_function_is_a_failure(
        self, tmp_path: Path,
    ) -> None:
        marker = '<!-- vera:run fn="absent" stdout="2" -->'
        findings = _findings(_gate(tmp_path, _fence(_TWO, marker)))
        assert len(findings.failures) == 1 and "exited" in findings.failures[0]

    def test_run_marker_beside_a_skip_marker_is_a_problem(
        self, tmp_path: Path,
    ) -> None:
        markers = (
            '<!-- vera:skip-verify category="ILLUSTRATIVE" reason="loose" -->',
            '<!-- vera:run fn="f" args="1" stdout="1" -->',
        )
        report = _gate(tmp_path, _fence(_OLD_CORRECT, *markers))
        findings = _findings(report)
        assert len(findings.problems) == 1
        assert "never run" in findings.problems[0]
        (result,) = report.results
        assert result.run_errors == ()

    def test_imports_resolve_against_the_stub_modules(
        self, tmp_path: Path,
    ) -> None:
        """`import vera.math` resolves to examples/vera/math.vera, for the
        in-process stages and for the run alike."""
        program = """\
import vera.math(magnitude);

public fn size(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  magnitude(@Int.0)
}"""
        marker = '<!-- vera:run fn="size" args="-5" stdout="5" -->'
        report = _gate(tmp_path, _fence(program, marker))
        assert _findings(report) == _MOD.Findings([], [], [])

    def test_diagnostic_pair_is_an_expected_check_failure(
        self, tmp_path: Path,
    ) -> None:
        """A `vera:diagnostic` pair holds its program to fail at the pair's
        stage, as a skip marker would: the typo'd program is skipped, and
        the corrected one is a stale expectation."""
        program = """\
type Meters = Int;

private fn half(@Meters -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Metres.0 / 2
}"""
        pair = (
            '<!-- vera:diagnostic file="main.vera" stage="check" '
            'error_code="E130" -->\n'
            + _fence(program)
            + "<!-- /vera:diagnostic -->\n```text\nrendered\n```\n"
        )
        report = _gate(tmp_path, pair)
        assert _findings(report) == _MOD.Findings([], [], [])
        (result,) = report.results
        assert result.outcomes[-1].status == "skipped"
        assert result.outcomes[-1].annotation.category == "WRONG"

        fixed_dir = tmp_path / "fixed"
        fixed_dir.mkdir()
        stale = _findings(_gate(fixed_dir, pair.replace("@Metres.0", "@Meters.0")))
        assert stale.failures == []
        assert len(stale.stale) == 1

    def test_expected_stdout_ends_with_the_newline_vera_run_adds(self) -> None:
        marker = _MOD.RunMarker(1, "f", (), "15")
        assert _MOD.expected_stdout(marker) == "15\n"
        assert _MOD.expected_stdout(marker._replace(stdout="a\n")) == "a\n"
        assert _MOD.expected_stdout(marker._replace(stdout="")) == ""

    def test_exit_code_and_envelope_must_agree(self, tmp_path: Path) -> None:
        path = tmp_path / "x.vera"
        path.write_text("", encoding="utf-8")

        def says_ok_exits_1(_path: str, as_json: bool) -> int:
            print(json.dumps({"ok": True, "diagnostics": [], "warnings": []}))
            return 1

        def says_not_ok_exits_0(_path: str, as_json: bool) -> int:
            print(json.dumps({"ok": False, "diagnostics": [], "warnings": []}))
            return 0

        for command in (says_ok_exits_1, says_not_ok_exits_0):
            error = _MOD.cli_stage_error(command, path)
            assert error is not None and "disagrees" in error

    def test_unreadable_envelope_is_a_failure(self, tmp_path: Path) -> None:
        path = tmp_path / "x.vera"
        path.write_text("", encoding="utf-8")

        def prints_prose(_path: str, as_json: bool) -> int:
            print("OK: not json")
            return 0

        error = _MOD.cli_stage_error(prints_prose, path)
        assert error is not None and "did not parse" in error

    def test_workspace_lays_out_the_import_root(self, tmp_path: Path) -> None:
        workspace = _MOD.Workspace(ROOT, tmp_path)
        assert (workspace.blocks / "vera" / "math.vera").is_file()
        assert (workspace.blocks / "vera" / "collections.vera").is_file()
        assert workspace.cwd.is_dir() and not any(workspace.cwd.iterdir())


# ---------------------------------------------------------------------------
# Which blocks are Vera
# ---------------------------------------------------------------------------


class TestSelection:
    def _block(self, lang: str, content: str) -> Any:
        return _MOD.CodeBlock(1, lang, content, ())

    def test_a_vera_fence_is_always_read(self) -> None:
        assert _MOD.selects(self._block("vera", "1 + 2"))
        assert _MOD.selects(self._block("Vera", "anything at all"))

    def test_an_untagged_declaration_is_read(self) -> None:
        assert _MOD.selects(self._block("", "-- note\npublic fn f(-> @Int)"))
        assert _MOD.selects(self._block("", "forall<T> fn id(@T -> @T)"))

    def test_untagged_prose_or_output_is_not(self) -> None:
        assert not _MOD.selects(self._block("", "[E001] Error at main.vera"))
        assert not _MOD.selects(self._block("", "$ vera check x.vera"))

    def test_another_language_is_not(self) -> None:
        assert not _MOD.selects(self._block("bash", "fn looks_like_vera()"))
        assert not _MOD.selects(self._block("text", "private fn f(@Int)"))

    def test_marker_on_a_block_the_gate_does_not_read_is_a_problem(
        self, tmp_path: Path,
    ) -> None:
        text = (
            '<!-- vera:run fn="main" stdout="1" -->\n```bash\nvera run x\n```\n'
            '<!-- vera:skip-parse category="FRAGMENT" reason="r" -->\n'
            "```\nplain words\n```\n"
        )
        findings = _findings(_gate(tmp_path, text))
        assert len(findings.problems) == 2
        assert all("does not read as Vera" in p for p in findings.problems)


# ---------------------------------------------------------------------------
# The coverage rule — the wiring cell
# ---------------------------------------------------------------------------


# The agent-facing documents the issue names, which the gate must read.
_AGENT_FACING = (
    "SKILL.md",
    "README.md",
    "FAQ.md",
    "EXAMPLES.md",
    "DE_BRUIJN.md",
    "PYPI_README.md",
    "docs/index.html",
    "docs/index.md",
)

_RETIRED_GATES = (
    "check_skill_examples.py",
    "check_readme_examples.py",
    "check_faq_examples.py",
    "check_examples_doc.py",
    "check_debruijn_examples.py",
    "check_pypi_readme_examples.py",
    "check_html_examples.py",
    "check_spec_examples.py",
)


def _hook(config: str, hook_id: str) -> dict[str, str]:
    """The `entry:` and `files:` of one pre-commit hook, read as text (the
    project avoids a YAML dependency for this, as check_doc_counts.py does)."""
    m = re.search(
        rf"^ +- id: {re.escape(hook_id)}\n(?P<body>(?: {{8,}}\S.*\n)+)",
        config,
        re.MULTILINE,
    )
    assert m is not None, f"no {hook_id} hook"
    fields = {}
    for line in m.group("body").splitlines():
        key, _, value = line.strip().partition(": ")
        fields[key] = value.strip().strip("'")
    return fields


class TestCoverage:
    def test_every_tracked_document_with_vera_blocks_is_gated_or_exempt(
        self,
    ) -> None:
        """The live tree: a document added with Vera blocks and no entry in
        DOC_GATES or NOT_GATED turns this red."""
        gated, pattern_errors = _MOD.expand_gates(ROOT)
        assert pattern_errors == []
        tracked = _MOD.tracked_documents(ROOT)
        assert "SKILL.md" in tracked
        assert _MOD.check_coverage(ROOT, gated, _MOD.NOT_GATED, tracked) == []

    def test_the_gate_reads_every_agent_facing_document(self) -> None:
        gated, _errors = _MOD.expand_gates(ROOT)
        missing = [doc for doc in _AGENT_FACING if doc not in gated]
        assert missing == []
        spec = sorted(
            p.relative_to(ROOT).as_posix() for p in (ROOT / "spec").glob("*.md")
        )
        assert spec and all(chapter in gated for chapter in spec)

    def test_every_exemption_names_a_reason(self) -> None:
        assert _MOD.NOT_GATED
        assert all(reason.strip() for reason in _MOD.NOT_GATED.values())

    def test_an_unlisted_document_with_vera_blocks_is_an_error(
        self, tmp_path: Path,
    ) -> None:
        (tmp_path / "gated.md").write_text(_fence("fn x()"), encoding="utf-8")
        (tmp_path / "new.md").write_text(_fence("fn y()"), encoding="utf-8")
        (tmp_path / "prose.md").write_text("no code\n", encoding="utf-8")
        errors = _MOD.check_coverage(
            tmp_path, ["gated.md"], {}, ["gated.md", "new.md", "prose.md"]
        )
        assert len(errors) == 1 and errors[0].startswith("new.md has Vera blocks")

    def test_a_stale_exemption_is_an_error(self, tmp_path: Path) -> None:
        (tmp_path / "gated.md").write_text(_fence("fn x()"), encoding="utf-8")
        (tmp_path / "prose.md").write_text("no code\n", encoding="utf-8")
        errors = _MOD.check_coverage(
            tmp_path, ["gated.md"], {"prose.md": "was generated"},
            ["gated.md", "prose.md"],
        )
        assert len(errors) == 1 and "remove the stale entry" in errors[0]

    def test_a_document_in_both_lists_is_an_error(self, tmp_path: Path) -> None:
        (tmp_path / "gated.md").write_text(_fence("fn x()"), encoding="utf-8")
        errors = _MOD.check_coverage(
            tmp_path, ["gated.md"], {"gated.md": "r"}, ["gated.md"]
        )
        assert len(errors) == 1 and "both DOC_GATES and NOT_GATED" in errors[0]

    def test_discovering_nothing_is_an_error(self, tmp_path: Path) -> None:
        (tmp_path / "prose.md").write_text("no code\n", encoding="utf-8")
        errors = _MOD.check_coverage(tmp_path, [], {}, ["prose.md"])
        assert len(errors) == 1 and "matched nothing" in errors[0]

    def test_a_gate_pattern_matching_nothing_is_an_error(
        self, tmp_path: Path,
    ) -> None:
        (tmp_path / "a.md").write_text("x\n", encoding="utf-8")
        docs, errors = _MOD.expand_gates(tmp_path, ("a.md", "gone/*.md"))
        assert docs == ["a.md"]
        assert len(errors) == 1 and "'gone/*.md'" in errors[0]

    def test_precommit_runs_the_gate_over_every_document(self) -> None:
        config = (ROOT / ".pre-commit-config.yaml").read_text(encoding="utf-8")
        hook = _hook(config, "doc-examples")
        assert hook["entry"] == ".venv/bin/python scripts/check_doc_examples.py"
        trigger = re.compile(hook["files"])
        gated, _errors = _MOD.expand_gates(ROOT)
        for path in [
            *gated,
            *_MOD.NOT_GATED,
            "NEW_GUIDE.md",
            "docs/new-page.html",
            "examples/vera/math.vera",
            "scripts/doc_annotations.py",
            "scripts/check_doc_examples.py",
            "vera/checker/core.py",
        ]:
            assert trigger.search(path), path

    def test_ci_runs_the_gate_over_every_document(self) -> None:
        ci = (ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
        runs = re.findall(r"run: python scripts/check_doc_examples\.py(.*)", ci)
        assert runs == [""]

    def test_no_retired_per_document_gate_remains(self) -> None:
        config = (ROOT / ".pre-commit-config.yaml").read_text(encoding="utf-8")
        ci = (ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
        for name in _RETIRED_GATES:
            assert not (ROOT / "scripts" / name).exists(), name
            assert name not in config and name not in ci, name


# ---------------------------------------------------------------------------
# The real documents
# ---------------------------------------------------------------------------


_GATED_DOCUMENTS, _GATE_ERRORS = _MOD.expand_gates(ROOT)


class TestRealDocuments:
    def test_gate_patterns_all_match(self) -> None:
        assert _GATE_ERRORS == []

    @pytest.mark.parametrize("doc", _GATED_DOCUMENTS)
    def test_document_passes_the_gate(self, doc: str, tmp_path: Path) -> None:
        workspace = _MOD.Workspace(ROOT, tmp_path)
        report = _MOD.gate_document(ROOT, doc, workspace)
        assert _MOD.collect([report]) == _MOD.Findings([], [], [])
