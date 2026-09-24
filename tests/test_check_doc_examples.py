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
import subprocess
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
            assert "E502" in verdict.codes
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
        marker = '<!-- vera:skip-verify category="ILLUSTRATIVE" code="E500" reason="loose" -->'
        report = _gate(tmp_path, _fence(_OLD_CORRECT, marker))
        assert _findings(report) == _MOD.Findings([], [], [])
        (result,) = report.results
        assert [o.status for o in result.outcomes] == ["ok", "ok", "skipped"]

    def test_marked_passing_stage_is_stale(self, tmp_path: Path) -> None:
        marker = '<!-- vera:skip-verify category="ILLUSTRATIVE" code="E500" reason="loose" -->'
        findings = _findings(_gate(tmp_path, _fence(_FIXED_CORRECT, marker)))
        assert findings.failures == []
        assert len(findings.stale) == 1
        assert "vera:skip-verify ILLUSTRATIVE" in findings.stale[0]

    def test_marked_check_on_a_block_that_checks_is_stale(
        self, tmp_path: Path,
    ) -> None:
        marker = '<!-- vera:skip-check category="WRONG" code="E131" reason="it does not" -->'
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
        marker = '<!-- vera:skip-check category="INCOMPLETE" code="E200" reason="helper is elsewhere" -->'
        findings = _findings(_gate(tmp_path, _fence(program, marker)))
        assert findings == _MOD.Findings([], [], [])

    def test_undefined_constructor_fails_the_check_stage(
        self, tmp_path: Path,
    ) -> None:
        # `Color` is declared, and its one constructor is matched, so the
        # undefined `Red` and `Green` (E322, a warning) are the only thing
        # the stage can fail on: an undeclared `Color` would be E136 (#1489)
        # and fail it without them (PR #1508 review).
        program = """\
private data Color {
  Blue
}

private fn to_int(@Color -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Color.0 {
    Blue -> 2,
    Red -> 0,
    Green -> 1
  }
}"""
        findings = _findings(_gate(tmp_path, _fence(program)))
        assert len(findings.failures) == 1
        assert "[check]" in findings.failures[0]
        assert "[E322]" in findings.failures[0]
        assert "[E136]" not in findings.failures[0]

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
            '<!-- vera:skip-verify category="ILLUSTRATIVE" code="E500" reason="loose" -->',
            '<!-- vera:run fn="f" args="1" stdout="1" -->',
        )
        report = _gate(tmp_path, _fence(_OLD_CORRECT, *markers))
        findings = _findings(report)
        assert len(findings.problems) == 1
        assert "never reaches the run stage" in findings.problems[0]
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
            assert error is not None and "disagrees" in error.message

    def test_unreadable_envelope_is_a_failure(self, tmp_path: Path) -> None:
        path = tmp_path / "x.vera"
        path.write_text("", encoding="utf-8")

        def prints_prose(_path: str, as_json: bool) -> int:
            print("OK: not json")
            return 0

        error = _MOD.cli_stage_error(prints_prose, path)
        assert error is not None and "did not parse" in error.message

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
# The check stage fails every warning it does not name as benign
# ---------------------------------------------------------------------------


def _load_script(name: str) -> Any:
    """Load a script by path.  It is registered in `sys.modules` first,
    because a `@dataclass` in it resolves its annotations through there."""
    import sys

    key = f"_doc_gate_test_{name}"
    if key in sys.modules:
        return sys.modules[key]
    spec = importlib.util.spec_from_file_location(key, ROOT / "scripts" / f"{name}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[key] = module
    spec.loader.exec_module(module)
    return module


# The modules `vera check` runs: parse, transform, resolve, type-check.
_CHECK_PATH = ("vera/checker/", "vera/resolver.py", "vera/parser.py", "vera/transform.py")
# The later stages, whose warnings `vera check` never gives.
_LATER_STAGES = ("vera/codegen/", "vera/verifier.py", "vera/tester.py")


def _warning_sites() -> list[tuple[str, int, str | None]]:
    """Every warning-severity diagnostic site in `vera/`, as (module, line,
    code), from the sites `check_diagnostic_fields.py` enumerates."""
    import ast as pyast

    fields = _load_script("check_diagnostic_fields")
    sites: list[tuple[str, int, str | None]] = []
    for path in sorted((ROOT / "vera").rglob("*.py")):
        src = path.read_text(encoding="utf-8")
        tree = pyast.parse(src)
        rel = path.relative_to(ROOT).as_posix()
        for call in fields._diagnostic_call_sites(src, rel, tree):
            severity = None
            if isinstance(call.func, pyast.Attribute) and call.func.attr == "_warning":
                severity = "warning"
            code = None
            for kw in call.keywords:
                if kw.arg == "severity" and isinstance(kw.value, pyast.Constant):
                    severity = kw.value.value
                if kw.arg == "error_code" and isinstance(kw.value, pyast.Constant):
                    code = kw.value.value
            if severity == "warning":
                sites.append((rel, call.lineno, code))
    return sites


def _checker_warning_codes() -> set[str]:
    codes: set[str] = set()
    for module, line, code in _warning_sites():
        if module.startswith(_CHECK_PATH):
            assert code is not None, f"{module}:{line}: a warning with no literal code"
            codes.add(code)
    return codes


_WARNING_PLANT_HEAD = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
"""

# One block per warning the checker gives, drawing exactly that warning.
_WARNING_PLANTS: dict[str, str] = {
    "E200": _WARNING_PLANT_HEAD + "  helper(())\n}",
    "E210": _WARNING_PLANT_HEAD + "  let @Option<Int> = Circle(1);\n  @Int.0\n}",
    "E214": _WARNING_PLANT_HEAD + "  let @Option<Int> = Nothing;\n  @Int.0\n}",
    "E220": _WARNING_PLANT_HEAD + "  Nope.op(@Int.0)\n}",
    "E230": _WARNING_PLANT_HEAD + "  vera.geometry::magnitude(@Int.0)\n}",
    "E233": "import vera.math;\n\n" + _WARNING_PLANT_HEAD
    + "  vera.math::nonexistent(@Int.0)\n}",
    "E310": _WARNING_PLANT_HEAD + "  match @Int.0 {\n    _ -> 1,\n    0 -> 2\n  }\n}",
    "E320": _WARNING_PLANT_HEAD
    + "  match Some(@Int.0) {\n    Circle(@Int) -> 1,\n    _ -> 0\n  }\n}",
    "E322": _WARNING_PLANT_HEAD
    + "  match Some(@Int.0) {\n    Nothing -> 1,\n    _ -> 0\n  }\n}",
    "W001": _WARNING_PLANT_HEAD + "  ?\n}",
    "W002": """\
private fn shout(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("tick");
  @Int.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Async, IO>)
{
  await(async(shout(@Int.0)))
}""",
}


class TestCheckWarnings:
    """The check stage fails every warning outside a named benign set, so a
    warning the checker gains later fails the gate until it is classified
    (#1484 review: a hand list of undefined-name codes missed E214, E230 and
    E320)."""

    def test_every_checker_warning_code_has_a_plant(self) -> None:
        """Derived from the checker's source: a warning code added to it with
        no plant here turns this red."""
        assert set(_WARNING_PLANTS) == _checker_warning_codes()

    def test_warnings_outside_the_check_path_belong_to_a_later_stage(self) -> None:
        """A module that starts giving warnings must be placed on one side
        or the other, so the derivation above cannot miss it."""
        unplaced = sorted(
            {m for m, _line, _code in _warning_sites()
             if not m.startswith(_CHECK_PATH + _LATER_STAGES)}
        )
        assert unplaced == []

    def test_the_benign_set_is_the_named_three(self) -> None:
        assert set(_MOD.BENIGN_CHECK_WARNINGS) == {"W001", "W002", "E310"}
        assert set(_MOD.BENIGN_CHECK_WARNINGS) <= set(_WARNING_PLANTS)

    @pytest.mark.parametrize("code", sorted(_WARNING_PLANTS))
    def test_the_plant_draws_exactly_its_warning(
        self, code: str, tmp_path: Path,
    ) -> None:
        from vera.cli import cmd_check

        path = _write_block(tmp_path, _WARNING_PLANTS[code])
        rc, data, _raw = _MOD._cli_json(cmd_check, path)
        assert rc == 0 and data["ok"] is True
        assert data["diagnostics"] == []
        assert [w.get("error_code") for w in data["warnings"]] == [code]

    @pytest.mark.parametrize("code", sorted(_WARNING_PLANTS))
    def test_the_check_stage_passes_only_a_benign_warning(
        self, code: str, tmp_path: Path,
    ) -> None:
        failure = _MOD.check_error(_write_block(tmp_path, _WARNING_PLANTS[code]))
        if code in _MOD.BENIGN_CHECK_WARNINGS:
            assert failure is None
        else:
            assert failure is not None
            assert failure.codes == (code,)
            assert f"[{code}]" in failure.message


# ---------------------------------------------------------------------------
# Which untagged blocks are Vera: derived from the grammar
# ---------------------------------------------------------------------------


# One opening per word a program can start with.  A top-level form the
# grammar gains adds a word to `program_keywords()`, and this table must
# then gain its opening, so the selector is shown reading every form.
_SAMPLE_OPENINGS: dict[str, str] = {
    "ability": "ability Sized<T> {\n  op size(T -> Int);\n}",
    "data": "data Color {\n  Red\n}",
    "effect": "effect Log {\n  op note(String -> Unit);\n}",
    "fn": "fn f(@Int -> @Int)",
    "forall": "forall<T> fn id(@T -> @T)",
    "import": "import vera.math;",
    "module": "module a.b;",
    "private": "private fn f(@Int -> @Int)",
    "public": "public data Color {\n  Red\n}",
    "type": "type Id = Int;",
}


class TestGrammarSelection:
    """An untagged fence or `<pre>` block is Vera when its first word is a
    program keyword, as the compiler's own grammar says (#1484 review: the
    hand regex omitted `ability`, so five spec blocks were never gated).
    Selection reads that word and nothing else, so it never depends on the
    block being valid (#1484 re-review: a wrong second token hid a block)."""

    def test_every_program_keyword_has_a_sample(self) -> None:
        assert set(_SAMPLE_OPENINGS) == set(_MOD.program_keywords())

    @pytest.mark.parametrize("word", sorted(_SAMPLE_OPENINGS))
    def test_each_top_level_form_is_read(self, word: str) -> None:
        block = _MOD.CodeBlock(1, "", _SAMPLE_OPENINGS[word], ())
        assert _MOD.selects(block)

    @pytest.mark.parametrize("text", [
        "fn(@Int -> @Int) effects(pure) { @Int.0 }",
        "forall(@Nat, @Nat.0 < 3, fn(@Nat -> @Bool) effects(pure) { true })",
        "type the command below",
        "public class Foo {}",
    ])
    def test_a_keyword_led_non_program_is_read_until_marked(
        self, text: str, tmp_path: Path,
    ) -> None:
        """Selection is fail-closed (PR #1484 re-review): a block that opens
        with a program keyword is read whether or not it is a program, and
        fails until it is fixed or carries a marker with a reason."""
        assert _MOD.selects(_MOD.CodeBlock(1, "", text, ()))
        (tmp_path / "bare").mkdir()
        findings = _findings(_gate(tmp_path / "bare", f"```\n{text}\n```\n"))
        assert len(findings.failures) == 1
        assert "[parse]" in findings.failures[0]
        assert "fix the block or mark it" in findings.failures[0]
        (tmp_path / "marked").mkdir()
        marker = '<!-- vera:skip-parse category="ILLUSTRATIVE" reason="not a program" -->\n'
        marked = _gate(tmp_path / "marked", marker + f"```\n{text}\n```\n")
        assert _findings(marked) == _MOD.Findings([], [], [])

    # The re-review's nine mistaken openings: each opens with a program
    # keyword, and the parser rejects its second token.  Selection must not
    # depend on the block being valid, so every one is read.
    @pytest.mark.parametrize("text", [
        "fn Double(@Int -> @Int)",
        "public type",
        "public effect",
        "public ability",
        "effect logger {",
        "import Vera.Math;",
        "module Vera;",
        "forall T fn",
        "private import vera.math;",
    ])
    def test_a_mistaken_opening_is_read_and_fails(
        self, text: str, tmp_path: Path,
    ) -> None:
        assert _MOD.selects(_MOD.CodeBlock(1, "", text, ()))
        findings = _findings(_gate(tmp_path, f"```\n{text}\n```\n"))
        assert len(findings.failures) == 1
        assert "[parse]" in findings.failures[0]
        assert "fix the block or mark it" in findings.failures[0]

    def test_a_wrong_second_token_does_not_hide_the_rest(
        self, tmp_path: Path,
    ) -> None:
        """The re-review's repro: the `type` after `public` is the mistake,
        and the refuted function below it must not go unread with it."""
        text = "```\npublic type Pos = { @Int | @Int.0 > 0 };\n\n" + _OLD_CORRECT + "\n```\n"
        findings = _findings(_gate(tmp_path, text))
        assert len(findings.failures) == 1
        assert "[parse]" in findings.failures[0]

    @pytest.mark.parametrize("text", ["types are checked", "fnord", "publicly"])
    def test_a_word_that_only_starts_like_a_keyword_is_not_read(
        self, text: str,
    ) -> None:
        assert not _MOD.selects(_MOD.CodeBlock(1, "", text, ()))

    @pytest.mark.parametrize("text", ["fn foo bar", "data Foo = x"])
    def test_a_wrong_third_token_does_not_hide_the_block(
        self, text: str, tmp_path: Path,
    ) -> None:
        """The block is gated, and the parse stage reports the third token
        (PR #1484 review)."""
        assert _MOD.selects(_MOD.CodeBlock(1, "", text, ()))
        findings = _findings(_gate(tmp_path, f"```\n{text}\n```\n"))
        assert len(findings.failures) == 1 and "[parse]" in findings.failures[0]

    def test_an_untagged_ability_block_is_gated(self, tmp_path: Path) -> None:
        """The reviewer's repro: an untagged fence opening with `ability`
        and holding the refuted example is gated, and fails verify."""
        text = "```\nability Sized<T> {\n  op size(T -> Int);\n}\n\n" + _OLD_CORRECT + "\n```\n"
        findings = _findings(_gate(tmp_path, text))
        assert len(findings.failures) == 1
        assert "[verify]" in findings.failures[0] and "[E500]" in findings.failures[0]

    def test_the_spec_ability_blocks_are_gated(self) -> None:
        blocks, _problems = _MOD.scan_document(ROOT / "spec" / "09-standard-library.md")
        ability = [b for b in blocks if b.lang == "" and b.content.lstrip().startswith("ability")]
        assert len(ability) >= 5
        assert all(_MOD.selects(b) for b in ability)


# ---------------------------------------------------------------------------
# A vera:diagnostic pair excuses only a replayed failure
# ---------------------------------------------------------------------------


def _pair(program: str, stage: str, code: str | None) -> str:
    code_attr = f' error_code="{code}"' if code else ""
    return (
        f'<!-- vera:diagnostic file="f.vera" stage="{stage}"{code_attr} -->\n'
        + _fence(program)
        + "<!-- /vera:diagnostic -->\n```text\nanything at all\n```\n"
    )


class TestDiagnosticPairs:
    """A pair is honoured only at a stage the replay gate replays and only
    with a code, and the replay gate scans every document the example gate
    reads (#1484 review)."""

    def test_a_pair_at_an_unreplayed_stage_excuses_nothing(
        self, tmp_path: Path,
    ) -> None:
        """The reviewer's repro: a `stage="verify"` pair around the refuted
        CORRECT example."""
        findings = _findings(_gate(tmp_path, _pair(_OLD_CORRECT, "verify", None)))
        assert any("is not replayed" in p for p in findings.problems)
        assert len(findings.failures) == 1 and "[E500]" in findings.failures[0]

    def test_a_pair_with_no_code_excuses_nothing(self, tmp_path: Path) -> None:
        program = _TWO.replace("{\n  2\n}", "{\n  helper(())\n}")
        findings = _findings(_gate(tmp_path, _pair(program, "check", None)))
        assert any("no error_code" in p for p in findings.problems)
        assert len(findings.failures) == 1 and "[E200]" in findings.failures[0]

    def test_the_replay_gate_scans_every_gated_document(self) -> None:
        diag = _load_script("check_diagnostic_examples")
        gated, _errors = _MOD.expand_gates(ROOT)
        expected = [ROOT / d for d in gated if not d.endswith(".html")]
        assert list(diag.DOCS) == expected
        assert ROOT / "DE_BRUIJN.md" in diag.DOCS


# ---------------------------------------------------------------------------
# Fences as CommonMark reads them, through the gate
# ---------------------------------------------------------------------------


class TestFencesThroughTheGate:
    """A fence GitHub renders as Vera is one the gate reads, in every stage
    and in the coverage rule (#1484 review)."""

    @pytest.mark.parametrize("wrap", [
        lambda p: "- item\n\n  ```vera\n" + "".join(f"  {ln}\n" for ln in p.splitlines()) + "  ```\n",
        lambda p: f"~~~vera\n{p}\n~~~\n",
        lambda p: f"````vera\n{p}\n````\n",
        lambda p: f'```vera title="demo"\n{p}\n```\n',
    ], ids=["indented", "tilde", "four-backtick", "info-string"])
    def test_the_refuted_example_is_caught_in_any_fence(
        self, wrap: Any, tmp_path: Path,
    ) -> None:
        findings = _findings(_gate(tmp_path, wrap(_OLD_CORRECT)))
        assert len(findings.failures) == 1 and "[E500]" in findings.failures[0]

    def test_an_info_string_does_not_hide_the_next_block(
        self, tmp_path: Path,
    ) -> None:
        program = _TWO.replace("{\n  2\n}", "{\n  helper(())\n}")
        text = '```vera title="demo"\n' + _FIXED_CORRECT + "\n```\n\nprose\n\n" + _fence(program)
        findings = _findings(_gate(tmp_path, text))
        assert len(findings.failures) == 1 and "[E200]" in findings.failures[0]


# ---------------------------------------------------------------------------
# Every block the run stage reaches makes a run decision
# ---------------------------------------------------------------------------


_TRAPS_AT_RUN = """\
public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_char_code("abc", 7)
}"""


# The re-review's plant: an effectful export beside a runnable one.
_FETCH = """\
public fn fetch(@String -> @Result<String, String>)
  requires(true)
  ensures(true)
  effects(<Http>)
{
  Http.get(@String.0)
}

"""

_LOAD = """\
public fn load(@String -> @Result<String, String>)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.read_file(@String.0)
}

"""

# A public function that reads a file only through a private helper.
_LOADS_THROUGH_A_HELPER = """\
private fn read_it(@String -> @Result<String, String>)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.read_file(@String.0)
}

public fn has_data(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match read_it("data.txt") {
    Ok(@String) -> true,
    Err(@String) -> false
  }
}"""

# Returns a heap value, which `vera run` prints as an address.
_SOME_TWO = """\
public fn some_two(@Unit -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(2)
}"""

_SOME_TRAP = """\
public fn main(@Unit -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(string_char_code("abc", 7))
}"""


class TestRunDecision:
    """A block that reaches the run stage and exports a function names an
    invocation or says why it cannot run, so no example skips the run
    silently (#1484 review: the run stage was opt-in)."""

    def test_an_exported_block_with_no_decision_fails(self, tmp_path: Path) -> None:
        """The reviewer's repro: verify passes, and the run would trap."""
        findings = _findings(_gate(tmp_path, _fence(_TRAPS_AT_RUN)))
        assert len(findings.failures) == 1
        assert "[run]" in findings.failures[0]
        assert "names no invocation" in findings.failures[0]

    def test_with_a_run_marker_the_trap_is_caught(self, tmp_path: Path) -> None:
        marker = '<!-- vera:run fn="main" stdout="0" -->'
        findings = _findings(_gate(tmp_path, _fence(_TRAPS_AT_RUN, marker)))
        assert len(findings.failures) == 1 and "exited" in findings.failures[0]

    def test_an_unpinned_run_still_catches_a_trap(self, tmp_path: Path) -> None:
        marker = '<!-- vera:run fn="main" reason="prints an address" -->'
        findings = _findings(_gate(tmp_path, _fence(_SOME_TRAP, marker)))
        assert len(findings.failures) == 1 and "exited" in findings.failures[0]

    def test_an_unpinned_run_passes_a_clean_block(self, tmp_path: Path) -> None:
        marker = '<!-- vera:run fn="some_two" reason="prints an address" -->'
        assert _findings(_gate(tmp_path, _fence(_SOME_TWO, marker))) == _MOD.Findings([], [], [])

    @pytest.mark.parametrize(("program", "fn"), [
        (_TWO, "two"),
        ("type Small = { @Int | @Int.0 < 10 };\n\n"
         + _TWO.replace("-> @Int)", "-> @Small)").replace("@Int.result == 2", "true"),
         "two"),
        (_TWO.replace("-> @Int)", "-> @String)").replace("@Int.result == 2", "true")
         .replace("{\n  2\n}", '{\n  "two"\n}'), "two"),
    ])
    def test_a_value_return_must_pin_its_output(
        self, program: str, fn: str, tmp_path: Path,
    ) -> None:
        """`vera run` prints a scalar or a String as a value, alias and
        refinement included, so its marker pins `stdout` (PR #1484
        re-review: a reason let a wrong value pass)."""
        marker = f'<!-- vera:run fn="{fn}" reason="prints an address" -->'
        findings = _findings(_gate(tmp_path, _fence(program, marker)))
        assert len(findings.problems) == 1
        assert "pin its output with stdout" in findings.problems[0]

    def test_a_no_run_property_that_holds_passes(self, tmp_path: Path) -> None:
        program = _TWO.replace("{\n  2\n}", "{\n  ?\n}").replace(
            "ensures(@Int.result == 2)", "ensures(true)"
        )
        marker = '<!-- vera:no-run category="typed-hole" reason="shows the hole" -->'
        assert _findings(_gate(tmp_path, _fence(program, marker))) == _MOD.Findings([], [], [])

    def test_a_no_run_property_that_does_not_hold_is_stale(
        self, tmp_path: Path,
    ) -> None:
        marker = '<!-- vera:no-run category="network" reason="it does not" -->'
        findings = _findings(_gate(tmp_path, _fence(_TWO, marker)))
        assert len(findings.problems) == 1 and "does not hold" in findings.problems[0]

    def test_no_run_on_a_block_that_exports_nothing_is_a_problem(
        self, tmp_path: Path,
    ) -> None:
        marker = '<!-- vera:no-run category="network" reason="nothing to run" -->'
        findings = _findings(_gate(tmp_path, _fence(_FIXED_CORRECT, marker)))
        assert len(findings.problems) == 1
        assert "exports no public function" in findings.problems[0]

    def test_no_run_that_excuses_no_unrun_export_is_stale(
        self, tmp_path: Path,
    ) -> None:
        markers = (
            '<!-- vera:run fn="two" stdout="2" -->',
            '<!-- vera:no-run category="network" reason="both" -->',
        )
        findings = _findings(_gate(tmp_path, _fence(_TWO, *markers)))
        assert len(findings.problems) == 1 and "does not hold" in findings.problems[0]

    @pytest.mark.parametrize(("head", "category"), [(_FETCH, "network"), (_LOAD, "fixture")])
    def test_a_property_is_held_per_export(
        self, head: str, category: str, tmp_path: Path,
    ) -> None:
        """The re-review's plant: the property holds of one export, and the
        other export, which traps, must run rather than share the marker."""
        marker = f'<!-- vera:no-run category="{category}" reason="r" -->'
        findings = _findings(_gate(tmp_path, _fence(head + _TRAPS_AT_RUN, marker)))
        assert len(findings.failures) == 1
        assert "[run]" in findings.failures[0] and "main" in findings.failures[0]

    def test_an_export_the_property_misses_can_run_beside_it(
        self, tmp_path: Path,
    ) -> None:
        markers = (
            '<!-- vera:run fn="two" stdout="2" -->',
            '<!-- vera:no-run category="network" reason="fetches a URL" -->',
        )
        findings = _findings(_gate(tmp_path, _fence(_FETCH + _TWO, *markers)))
        assert findings == _MOD.Findings([], [], [])

    def test_exports_needing_two_properties_carry_two_markers(
        self, tmp_path: Path,
    ) -> None:
        """The round-3 re-review's repro: `fetch` needs `network` and
        `classify` needs `api-key`, so the block carries one marker per
        category, and each covers its export."""
        classify = _FETCH.replace("fetch", "classify").replace(
            "<Http>", "<Inference>"
        ).replace("Http.get", "Inference.complete")
        markers = (
            '<!-- vera:no-run category="network" reason="fetches a URL" -->',
            '<!-- vera:no-run category="api-key" reason="calls a model" -->',
        )
        program = (_FETCH + classify).rstrip()
        findings = _findings(_gate(tmp_path, _fence(program, *markers)))
        assert findings == _MOD.Findings([], [], [])

    def test_a_property_reaches_through_the_blocks_own_calls(
        self, tmp_path: Path,
    ) -> None:
        marker = '<!-- vera:no-run category="fixture" reason="reads data.txt" -->'
        findings = _findings(_gate(tmp_path, _fence(_LOADS_THROUGH_A_HELPER, marker)))
        assert findings == _MOD.Findings([], [], [])

    def test_an_unknown_no_run_category_is_a_problem(self, tmp_path: Path) -> None:
        marker = '<!-- vera:no-run category="too-slow" reason="r" -->'
        findings = _findings(_gate(tmp_path, _fence(_TWO, marker)))
        assert len(findings.problems) == 1 and "unknown category" in findings.problems[0]

    @pytest.mark.parametrize("category", ["network", "api-key", "stdin", "long-running"])
    def test_shared_properties_use_the_harness_definitions(self, category: str) -> None:
        assert _MOD.NO_RUN_PROPERTIES[category] == _MOD.SKIP_PROPERTIES[category]


# ---------------------------------------------------------------------------
# A skip marker excuses the failure it names
# ---------------------------------------------------------------------------


class TestCodedMarkers:
    """A check or verify marker names its codes, and a failure carrying any
    other code fails the gate (#1484 review: a marker pinned a stage, not a
    failure)."""

    def test_a_second_defect_under_a_marker_fails(self, tmp_path: Path) -> None:
        """The reviewer's plant: an undefined helper the marker excuses, and
        a type error it does not."""
        program = _TWO.replace("{\n  2\n}", "{\n  helper(());\n  @Int.0 + true\n}")
        marker = '<!-- vera:skip-check category="INCOMPLETE" code="E200" reason="helper is elsewhere" -->'
        findings = _findings(_gate(tmp_path, _fence(program, marker)))
        assert len(findings.failures) == 1
        assert "[check]" in findings.failures[0]
        assert "marker names E200" in findings.failures[0]

    def test_a_second_diagnostic_with_the_same_code_fails(
        self, tmp_path: Path,
    ) -> None:
        """The re-review's plant: a misspelt built-in is a second E200 beside
        the undefined helper, and `code="E200"` names one (PR #1484)."""
        program = _TWO.replace("{\n  2\n}", '{\n  helper(()) + strng_length("x")\n}').replace(
            "@Int.result == 2", "true"
        )
        one = '<!-- vera:skip-check category="INCOMPLETE" code="E200" reason="calls helper" -->'
        findings = _findings(_gate(tmp_path, _fence(program, one)))
        assert len(findings.failures) == 1
        assert "E200 E200" in findings.failures[0]
        (tmp_path / "two").mkdir()
        two = one.replace('code="E200"', 'code="E200 E200"')
        assert _findings(_gate(tmp_path / "two", _fence(program, two))) == _MOD.Findings([], [], [])

    @pytest.mark.parametrize("doc", ["spec/02-types.md", "spec/06-contracts.md"])
    def test_the_invariant_examples_are_marked_future(self, doc: str) -> None:
        blocks, _problems = _MOD.scan_document(ROOT / doc)
        invariant = [b for b in blocks if "invariant(" in b.content and b.annotations]
        assert invariant
        for block in invariant:
            (ann,) = block.annotations
            assert ann.category == "FUTURE" and "E130" in ann.codes


# ---------------------------------------------------------------------------
# Every example invocation a document names is run, or left to the harness
# ---------------------------------------------------------------------------


class TestDocumentedInvocations:
    """A `vera run examples/...` a document names is run here, unless
    `check_examples_run.py` already runs that exact invocation or skips that
    example by property (#1484 review: EXAMPLES.md named two that no gate
    ran)."""

    def test_invocations_are_read_in_their_written_forms(self, tmp_path: Path) -> None:
        doc = tmp_path / "doc.md"
        doc.write_text(
            "Run with `vera run examples/safe_divide.vera --fn safe_divide -- 3 10`.\n"
            "```bash\nvera run examples/hello_world.vera      # prints Hello\n```\n"
            "`VERA_DB_URL=x vera run examples/sqlitedb.vera` (requires a fixture)\n"
            "`vera run examples/modules.vera --fn abs_max -- -3 -5`\n",
            encoding="utf-8",
        )
        found, problems = _MOD.documented_invocations(doc, "doc.md")
        assert problems == []
        assert [(i.name, i.fn, i.args) for i in found] == [
            ("safe_divide", "safe_divide", ("3", "10")),
            ("hello_world", None, ()),
            ("sqlitedb", None, ()),
            ("modules", "abs_max", ("-3", "-5")),
        ]

    def test_an_unreadable_invocation_is_a_problem(self, tmp_path: Path) -> None:
        doc = tmp_path / "doc.md"
        doc.write_text(
            "`vera run --json examples/hello_world.vera`\n"
            "`vera run examples/hello_world.vera --weird`\n",
            encoding="utf-8",
        )
        found, problems = _MOD.documented_invocations(doc, "doc.md")
        assert found == [] and len(problems) == 2

    def test_the_owner_is_the_harness_when_it_runs_or_skips_the_example(self) -> None:
        inv = _MOD.Invocation
        assert _MOD.invocation_owner(inv("d", 1, "safe_divide", "safe_divide", ("3", "10")))
        assert _MOD.invocation_owner(inv("d", 1, "hello_world", None, ()))
        assert "skips" in _MOD.invocation_owner(inv("d", 1, "http", None, ()))
        assert _MOD.invocation_owner(inv("d", 1, "effect_handler", "run_counter", ())) is None

    def test_an_invocation_no_gate_runs_is_run_here(self, tmp_path: Path) -> None:
        inv = _MOD.Invocation
        failing = inv("d", 3, "safe_divide", "safe_divide", ("0", "5"))
        passing = inv("d", 4, "effect_handler", "run_counter", ())
        failures = _MOD.run_invocations(ROOT, [failing, passing], tmp_path)
        assert len(failures) == 1
        assert failures[0].startswith("d line 3 [invocation]")

    def test_a_missing_example_is_a_failure(self, tmp_path: Path) -> None:
        inv = _MOD.Invocation("d", 5, "no_such_example", None, ())
        failures = _MOD.run_invocations(ROOT, [inv], tmp_path)
        assert len(failures) == 1 and "does not exist" in failures[0]

    def test_the_gate_runs_the_invocations_its_documents_name(
        self, tmp_path: Path,
    ) -> None:
        """`run_gate` itself, not only its parts: a document that names a
        failing invocation fails the gate."""
        import shutil

        shutil.copytree(ROOT / "examples", tmp_path / "examples")
        (tmp_path / "d.md").write_text(
            "`vera run examples/safe_divide.vera --fn safe_divide -- 0 5`\n",
            encoding="utf-8",
        )
        (report,) = _MOD.run_gate(tmp_path, ["d.md"])
        assert len(report.problems) == 1
        assert report.problems[0].startswith("d.md line 1 [invocation]")

    def test_examples_md_names_the_two_the_harness_does_not_run(self) -> None:
        found, problems = _MOD.documented_invocations(ROOT / "EXAMPLES.md", "EXAMPLES.md")
        assert problems == []
        unowned = {(i.name, i.fn, i.args) for i in found if _MOD.invocation_owner(i) is None}
        assert {("effect_handler", "run_counter", ()),
                ("effect_handler", "safe_div", ("10", "0"))} <= unowned


# ---------------------------------------------------------------------------
# The instrument's own pieces
# ---------------------------------------------------------------------------


# The document types agents read, stated here rather than read from the
# gate, so a type dropped from DOCUMENT_SUFFIXES fails a cell.
_AGENT_DOCUMENT_SUFFIXES = (".md", ".html", ".txt")


class TestLiveEnumeration:
    """The coverage rule through its own enumeration, `tracked_documents`,
    not a list handed to it (PR #1484 re-review: dropping `.html` from
    DOCUMENT_SUFFIXES left every cell green)."""

    def test_every_agent_document_type_is_enumerated(self) -> None:
        assert set(_AGENT_DOCUMENT_SUFFIXES) <= set(_MOD.DOCUMENT_SUFFIXES)

    def test_a_tracked_document_of_each_type_must_be_classified(
        self, tmp_path: Path,
    ) -> None:
        # The git commands here reach the temporary repository only because
        # tests/conftest.py clears every inherited GIT_* variable for the
        # suite; test_git_hermetic.py holds the suite to that.
        repo = tmp_path / "repo"
        repo.mkdir()
        files = {
            "page.html": f"<pre>\n{_TWO}\n</pre>\n",
            "guide.md": _fence(_TWO),
            "notes.txt": _fence(_TWO),
        }
        assert {Path(n).suffix for n in files} == set(_AGENT_DOCUMENT_SUFFIXES)
        for name, text in files.items():
            (repo / name).write_text(text, encoding="utf-8")
        subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
        subprocess.run(["git", "add", "--", *files], cwd=repo, check=True)
        tracked = _MOD.tracked_documents(repo)
        assert tracked == sorted(files)
        errors = _MOD.check_coverage(repo, [], {}, tracked)
        for name in files:
            assert any(e.startswith(f"{name} has Vera blocks") for e in errors), errors


def _repo_with(path: Path, files: dict[str, str]) -> Path:
    """A git repository at *path* tracking *files*."""
    path.mkdir()
    for name, text in files.items():
        (path / name).write_text(text, encoding="utf-8")
    subprocess.run(["git", "init", "-q"], cwd=path, check=True)
    subprocess.run(["git", "add", "--", *files], cwd=path, check=True)
    return path


class TestEnumerationIgnoresAnInheritedRepository:
    """`tracked_documents` answers for the repository its root names, even
    when the environment names another, as a git hook's does (PR #1484)."""

    def test_an_inherited_git_dir_does_not_redirect_it(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        decoy = _repo_with(tmp_path / "decoy", {"decoy.md": _fence(_TWO)})
        repo = _repo_with(tmp_path / "repo", {"guide.md": _fence(_TWO)})
        monkeypatch.setenv("GIT_DIR", str(decoy / ".git"))
        monkeypatch.setenv("GIT_INDEX_FILE", str(decoy / ".git" / "index"))
        assert _MOD.tracked_documents(repo) == ["guide.md"]


class TestInstrumentPieces:
    """Cells for the pieces a mutation could otherwise remove unseen (#1484
    review)."""

    @pytest.mark.parametrize("name,text", [
        ("page.html", "<pre>public fn f(-> @Int)</pre>\n"),
        ("notes.txt", "```vera\nx\n```\n"),
        ("untagged.md", "```\npublic fn f(-> @Int)\n```\n"),
        ("tilde.md", "~~~vera\nx\n~~~\n"),
        ("indented.md", "- item\n\n  ```vera\n  x\n  ```\n"),
    ])
    def test_every_selection_arm_makes_a_document_need_classifying(
        self, name: str, text: str, tmp_path: Path,
    ) -> None:
        (tmp_path / name).write_text(text, encoding="utf-8")
        errors = _MOD.check_coverage(tmp_path, [], {}, [name])
        assert errors == [
            f"{name} has Vera blocks the gate does not read — add it to "
            f"DOC_GATES, or to NOT_GATED with the reason it is exempt"
        ]

    def test_the_canary_refuses_another_checkout(self) -> None:
        assert _MOD.compiler_canary(ROOT) is None
        elsewhere = Path("/elsewhere/vera/__init__.py")
        message = _MOD.compiler_canary(ROOT, elsewhere)
        assert message is not None and "not from" in message

    def test_the_run_stage_puts_this_checkout_first(self) -> None:
        import os

        env = _MOD.run_env(ROOT)
        assert env["PYTHONPATH"].split(os.pathsep)[0] == str(ROOT)
        assert not set(_MOD.NEUTRALISED_ENV) & set(env)


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
