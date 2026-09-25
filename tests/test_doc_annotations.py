"""Tests for scripts/doc_annotations.py — inline fence markers (#538, #1481).

The documentation gates used to keep line-number-keyed ALLOWLIST dicts that
went stale on every doc edit and needed scripts/fix_allowlists.py to renumber
(whose bulk-shift heuristic was itself buggy — #606).  #538 replaced both with
inline HTML-comment annotations placed immediately before each fence:

    <!-- vera:skip-parse category="FRAGMENT" reason="bare type expression" -->
    ```vera
    List<Result<User, Error>>
    ```

These tests pin the shared scanning/evaluation module the documentation
example gate (scripts/check_doc_examples.py) uses:

  - an annotated unparseable block is SKIPPED (expected failure — gate green)
  - an unannotated unparseable block FAILS the gate
  - a STALE annotation (block passes the stage it is exempted from) FAILS the
    gate, so the skip surface shrinks over time (mirrors check_e602_clean.py's
    stale-entry treatment)
  - malformed / dangling / duplicate annotations are hard problems, and so is
    a category outside the closed vocabulary (#1481)
  - a `vera:run` marker names an invocation and its exact output, and every
    way of writing one wrong is a problem rather than a silently ignored
    line (#1481)
  - build_site.py's strip helper removes skip AND run marker lines so they
    never leak into generated site assets (docs/SKILL.md, docs/llms-full.txt)
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from typing import Any

from vera.parser import parse

_SCRIPT = Path(__file__).parent.parent / "scripts" / "doc_annotations.py"

# scripts/ is not a package: load the module by file path (same pattern as
# tests/test_build_site.py).
_spec = importlib.util.spec_from_file_location("doc_annotations", _SCRIPT)
assert _spec is not None and _spec.loader is not None
doc_annotations = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(doc_annotations)

scan_markdown = doc_annotations.scan_markdown
scan_html = doc_annotations.scan_html
evaluate_block = doc_annotations.evaluate_block
strip_annotations = doc_annotations.strip_annotations
parse_run_marker = doc_annotations.parse_run_marker
RunMarker = doc_annotations.RunMarker
CATEGORIES = doc_annotations.CATEGORIES
CodeBlock = doc_annotations.CodeBlock
scan_diagnostic_examples = doc_annotations.scan_diagnostic_examples
replay_diagnostic_examples = doc_annotations.replay_diagnostic_examples


def _try_parse(content: str) -> str | None:
    """The gates' parse runner: error message or None."""
    try:
        parse(content, file="<test>")
        return None
    except Exception as exc:  # noqa: BLE001 — a failing doc example is reported, not raised
        return str(exc).split("\n")[0][:200]


def _md(tmp_path: Path, text: str) -> Path:
    p = tmp_path / "doc.md"
    p.write_text(text, encoding="utf-8")
    return p


class TestScanMarkdown:
    def test_plain_fence_extracted(self, tmp_path: Path) -> None:
        path = _md(tmp_path, "# Title\n\n```vera\nfn broken(\n```\n")
        blocks, problems = scan_markdown(path)
        assert problems == []
        assert len(blocks) == 1
        assert blocks[0].line == 3
        assert blocks[0].lang == "vera"
        assert blocks[0].content == "fn broken("
        assert blocks[0].annotations == ()

    def test_annotation_attached_to_following_fence(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-parse category="FRAGMENT" reason="bare expr" -->\n'
            "```vera\n1 + 2\n```\n",
        )
        blocks, problems = scan_markdown(path)
        assert problems == []
        assert len(blocks) == 1
        (ann,) = blocks[0].annotations
        assert ann.stage == "parse"
        assert ann.category == "FRAGMENT"
        assert ann.reason == "bare expr"

    def test_stacked_annotations(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-check category="INCOMPLETE" code="E200" reason="uses ext fn" -->\n'
            '<!-- vera:skip-verify category="ILLUSTRATIVE" code="E500" reason="loose contract" -->\n'
            "```vera\nx\n```\n",
        )
        blocks, problems = scan_markdown(path)
        assert problems == []
        stages = [a.stage for a in blocks[0].annotations]
        assert stages == ["check", "verify"]
        assert [a.codes for a in blocks[0].annotations] == [("E200",), ("E500",)]

    def test_dangling_annotation_is_problem(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-parse category="FRAGMENT" reason="orphan" -->\n'
            "\n"
            "```vera\nx\n```\n",
        )
        blocks, problems = scan_markdown(path)
        assert len(problems) == 1
        assert "dangling" in problems[0]
        # The fence itself is still extracted, without the annotation.
        assert len(blocks) == 1
        assert blocks[0].annotations == ()

    def test_dangling_annotation_at_eof_is_problem(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            'text\n<!-- vera:skip-parse category="FRAGMENT" reason="eof" -->\n',
        )
        _blocks, problems = scan_markdown(path)
        assert len(problems) == 1
        assert "dangling" in problems[0]

    def test_malformed_annotation_is_problem(self, tmp_path: Path) -> None:
        # Typo'd attribute name must not be silently ignored.
        path = _md(
            tmp_path,
            '<!-- vera:skip-parse categry="FRAGMENT" reason="typo" -->\n'
            "```vera\nfn broken(\n```\n",
        )
        _blocks, problems = scan_markdown(path)
        assert len(problems) == 1
        assert "unknown attribute 'categry'" in problems[0]

    def test_unknown_stage_is_problem(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-run category="FRAGMENT" reason="no such stage" -->\n'
            "```vera\nx\n```\n",
        )
        _blocks, problems = scan_markdown(path)
        assert len(problems) == 1
        assert "malformed" in problems[0]

    def test_duplicate_stage_is_problem(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-parse category="FRAGMENT" reason="one" -->\n'
            '<!-- vera:skip-parse category="INCOMPLETE" reason="two" -->\n'
            "```vera\nx\n```\n",
        )
        _blocks, problems = scan_markdown(path)
        assert len(problems) == 1
        assert "duplicate" in problems[0]

    def test_prose_mention_without_comment_syntax_is_fine(
        self, tmp_path: Path
    ) -> None:
        path = _md(tmp_path, "Use a `vera:skip-parse` annotation here.\n")
        blocks, problems = scan_markdown(path)
        assert problems == []
        assert blocks == []

    def test_unterminated_fence_is_problem(self, tmp_path: Path) -> None:
        # A fence that runs to EOF is malformed markdown — it must fail the
        # gate loudly, not be tested (or skip-annotated) as if well-formed.
        path = _md(tmp_path, "# Title\n\n```vera\nfn broken(\n")
        blocks, problems = scan_markdown(path)
        assert len(problems) == 1
        assert "unterminated" in problems[0]
        assert "line 3" in problems[0]
        assert blocks == []

    def test_unterminated_fence_discards_pending_annotation(
        self, tmp_path: Path
    ) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-parse category="FRAGMENT" reason="r" -->\n'
            "```vera\nfn broken(\n",
        )
        blocks, problems = scan_markdown(path)
        assert blocks == []
        # Exactly the unterminated-fence problem — the pending annotation is
        # consumed by the broken fence, not double-reported as dangling.
        assert len(problems) == 1
        assert "unterminated" in problems[0]


class TestScanHtml:
    def test_pre_block_with_annotation(self, tmp_path: Path) -> None:
        path = tmp_path / "index.html"
        path.write_text(
            '<div class="code-block">\n'
            '<!-- vera:skip-parse category="FRAGMENT" reason="teaser" -->\n'
            '<pre><span class="kw">fn</span> broken(</pre>\n'
            "</div>\n",
            encoding="utf-8",
        )
        blocks, problems = scan_html(path)
        assert problems == []
        assert len(blocks) == 1
        assert blocks[0].line == 3
        assert blocks[0].content == "fn broken("
        (ann,) = blocks[0].annotations
        assert ann.stage == "parse"

    def test_pre_block_without_annotation(self, tmp_path: Path) -> None:
        path = tmp_path / "index.html"
        path.write_text(
            "<pre>fn f(@Int -&gt; @Int)</pre>\n",
            encoding="utf-8",
        )
        blocks, problems = scan_html(path)
        assert problems == []
        assert len(blocks) == 1
        assert blocks[0].content == "fn f(@Int -> @Int)"
        assert blocks[0].annotations == ()

    def test_unterminated_pre_is_problem(self, tmp_path: Path) -> None:
        # An unclosed <pre> running to EOF is malformed HTML — it must fail
        # the gate loudly even with no annotation pending.
        path = tmp_path / "index.html"
        path.write_text(
            "<div>\n<pre>fn broken(\nno closing tag\n",
            encoding="utf-8",
        )
        blocks, problems = scan_html(path)
        assert blocks == []
        assert len(problems) == 1
        assert "unterminated" in problems[0]
        assert "line 2" in problems[0]


class TestEvaluateBlock:
    """The gate round-trip: skip vs fail vs stale."""

    def test_unannotated_unparseable_block_fails(self) -> None:
        block = CodeBlock(1, "vera", "fn broken(", ())
        outcomes = evaluate_block(block, [("parse", _try_parse)])
        assert outcomes[-1].status == "failed"
        assert outcomes[-1].error is not None

    def test_annotated_unparseable_block_is_skipped(self) -> None:
        ann = doc_annotations.Annotation(1, "parse", "FRAGMENT", "bare expr")
        block = CodeBlock(2, "vera", "fn broken(", (ann,))
        outcomes = evaluate_block(block, [("parse", _try_parse)])
        assert outcomes[-1].status == "skipped"
        assert outcomes[-1].annotation == ann

    def test_stale_annotation_on_parseable_block(self) -> None:
        # The block parses fine — the annotation must be flagged stale so
        # the gate forces its removal (the skip surface shrinks over time).
        good = (
            "private fn id(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n  @Int.0\n}"
        )
        ann = doc_annotations.Annotation(1, "parse", "FRAGMENT", "stale")
        block = CodeBlock(2, "vera", good, (ann,))
        outcomes = evaluate_block(block, [("parse", _try_parse)])
        assert outcomes[-1].status == "stale"
        assert outcomes[-1].annotation == ann

    def test_unannotated_parseable_block_is_ok(self) -> None:
        good = (
            "private fn id(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n  @Int.0\n}"
        )
        block = CodeBlock(1, "vera", good, ())
        outcomes = evaluate_block(block, [("parse", _try_parse)])
        assert [o.status for o in outcomes] == ["ok"]

    def test_skip_check_runs_parse_first(self) -> None:
        # A skip-check block must still parse; the pipeline stops at the
        # annotated stage with "skipped" when that stage fails as expected.
        ann = doc_annotations.Annotation(1, "check", "INCOMPLETE", "ext fn")
        block = CodeBlock(2, "vera", "content", (ann,))
        calls: list[str] = []

        def parse_ok(_c: str) -> str | None:
            calls.append("parse")
            return None

        def check_fails(_c: str) -> str | None:
            calls.append("check")
            return "type error"

        def verify_never(_c: str) -> str | None:  # pragma: no cover
            calls.append("verify")
            return None

        outcomes = evaluate_block(
            block,
            [("parse", parse_ok), ("check", check_fails), ("verify", verify_never)],
        )
        assert calls == ["parse", "check"]
        assert [o.status for o in outcomes] == ["ok", "skipped"]

    def test_skip_check_stale_when_check_passes(self) -> None:
        ann = doc_annotations.Annotation(1, "check", "INCOMPLETE", "ext fn")
        block = CodeBlock(2, "vera", "content", (ann,))
        outcomes = evaluate_block(
            block,
            [("parse", lambda _c: None), ("check", lambda _c: None)],
        )
        assert [o.status for o in outcomes] == ["ok", "stale"]


class TestCategories:
    """A skip marker's category is one of a closed vocabulary (#1481), so a
    typo cannot mint a new label the gate's report would count on its own."""

    def test_every_defined_category_is_accepted(self, tmp_path: Path) -> None:
        text = "".join(
            f'<!-- vera:skip-parse category="{c}" code="E005" reason="r" -->\n'
            "```vera\nx\n```\n\n"
            for c in CATEGORIES
        )
        blocks, problems = scan_markdown(_md(tmp_path, text))
        assert problems == []
        assert [b.annotations[0].category for b in blocks] == list(CATEGORIES)

    def test_unknown_category_is_problem(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-parse category="SNIPPET" reason="retired label" -->\n'
            "```vera\nx\n```\n",
        )
        blocks, problems = scan_markdown(path)
        assert len(problems) == 1
        assert "unknown category 'SNIPPET'" in problems[0]
        # The marker still attaches, so the block's stage outcome is still
        # computed; the problem alone fails the gate.
        assert blocks[0].annotations[0].category == "SNIPPET"

    def test_every_category_has_a_definition(self) -> None:
        assert CATEGORIES
        assert all(text.strip() for text in CATEGORIES.values())


class TestRunMarkers:
    """`vera:run` names an invocation and the exact output it prints (#1481)."""

    def test_marker_attaches_to_following_fence(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:run fn="sum_with_state" args="5" stdout="15" -->\n'
            '<!-- vera:run fn="sum_with_state" args="0" stdout="0" -->\n'
            "```vera\nprogram\n```\n",
        )
        blocks, problems = scan_markdown(path)
        assert problems == []
        assert blocks[0].annotations == ()
        assert blocks[0].runs == (
            RunMarker(1, "sum_with_state", ("5",), "15"),
            RunMarker(2, "sum_with_state", ("0",), "0"),
        )

    def test_args_split_like_a_shell_and_escapes_decode(self) -> None:
        line = (
            '<!-- vera:run fn="f" args="\'two words\' -3" '
            'stdout="a\\nb \\"q\\" \\\\ end" -->'
        )
        marker = parse_run_marker(line, 7)
        assert marker == RunMarker(7, "f", ("two words", "-3"), 'a\nb "q" \\ end')

    def test_args_is_optional_and_stdout_may_be_empty(self) -> None:
        marker = parse_run_marker('<!-- vera:run fn="main" stdout="" -->', 1)
        assert marker == RunMarker(1, "main", (), "")

    def test_a_line_that_is_not_a_run_marker_is_none(self) -> None:
        assert parse_run_marker("plain prose", 1) is None
        assert parse_run_marker(
            '<!-- vera:skip-parse category="FRAGMENT" reason="r" -->', 1
        ) is None

    def test_missing_stdout_and_reason_is_problem(self) -> None:
        problem = parse_run_marker('<!-- vera:run fn="main" -->', 3)
        assert isinstance(problem, str)
        assert problem.startswith("line 3:") and "exactly one" in problem

    def test_stdout_and_reason_together_is_problem(self) -> None:
        problem = parse_run_marker(
            '<!-- vera:run fn="main" stdout="1" reason="both" -->', 3
        )
        assert isinstance(problem, str) and "exactly one" in problem

    def test_reason_instead_of_stdout_leaves_the_output_unpinned(self) -> None:
        marker = parse_run_marker(
            '<!-- vera:run fn="grid" reason="returns an array" -->', 4
        )
        assert marker == RunMarker(4, "grid", (), None, "returns an array")

    def test_blank_run_reason_is_problem(self) -> None:
        problem = parse_run_marker('<!-- vera:run fn="grid" reason=" " -->', 4)
        assert isinstance(problem, str) and "blank 'reason'" in problem

    def test_missing_fn_is_problem(self) -> None:
        problem = parse_run_marker('<!-- vera:run stdout="1" -->', 3)
        assert isinstance(problem, str) and "'fn'" in problem

    def test_unknown_attribute_is_problem(self) -> None:
        problem = parse_run_marker(
            '<!-- vera:run fn="main" stdin="x" stdout="1" -->', 1
        )
        assert isinstance(problem, str) and "unknown attribute 'stdin'" in problem

    def test_repeated_attribute_is_problem(self) -> None:
        problem = parse_run_marker(
            '<!-- vera:run fn="a" fn="b" stdout="1" -->', 1
        )
        assert isinstance(problem, str) and "repeats the attribute 'fn'" in problem

    def test_unknown_escape_is_problem(self) -> None:
        problem = parse_run_marker(
            '<!-- vera:run fn="main" stdout="a\\zb" -->', 1
        )
        assert isinstance(problem, str) and "escape" in problem

    def test_text_outside_the_attributes_is_problem(self) -> None:
        problem = parse_run_marker(
            '<!-- vera:run fn="main" stdout="1" trailing -->', 1
        )
        assert isinstance(problem, str) and "malformed vera:run" in problem

    def test_fn_must_be_a_function_name(self) -> None:
        problem = parse_run_marker('<!-- vera:run fn="Main" stdout="1" -->', 1)
        assert isinstance(problem, str) and "not a function name" in problem

    def test_unbalanced_args_quote_is_problem(self) -> None:
        problem = parse_run_marker(
            '<!-- vera:run fn="main" args="\'open" stdout="1" -->', 1
        )
        assert isinstance(problem, str) and "do not split" in problem

    def test_problem_surfaces_through_the_scanner(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:run fn="main" -->\n```vera\nprogram\n```\n',
        )
        blocks, problems = scan_markdown(path)
        assert len(problems) == 1 and "exactly one" in problems[0]
        assert blocks[0].runs == ()

    def test_misspelt_directive_is_malformed_not_ignored(
        self, tmp_path: Path,
    ) -> None:
        """A directive the grammar does not know must not quietly do
        nothing: `vera:runs` would otherwise leave the block unrun while
        the document claims an output."""
        path = _md(
            tmp_path,
            '<!-- vera:runs fn="main" stdout="1" -->\n```vera\nprogram\n```\n',
        )
        blocks, problems = scan_markdown(path)
        assert len(problems) == 1 and "malformed vera marker" in problems[0]
        assert blocks[0].runs == ()

    def test_dangling_run_marker_is_problem(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:run fn="main" stdout="1" -->\n\nprose\n',
        )
        _blocks, problems = scan_markdown(path)
        assert len(problems) == 1 and "dangling" in problems[0]

    def test_diagnostic_pair_is_not_a_marker_problem(
        self, tmp_path: Path,
    ) -> None:
        """The `vera:diagnostic` pair belongs to its own scanner; the marker
        hint must leave it alone."""
        _blocks, problems = scan_markdown(_md(tmp_path, _E130_EXAMPLE))
        assert problems == []

    def test_run_marker_on_a_pre_block(self, tmp_path: Path) -> None:
        path = tmp_path / "index.html"
        path.write_text(
            '<!-- vera:run fn="main" stdout="5" -->\n'
            "<pre>public fn main(-&gt; @Int) {}</pre>\n",
            encoding="utf-8",
        )
        blocks, problems = scan_html(path)
        assert problems == []
        assert blocks[0].runs == (RunMarker(1, "main", (), "5"),)


class TestMarkerValues:
    """Every marker says something, and a skip marker at a stage that reports
    every error names the codes it excuses (#1484 review)."""

    def test_blank_reason_is_problem(self, tmp_path: Path) -> None:
        for reason in ("", " "):
            path = _md(
                tmp_path,
                f'<!-- vera:skip-parse category="FRAGMENT" reason="{reason}" -->\n'
                "```vera\nx\n```\n",
            )
            _blocks, problems = scan_markdown(path)
            assert len(problems) == 1, reason
            assert "blank 'reason'" in problems[0], reason

    def test_blank_category_is_problem(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-parse category=" " reason="r" -->\n```vera\nx\n```\n',
        )
        _blocks, problems = scan_markdown(path)
        assert len(problems) == 1 and "blank 'category'" in problems[0]

    def test_codes_are_read(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-check category="FUTURE" code="E130 E200" reason="r" -->\n'
            "```vera\nx\n```\n",
        )
        blocks, problems = scan_markdown(path)
        assert problems == []
        assert blocks[0].annotations[0].codes == ("E130", "E200")

    def test_none_names_a_diagnostic_without_a_code(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-check category="ILLUSTRATIVE" code="none" reason="r" -->\n'
            "```vera\nx\n```\n",
        )
        blocks, problems = scan_markdown(path)
        assert problems == [] and blocks[0].annotations[0].codes == ("none",)

    def test_a_code_that_is_not_one_is_problem(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-check category="FUTURE" code="E13" reason="r" -->\n'
            "```vera\nx\n```\n",
        )
        _blocks, problems = scan_markdown(path)
        assert len(problems) == 1 and "not an error code" in problems[0]

    def test_check_and_verify_markers_must_name_codes(self, tmp_path: Path) -> None:
        for stage in ("check", "verify"):
            path = _md(
                tmp_path,
                f'<!-- vera:skip-{stage} category="INCOMPLETE" reason="r" -->\n'
                "```vera\nx\n```\n",
            )
            _blocks, problems = scan_markdown(path)
            assert len(problems) == 1, stage
            assert "must name the codes" in problems[0], stage

    def test_a_wrong_marker_must_name_its_code(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-parse category="WRONG" reason="missing contracts" -->\n'
            "```vera\nx\n```\n",
        )
        _blocks, problems = scan_markdown(path)
        assert len(problems) == 1 and "what a WRONG example teaches" in problems[0]

    def test_a_parse_fragment_need_not_name_a_code(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:skip-parse category="FRAGMENT" reason="bare call" -->\n'
            "```vera\nx\n```\n",
        )
        _blocks, problems = scan_markdown(path)
        assert problems == []


class TestCodedEvaluation:
    """A marker that names codes excuses that failure, not any failure at its
    stage (#1484 review)."""

    def _block(self, codes: tuple[str, ...]) -> Any:
        ann = doc_annotations.Annotation(1, "check", "INCOMPLETE", "r", codes)
        return CodeBlock(2, "vera", "x", (ann,))

    def test_the_named_failure_is_skipped(self) -> None:
        outcomes = evaluate_block(
            self._block(("E200",)),
            [("check", lambda _c: doc_annotations.StageFailure("m", ("E200",)))],
        )
        assert outcomes[-1].status == "skipped"

    def test_a_failure_with_another_code_fails(self) -> None:
        outcomes = evaluate_block(
            self._block(("E200",)),
            [("check", lambda _c: doc_annotations.StageFailure(
                "m", ("E121", "E200")))],
        )
        assert outcomes[-1].status == "failed"
        assert "E121 E200" in (outcomes[-1].error or "")
        assert "names E200" in (outcomes[-1].error or "")

    def test_a_second_diagnostic_with_the_named_code_fails(self) -> None:
        """Codes are a multiset, one entry per diagnostic: `E200` names one
        E200, and a second is a different failure (PR #1484 re-review)."""
        outcomes = evaluate_block(
            self._block(("E200",)),
            [("check", lambda _c: doc_annotations.StageFailure("m", ("E200", "E200")))],
        )
        assert outcomes[-1].status == "failed"
        assert "E200 E200" in (outcomes[-1].error or "")

    def test_a_repeated_code_names_each_diagnostic(self) -> None:
        outcomes = evaluate_block(
            self._block(("E200", "E200")),
            [("check", lambda _c: doc_annotations.StageFailure("m", ("E200", "E200")))],
        )
        assert outcomes[-1].status == "skipped"

    def test_a_failure_carrying_only_some_named_codes_fails(self) -> None:
        """The marker names the failure exactly: when one of its codes
        stops appearing — the #686 half of an `E130 E200` marker, once the
        invariant clause lands — the marker is out of date and fails (PR
        #1484 review)."""
        outcomes = evaluate_block(
            self._block(("E130", "E200")),
            [("check", lambda _c: doc_annotations.StageFailure(
                "m", ("E200",)))],
        )
        assert outcomes[-1].status == "failed"

    def test_a_failure_with_no_code_fails_a_coded_marker(self) -> None:
        outcomes = evaluate_block(
            self._block(("E200",)), [("check", lambda _c: "no code at all")]
        )
        assert outcomes[-1].status == "failed"

    def test_an_uncoded_marker_excuses_any_failure_at_parse(self) -> None:
        ann = doc_annotations.Annotation(1, "parse", "FRAGMENT", "r")
        block = CodeBlock(2, "vera", "x", (ann,))
        outcomes = evaluate_block(block, [("parse", _try_parse)])
        assert outcomes[-1].status == "skipped"


class TestNoRunMarkers:
    """`vera:no-run` says why a block that exports a function names no
    invocation (#1484 review)."""

    def test_marker_attaches_to_following_fence(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:no-run category="network" reason="calls Http" -->\n'
            "```vera\nprogram\n```\n",
        )
        blocks, problems = scan_markdown(path)
        assert problems == []
        assert blocks[0].no_runs == (
            doc_annotations.NoRunMarker(1, "network", "calls Http"),
        )

    def test_blank_reason_is_problem(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:no-run category="network" reason="" -->\n```vera\nx\n```\n',
        )
        _blocks, problems = scan_markdown(path)
        assert len(problems) == 1 and "blank 'reason'" in problems[0]

    def test_no_run_markers_of_two_categories_attach(self, tmp_path: Path) -> None:
        """Exports that need different properties each carry their own
        marker (PR #1484 round-3 review)."""
        path = _md(
            tmp_path,
            '<!-- vera:no-run category="network" reason="a" -->\n'
            '<!-- vera:no-run category="api-key" reason="b" -->\n'
            "```vera\nx\n```\n",
        )
        blocks, problems = scan_markdown(path)
        assert problems == []
        assert [m.category for m in blocks[0].no_runs] == ["network", "api-key"]

    def test_a_repeated_no_run_category_is_a_problem(self, tmp_path: Path) -> None:
        path = _md(
            tmp_path,
            '<!-- vera:no-run category="network" reason="a" -->\n'
            '<!-- vera:no-run category="network" reason="b" -->\n'
            "```vera\nx\n```\n",
        )
        _blocks, problems = scan_markdown(path)
        assert len(problems) == 1 and "one marker per category" in problems[0]

    def test_no_run_marker_lines_are_stripped(self) -> None:
        text = (
            "before\n"
            '<!-- vera:no-run category="network" reason="calls Http" -->\n'
            "```vera\nprogram\n```\n"
        )
        assert "vera:no-run" not in strip_annotations(text)


class TestCommonMarkFences:
    """A fence is recognised as CommonMark recognises one, so a fence GitHub
    renders is one the gate reads (#1484 review)."""

    def _one(self, tmp_path: Path, text: str) -> Any:
        blocks, problems = scan_markdown(_md(tmp_path, text))
        assert problems == []
        assert len(blocks) == 1
        return blocks[0]

    def test_indented_fence(self, tmp_path: Path) -> None:
        block = self._one(
            tmp_path, "- item\n\n  ```vera\n  fn broken(\n    body\n  ```\n"
        )
        assert block.lang == "vera"
        assert block.content == "fn broken(\n  body"

    def test_tilde_fence(self, tmp_path: Path) -> None:
        block = self._one(tmp_path, "~~~vera\nfn broken(\n~~~\n")
        assert block.lang == "vera"

    def test_longer_fence_holds_shorter_runs(self, tmp_path: Path) -> None:
        block = self._one(tmp_path, "````vera\nx\n```\ny\n````\n")
        assert block.content == "x\n```\ny"

    def test_closer_must_use_the_same_character(self, tmp_path: Path) -> None:
        block = self._one(tmp_path, "```vera\nx\n~~~\ny\n```\n")
        assert block.content == "x\n~~~\ny"

    def test_info_string_takes_its_first_word(self, tmp_path: Path) -> None:
        block = self._one(tmp_path, '```vera title="demo"\nx\n```\n')
        assert block.lang == "vera"

    def test_info_string_keeps_the_scan_in_step(self, tmp_path: Path) -> None:
        """The reviewer's desync: an opener with attributes used to be
        misread, its closer taken for an opener, and the next real block
        swallowed.  Both blocks are found, each with its own content."""
        blocks, problems = scan_markdown(_md(
            tmp_path,
            '```vera title="demo"\na\n```\n\nprose\n\n```vera\nb\n```\n',
        ))
        assert problems == []
        assert [(b.lang, b.content) for b in blocks] == [("vera", "a"), ("vera", "b")]

    def test_backtick_in_a_backtick_info_string_is_not_a_fence(self) -> None:
        assert doc_annotations.fence_opener("```vera `x`") is None
        assert doc_annotations.fence_opener("~~~vera `x`") is not None

    def test_closer_is_at_least_as_long(self) -> None:
        opener = doc_annotations.fence_opener("````vera")
        assert opener is not None
        assert not doc_annotations.fence_closes(opener, "```")
        assert doc_annotations.fence_closes(opener, "`````")


class TestStripAnnotations:
    """build_site.py must not leak annotations into generated site assets."""

    def test_run_marker_lines_removed(self) -> None:
        text = (
            "before\n"
            '<!-- vera:run fn="main" stdout="5" -->\n'
            "```vera\nprogram\n```\n"
        )
        stripped = strip_annotations(text)
        assert "vera:run" not in stripped
        assert "before\n```vera\nprogram\n```" in stripped

    def test_annotation_lines_removed(self) -> None:
        text = (
            "before\n"
            '<!-- vera:skip-parse category="FRAGMENT" reason="bare expr" -->\n'
            "```vera\n1 + 2\n```\n"
            "after\n"
        )
        stripped = strip_annotations(text)
        assert "vera:skip" not in stripped
        assert "```vera\n1 + 2\n```" in stripped
        assert "before\n```vera" in stripped  # no blank residue line

    def test_other_html_comments_survive(self) -> None:
        text = "<!-- a normal comment -->\ncontent\n"
        assert strip_annotations(text) == text


# =====================================================================
# `vera:diagnostic` — rendered-diagnostic replay (#1291)
# =====================================================================

_E130_EXAMPLE = (
    '<!-- vera:diagnostic file="main.vera" stage="check" error_code="E130" -->\n'
    "```vera\n"
    "type Meters = Int;\n"
    "type Feet = Int;\n"
    "\n"
    "private fn excess(@Meters, @Feet -> @Int)\n"
    "  requires(true)\n"
    "  ensures(true)\n"
    "  effects(pure)\n"
    "{\n"
    "  @Metres.0 - @Feet.0 / 3\n"
    "}\n"
    "```\n"
    "<!-- /vera:diagnostic -->\n"
    "```text\n"
    "[E130] Error at main.vera, line 9, column 3:\n"
    "\n"
    "      @Metres.0 - @Feet.0 / 3\n"
    "      ^\n"
    "\n"
    "  Cannot resolve @Metres.0: no Metres bindings in scope.\n"
    "\n"
    "  Slot reference @Metres.0 requires at least 1 binding(s) of type Metres.\n"
    "\n"
    "  Fix:\n"
    "\n"
    "    Ensure enough Metres bindings are in scope, or use a lower index."
    " Available bindings: @Feet.0: Int; @Meters.0: Int.\n"
    "\n"
    '  See: Chapter 3, Section 3.4 "Reference Resolution"\n'
    "```\n"
)


class TestScanDiagnosticExamples:
    def test_well_formed_example_is_extracted(self, tmp_path: Path) -> None:
        p = _md(tmp_path, _E130_EXAMPLE)
        examples, problems = scan_diagnostic_examples(p)
        assert problems == []
        assert len(examples) == 1
        ex = examples[0]
        assert ex.file == "main.vera"
        assert ex.stage == "check"
        assert ex.error_code == "E130"
        assert "@Metres.0 - @Feet.0 / 3" in ex.program
        assert "[E130] Error at main.vera" in ex.fence_content

    def test_stage_defaults_to_check_when_omitted(self, tmp_path: Path) -> None:
        text = (
            '<!-- vera:diagnostic file="main.vera" -->\n'
            "```vera\nprogram\n```\n"
            "<!-- /vera:diagnostic -->\n"
            "```text\nx\n```\n"
        )
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert problems == []
        assert examples[0].stage == "check"
        assert examples[0].error_code is None

    def test_dangling_open_with_no_close_is_a_problem(
        self, tmp_path: Path,
    ) -> None:
        text = '<!-- vera:diagnostic file="main.vera" -->\nprogram\n'
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert examples == []
        assert len(problems) == 1 and "no matching" in problems[0]

    def test_close_with_no_open_is_a_problem(self, tmp_path: Path) -> None:
        text = "prose\n<!-- /vera:diagnostic -->\n"
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert examples == []
        assert len(problems) == 1 and "no preceding" in problems[0]

    def test_bare_unfenced_body_is_a_problem(self, tmp_path: Path) -> None:
        """CodeRabbit #1377: a program left bare between the two
        annotation comments (not wrapped in its own ```vera fence) is
        invisible to the documentation example gate, which only
        collects fenced blocks — so the scanner must refuse it rather
        than silently replay an example the sibling gate never sees."""
        text = (
            '<!-- vera:diagnostic file="main.vera" -->\n'
            "program\n<!-- /vera:diagnostic -->\n```text\nx\n```\n"
        )
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert examples == []
        assert len(problems) == 1
        assert "must be wrapped in its own ```vera fence" in problems[0]

    def test_missing_fence_after_close_is_a_problem(
        self, tmp_path: Path,
    ) -> None:
        text = (
            '<!-- vera:diagnostic file="main.vera" -->\n'
            "```vera\nprogram\n```\n<!-- /vera:diagnostic -->\nno fence here\n"
        )
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert examples == []
        assert len(problems) == 1 and "not immediately followed" in problems[0]

    def test_non_text_fence_after_close_is_a_problem(
        self, tmp_path: Path,
    ) -> None:
        text = (
            '<!-- vera:diagnostic file="main.vera" -->\n'
            "```vera\nprogram\n```\n<!-- /vera:diagnostic -->\n```vera\nnope\n```\n"
        )
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert examples == []
        assert len(problems) == 1 and "not ```text" in problems[0]

    def test_malformed_annotation_is_a_problem(self, tmp_path: Path) -> None:
        text = "<!-- vera:diagnostic file=main.vera -->\nprogram\n"
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert examples == []
        assert any("malformed" in p for p in problems)

    def test_two_examples_in_one_document(self, tmp_path: Path) -> None:
        text = _E130_EXAMPLE + "\nmore prose\n\n" + _E130_EXAMPLE
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert problems == []
        assert len(examples) == 2

    def test_unterminated_fence_is_a_problem(self, tmp_path: Path) -> None:
        """Keyed to the FENCE's own line (`fence_line`), not the
        annotation's `start_line` — the one problem message in this
        scanner with that anchor, so an off-by-one there would
        otherwise stay invisible (CodeRabbit #1377)."""
        text = (
            '<!-- vera:diagnostic file="main.vera" -->\n'
            "```vera\nprogram\n```\n<!-- /vera:diagnostic -->\n```text\nno close\n"
        )
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert examples == []
        # The fence opens on line 6, not on the annotation's line 1.
        assert problems == [
            "line 6: unterminated code fence "
            "(no closing ``` before end of file)"
        ]

    def test_second_open_before_close_reports_and_reparses(
        self, tmp_path: Path,
    ) -> None:
        """A second `vera:diagnostic` open before the first one closes
        must both report the dangling first annotation AND re-process
        the second one as its own example, not silently consume it."""
        text = (
            '<!-- vera:diagnostic file="a.vera" -->\n'
            "program\n" + _E130_EXAMPLE
        )
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert len(examples) == 1
        assert examples[0].file == "main.vera"
        assert len(problems) == 1
        assert "no matching" in problems[0] and "line 1:" in problems[0]


class TestReplayDiagnosticExamples:
    def test_matching_fence_produces_no_failures(self, tmp_path: Path) -> None:
        examples, _ = scan_diagnostic_examples(_md(tmp_path, _E130_EXAMPLE))
        assert replay_diagnostic_examples(examples) == []

    def test_stale_fence_is_a_failure(self, tmp_path: Path) -> None:
        """The #1262 shape: the fix text is extended in vera/errors.py-
        adjacent code, but the doc's fence is not updated."""
        stale = _E130_EXAMPLE.replace(
            "Ensure enough Metres bindings are in scope, or use a lower index.",
            "Ensure enough Metres bindings are in scope, or use a lower index."
            " NEW TEXT.",
        )
        examples, _ = scan_diagnostic_examples(_md(tmp_path, stale))
        failures = replay_diagnostic_examples(examples)
        assert len(failures) == 1
        assert "does not match live output" in failures[0]

    def test_wrong_error_code_is_a_failure(self, tmp_path: Path) -> None:
        wrong_code = _E130_EXAMPLE.replace('error_code="E130"', 'error_code="E999"')
        examples, _ = scan_diagnostic_examples(_md(tmp_path, wrong_code))
        failures = replay_diagnostic_examples(examples)
        assert len(failures) == 1
        assert "found 0" in failures[0]

    def test_no_error_code_requires_exactly_one_diagnostic(
        self, tmp_path: Path,
    ) -> None:
        no_code = _E130_EXAMPLE.replace(' error_code="E130"', "")
        examples, _ = scan_diagnostic_examples(_md(tmp_path, no_code))
        # The program produces exactly one diagnostic (E130), so omitting
        # error_code must still resolve unambiguously.
        assert replay_diagnostic_examples(examples) == []

    def test_no_error_code_with_multiple_diagnostics_is_ambiguous(
        self, tmp_path: Path,
    ) -> None:
        """The complement of the test above: a second `@Metres` typo
        makes the program produce two E130 diagnostics, so an example
        with no error_code to disambiguate must fail rather than
        silently pick one (CodeRabbit #1377)."""
        two_diagnostics = _E130_EXAMPLE.replace(
            "  @Metres.0 - @Feet.0 / 3\n",
            "  @Metres.0 - @Metres.1 - @Feet.0 / 3\n",
        ).replace(' error_code="E130"', "")
        examples, _ = scan_diagnostic_examples(_md(tmp_path, two_diagnostics))
        failures = replay_diagnostic_examples(examples)
        assert len(failures) == 1
        assert "found 2" in failures[0]

    def test_explicit_error_code_with_multiple_matches_is_ambiguous(
        self, tmp_path: Path,
    ) -> None:
        """CodeRabbit #1377 (the ninth thread): the test above covers
        only the NO-error_code branch. A regression that accepts
        multiple matches for a SELECTED code — e.g. `!= 1` weakened to
        `< 1` — would pass every existing test if this one did not
        exist, since the two `@Metres` typos here both carry the SAME
        error_code, `error_code="E130"` kept (not stripped)."""
        two_diagnostics = _E130_EXAMPLE.replace(
            "  @Metres.0 - @Feet.0 / 3\n",
            "  @Metres.0 - @Metres.1 - @Feet.0 / 3\n",
        )
        examples, _ = scan_diagnostic_examples(_md(tmp_path, two_diagnostics))
        failures = replay_diagnostic_examples(examples)
        assert len(failures) == 1
        assert "found 2" in failures[0]

    def test_zero_diagnostics_is_a_failure(self, tmp_path: Path) -> None:
        text = (
            '<!-- vera:diagnostic file="main.vera" -->\n'
            "```vera\n"
            "public fn main(@Unit -> @Unit)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ () }\n"
            "```\n"
            "<!-- /vera:diagnostic -->\n"
            "```text\nsomething\n```\n"
        )
        examples, _ = scan_diagnostic_examples(_md(tmp_path, text))
        failures = replay_diagnostic_examples(examples)
        assert len(failures) == 1 and "found 0" in failures[0]

    def test_unsupported_stage_is_a_failure(self, tmp_path: Path) -> None:
        verify_stage = _E130_EXAMPLE.replace('stage="check"', 'stage="verify"')
        examples, _ = scan_diagnostic_examples(_md(tmp_path, verify_stage))
        failures = replay_diagnostic_examples(examples)
        assert len(failures) == 1 and "not replayed yet" in failures[0]

    def test_unparseable_program_is_a_failure_not_a_raise(
        self, tmp_path: Path,
    ) -> None:
        text = (
            '<!-- vera:diagnostic file="main.vera" -->\n'
            "```vera\nthis is not valid vera at all {{{\n```\n"
            "<!-- /vera:diagnostic -->\n"
            "```text\nanything\n```\n"
        )
        examples, _ = scan_diagnostic_examples(_md(tmp_path, text))
        failures = replay_diagnostic_examples(examples)
        assert len(failures) == 1 and "raised" in failures[0]


class TestDeBruijnHasTheLiveExample:
    """The actual DE_BRUIJN.md annotation this issue was filed about must
    stay live-accurate — the same regression pin `check_diagnostic_examples.py`
    runs, exercised here too so `pytest tests/` alone catches a drift."""

    def test_de_bruijn_diagnostic_examples_match_live_output(self) -> None:
        path = Path(__file__).parent.parent / "DE_BRUIJN.md"
        examples, problems = scan_diagnostic_examples(path)
        assert problems == []
        assert len(examples) >= 1
        assert replay_diagnostic_examples(examples) == []
