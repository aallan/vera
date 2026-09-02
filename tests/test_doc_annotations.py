"""Tests for scripts/doc_annotations.py — inline fence-annotation support (#538).

The doc code-block gates (check_skill_examples.py and friends) used to keep
line-number-keyed ALLOWLIST dicts that went stale on every doc edit and needed
scripts/fix_allowlists.py to renumber (whose bulk-shift heuristic was itself
buggy — #606).  #538 replaced both with inline HTML-comment annotations placed
immediately before each fence:

    <!-- vera:skip-parse category="FRAGMENT" reason="bare type expression" -->
    ```vera
    List<Result<User, Error>>
    ```

These tests pin the shared scanning/evaluation module the gates now use:

  - an annotated unparseable block is SKIPPED (expected failure — gate green)
  - an unannotated unparseable block FAILS the gate
  - a STALE annotation (block passes the stage it is exempted from) FAILS the
    gate, so the skip surface shrinks over time (mirrors check_e602_clean.py's
    stale-entry treatment)
  - malformed / dangling / duplicate annotations are hard problems
  - build_site.py's strip helper removes annotation lines so they never leak
    into generated site assets (docs/SKILL.md, docs/llms-full.txt)
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

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
unsupported_stage_annotations = doc_annotations.unsupported_stage_annotations
strip_annotations = doc_annotations.strip_annotations
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
            '<!-- vera:skip-check category="INCOMPLETE" reason="uses ext fn" -->\n'
            '<!-- vera:skip-verify category="ILLUSTRATIVE" reason="loose contract" -->\n'
            "```vera\nx\n```\n",
        )
        blocks, problems = scan_markdown(path)
        assert problems == []
        stages = [a.stage for a in blocks[0].annotations]
        assert stages == ["check", "verify"]

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
        assert "malformed" in problems[0]

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
            '<!-- vera:skip-parse category="A" reason="one" -->\n'
            '<!-- vera:skip-parse category="B" reason="two" -->\n'
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

    def test_unsupported_stage_annotations(self) -> None:
        ann_p = doc_annotations.Annotation(1, "parse", "FRAGMENT", "r")
        ann_c = doc_annotations.Annotation(2, "check", "INCOMPLETE", "r")
        block = CodeBlock(3, "vera", "x", (ann_p, ann_c))
        extra = unsupported_stage_annotations(block, {"parse"})
        assert extra == [ann_c]


class TestStripAnnotations:
    """build_site.py must not leak annotations into generated site assets."""

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
            "program\n"
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

    def test_missing_fence_after_close_is_a_problem(
        self, tmp_path: Path,
    ) -> None:
        text = (
            '<!-- vera:diagnostic file="main.vera" -->\n'
            "program\n<!-- /vera:diagnostic -->\nno fence here\n"
        )
        examples, problems = scan_diagnostic_examples(_md(tmp_path, text))
        assert examples == []
        assert len(problems) == 1 and "not immediately followed" in problems[0]

    def test_non_text_fence_after_close_is_a_problem(
        self, tmp_path: Path,
    ) -> None:
        text = (
            '<!-- vera:diagnostic file="main.vera" -->\n'
            "program\n<!-- /vera:diagnostic -->\n```vera\nnope\n```\n"
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

    def test_zero_diagnostics_is_a_failure(self, tmp_path: Path) -> None:
        text = (
            '<!-- vera:diagnostic file="main.vera" -->\n'
            "public fn main(@Unit -> @Unit)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ () }\n"
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
            "this is not valid vera at all {{{\n"
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
