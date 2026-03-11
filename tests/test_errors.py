"""Error message tests — verify LLM-oriented diagnostic quality."""

from __future__ import annotations

import html as html_mod
import re
from pathlib import Path

import pytest

from vera.errors import (
    Diagnostic,
    ParseError,
    SourceLocation,
    VeraError,
    diagnose_lark_error,
    missing_contract_block,
    missing_effect_clause,
    malformed_slot_reference,
    unclosed_block,
    unexpected_token,
    _get_source_line,
)
from vera.parser import parse

ROOT = Path(__file__).parent.parent
README = ROOT / "README.md"
INDEX_HTML = ROOT / "docs" / "index.html"
SPEC_INTRO = ROOT / "spec" / "00-introduction.md"


class TestDiagnosticFormat:
    """Diagnostics must include all required fields per spec 0.5."""

    def test_includes_location(self) -> None:
        d = Diagnostic(
            description="test",
            location=SourceLocation(file="test.vera", line=5, column=3),
        )
        formatted = d.format()
        assert "line 5" in formatted
        assert "column 3" in formatted
        assert "test.vera" in formatted

    def test_includes_source_line(self) -> None:
        d = Diagnostic(
            description="test",
            location=SourceLocation(line=1, column=1),
            source_line="fn bad(@Int -> @Int)",
        )
        formatted = d.format()
        assert "fn bad(@Int -> @Int)" in formatted

    def test_includes_fix(self) -> None:
        d = Diagnostic(
            description="test",
            location=SourceLocation(line=1, column=1),
            fix="Add requires(true)",
        )
        formatted = d.format()
        assert "Fix:" in formatted
        assert "requires(true)" in formatted

    def test_includes_spec_ref(self) -> None:
        d = Diagnostic(
            description="test",
            location=SourceLocation(line=1, column=1),
            spec_ref="Chapter 5, Section 5.1",
        )
        formatted = d.format()
        assert "Chapter 5" in formatted


class TestMissingContractDiagnostic:
    def test_has_description(self) -> None:
        d = missing_contract_block("test.vera", "fn f(@Int -> @Int) {", 1, 1)
        assert "missing" in d.description.lower()
        assert "contract" in d.description.lower()

    def test_has_fix_with_example(self) -> None:
        d = missing_contract_block("test.vera", "fn f(@Int -> @Int) {", 1, 1)
        assert "requires" in d.fix
        assert "ensures" in d.fix
        assert "effects" in d.fix

    def test_has_spec_ref(self) -> None:
        d = missing_contract_block("test.vera", "fn f(@Int -> @Int) {", 1, 1)
        assert "Chapter 5" in d.spec_ref


class TestMissingEffectDiagnostic:
    def test_has_description(self) -> None:
        d = missing_effect_clause("test.vera", "", 1, 1)
        assert "effects" in d.description.lower()

    def test_has_fix_examples(self) -> None:
        d = missing_effect_clause("test.vera", "", 1, 1)
        assert "effects(pure)" in d.fix
        assert "effects(<IO>)" in d.fix

    def test_has_spec_ref(self) -> None:
        d = missing_effect_clause("test.vera", "", 1, 1)
        assert "Chapter 7" in d.spec_ref


class TestSlotReferenceDiagnostic:
    def test_has_description(self) -> None:
        d = malformed_slot_reference("test.vera", "", 1, 1, "@int.0")
        assert "@int.0" in d.description
        assert "slot reference" in d.description.lower()

    def test_has_fix_examples(self) -> None:
        d = malformed_slot_reference("test.vera", "", 1, 1, "@int.0")
        assert "@Int.0" in d.fix
        assert "@T.result" in d.fix

    def test_has_spec_ref(self) -> None:
        d = malformed_slot_reference("test.vera", "", 1, 1, "@int.0")
        assert "Chapter 3" in d.spec_ref


class TestParseErrorDiagnostics:
    """End-to-end: actual parse errors produce LLM-friendly messages."""

    def test_missing_contracts_error_message(self) -> None:
        """Missing contracts should produce a helpful diagnostic."""
        with pytest.raises(ParseError) as exc_info:
            parse("fn f(@Int -> @Int) { @Int.0 }")
        msg = exc_info.value.diagnostic.format()
        # Should mention the problem, not just "unexpected token"
        assert "line" in msg.lower()

    def test_error_includes_source_context(self) -> None:
        """Error messages should show the offending source line."""
        with pytest.raises(ParseError) as exc_info:
            parse("fn f(@Int -> @Int) { @Int.0 }")
        msg = exc_info.value.diagnostic.format()
        assert "fn f" in msg

    def test_invalid_character_error(self) -> None:
        """Invalid characters should produce a clear diagnostic."""
        with pytest.raises(ParseError) as exc_info:
            parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { $ }")
        msg = exc_info.value.diagnostic.format()
        assert "line" in msg.lower()


# =====================================================================
# SourceLocation
# =====================================================================

class TestSourceLocation:
    def test_str_with_file(self) -> None:
        loc = SourceLocation(file="foo.vera", line=3, column=7)
        s = str(loc)
        assert "foo.vera" in s
        assert "line 3" in s
        assert "column 7" in s

    def test_str_without_file(self) -> None:
        loc = SourceLocation(line=10, column=1)
        s = str(loc)
        assert "line 10" in s
        assert "column 1" in s
        # No file path in output
        assert ".vera" not in s

    def test_to_dict_with_file(self) -> None:
        loc = SourceLocation(file="bar.vera", line=5, column=2)
        d = loc.to_dict()
        assert d["line"] == 5
        assert d["column"] == 2
        assert d["file"] == "bar.vera"

    def test_to_dict_without_file(self) -> None:
        loc = SourceLocation(line=1, column=1)
        d = loc.to_dict()
        assert "file" not in d
        assert d["line"] == 1


# =====================================================================
# Diagnostic serialization
# =====================================================================

class TestDiagnosticSerialization:
    def test_to_dict_all_fields(self) -> None:
        d = Diagnostic(
            description="bad thing",
            location=SourceLocation(file="x.vera", line=2, column=3),
            source_line="  let @Int = 5;",
            rationale="because rules",
            fix="do this instead",
            spec_ref="Chapter 1",
            severity="error",
        )
        result = d.to_dict()
        assert result["severity"] == "error"
        assert result["description"] == "bad thing"
        assert result["source_line"] == "  let @Int = 5;"
        assert result["rationale"] == "because rules"
        assert result["fix"] == "do this instead"
        assert result["spec_ref"] == "Chapter 1"
        assert result["location"]["line"] == 2

    def test_to_dict_minimal(self) -> None:
        d = Diagnostic(
            description="oops",
            location=SourceLocation(line=1, column=1),
        )
        result = d.to_dict()
        assert result["severity"] == "error"
        assert result["description"] == "oops"
        # Optional fields omitted
        assert "source_line" not in result
        assert "rationale" not in result
        assert "fix" not in result
        assert "spec_ref" not in result

    def test_warning_severity(self) -> None:
        d = Diagnostic(
            description="mild concern",
            location=SourceLocation(line=1, column=1),
            severity="warning",
        )
        assert d.to_dict()["severity"] == "warning"
        assert "Warning" in d.format()


# =====================================================================
# diagnose_lark_error
# =====================================================================

class TestDiagnoseLarkError:
    def test_unknown_exception_wraps(self) -> None:
        """Non-Lark exceptions produce an 'Internal parser error' diagnostic."""
        exc = ValueError("something weird")
        d = diagnose_lark_error(exc, "fn f() {}")
        assert "Internal parser error" in d.description
        assert "something weird" in d.description

    def test_unexpected_characters(self) -> None:
        """UnexpectedCharacters produces a diagnostic with line info."""
        with pytest.raises(ParseError) as exc_info:
            parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { ` }")
        d = exc_info.value.diagnostic
        assert d.location.line > 0
        assert "Unexpected" in d.description


# =====================================================================
# Helpers and additional diagnostic factories
# =====================================================================

class TestHelpers:
    def test_get_source_line_valid(self) -> None:
        source = "line1\nline2\nline3"
        assert _get_source_line(source, 2) == "line2"

    def test_get_source_line_out_of_range(self) -> None:
        assert _get_source_line("hello", 5) == ""

    def test_get_source_line_zero(self) -> None:
        assert _get_source_line("hello", 0) == ""


class TestUnclosedBlock:
    def test_has_description(self) -> None:
        d = unclosed_block("test.vera", "fn f() {", 1, 9)
        assert '"}"' in d.description or "closing brace" in d.description

    def test_has_spec_ref(self) -> None:
        d = unclosed_block("test.vera", "", 1, 1)
        assert "Chapter 1" in d.spec_ref


class TestUnexpectedToken:
    def test_lists_expected(self) -> None:
        d = unexpected_token("test.vera", "bad code", 1, 1, "foo", {"BAR", "BAZ"})
        assert "foo" in d.description
        assert "BAR" in d.description or "BAZ" in d.description

    def test_truncates_long_expected(self) -> None:
        many = {f"TOK{i}" for i in range(20)}
        d = unexpected_token("test.vera", "", 1, 1, "x", many)
        assert "..." in d.description


class TestVeraError:
    def test_diagnostic_accessible(self) -> None:
        d = Diagnostic(description="test error", location=SourceLocation(line=1, column=1))
        err = VeraError(d)
        assert err.diagnostic is d

    def test_str_contains_format(self) -> None:
        d = Diagnostic(description="test error", location=SourceLocation(line=1, column=1))
        err = VeraError(d)
        assert "test error" in str(err)


# =====================================================================
# Error display sync: documentation must match compiler output
# =====================================================================

def _extract_readme_error_block() -> str:
    """Extract the fenced code block under 'What Errors Look Like' in README.md."""
    lines = README.read_text(encoding="utf-8").splitlines()
    in_section = False
    in_fence = False
    block_lines: list[str] = []
    for line in lines:
        if line.startswith("## What Errors Look Like"):
            in_section = True
            continue
        if in_section and line.startswith("## "):
            break  # next section
        if in_section and not in_fence and line.strip() == "```":
            in_fence = True
            continue
        if in_fence and line.strip() == "```":
            break
        if in_fence:
            block_lines.append(line)
    return "\n".join(block_lines)


def _extract_html_error_block() -> str:
    """Extract the error display <pre> block from docs/index.html.

    Strips all <span> tags and decodes HTML entities to recover plain text.
    """
    text = INDEX_HTML.read_text(encoding="utf-8")
    # Find the <pre> block containing the E001 error
    match = re.search(
        r"<pre>(<span[^>]*>\[E001\].*?)</pre>", text, re.DOTALL
    )
    assert match, "Could not find E001 error block in docs/index.html"
    raw = match.group(1)
    # Strip HTML tags and decode entities
    plain = re.sub(r"<[^>]+>", "", raw)
    return html_mod.unescape(plain)


def _extract_spec_error_block() -> str:
    """Extract the fenced code block under '0.5.2 Example' in spec/00-introduction.md."""
    lines = SPEC_INTRO.read_text(encoding="utf-8").splitlines()
    in_section = False
    in_fence = False
    block_lines: list[str] = []
    for line in lines:
        if line.startswith("### 0.5.2 Example"):
            in_section = True
            continue
        if in_section and line.startswith("### "):
            break  # next subsection
        if in_section and not in_fence and line.strip() == "```":
            in_fence = True
            continue
        if in_fence and line.strip() == "```":
            break
        if in_fence:
            block_lines.append(line)
    return "\n".join(block_lines)


def _normalize_ws(text: str) -> str:
    """Collapse all whitespace sequences to single spaces."""
    return " ".join(text.split())


class TestErrorDisplaySync:
    """The E001 error in README, docs/index.html, and spec must match the compiler.

    Generates the canonical E001 diagnostic from vera.errors and verifies
    that every semantic component (description, rationale, fix, spec_ref)
    appears identically in all documentation files.  Whitespace is
    normalised before comparison because the docs wrap long lines.
    """

    @pytest.fixture()
    def canonical(self) -> Diagnostic:
        """Generate the canonical E001 diagnostic."""
        return missing_contract_block(
            "main.vera",
            "private fn add(@Int, @Int -> @Int)\n{",
            2,
            1,
        )

    # -- README.md --------------------------------------------------------

    def test_readme_has_error_code(self, canonical: Diagnostic) -> None:
        block = _extract_readme_error_block()
        assert f"[{canonical.error_code}]" in block

    def test_readme_has_description(self, canonical: Diagnostic) -> None:
        block = _normalize_ws(_extract_readme_error_block())
        expected = _normalize_ws(canonical.description)
        assert expected in block, (
            f"README error block is missing the canonical description.\n"
            f"Expected: {expected!r}"
        )

    def test_readme_has_rationale(self, canonical: Diagnostic) -> None:
        block = _normalize_ws(_extract_readme_error_block())
        expected = _normalize_ws(canonical.rationale)
        assert expected in block, (
            f"README error block is missing the canonical rationale.\n"
            f"Expected: {expected!r}"
        )

    def test_readme_has_fix(self, canonical: Diagnostic) -> None:
        block = _extract_readme_error_block()
        # Check each non-blank line of the fix individually (indentation
        # differs between the Diagnostic.fix field and the formatted output).
        for line in canonical.fix.splitlines():
            stripped = line.strip()
            if stripped:
                assert stripped in block, (
                    f"README error block is missing fix line: {stripped!r}"
                )

    def test_readme_has_spec_ref(self, canonical: Diagnostic) -> None:
        block = _extract_readme_error_block()
        assert canonical.spec_ref in block, (
            f"README error block is missing the canonical spec ref.\n"
            f"Expected: {canonical.spec_ref!r}"
        )

    # -- docs/index.html --------------------------------------------------

    def test_html_has_error_code(self, canonical: Diagnostic) -> None:
        block = _extract_html_error_block()
        assert f"[{canonical.error_code}]" in block

    def test_html_has_description(self, canonical: Diagnostic) -> None:
        block = _normalize_ws(_extract_html_error_block())
        expected = _normalize_ws(canonical.description)
        assert expected in block, (
            f"HTML error block is missing the canonical description.\n"
            f"Expected: {expected!r}"
        )

    def test_html_has_rationale(self, canonical: Diagnostic) -> None:
        block = _normalize_ws(_extract_html_error_block())
        expected = _normalize_ws(canonical.rationale)
        assert expected in block, (
            f"HTML error block is missing the canonical rationale.\n"
            f"Expected: {expected!r}"
        )

    def test_html_has_fix(self, canonical: Diagnostic) -> None:
        block = _extract_html_error_block()
        for line in canonical.fix.splitlines():
            stripped = line.strip()
            if stripped:
                assert stripped in block, (
                    f"HTML error block is missing fix line: {stripped!r}"
                )

    def test_html_has_spec_ref(self, canonical: Diagnostic) -> None:
        block = _extract_html_error_block()
        assert canonical.spec_ref in block, (
            f"HTML error block is missing the canonical spec ref.\n"
            f"Expected: {canonical.spec_ref!r}"
        )

    def test_html_has_header_format(self, canonical: Diagnostic) -> None:
        """The header line should follow the [CODE] Error at FILE, line N format."""
        block = _extract_html_error_block()
        assert re.search(
            r"\[E001\] Error at .+, line \d+, column \d+:", block
        ), "HTML error block header doesn't match expected format"

    def test_readme_has_header_format(self, canonical: Diagnostic) -> None:
        """The header line should follow the [CODE] Error at FILE, line N format."""
        block = _extract_readme_error_block()
        assert re.search(
            r"\[E001\] Error at .+, line \d+, column \d+:", block
        ), "README error block header doesn't match expected format"

    # -- spec/00-introduction.md ------------------------------------------

    def test_spec_has_error_code(self, canonical: Diagnostic) -> None:
        block = _extract_spec_error_block()
        assert f"[{canonical.error_code}]" in block

    def test_spec_has_description(self, canonical: Diagnostic) -> None:
        block = _normalize_ws(_extract_spec_error_block())
        expected = _normalize_ws(canonical.description)
        assert expected in block, (
            f"Spec error block is missing the canonical description.\n"
            f"Expected: {expected!r}"
        )

    def test_spec_has_rationale(self, canonical: Diagnostic) -> None:
        block = _normalize_ws(_extract_spec_error_block())
        expected = _normalize_ws(canonical.rationale)
        assert expected in block, (
            f"Spec error block is missing the canonical rationale.\n"
            f"Expected: {expected!r}"
        )

    def test_spec_has_fix(self, canonical: Diagnostic) -> None:
        block = _extract_spec_error_block()
        for line in canonical.fix.splitlines():
            stripped = line.strip()
            if stripped:
                assert stripped in block, (
                    f"Spec error block is missing fix line: {stripped!r}"
                )

    def test_spec_has_spec_ref(self, canonical: Diagnostic) -> None:
        block = _extract_spec_error_block()
        assert canonical.spec_ref in block, (
            f"Spec error block is missing the canonical spec ref.\n"
            f"Expected: {canonical.spec_ref!r}"
        )

    def test_spec_has_header_format(self, canonical: Diagnostic) -> None:
        """The spec header should follow the [CODE] Error at FILE, line N format."""
        block = _extract_spec_error_block()
        assert re.search(
            r"\[E001\] Error at .+, line \d+, column \d+:", block
        ), "Spec error block header doesn't match expected format"
