"""Error message tests — verify LLM-oriented diagnostic quality."""

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
