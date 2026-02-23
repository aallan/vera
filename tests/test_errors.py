"""Error message tests — verify LLM-oriented diagnostic quality."""

import pytest

from vera.errors import (
    Diagnostic,
    ParseError,
    SourceLocation,
    missing_contract_block,
    missing_effect_clause,
    malformed_slot_reference,
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
