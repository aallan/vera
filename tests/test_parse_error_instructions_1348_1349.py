"""#1349 / #1348 — the parser's fallback, brought up to the project's bar.

Two symptoms of one thing: `unexpected_token` is a *fallback*, and both
halves of what it prints were below the standard spec §0.5 sets for a
diagnostic.

**#1349** — it rendered Lark's terminal names verbatim, so the expected
set read `COMMA, EQUAL, LBRACE, MORETHAN, RPAR, SEMICOLON, VBAR,
__ANON_0`.  `__ANON_0` names nothing a Vera author can write; it is the
parser generator's own label for the literal `->`.  The codebase already
knew these names were internal — `vera/errors.py` carried a special case
keyed on `__ANON_9` with a comment identifying it as `"::"` — it just
never filtered them before display.  All ten anonymous terminals in the
grammar are literal strings, so the display table is *derived* from the
live grammar rather than hand-written, and the completeness cell below
walks every terminal the parser has.

**#1348** — the fix line it offered ("Replace the unexpected token with
one of the expected tokens, or check for a missing delimiter") cannot be
acted on for the shape that produces it most often: a contract clause
written after `effects`.  Replacing `decreases` with `COMMA` is not a
repair and there is no missing delimiter; the actual repair — move the
clause above `effects` — was never stated.  E032 now states it.
"""
from __future__ import annotations

import pytest

from vera.errors import ERROR_CODES
from vera.parser import parse_to_ast


def _diag(source: str):
    """Parse and return the single diagnostic a rejected program yields."""
    from vera.errors import VeraError

    try:
        parse_to_ast(source)
    except VeraError as exc:
        return exc.diagnostic
    raise AssertionError("expected a parse error, got a clean parse")


def _fn(clauses: str, extra: str = "") -> str:
    return (
        f"{extra}public fn f(@Int -> @Int)\n"
        f"{clauses}"
        "{\n"
        "  @Int.0\n"
        "}\n"
    )


CLAUSES_OK = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


# =====================================================================
# #1349 — no internal name reaches the reader
# =====================================================================

class TestTerminalNamesAreDisplayable:

    def test_the_repro_list_has_no_anonymous_terminal(self) -> None:
        d = _diag(_fn(CLAUSES_OK + "  decreases(@Int.0)\n"))
        assert "__ANON" not in d.description, d.description

    def test_the_literal_is_shown_instead(self) -> None:
        """`__ANON_0` is `->`; showing it is the point, not hiding it.

        Asserted on the DIAGNOSTIC, not only on `terminal_display`: a
        change that filtered anonymous terminals out of the expected set
        instead of translating them would satisfy "no `__ANON`" while
        removing the most useful entry in the list.
        """
        d = _diag("public fn f(@Int @Int) requires(true) ensures(true)\n"
                  "effects(pure)\n{\n  @Int.0\n}\n")
        assert "__ANON" not in d.description
        assert '"->"' in d.description, d.description

    def test_every_terminal_in_the_live_grammar_displays(self) -> None:
        """The completeness walk: no terminal renders as a raw Lark name.

        Asserted against the grammar the parser actually built, so a
        terminal added to `grammar.lark` — anonymous or not — fails here
        rather than surfacing in someone's error message.
        """
        from vera.errors import terminal_display
        from vera.parser import _get_parser

        raw = []
        for term in _get_parser().terminals:
            shown = terminal_display(term.name)
            if shown.startswith("__ANON") or shown != shown.strip():
                raw.append((term.name, shown))
        assert raw == [], f"terminals with no display form: {raw}"

    def test_a_literal_terminal_shows_its_spelling(self) -> None:
        from vera.errors import terminal_display

        assert terminal_display("__ANON_0") == '"->"'
        assert terminal_display("COMMA") == '","'
        assert terminal_display("LBRACE") == '"{"'

    def test_a_pattern_terminal_keeps_its_name(self) -> None:
        """A class of tokens has no single spelling to show."""
        from vera.errors import terminal_display

        assert terminal_display("INT_LIT") == "INT_LIT"
        assert terminal_display("LOWER_IDENT") == "LOWER_IDENT"

    def test_an_unknown_name_is_returned_unchanged(self) -> None:
        from vera.errors import terminal_display

        assert terminal_display("NOT_A_TERMINAL") == "NOT_A_TERMINAL"


# =====================================================================
# #1348 — the clause-order diagnostic
# =====================================================================

class TestContractClauseAfterEffects:

    @pytest.mark.parametrize(
        "clause",
        ["requires(true)", "ensures(true)", "decreases(@Int.0)"],
    )
    def test_each_contract_keyword_after_effects(self, clause: str) -> None:
        d = _diag(_fn(CLAUSES_OK + f"  {clause}\n"))
        assert d.error_code == "E032", (d.error_code, d.description)
        keyword = clause.split("(")[0]
        assert keyword in d.description
        assert "effects" in d.description

    def test_the_fix_names_the_move(self) -> None:
        d = _diag(_fn(CLAUSES_OK + "  decreases(@Int.0)\n"))
        assert "above" in d.fix and "effects" in d.fix
        # The generic advice is what this diagnostic exists to replace.
        assert "Replace the unexpected token" not in d.fix
        assert "missing delimiter" not in d.fix

    def test_it_carries_the_full_diagnostic_shape(self) -> None:
        d = _diag(_fn(CLAUSES_OK + "  decreases(@Int.0)\n"))
        assert d.rationale and len(d.rationale) > 30
        assert d.spec_ref
        assert d.location.line == 5 and d.location.column == 3

    def test_invariant_is_not_a_function_clause(self) -> None:
        """`invariant` belongs to `data`, so E032's advice would be wrong.

        The grammar attaches `invariant_clause` to `data_decl` alone, so
        an `invariant` in a function is not a misplaced contract clause —
        moving it above `effects`, which is what E032 instructs, produces
        `[E002] Missing effect clause` rather than a working program.  It
        keeps the generic fallback, and the cell pins that the E032 arm
        does not reach for it.
        """
        after = _diag(_fn(CLAUSES_OK + "  invariant(true)\n"))
        assert after.error_code != "E032", after.description
        before = _diag(_fn("  requires(true)\n  ensures(true)\n"
                           "  invariant(true)\n  effects(pure)\n"))
        assert before.error_code == "E002", before.description

    def test_e032_is_registered(self) -> None:
        assert "E032" in ERROR_CODES and ERROR_CODES["E032"]

    def test_the_correct_order_still_parses(self) -> None:
        """The control: `decreases` before `effects` is legal."""
        src = _fn("  requires(true)\n  ensures(true)\n"
                  "  decreases(@Int.0)\n  effects(pure)\n")
        parse_to_ast(src)  # must not raise

    def test_an_unrelated_token_keeps_the_generic_fallback(self) -> None:
        """The boundary: E032 fires on the clause-order shape alone."""
        d = _diag("public fn f(@Int -> @Int)\n  requires(true)\n"
                  "  ensures(true)\n  effects(pure)\n{\n  @Int.0 +\n}\n")
        assert d.error_code != "E032", d.description
