"""Regression tests for #802 — string_length code-point vs UTF-8 byte mismatch.

Part of the #392 ``smt.py`` soundness audit.  Vera's runtime ``string_length``
counts UTF-8 **bytes**; Z3's ``Length`` over ``z3.String`` counts Unicode **code
points**.  They disagree on every multibyte character, so modeling
``string_length`` with ``z3.Length`` proved *false* contracts at Tier 1 — e.g.
``string_length("é") == 1`` verified, yet the runtime returns ``2``:

    public fn f(@String -> @Int)
      requires(@String.0 == "é")     # U+00E9: 1 code point, 2 UTF-8 bytes
      ensures(@Int.result == 1)      # FALSE — runtime returns 2
      effects(pure)
    { string_length(@String.0) }

Fix (#802): a ``string_length`` of a **non-literal** argument defers to Tier 3
(no byte-length operator exists in Z3's string theory), matching the numeric-cast
/ quantifier / decimal precedent; a string **literal** is modeled at its exact
UTF-8 byte length (sound *and* precise).

Written test-first: the slot-deferral and literal-byte-count tests fail on the
pre-fix verifier, which proves the false contract at Tier 1 via ``z3.Length``.
"""

from __future__ import annotations

from vera.checker import typecheck_with_artifacts
from vera.parser import parse_to_ast
from vera.verifier import VerifyResult, verify


def _verify(source: str) -> VerifyResult:
    ast_ = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast_, source)
    return verify(
        ast_, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


def _ok(result: VerifyResult) -> bool:
    """Verification succeeded iff no error-severity diagnostics (mirrors the
    ``ok`` field of ``vera verify --json``)."""
    return not any(d.severity == "error" for d in result.diagnostics)


class TestStringLengthSoundness802:
    def test_slot_arg_false_length_not_proved_at_tier1(self) -> None:
        # The issue's probe: byte length of "é" is 2, so ensures(result == 1) is
        # FALSE.  Pre-fix the verifier PROVED it at Tier 1 (z3.Length("é") == 1).
        # After the fix the slot-arg string_length defers to Tier 3, so the false
        # postcondition is NOT proved — it is runtime-guarded, and the runtime
        # correctly rejects it.
        result = _verify("""
public fn f(@String -> @Int)
  requires(@String.0 == "é")
  ensures(@Int.result == 1)
  effects(pure)
{ string_length(@String.0) }
""")
        # The string_length-derived postcondition must not be a Tier-1 proof;
        # it must defer to a runtime-guarded Tier-3 obligation.
        assert result.summary.tier3_runtime >= 1, (
            result.summary.tier1_verified, result.summary.tier3_runtime,
        )

    def test_slot_arg_true_length_also_defers(self) -> None:
        # Even the TRUE byte-length contract defers for a slot argument (Z3 has no
        # byte-length operator) — soundness over precision.
        result = _verify("""
public fn f(@String -> @Int)
  requires(@String.0 == "é")
  ensures(@Int.result == 2)
  effects(pure)
{ string_length(@String.0) }
""")
        assert result.summary.tier3_runtime >= 1, (
            result.summary.tier1_verified, result.summary.tier3_runtime,
        )

    def test_literal_arg_byte_length_proved_at_tier1(self) -> None:
        # A string LITERAL has a known exact UTF-8 byte length, modeled precisely:
        # string_length("é") == 2 verifies at Tier 1 (byte model).  Pre-fix this
        # was DISPROVED (z3.Length gave the code-point count 1).
        ok = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == 2) effects(pure)
{ string_length("é") }
""")
        assert _ok(ok), [d.description for d in ok.diagnostics]
        assert ok.summary.tier1_verified >= 1

    def test_literal_arg_wrong_codepoint_length_disproved(self) -> None:
        # The code-point count (1) is the wrong answer for "é"; it must NOT
        # verify.  Pre-fix this was PROVED (z3.Length("é") == 1) — the bug.
        bad = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ string_length("é") }
""")
        assert not _ok(bad), "string_length(\"é\") == 1 is false (byte length is 2)"

    def test_ascii_literal_byte_length_still_proved(self) -> None:
        # ASCII is 1 byte per code point, so the byte model agrees with the old
        # code-point answer — ASCII literal lengths still verify at Tier 1.
        ok = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == 2) effects(pure)
{ string_length("ab") }
""")
        assert _ok(ok) and ok.summary.tier1_verified >= 1

    def test_escaped_unicode_literal_byte_length(self) -> None:
        # The byte count comes from the DECODED literal value, not the raw source
        # text: "\\u{e9}" decodes to é (2 UTF-8 bytes), not its 6 source chars.
        # A naive raw-source-length model would (wrongly) prove == 6.
        ok = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == 2) effects(pure)
{ string_length("\\u{e9}") }
""")
        assert _ok(ok) and ok.summary.tier1_verified >= 1

    def test_four_byte_emoji_literal_byte_length(self) -> None:
        # A 4-byte UTF-8 character (U+1F600) — code-point count 1, byte count 4,
        # the case where code points and bytes diverge most.
        ok = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == 4) effects(pure)
{ string_length("\\u{1F600}") }
""")
        assert _ok(ok) and ok.summary.tier1_verified >= 1

    def test_empty_string_literal_byte_length(self) -> None:
        ok = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == 0) effects(pure)
{ string_length("") }
""")
        assert _ok(ok) and ok.summary.tier1_verified >= 1


class TestStringPredicateSoundness802:
    """contains / starts_with / ends_with are boolean predicates; under UTF-8
    self-synchronization a valid-UTF-8 needle matches at the byte level iff at
    the code-point level, so Z3's Contains/PrefixOf/SuffixOf stay sound on
    non-ASCII input — they remain Tier-1 (this is the verifier side; the
    end-to-end runtime byte semantics are pinned by the non-ASCII string_length
    runtime tests in tests/test_codegen_strings.py)."""

    def test_starts_with_non_ascii_tier1(self) -> None:
        result = _verify("""
public fn f(@String -> @Bool)
  requires(@String.0 == "été")
  ensures(@Bool.result == true)
  effects(pure)
{ string_starts_with(@String.0, "ét") }
""")
        assert _ok(result) and result.summary.tier3_runtime == 0

    def test_ends_with_non_ascii_tier1(self) -> None:
        result = _verify("""
public fn f(@String -> @Bool)
  requires(@String.0 == "café")
  ensures(@Bool.result == true)
  effects(pure)
{ string_ends_with(@String.0, "fé") }
""")
        assert _ok(result) and result.summary.tier3_runtime == 0

    def test_contains_non_ascii_tier1(self) -> None:
        result = _verify("""
public fn f(@String -> @Bool)
  requires(@String.0 == "café")
  ensures(@Bool.result == true)
  effects(pure)
{ string_contains(@String.0, "afé") }
""")
        assert _ok(result) and result.summary.tier3_runtime == 0


class TestAstralStringLiteral802:
    """Z3's string sort alphabet is U+0000..U+2FFFF.  Above that the Python
    binding's `z3.StringVal` silently stores the literal's *escape string*
    instead of the character, so a predicate over such a literal could prove a
    false contract (`string_contains("\\u{10FFFF}", "f")` — the astral char has
    no `f` byte, yet the phantom escape string does).  Such literals defer to
    Tier 3 (smt.py returns None for them), so the verifier never falsely proves
    over them.  `string_length` is unaffected — it byte-counts the decoded value,
    not `z3.StringVal` (covered in TestStringLengthSoundness802)."""

    def test_astral_literal_predicate_defers_to_tier3(self) -> None:
        # Pre-fix the verifier PROVED this false contract at Tier 1 (the phantom
        # escape string matched "f"); now the astral literal defers cleanly to a
        # runtime-guarded Tier-3 obligation.  (U+10FFFF as bytes f4 8f bf bf
        # contains no "f", so the runtime returns false — the contract is false,
        # and the verifier must NOT prove it.)
        result = _verify("""
public fn f(@Unit -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{ string_contains("\\u{10FFFF}", "f") }
""")
        # Verification succeeds with no spurious error, no false Tier-1 proof:
        # the astral predicate is a runtime-guarded Tier-3 obligation (pre-fix it
        # was a Tier-1 proof, so tier3_runtime was 0).
        assert _ok(result), [d.description for d in result.diagnostics]
        assert result.summary.tier3_runtime >= 1, (
            result.summary.tier1_verified, result.summary.tier3_runtime,
        )

    def test_astral_cutoff_boundary(self) -> None:
        # Pin the exact `ord(ch) > 0x2FFFF` cutoff (guards against a `>=`
        # regression): U+2FFFF is on the modeled side — a predicate over it stays
        # Tier 1 (tier3 == 0); U+30000, one above, defers (tier3 >= 1).  Uses a
        # predicate, not string_length, because string_length byte-counts via
        # Python and so does not exercise the z3.StringVal alphabet cutoff.
        #
        # Literal-on-literal with requires(true) so the *single* ensures
        # obligation is driven solely by the body predicate's astral literal.
        # A slot-arg requires(@String.0 == "\u{30000}") form adds a second
        # tier3 obligation (the astral requires literal also defers), so
        # `tier3 >= 1` there would still pass if only the requires deferred and
        # the body predicate regressed to Tier 1 — masking the soundness-
        # critical path.  Pinning one obligation removes that ambiguity.
        modeled = _verify("""
public fn f(@Unit -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{ string_starts_with("\\u{2FFFF}", "\\u{2FFFF}") }
""")
        assert _ok(modeled) and modeled.summary.tier3_runtime == 0, (
            modeled.summary.tier1_verified, modeled.summary.tier3_runtime,
        )
        deferred = _verify("""
public fn f(@Unit -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{ string_starts_with("\\u{30000}", "\\u{30000}") }
""")
        assert _ok(deferred), [d.description for d in deferred.diagnostics]
        assert deferred.summary.tier3_runtime >= 1, (
            deferred.summary.tier1_verified, deferred.summary.tier3_runtime,
        )

    def test_surrogate_literal_does_not_crash(self) -> None:
        # A lone surrogate (U+D800) is not UTF-8-encodable, so string_length's
        # `value.encode("utf-8")` raised UnicodeEncodeError and crashed
        # `vera verify` before the guard.  (The predicate's `z3.StringVal` does
        # not raise — it stores phantom escape text like the astral case — but is
        # guarded the same way.)  Both must now defer to Tier 3 without crashing.
        length = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ string_length("\\u{D800}") }
""")
        # Graceful Tier-3 fallback, not a crash and not an E500/checker error.
        assert _ok(length), [d.description for d in length.diagnostics]
        assert length.summary.tier3_runtime >= 1
        predicate = _verify("""
public fn f(@Unit -> @Bool)
  requires(true) ensures(@Bool.result == true) effects(pure)
{ string_contains("\\u{D800}", "x") }
""")
        assert _ok(predicate), [d.description for d in predicate.diagnostics]
        assert predicate.summary.tier3_runtime >= 1

    def test_astral_string_length_still_byte_modeled(self) -> None:
        # string_length bypasses z3.StringVal (it byte-counts the decoded value),
        # so even an astral literal's byte length is soundly Tier-1: U+10FFFF is
        # 4 UTF-8 bytes.
        ok = _verify("""
public fn f(@Unit -> @Int)
  requires(true) ensures(@Int.result == 4) effects(pure)
{ string_length("\\u{10FFFF}") }
""")
        assert _ok(ok) and ok.summary.tier1_verified >= 1
