"""Tests for vera.formatter — canonical code formatter."""

from __future__ import annotations

from typing import ClassVar

import os
from pathlib import Path
from textwrap import dedent

import pytest

from vera.formatter import (
    Formatter,
    _Attached,
    extract_comments,
    format_source,
)
from vera.parser import parse_to_ast
from tests import pipeline


EXAMPLES_DIR = Path(__file__).parent.parent / "examples"
EXAMPLE_FILES = sorted(
    f for f in os.listdir(EXAMPLES_DIR) if f.endswith(".vera")
)


# =====================================================================
# Helpers
# =====================================================================

def _fmt(source: str) -> str:
    """Format source and return the result."""
    return format_source(dedent(source).lstrip())


def _fmt_roundtrip(source: str) -> None:
    """Assert formatting is idempotent: fmt(fmt(x)) == fmt(x)."""
    first = _fmt(source)
    second = format_source(first)
    assert first == second, (
        f"Not idempotent.\nFirst pass:\n{first}\nSecond pass:\n{second}"
    )


def _fmt_check(source: str, expected: str) -> None:
    """Assert formatted output matches expected exactly."""
    result = _fmt(source)
    expected_clean = dedent(expected).lstrip()
    assert result == expected_clean, (
        f"Mismatch.\nGot:\n{result}\nExpected:\n{expected_clean}"
    )


# =====================================================================
# Comment extraction
# =====================================================================

_TRIVIAL_FN = """
public fn keep(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


def _line_with(text: str, needle: str) -> str:
    """The single output line containing `needle` (fails if 0 or >1)."""
    hits = [ln for ln in text.splitlines() if needle in ln]
    assert len(hits) == 1, f"expected exactly one line with {needle!r}, got {hits}"
    return hits[0]


class TestCommentExtraction:
    def test_line_comment(self) -> None:
        comments = extract_comments("-- hello\n")
        assert len(comments) == 1
        assert comments[0].kind == "line"
        assert comments[0].text == "-- hello"
        assert comments[0].line == 1
        assert comments[0].inline is False

    def test_inline_line_comment(self) -> None:
        comments = extract_comments("x + y -- add\n")
        assert len(comments) == 1
        assert comments[0].inline is True

    def test_block_comment(self) -> None:
        comments = extract_comments("{- block -}\n")
        assert len(comments) == 1
        assert comments[0].kind == "block"
        assert comments[0].text == "{- block -}"

    def test_nested_block_comment(self) -> None:
        comments = extract_comments("{- outer {- inner -} outer -}\n")
        assert len(comments) == 1
        assert comments[0].text == "{- outer {- inner -} outer -}"

    def test_annotation_comment(self) -> None:
        comments = extract_comments("/* width */ x\n")
        assert len(comments) == 1
        assert comments[0].kind == "annotation"

    def test_no_comments(self) -> None:
        comments = extract_comments("fn foo() {}\n")
        assert len(comments) == 0

    def test_annotation_labels_survive_formatting(self) -> None:
        """`vera fmt` must not delete a binding's label (spec 1.3, #1112).

        Labels are emitted from the AST rather than from the comment
        stream: they are the one comment form the spec requires the AST
        to carry, and the line-keyed inline store could not hold two on
        one line anyway (#1123).
        """
        out = format_source(dedent("""\
            private fn add(@Int /* left */, @Int /* right */ -> @Int /* sum */)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
        """))
        # Exactly once, not merely present: the label is emitted from the
        # AST *and* visible to the inline-comment path, so a presence
        # assertion cannot tell correct emission from double emission.
        assert out.count("/* left */") == 1
        assert out.count("/* right */") == 1
        assert out.count("/* sum */") == 1
        # Each on its own slot, in order. The counts above survive any
        # permutation, and a permuted emission otherwise only shows up as
        # an idempotence failure (it oscillates on the second pass), which
        # reports the wrong problem.
        assert out.splitlines()[0] == (
            "private fn add(@Int /* left */, @Int /* right */ "
            "-> @Int /* sum */)"
        )

    def test_unlabelled_slot_does_not_shift_later_labels(self) -> None:
        """A None gap must hold its position through emission.

        `test_partially_labelled_params_keep_their_positions` pins this on
        the AST; this pins the *emitted* signature, which is a separate
        failure surface. Compacting the gaps away in `_fmt_signature`
        moves `/* right */` onto parameter 0 — a label naming the wrong
        slot, which is the mistake positional storage exists to prevent —
        and neither the AST tests nor idempotence catch it: unlike a
        permutation, a compaction reaches a fixed point on the second
        pass, so `fmt(fmt(x)) == fmt(x)` still holds.
        """
        out = format_source(dedent("""\
            private fn add(@Int, @Int /* right */ -> @Int /* sum */)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
        """))
        assert out.splitlines()[0] == (
            "private fn add(@Int, @Int /* right */ -> @Int /* sum */)"
        )

    def test_annotation_formatting_is_idempotent(self) -> None:
        """Formatting the formatted output must be a fixed point.

        Emitting labels re-introduces comments into the formatter's own
        input, so this is the check that they round-trip rather than
        accumulating or shifting slot on a second pass.
        """
        src = dedent("""\
            private fn area(@Int /* width */, @Int /* height */ -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 * @Int.1
            }
        """)
        once = format_source(src)
        twice = format_source(once)
        assert once == twice

    def test_inline_line_comment_survives_formatting(self) -> None:
        """`vera fmt` must not delete a trailing `--` comment (#1123)."""
        out = format_source(dedent("""\
            public fn add(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.1 + @Int.0 -- sum the operands
            }
        """))
        line = _line_with(out, "-- sum the operands")
        assert "@Int.1 + @Int.0" in line, (
            "must trail its own expression, not be swept to the backstop"
        )

    def test_inline_block_comment_survives_formatting(self) -> None:
        """The same for `{- -}`, which is equally inline-capable (#1123)."""
        out = format_source(dedent("""\
            public fn add(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.1 + @Int.0 {- sum the operands -}
            }
        """))
        line = _line_with(out, "{- sum the operands -}")
        assert "@Int.1 + @Int.0" in line

    def test_each_statement_keeps_its_own_inline_comment(self) -> None:
        """Two trailing comments must not collapse onto one statement.

        The old store was `dict[int, Comment]` keyed by line, so this is
        the shape that proves attachment is per-construct rather than
        per-line, and that neither comment overwrites the other.
        """
        out = format_source(dedent("""\
            public fn add(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = @Int.1 + @Int.0; -- first the sum
              @Int.0 * 2 -- then double it
            }
        """))
        # Each must trail its own statement — checking presence alone
        # would pass even if both were swept to the declaration backstop.
        assert "let" in _line_with(out, "-- first the sum")
        assert "@Int.0 * 2" in _line_with(out, "-- then double it")

    def test_inline_comment_formatting_is_idempotent(self) -> None:
        """Re-emitting inline comments must reach a fixed point.

        Emission puts the comment back into the formatter's own input, so
        this is what proves it lands somewhere stable rather than drifting
        one construct outward on every pass.
        """
        src = dedent("""\
            public fn add(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.1 + @Int.0 -- sum the operands
            }
        """)
        once = format_source(src)
        twice = format_source(once)
        assert once == twice

    def test_inline_comment_in_declaration_header_survives(self) -> None:
        """Signature, contract and effects trailers are outside any statement.

        The block-body hook cannot reach them, so each needs its own claim
        point; without them all three are swept to the declaration
        backstop and land on the closing brace instead of trailing the
        construct they belong to.  Nothing is deleted, which is why this
        test asserts placement rather than presence.
        """
        out = format_source(dedent("""\
            public fn f(@Int -> @Int) -- on the signature
              requires(true) -- on the contract
              ensures(true)
              effects(pure) -- on the effects
            {
              @Int.0
            }
        """))
        assert "fn f(" in _line_with(out, "-- on the signature")
        assert "requires(" in _line_with(out, "-- on the contract")
        assert "effects(" in _line_with(out, "-- on the effects")

    def test_inline_comment_inside_nested_block_survives(self) -> None:
        """A comment in an if-branch belongs to the branch, not the function.

        Inner constructs are emitted first and claim greedily, so this is
        what pins "innermost wins" rather than everything collecting at the
        end of the enclosing declaration.
        """
        out = format_source(dedent("""\
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              if @Int.0 >= 0 then {
                1 -- the positive case
              } else {
                0
              }
            }
        """))
        assert _line_with(out, "-- the positive case").strip().startswith("1")

    def test_comment_on_a_brace_line_is_not_dropped(self) -> None:
        """The declaration backstop, which is the only thing covering this.

        A comment on the opening brace sits inside the function but inside
        no statement, contract, effects clause or signature, so every
        precise hook misses it. It is relocated to the end of the
        declaration rather than deleted: moving a comment is recoverable,
        deleting one is not.
        """
        out = format_source(dedent("""\
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            { -- brace trailer
              @Int.0
            }
        """))
        assert "-- brace trailer" in out

    def test_multiline_inline_comment_stays_on_one_line(self) -> None:
        """A claimed comment must not inject raw newlines into a line.

        `{- -}` may span lines while still being inline. Appending its text
        verbatim to an emitted line puts the continuation into the same
        `_lines` entry carrying its *original* source indentation, which
        survives the final join as a physically misindented line — against
        spec 1.8 rule 1 (2 spaces per level).
        """
        out = format_source(dedent("""\
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + 1 {- this comment
                 spans two lines -}
            }
        """))
        assert "this comment" in out and "spans two lines" in out
        # Whole comment on the code's line, and every line canonically indented.
        line = _line_with(out, "this comment")
        assert "spans two lines" in line
        assert "@Int.0 + 1" in line
        for ln in out.splitlines():
            indent = len(ln) - len(ln.lstrip())
            assert indent % 2 == 0, f"non-canonical indent {indent}: {ln!r}"

    def test_annotation_outside_the_parens_is_not_a_binding_label(self) -> None:
        """Only a comment inside the signature's parens labels a binding.

        Spec 1.3 makes an annotation elsewhere an ordinary comment. The
        return slot's label search is bounded by the first contract, so a
        comment after the closing paren would otherwise be adopted as the
        return label and re-emitted *inside* the parens — turning a
        trailing remark into a claim about the return value.
        """
        src = dedent("""\
            public fn f(@Int -> @Int) /* not a label */
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """)
        fn = parse_to_ast(src).declarations[0].decl
        assert fn.return_annotation is None
        out = format_source(src)
        # Preserved, but left outside the signature: after the closing
        # paren as an ordinary trailing comment, not inside it as a label.
        line = _line_with(out, "not a label")
        assert line.rstrip().endswith("/* not a label */")
        assert "@Int)" in line
        assert "@Int /* not a label */" not in line

    def test_unconsumed_annotation_in_parens_is_kept(self) -> None:
        """An in-paren annotation that labels nothing is still a comment.

        The label walk takes the first annotation *after* each slot, so a
        leading one — and a second one behind an already-labelled slot —
        is consumed by nobody. Retiring every in-paren annotation would
        delete exactly those, which is the defect this PR exists to fix.
        """
        out = format_source(dedent("""\
            public fn f(/* lead */ @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """))
        assert "/* lead */" in out

        out2 = format_source(dedent("""\
            public fn f(@Int /* label */ /* extra */ -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """))
        assert "/* label */" in out2, "the consumed label must still emit"
        assert "/* extra */" in out2, "the unconsumed one must not be dropped"

    def test_same_line_statements_keep_their_own_comments(self) -> None:
        """Claiming by line alone gives every same-line comment to the first.

        Two statements may share a source line, so a line-granular claim
        hands both trailing comments to whichever is emitted first. The
        claim has to compare full (line, column) positions and stop at the
        next statement's start.
        """
        out = format_source(dedent("""\
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = 1; {- first -} let @Int = 2; {- second -}
              @Int.0
            }
        """))
        assert "= 1;" in _line_with(out, "{- first -}")
        assert "= 2;" in _line_with(out, "{- second -}")

    @pytest.mark.parametrize("src,marker,anchor", [
        ("private data Color {\n  Red,  -- warm\n  Green\n}\n",
         "-- warm", "Red"),
        ("effect Log {\n  op write(String -> Unit);  -- writes\n}\n",
         "-- writes", "op write"),
        ("ability Show<T> {\n  op show(T -> String);  -- renders\n}\n",
         "-- renders", "op show"),
        ("type Row = Array<Bool>;  -- the row\n",
         "-- the row", "type Row"),
        ("module demo;  -- the entry point\n",
         "-- the entry point", "module demo"),
        ("module demo;\nimport other;  -- pulled in\n",
         "-- pulled in", "import other"),
    ])
    def test_non_fn_declarations_keep_their_comments(
        self, src: str, marker: str, anchor: str,
    ) -> None:
        """Every declaration form, not just `fn` (#1123).

        The claim points and the backstop all began life inside
        `_emit_fn_decl`, so `data`, `effect`, `ability`, `type`, `module`
        and `import` had none and dropped trailing comments outright —
        while the CHANGELOG and spec 1.8 rule 11 claimed otherwise. Found
        by review, because every earlier test used a function.

        Asserting the anchor, not just presence: the declaration backstop
        would otherwise satisfy a presence check by sweeping the comment
        to the end of the declaration, leaving the per-item claim points
        untested. That is exactly how the gap survived the first time.
        """
        out = format_source(src + _TRIVIAL_FN)
        assert anchor in _line_with(out, marker)
        assert format_source(out) == out, "must reach a fixed point"

    def test_line_comment_does_not_swallow_the_next_comment(self) -> None:
        """A `--` runs to EOL, so nothing may be appended after one.

        Claimed comments are joined onto one physical line; putting a
        second comment after a `--` folds it into that comment's text, so
        four comments re-read as one and the attribution is unrecoverable.
        At most one line comment per physical line, and it must be last.
        """
        out = format_source(dedent("""\
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {  -- open brace
              @Int.0
            }  -- close brace
        """))
        # Both survive as *separate* comments, so a re-scan still sees two.
        assert len(extract_comments(out)) == 2
        assert format_source(out) == out

    def test_multiline_annotation_label_stays_on_one_line(self) -> None:
        """The AST-driven label path needs the same collapse as claiming.

        `_claim_inline_range` flattens a multi-line comment; the label
        emitted from `param_annotations` went through `_annotation_suffix`
        instead, which spliced the raw text and left the continuation
        carrying its original source indentation.
        """
        out = format_source(dedent("""\
            public fn f(@Int /* the number
               to double */ -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """))
        assert "the number to double" in out
        for line in out.splitlines():
            indent = len(line) - len(line.lstrip())
            assert indent % 2 == 0, f"non-canonical indent: {line!r}"

    def test_each_match_arm_keeps_its_own_comment(self) -> None:
        """An arm comment belongs to its arm, not the match's closing brace.

        A match arm is not a `Block`, so `_emit_block_body`'s claim never
        reaches it and every arm comment fell to the declaration backstop.
        Placement is the only thing that catches this: the comments still
        survive and the result is still idempotent when they are all piled
        onto the closing brace, so neither invariant in
        `TestCommentInvariants` can see it.
        """
        out = format_source(dedent("""\
            public fn f(@Int -> @String)
              requires(true)
              ensures(true)
              effects(pure)
            {
              match @Int.0 {
                0 -> "zero",  -- the zero case
                _ -> "other"  -- everything else
              }
            }
        """))
        assert '"zero"' in _line_with(out, "-- the zero case")
        assert '"other"' in _line_with(out, "-- everything else")

    def test_annotation_label_is_not_emitted_twice(self) -> None:
        """A binding label comes from the AST, so the inline path must skip it.

        Both mechanisms can see the same `/* */`: the signature emitter
        renders it from `param_annotations`, and it is also an inline
        comment by position. Claiming it in both places prints it twice.
        """
        out = format_source(dedent("""\
            private fn area(@Int /* width */, @Int /* height */ -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 * @Int.1
            }
        """))
        assert out.count("/* width */") == 1
        assert out.count("/* height */") == 1

    def test_own_line_comments_are_unaffected(self) -> None:
        """The guard: own-line comments already worked and must keep working."""
        out = format_source(dedent("""\
            -- header comment
            public fn add(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              -- explain the sum
              @Int.1 + @Int.0
            }
        """))
        assert "-- header comment" in out
        assert "-- explain the sum" in out
        # Still on its own line, not folded onto the expression.
        explain = next(ln for ln in out.splitlines() if "explain the sum" in ln)
        assert explain.strip() == "-- explain the sum"

    def test_unlabelled_signature_gains_no_annotation(self) -> None:
        """The negative direction — no label must mean no emitted `/* */`."""
        out = format_source(dedent("""\
            private fn add(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
        """))
        assert "/*" not in out

    def test_comments_inside_string_ignored(self) -> None:
        comments = extract_comments('"-- not a comment"\n')
        assert len(comments) == 0

    def test_multiple_comments(self) -> None:
        src = "-- first\n-- second\n"
        comments = extract_comments(src)
        assert len(comments) == 2


# =====================================================================
# Expression formatting
# =====================================================================

class TestFormatExpressions:
    def test_integer_literal(self) -> None:
        _fmt_check(
            """
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              42
            }
            """,
            """
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              42
            }
            """,
        )

    def test_binary_operators(self) -> None:
        _fmt_check(
            """
            public fn f(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
            """,
            """
            public fn f(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
            """,
        )

    def test_slot_ref_with_type_args(self) -> None:
        src = _fmt("""
            private data Option<T> { None, Some(T) }

            public fn f(@Option<Int> -> @Bool)
              requires(true)
              ensures(true)
              effects(pure)
            {
              match @Option<Int>.0 {
                None -> false,
                Some(@Int) -> true
              }
            }
        """)
        assert "@Option<Int>.0" in src

    def test_unary_neg(self) -> None:
        src = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              -@Int.0
            }
        """)
        assert "-@Int.0" in src

    def test_array_literal(self) -> None:
        src = _fmt("""
            public fn f(-> @Array<Int>)
              requires(true)
              ensures(true)
              effects(pure)
            {
              [1, 2, 3]
            }
        """)
        assert "[1, 2, 3]" in src


# =====================================================================
# Declaration formatting
# =====================================================================

class TestFormatDeclarations:
    def test_simple_function(self) -> None:
        _fmt_roundtrip("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """)

    def test_forall_function(self) -> None:
        src = _fmt("""
            private forall<T> fn identity(@T -> @T)
              requires(true)
              ensures(@T.result == @T.0)
              effects(pure)
            {
              @T.0
            }
        """)
        assert "private forall<T> fn identity" in src

    def test_data_declaration(self) -> None:
        _fmt_check(
            """
            private data Option<T> {
              -- no value
              None,
              -- one value
              Some(T)
            }
            """,
            """
            private data Option<T> {
              -- no value
              None,
              -- one value
              Some(T)
            }
            """,
        )

    def test_type_alias(self) -> None:
        src = _fmt("""
            type IntToInt = fn(Int -> Int) effects(pure);
        """)
        assert "type IntToInt = fn(Int -> Int) effects(pure);" in src

    def test_refinement_type_alias(self) -> None:
        src = _fmt("""
            type PosInt = { @Int | @Int.0 > 0 };
        """)
        assert "type PosInt = { @Int | @Int.0 > 0 };" in src

    def test_effect_declaration(self) -> None:
        _fmt_check(
            """
            effect Counter {
              -- read the counter
              op get_count(Unit -> Int);
              -- update the counter
              op increment(Unit -> Unit);
            }
            """,
            """
            effect Counter {
              -- read the counter
              op get_count(Unit -> Int);
              -- update the counter
              op increment(Unit -> Unit);
            }
            """,
        )

    def test_effect_declaration_single_line_expands(self) -> None:
        # A one-line `effect X { op ...; }` must expand to the canonical
        # multi-line form.  Previously covered incidentally by the `effect IO`
        # preambles of the match-arm fixtures, which #1149 removed (the block
        # is now E152), so the expansion is pinned directly here.
        _fmt_check(
            """
            effect Counter { op increment(Unit -> Unit); }
            """,
            """
            effect Counter {
              op increment(Unit -> Unit);
            }
            """,
        )

    def test_ability_declaration(self) -> None:
        _fmt_check(
            """
            ability Eq<T> {
              -- compare values
              op eq(T, T -> Bool);
            }
            """,
            """
            ability Eq<T> {
              -- compare values
              op eq(T, T -> Bool);
            }
            """,
        )

    def test_ability_multiple_ops(self) -> None:
        _fmt_check(
            """
            ability Ord<T> {
              op lt(T, T -> Bool);
              op le(T, T -> Bool);
            }
            """,
            """
            ability Ord<T> {
              op lt(T, T -> Bool);
              op le(T, T -> Bool);
            }
            """,
        )

    def test_forall_with_constraint(self) -> None:
        _fmt_check(
            """
            private forall<T where Eq<T>> fn contains(@Array<T>, @T -> @Bool)
              requires(true)
              ensures(true)
              effects(pure)
            {
              true
            }
            """,
            """
            private forall<T where Eq<T>> fn contains(@Array<T>, @T -> @Bool)
              requires(true)
              ensures(true)
              effects(pure)
            {
              true
            }
            """,
        )

    def test_forall_with_multiple_constraints(self) -> None:
        _fmt_check(
            """
            private forall<T where Eq<T>, Ord<T>> fn sorted(@Array<T> -> @Array<T>)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Array<T>.0
            }
            """,
            """
            private forall<T where Eq<T>, Ord<T>> fn sorted(@Array<T> -> @Array<T>)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Array<T>.0
            }
            """,
        )

    def test_ability_roundtrip(self) -> None:
        _fmt_roundtrip("""
            ability Eq<T> {
              op eq(T, T -> Bool);
            }

            private forall<T where Eq<T>> fn contains(@Array<T>, @T -> @Bool)
              requires(true)
              ensures(true)
              effects(pure)
            {
              true
            }
        """)

    def test_where_block(self) -> None:
        src = _fmt("""
            public fn is_even(@Nat -> @Bool)
              requires(true)
              ensures(true)
              decreases(@Nat.0)
              effects(pure)
            {
              if @Nat.0 == 0 then {
                true
              } else {
                is_odd(@Nat.0 - 1)
              }
            }
            where {
              fn is_odd(@Nat -> @Bool)
                requires(true)
                ensures(true)
                decreases(@Nat.0)
                effects(pure)
              {
                if @Nat.0 == 0 then {
                  false
                } else {
                  is_even(@Nat.0 - 1)
                }
              }
            }
        """)
        # Where-block functions have no visibility prefix
        assert "  fn is_odd" in src
        assert "private fn is_odd" not in src


# =====================================================================
# Program formatting
# =====================================================================

class TestFormatProgram:
    def test_blank_lines_between_decls(self) -> None:
        src = _fmt("""
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              1
            }

            public fn g(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              2
            }
        """)
        # Should have exactly one blank line between declarations
        assert "\n\npublic fn g" in src

    def test_module_and_imports(self) -> None:
        src = _fmt("""
            module vera.example;

            import vera.math(abs, max);

            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              vera.math::abs(-1)
            }
        """)
        assert src.startswith("module vera.example;\n")
        assert "import vera.math(abs, max);" in src


# =====================================================================
# Formatting rules (Spec Section 1.8)
# =====================================================================

class TestFormatRules:
    def test_rule_1_indentation(self) -> None:
        """Rule 1: 2 spaces per level, no tabs."""
        src = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """)
        assert "\t" not in src
        # Contract lines indented 2 spaces
        for line in src.split("\n"):
            if line.startswith("  requires") or line.startswith("  ensures"):
                assert line.startswith("  ")
                assert not line.startswith("    ")

    def test_rule_3_commas(self) -> None:
        """Rule 3: commas followed by single space."""
        src = _fmt("""
            public fn f(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
        """)
        assert "@Int, @Int" in src

    def test_rule_4_operators(self) -> None:
        """Rule 4: operators surrounded by single spaces."""
        src = _fmt("""
            public fn f(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
        """)
        assert "@Int.0 + @Int.1" in src

    def test_rule_5_semicolons(self) -> None:
        """Rule 5: no space before semicolon, newline after."""
        src = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = @Int.0 + 1;
              @Int.0
            }
        """)
        assert "let @Int = @Int.0 + 1;" in src

    def test_rule_6_parentheses(self) -> None:
        """Rule 6: no space inside parentheses."""
        src = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              f(@Int.0)
            }
        """)
        assert "f(@Int.0)" in src

    def test_rule_9_no_trailing_whitespace(self) -> None:
        """Rule 9: no trailing whitespace on any line."""
        src = _fmt("""
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              42
            }
        """)
        for line in src.split("\n"):
            assert line == line.rstrip(), f"Trailing whitespace: {line!r}"

    def test_rule_10_single_trailing_newline(self) -> None:
        """Rule 10: file ends with a single newline."""
        src = _fmt("""
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              42
            }
        """)
        assert src.endswith("\n")
        assert not src.endswith("\n\n")


# =====================================================================
# Comment preservation
# =====================================================================

class TestCommentPreservation:
    def test_comment_before_function(self) -> None:
        src = _fmt("""
            -- A comment
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              42
            }
        """)
        assert "-- A comment" in src

    def test_comment_between_functions(self) -> None:
        src = _fmt("""
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              1
            }

            -- Second function
            public fn g(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              2
            }
        """)
        assert "-- Second function" in src


# =====================================================================
# Parenthesization
# =====================================================================

class TestParenthesization:
    def test_precedence_preserved(self) -> None:
        """Lower precedence child of higher precedence parent gets parens."""
        src = _fmt("""
            public fn f(@Int, @Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              (@Int.0 + @Int.1) * @Int.2
            }
        """)
        assert "(@Int.0 + @Int.1) * @Int.2" in src

    def test_no_unnecessary_parens(self) -> None:
        """Higher precedence child of lower precedence parent: no parens."""
        src = _fmt("""
            public fn f(@Int, @Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1 * @Int.2
            }
        """)
        assert "@Int.0 + @Int.1 * @Int.2" in src

    def test_right_child_of_left_assoc(self) -> None:
        """Right child at same prec of left-assoc op gets parens: a - (b - c)."""
        src = _fmt("""
            public fn f(@Int, @Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 - (@Int.1 - @Int.2)
            }
        """)
        assert "@Int.0 - (@Int.1 - @Int.2)" in src


# =====================================================================
# Match arm block bodies (#274)
# =====================================================================

class TestMatchBlockArms:
    """Formatter must preserve braces on multi-statement match arm blocks."""

    def test_match_arm_block_body_multiline(self) -> None:
        """Block arm body with statements emits multi-line with braces."""
        _fmt_check(
            """
            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  IO.print("zero");
                  IO.print("done")
                },
                _ -> IO.print("other")
              }
            }
            """,
            """
            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  IO.print("zero");
                  IO.print("done")
                },
                _ -> IO.print("other")
              }
            }
            """,
        )

    def test_match_arm_block_body_idempotent(self) -> None:
        """Formatting a match with block arms twice gives identical output."""
        _fmt_roundtrip("""
            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  IO.print("hello");
                  IO.print("world")
                },
                _ -> IO.print("other")
              }
            }
        """)

    def test_match_arm_block_body_roundtrip_parses(self) -> None:
        """Formatted output with block arms must parse without error."""
        from vera.parser import parse as vera_parse
        from vera.transform import transform

        src = _fmt("""
            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  IO.print("hello");
                  IO.print("world")
                },
                _ -> IO.print("other")
              }
            }
        """)
        tree = vera_parse(src)
        transform(tree)  # Should not raise

    def test_match_arm_mixed_simple_and_block(self) -> None:
        """Mix of simple and block arms: simple stays inline, block expands."""
        src = _fmt("""
            private data Maybe { Nothing, Just(Int) }

            public fn f(@Maybe -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Maybe.0 {
                Nothing -> IO.print("none"),
                Just(@Int) -> {
                  IO.print("got:");
                  IO.print(int_to_string(@Int.0))
                }
              }
            }
        """)
        assert "Nothing -> IO.print(\"none\")," in src
        assert "Just(@Int) -> {" in src
        assert '  IO.print("got:");' in src
        assert "  IO.print(int_to_string(@Int.0))" in src

    def test_match_arm_block_trailing_comma(self) -> None:
        """Non-final block arm gets comma after closing brace."""
        src = _fmt("""
            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  IO.print("a");
                  IO.print("b")
                },
                _ -> IO.print("c")
              }
            }
        """)
        assert "},\n" in src

    def test_match_arm_block_no_trailing_comma_final(self) -> None:
        """Final block arm has no comma after closing brace."""
        src = _fmt("""
            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> IO.print("a"),
                _ -> {
                  IO.print("b");
                  IO.print("c")
                }
              }
            }
        """)
        # Final arm: closing brace without comma
        lines = src.strip().splitlines()
        # Find the closing brace of the block arm
        block_close = [line for line in lines if line.strip() == "}"]
        assert len(block_close) >= 1  # at least one bare }

    def test_match_arm_block_in_let_binding_context(self) -> None:
        """A match bound by a `let` keeps its arm block multi-line.

        This used to assert the inline form
        (`{ let @Int = 10; @Int.0 + 1 }` on one line, under the name
        `test_match_arm_block_inline_context`), pinning a `let` value
        as the one position where rule 2 did not apply.  That made the
        canonical shape of a construct depend on where it sat, which is
        the "no equivalent alternatives" rule DESIGN.md principle 3
        rules out.  Rule 2 now holds in value position too, so the
        binding expands exactly as statement position does and the
        trailing `;` rides the closing brace.
        """
        src = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = match @Int.0 { 0 -> { let @Int = 10; @Int.0 + 1 }, _ -> 0 };
              @Int.0
            }
        """)
        lines = src.splitlines()
        assert lines[lines.index("{") + 1:-1] == [
            "  let @Int = match @Int.0 {",
            "    0 -> {",
            "      let @Int = 10;",
            "      @Int.0 + 1",
            "    },",
            "    _ -> 0",
            "  };",
            "  @Int.0",
        ], src
        assert format_source(src) == src, "second pass differs"

    def test_match_arm_block_in_exprstmt(self) -> None:
        """A match in statement position keeps its arm block multi-line.

        This used to assert the inline form
        (`{ IO.print("a"); IO.print("b") }` on one line), which put a
        match's braces on a single line against rule 2 and two
        statements on one line against rule 8.  Statement position now
        gets the same treatment as result position; the trailing `;`
        rides the closing brace.
        """
        src = _fmt("""
            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 { 0 -> { IO.print("a"); IO.print("b") }, _ -> IO.print("c") };
              IO.print("done")
            }
        """)
        assert src.splitlines()[-9:-1] == [
            "  match @Int.0 {",
            "    0 -> {",
            '      IO.print("a");',
            '      IO.print("b")',
            "    },",
            '    _ -> IO.print("c")',
            "  };",
            '  IO.print("done")',
        ], src
        parse_to_ast(src)
        # The suffix-bearing layout must also be a fixed point:
        # the `;` rides the closing brace, and re-emitting it is
        # where a dropped or doubled suffix would show up.
        assert format_source(src) == src, "second pass differs"


# =====================================================================
# Interior comment positioning (#274)
# =====================================================================

class TestInteriorComments:
    """Comments inside function bodies must stay in position, not move to footer."""

    def test_comment_before_statement(self) -> None:
        """A comment before a let statement stays before it."""
        _fmt_check(
            """
            public fn main(@Unit -> @Unit)
              requires(true) ensures(true) effects(<IO>)
            {
              -- set up the value
              let @Int = 42;
              IO.print(int_to_string(@Int.0))
            }
            """,
            """
            public fn main(@Unit -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              -- set up the value
              let @Int = 42;
              IO.print(int_to_string(@Int.0))
            }
            """,
        )

    def test_comment_before_result_expr(self) -> None:
        """A comment before the result expression stays before it."""
        _fmt_check(
            """
            public fn main(@Unit -> @Unit)
              requires(true) ensures(true) effects(<IO>)
            {
              let @Int = 42;
              -- now print it
              IO.print(int_to_string(@Int.0))
            }
            """,
            """
            public fn main(@Unit -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              let @Int = 42;
              -- now print it
              IO.print(int_to_string(@Int.0))
            }
            """,
        )

    def test_multiple_interior_comments(self) -> None:
        """Multiple comments inside a body each stay before their statement."""
        _fmt_check(
            """
            public fn main(@Unit -> @Unit)
              requires(true) ensures(true) effects(<IO>)
            {
              -- first
              let @Int = 1;
              -- second
              let @Int = 2;
              -- result
              IO.print(int_to_string(@Int.0))
            }
            """,
            """
            public fn main(@Unit -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              -- first
              let @Int = 1;
              -- second
              let @Int = 2;
              -- result
              IO.print(int_to_string(@Int.0))
            }
            """,
        )

    def test_comment_inside_match_arm_block(self) -> None:
        """Comments inside a match arm block body stay in position."""
        _fmt_check(
            """
            public fn f(@Int -> @Unit)
              requires(true) ensures(true) effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  -- zero case
                  let @String = "zero";
                  IO.print(@String.0)
                },
                _ -> IO.print("other")
              }
            }
            """,
            """
            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  -- zero case
                  let @String = "zero";
                  IO.print(@String.0)
                },
                _ -> IO.print("other")
              }
            }
            """,
        )

    def test_comment_not_moved_to_footer(self) -> None:
        """Interior comments must NOT appear after the closing brace."""
        src = _fmt("""
            public fn main(@Unit -> @Unit)
              requires(true) ensures(true) effects(<IO>)
            {
              -- this stays inside
              let @Int = 42;
              IO.print(int_to_string(@Int.0))
            }
        """)
        # The comment must appear before the let, not after the closing }
        lines = src.strip().splitlines()
        closing_brace_idx = None
        for i, line in enumerate(lines):
            if line.strip() == "}":
                closing_brace_idx = i
        assert closing_brace_idx is not None
        # Nothing after closing brace except empty lines
        after = [line for line in lines[closing_brace_idx + 1:] if line.strip()]
        assert not after, f"Comment leaked to footer: {after}"
        # Comment is inside the body
        assert "-- this stays inside" in src
        body_start = src.index("{", src.index("effects"))
        body_end = src.rindex("}")
        comment_pos = src.index("-- this stays inside")
        assert body_start < comment_pos < body_end

    def test_interior_comment_idempotent(self) -> None:
        """Formatting a program with interior comments is idempotent."""
        _fmt_roundtrip("""
            public fn main(@Unit -> @Unit)
              requires(true) ensures(true) effects(<IO>)
            {
              -- first comment
              let @Int = 1;
              -- second comment
              let @Int = 2;
              -- before result
              IO.print(int_to_string(@Int.0))
            }
        """)

    def test_if_branch_interior_comment(self) -> None:
        """Comments inside if/else branch blocks stay in position."""
        _fmt_check(
            """
            public fn f(@Bool -> @Unit)
              requires(true) ensures(true) effects(<IO>)
            {
              if @Bool.0 then {
                -- true branch
                IO.print("yes")
              } else {
                -- false branch
                IO.print("no")
              }
            }
            """,
            """
            public fn f(@Bool -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              if @Bool.0 then {
                -- true branch
                IO.print("yes")
              } else {
                -- false branch
                IO.print("no")
              }
            }
            """,
        )


# =====================================================================
# Idempotency — all examples
# =====================================================================

class TestIdempotency:
    @pytest.mark.parametrize("name", EXAMPLE_FILES)
    def test_example_idempotent(self, name: str) -> None:
        """Formatting the formatted output should produce identical output."""
        path = EXAMPLES_DIR / name
        source = path.read_text(encoding="utf-8")
        first = format_source(source, file=str(path))
        second = format_source(first)
        assert first == second, f"{name} is not idempotent"

    @pytest.mark.parametrize("name", EXAMPLE_FILES)
    def test_formatted_still_parses(self, name: str) -> None:
        """Formatted output should still parse and transform without errors."""
        from vera.parser import parse as vera_parse
        from vera.transform import transform

        path = EXAMPLES_DIR / name
        source = path.read_text(encoding="utf-8")
        formatted = format_source(source, file=str(path))
        tree = vera_parse(formatted)
        transform(tree)  # Should not raise


class TestCorpusCommentPreservation:
    """No corpus file may lose a comment when formatted.

    The whole of #1123 survived because the corpus contains no inline
    comments to lose and nothing format-checks it, so a regression that
    deleted every inline comment in the language passed the full gate.
    These two tests close that: the sweep guards real files as soon as any
    gains a comment, and the fixture gives it something to bite on today.
    """

    ALL_SOURCES = sorted(
        [*(Path(__file__).parent.parent / "examples").rglob("*.vera"),
         *(Path(__file__).parent / "conformance").glob("*.vera")],
    )

    @pytest.mark.parametrize(
        "path", ALL_SOURCES, ids=lambda p: p.name,
    )
    def test_formatting_preserves_every_comment(self, path: Path) -> None:
        src = path.read_text(encoding="utf-8")
        before = len(extract_comments(src))
        after = len(extract_comments(format_source(src)))
        assert after == before, f"{path.name}: {before} -> {after} comments"

    def test_comments_in_every_position_survive(self) -> None:
        """One fixture carrying a comment in each construct the emitter has.

        Deliberately not a `.vera` corpus file: `vera fmt` is not run over
        the corpus by any gate, so a fixture there would guard nothing.
        """
        src = dedent("""            module demo;  -- the module
            import other;  -- the import

            type Row = Array<Bool>;  -- the alias

            private data Color {
              Red,  -- warm
              Green  -- cool
            }

            effect Log {
              op write(String -> Unit);  -- the op
            }

            public fn f(@Int -> @Int)  -- the signature
              requires(true)  -- the precondition
              ensures(true)
              effects(pure)  -- the effects
            {
              @Int.0 + 1  -- the body
            }
        """)
        out = format_source(src)
        for marker in (
            "-- the module", "-- the import", "-- the alias",
            "-- warm", "-- cool", "-- the op", "-- the signature",
            "-- the precondition", "-- the effects", "-- the body",
        ):
            assert marker in out, f"lost {marker!r}"
        assert len(extract_comments(out)) == len(extract_comments(src))
        assert format_source(out) == out


_COMMENT_SHAPES = {
    "trailing statement": "  @Int.0 + 1  -- trailing\n",
    "trailing block": "  @Int.0 + 1  {- trailing -}\n",
    "two on one statement": "  @Int.0 + 1  {- a -} -- b\n",
    "two statements one line": "  let @Int = 1; -- one\n  @Int.0 -- two\n",
    "own line": "  -- above\n  @Int.0\n",
    "multi-line block": "  @Int.0 {- spans\n     two lines -}\n",
    "brace trailers": None,          # supplied whole below
    "match arms": None,
    "if branches": None,
    "nested block": "  if @Int.0 > 0 then {\n    1  -- yes\n  } else {\n    0  -- no\n  }\n",
}

_WHOLE_FILE_SHAPES = {
    "brace trailers": """public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{  -- open
  @Int.0
}  -- close
""",
    "match arms": """public fn f(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    0 -> "zero",  -- zero
    _ -> "other"  -- other
  }
}
""",
    "if branches": """public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 >= 0 then {
    1  -- positive
  } else {
    0  -- negative
  }
}
""",
    "declaration forms": """module demo;  -- mod
import other;  -- imp

type Row = Array<Bool>;  -- alias

private data Color {
  Red,  -- warm
  Green  -- cool
}

effect Log {
  op write(String -> Unit);  -- op
}

public fn f(@Int -> @Int)  -- sig
  requires(true)  -- pre
  ensures(true)
  effects(pure)  -- eff
{
  @Int.0  -- body
}
""",
    "signature labels": """public fn area(@Int /* w */, @Int /* h */ -> @Int /* a */)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.1 * @Int.0
}
""",
}


def _wrap(body: str) -> str:
    return (
        "public fn f(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
        + body + "}\n"
    )


class TestCommentInvariants:
    """Two invariants over every comment shape, not a hand-picked few.

    Count-preservation and idempotence are the pair that catches this
    whole bug family. Every defect found in review was invisible to one
    of them alone: deletion and merging show up in the count, relocation
    and drift only in idempotence — and a comment that walks out of its
    function on each pass violates only the second.
    """

    ALL: ClassVar[dict[str, str]] = {
        **{k: _wrap(v) for k, v in _COMMENT_SHAPES.items() if v is not None},
        **_WHOLE_FILE_SHAPES,
    }

    @pytest.mark.parametrize("name", sorted(ALL))
    def test_no_comment_is_lost_or_merged(self, name: str) -> None:
        src = self.ALL[name]
        before = len(extract_comments(src))
        after = len(extract_comments(format_source(src)))
        assert after == before, f"{name}: {before} comments in, {after} out"

    @pytest.mark.parametrize("name", sorted(ALL))
    def test_formatting_reaches_a_fixed_point(self, name: str) -> None:
        once = format_source(self.ALL[name])
        assert format_source(once) == once, (
            f"{name}: not idempotent — a comment that moves on every pass "
            f"drifts out of the construct it documents"
        )


# =====================================================================
# Canonical-form gaps that blocked the corpus gate (#1124)
# =====================================================================

class TestCanonicalFormGaps:
    """The four defects that kept `examples/` off `vera fmt --check`.

    Every one is an *omission* rather than an error: the formatter
    emits something, the suite stays green, and only an assertion about
    where a construct ended up can tell the difference.  The corpus
    gate exists because that class cannot be caught by counting.
    """

    # -- F1 (#1136): leading-comment attachment ------------------------
    #
    # A comment is claimed by the innermost construct whose span
    # *contains* it, never bound to the construct that *follows* it.
    # Three positions have no anchor, so each one's comment falls
    # through to the enclosing declaration and is re-emitted elsewhere.

    def test_own_line_comment_stays_above_each_contract_clause(self) -> None:
        """All three clauses, including `ensures` between the others."""
        out = _fmt("""
            public fn demo(@Int -> @Int)
              -- before requires
              requires(true)
              -- before ensures
              ensures(true) -- after ensures
              -- before effects
              effects(pure)
            {
              @Int.0
            }
        """)
        assert out.splitlines() == [
            "public fn demo(@Int -> @Int)",
            "  -- before requires",
            "  requires(true)",
            "  -- before ensures",
            "  ensures(true)  -- after ensures",
            "  -- before effects",
            "  effects(pure)",
            "{",
            "  @Int.0",
            "}",
        ]

    def test_own_line_comment_stays_above_a_where_clause(self) -> None:
        """The `where` block is a construct a comment can precede."""
        out = _fmt("""
            public fn is_even(@Nat -> @Bool)
              requires(true)
              ensures(true)
              decreases(@Nat.0)
              effects(pure)
            {
              if @Nat.0 == 0 then {
                true
              } else {
                is_odd(@Nat.0 - 1)
              }
            }
            -- Trailing where for mutual recursion.
            where {
              fn is_odd(@Nat -> @Bool)
                requires(true)
                ensures(true)
                decreases(@Nat.0)
                effects(pure)
              {
                if @Nat.0 == 0 then {
                  false
                } else {
                  is_even(@Nat.0 - 1)
                }
              }
            }
        """)
        lines = out.splitlines()
        comment = "-- Trailing where for mutual recursion."
        idx = next(i for i, ln in enumerate(lines) if comment in ln)
        assert lines[idx] == comment, (
            f"comment must stay at column 0, got {lines[idx]!r}"
        )
        assert lines[idx + 1].startswith("where"), (
            f"comment must stay directly above `where`, got {lines[idx + 1]!r}"
        )

    def test_own_line_comment_stays_above_a_match_arm(self) -> None:
        """Arms are anchors too — a comment must not leave the match."""
        out = _fmt("""
            private data Colour {
              Red,
              Green
            }

            public fn rank(@Colour -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              match @Colour.0 {
                -- warm
                Red -> 1,
                -- cool
                Green -> 2
              }
            }
        """)
        lines = out.splitlines()
        for comment, arm in (("-- warm", "Red -> 1"), ("-- cool", "Green -> 2")):
            idx = next(i for i, ln in enumerate(lines) if comment in ln)
            assert lines[idx].strip() == comment
            assert lines[idx + 1].strip().startswith(arm), (
                f"{comment!r} must stay directly above {arm!r}, "
                f"got {lines[idx + 1]!r}"
            )

    # -- F2: nested match collapses, violating 1.8 rule 2 --------------

    def test_a_nested_match_keeps_its_closing_brace_on_its_own_line(
        self,
    ) -> None:
        """`{ match ... }` has empty `statements`, so it took the inline path.

        Rule 2 requires the closing brace on its own line aligned with
        the construct.  A top-level match already obeys it; a match
        reached through a block whose only content is a trailing
        expression did not.
        """
        out = _fmt("""
            public fn main(-> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match IO.write_file("a.txt", "x") {
                Ok(_) -> {
                  match IO.read_file("a.txt") {
                    Ok(@String) -> IO.print(@String.0),
                    Err(@String) -> IO.print(@String.0)
                  }
                },
                Err(@String) -> IO.print(@String.0)
              };

              ()
            }
        """)
        for line in out.splitlines():
            assert not ("{" in line and "}" in line and "match" in line), (
                f"rule 2: a match's braces must not share a line: {line!r}"
            )
        # And the nesting must survive as nesting, not one long line.
        assert max(len(ln) for ln in out.splitlines()) < 100, (
            f"collapsed to a long line:\n{out}"
        )
        # Layout assertions alone are satisfied by output that no
        # longer parses: moving the closing brace onto its own line
        # drops the arm's `,` and the statement's `;` with it unless
        # they are carried over too.
        parse_to_ast(out)
        assert format_source(out) == out, "second pass differs"

    def test_a_block_wrapped_match_statement_does_not_flatten(self) -> None:
        """`{ match ... };` reaches the same hole one level out.

        The multi-line branch keys on the expression being a
        match/if/handle, but a written block wrapper holds the match in
        `expr` with `statements` empty — so the branch saw a Block,
        declined, and the construct flattened exactly as it did before
        the fix.  Found in review of PR #1138; the arm path already
        unwrapped, the statement path did not.
        """
        out = _fmt("""
            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              { match @Int.0 { 0 -> IO.print("a"), _ -> IO.print("b") } };
              IO.print("done")
            }
        """)
        for line in out.splitlines():
            assert not ("{" in line and "}" in line and "match" in line), (
                f"rule 2: a match's braces must not share a line: {line!r}"
            )
        parse_to_ast(out)
        assert format_source(out) == out, "second pass differs"

    def test_blank_lines_between_repeated_own_line_items_survive(self) -> None:
        """Rule 13 covers any repeated own-line item, not just statements.

        Match arms already went through the arm anchor, but contract
        clauses, the effects row and handler clauses each emitted
        straight from their loop with no gap check, so an authored
        paragraph break between two clauses was dropped.  Raised in
        review of PR #1138.
        """
        out = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)

              ensures(true)

              effects(pure)
            {
              @Int.0
            }
        """)
        lines = out.splitlines()
        req = lines.index("  requires(true)")
        assert lines[req + 1] == "", f"gap above ensures lost:\n{out}"
        ens = lines.index("  ensures(true)")
        assert lines[ens + 1] == "", f"gap above effects lost:\n{out}"
        parse_to_ast(out)
        assert format_source(out) == out, "second pass differs"

    def test_blank_lines_between_arms_and_handler_clauses_survive(self) -> None:
        """The other two repeated own-line item kinds.

        Arms looked correct under a loose probe that searched the whole
        body for any blank — the one it found sat between the `data`
        declaration and the function.  Asserting the line *directly
        after* the first arm is what distinguishes them.
        """
        out = _fmt("""
            effect Counter {
              op get(Unit -> Int);
              op inc(Unit -> Unit);
            }

            private data C {
              R,
              G
            }

            public fn rank(@C -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              match @C.0 {
                R -> 1,

                G -> 2
              }
            }

            public fn counted(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              handle[Counter](@Int = 0) {
                get(@Unit) -> resume(@Int.0),

                inc(@Unit) -> resume(())
              } in {
                @Int.0
              }
            }
        """)
        lines = out.splitlines()

        def gap_after(needle: str) -> None:
            i = next(n for n, ln in enumerate(lines) if needle in ln)
            assert lines[i + 1] == "", (
                f"gap after {needle!r} lost:\n{out}"
            )

        gap_after("R -> 1,")
        gap_after("get(@Unit) ->")
        parse_to_ast(out)
        assert format_source(out) == out, "second pass differs"

    def test_own_line_comment_stays_above_a_handler_clause(self) -> None:
        """The fourth position with no anchor of its own (#1136).

        Handler clauses were never anchored, so both clause comments
        fell through to the declaration backstop and were re-emitted
        together below the whole `handle`, out of the clauses they
        document.
        """
        out = _fmt("""
            effect Counter {
              op get(Unit -> Int);
              op inc(Unit -> Unit);
            }

            public fn counted(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              handle[Counter](@Int = 0) {
                -- read the counter
                get(@Unit) -> resume(@Int.0),
                -- bump it
                inc(@Unit) -> resume(())
              } in {
                @Int.0
              }
            }
        """)
        lines = out.splitlines()
        for comment, clause in (
            ("-- read the counter", "get(@Unit) ->"),
            ("-- bump it", "inc(@Unit) ->"),
        ):
            i = next(n for n, ln in enumerate(lines) if comment in ln)
            assert clause in lines[i + 1], (
                f"{comment!r} must sit directly above {clause!r}, "
                f"got {lines[i + 1]!r}\n{out}"
            )
        parse_to_ast(out)
        assert format_source(out) == out, "second pass differs"

    def test_the_corpus_gate_reaches_nested_module_directories(self) -> None:
        """The gate must sweep everything `vera check` can reach.

        A direct-child `glob` skipped the six imported modules under
        `examples/vera/` and `tests/conformance/vera/`, and one of them
        was in fact non-canonical while the gate reported the corpus
        clean -- `examples/modules.vera` imports it. Asserted as a
        differential against an independent recursive walk rather than
        a fixed count, so adding a module cannot silently re-open it.
        """
        import sys
        root = Path(__file__).parent.parent
        sys.path.insert(0, str(root / "scripts"))
        from check_corpus_canonical import _corpus_files

        swept = {p.resolve() for p in _corpus_files()}
        expected = {
            p.resolve()
            for d in ("examples", "tests/conformance")
            for p in (root / d).rglob("*.vera")
        }
        assert swept == expected, (
            f"gate misses {sorted(expected - swept)}; "
            f"over-reaches {sorted(swept - expected)}"
        )
        assert any(p.parent.name == "vera" for p in swept), (
            "no nested module directory in the sweep — the case that "
            "made this necessary would not be covered"
        )

    def test_unwrapping_a_redundant_block_keeps_its_comments(self) -> None:
        """Rule 11 forbids *discarding* a comment, not just moving it.

        Dropping the `{ }` around a nested match drops its span, and any
        comment anchored inside went with it — one comment in, zero out.
        Count is the right assertion here precisely because this is the
        one failure mode counting can see.
        """
        src = dedent("""\
            private data C {
              R,
              G
            }

            public fn f(@C -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              match @C.0 {
                R -> {
                  -- inner note
                  match @C.0 {
                    R -> 1,
                    G -> 2
                  }
                },
                G -> 0
              }
            }
        """)
        out = format_source(src)
        assert len(extract_comments(out)) == len(extract_comments(src)), (
            f"a comment was discarded by the unwrap:\n{out}"
        )
        assert "-- inner note" in out
        parse_to_ast(out)
        assert format_source(out) == out, "second pass differs"

    def test_trailing_comment_stays_on_its_handler_clause(self) -> None:
        """A trailing comment belongs to its clause, not the closing brace."""
        out = _fmt("""
            effect Counter {
              op get(Unit -> Int);
              op inc(Unit -> Unit);
            }

            public fn c(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              handle[Counter](@Int = 0) {
                get(@Unit) -> resume(@Int.0), -- trailing on get
                inc(@Unit) -> resume(())
              } in {
                @Int.0
              }
            }
        """)
        line = next(
            ln for ln in out.splitlines() if "trailing on get" in ln
        )
        assert "get(@Unit)" in line, (
            f"comment swept off its clause onto {line!r}"
        )
        parse_to_ast(out)
        assert format_source(out) == out, "second pass differs"

    def test_own_line_comment_stays_above_a_where_function(self) -> None:
        """The `where` keyword was anchored; the functions inside were not."""
        out = _fmt("""
            public fn is_even(@Nat -> @Bool)
              requires(true)
              ensures(true)
              decreases(@Nat.0)
              effects(pure)
            {
              if @Nat.0 == 0 then { true } else { is_odd(@Nat.0 - 1) }
            }
            where {
              -- comment above where-fn is_odd
              fn is_odd(@Nat -> @Bool)
                requires(true)
                ensures(true)
                decreases(@Nat.0)
                effects(pure)
              {
                if @Nat.0 == 0 then { false } else { is_even(@Nat.0 - 1) }
              }
            }
        """)
        lines = out.splitlines()
        i = next(n for n, ln in enumerate(lines) if "above where-fn" in ln)
        assert lines[i + 1].strip().startswith("fn is_odd"), (
            f"comment drifted onto {lines[i + 1]!r} — it documents the "
            f"function, not its first clause\n{out}"
        )
        parse_to_ast(out)
        assert format_source(out) == out, "second pass differs"

    def test_comment_above_a_brace_less_nested_match_is_not_duplicated(
        self,
    ) -> None:
        """Two anchors can collapse onto one line — and did.

        Anchoring the nested match fixed the drift, but `_emit_comments`
        read the store without consuming it. After the first pass put
        `Some(@Int) -> match ... {` on one line, the arm anchor and the
        match anchor were the same line, so the comment was emitted
        twice on the second pass. Idempotence is the only assertion
        that sees it; position and count both pass on pass one.
        """
        out = _fmt("""
            public fn f(@Option<Int> -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              match @Option<Int>.0 {
                Some(@Int) ->
                  -- comment above nested match
                  match @Option<Int>.0 {
                    Some(@Int) -> @Int.0,
                    None -> 0
                  },
                None -> 0
              }
            }
        """)
        assert out.count("-- comment above nested match") == 1, (
            f"comment duplicated:\n{out}"
        )
        lines = out.splitlines()
        i = next(n for n, ln in enumerate(lines) if "above nested match" in ln)
        assert "match" in lines[i + 1], (
            f"comment must stay above the nested match, got "
            f"{lines[i + 1]!r}"
        )
        parse_to_ast(out)
        assert format_source(out) == out, "second pass differs"

    def test_a_handle_in_operand_position_is_not_destroyed(self) -> None:
        """`_fmt_handle_inline` emitted a literal ellipsis (#1136 sweep).

        The stub never read `expr.state`, `expr.clauses` or
        `expr.body`, so a `handle` reached through any sub-expression
        position formatted to `handle[E] { ... }` — state, every clause
        and the `in` body deleted — and the result did not parse. It
        carried `# pragma: no cover` on the belief the path was
        unreachable, but `handle_expr` is a bare alternative of
        `primary_expr` in the grammar.

        Worse than the relocations this PR fixes elsewhere: those moved
        a comment, this destroys the program.
        """
        out = _fmt("""
            effect Counter {
              op get(Unit -> Int);
              op inc(Unit -> Unit);
            }

            public fn run(@Unit -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              1 + handle[Counter](@Int = 0) {
                get(@Unit) -> resume(@Int.0),
                inc(@Unit) -> resume(())
              } in {
                get(())
              }
            }
        """)
        assert "..." not in out, f"the stub's ellipsis survived:\n{out}"
        for fragment in ("@Int = 0", "get(", "inc(", "} in {"):
            assert fragment in out, (
                f"{fragment!r} was deleted by formatting:\n{out}"
            )
        # The output must still be a program.
        parse_to_ast(out)
        assert format_source(out) == out, "second pass differs"

    # -- F3: blank line before a leading comment block ------------------

    def test_blank_line_between_a_comment_block_and_its_declaration(
        self,
    ) -> None:
        """A separated header block must not be glued to what follows."""
        out = _fmt("""
            -- A note about the type below.
            -- It runs to two lines.

            private data Colour {
              Red,
              Green
            }
        """)
        lines = out.splitlines()
        decl = next(i for i, ln in enumerate(lines) if ln.startswith("private"))
        assert lines[decl - 1] == "", (
            f"blank line separating the header block was swallowed:\n{out}"
        )

    # -- F4: escape normalisation --------------------------------------
    #
    # Ruling: escape what cannot be read safely, keep printable
    # non-ASCII literal.  `_STRING_ENCODE_MAP` covered six characters,
    # so everything else — including invisibles — passed through raw.

    def test_printable_non_ascii_stays_literal(self) -> None:
        out = _fmt("""
            public fn main(-> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              IO.print("café \U0001F600\\n");
              ()
            }
        """)
        assert "café \U0001F600" in out, out

    def test_invisible_characters_are_escaped_so_they_cannot_hide(
        self,
    ) -> None:
        """A zero-width space in source must become visible as `\\u{200B}`."""
        out = _fmt(
            'public fn main(-> @Unit)\n'
            '  requires(true)\n'
            '  ensures(true)\n'
            '  effects(<IO>)\n'
            '{\n'
            '  IO.print("a​b\\n");\n'
            '  ()\n'
            '}\n'
        )
        assert "\\u{200B}" in out, (
            f"a zero-width space must not survive as an invisible byte:\n{out!r}"
        )
        assert "​" not in out, "the raw invisible character is still there"

    # -- F5: blank lines between statements ----------------------------
    #
    # F3 taught the emitter to keep the blank under a *comment* block,
    # which left the formatter inconsistent: a blank below a comment
    # survived while a blank between two plain statements did not.  The
    # AST records no gap, so only the source line map can tell them
    # apart.  Both halves matter — preserving a real blank and never
    # inventing one — and only the second catches an over-eager fix.

    def _body_lines(self, out: str) -> list[str]:
        """The lines strictly inside the outermost `{ ... }`."""
        lines = out.splitlines()
        open_i = lines.index("{")
        close_i = len(lines) - 1 - lines[::-1].index("}")
        return lines[open_i + 1:close_i]

    def test_a_blank_line_between_two_statements_survives(self) -> None:
        """A paragraph break between statements is authored, not noise."""
        out = _fmt("""
            public fn main(-> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              IO.print("a");

              IO.print("b");
              ()
            }
        """)
        assert self._body_lines(out) == [
            '  IO.print("a");',
            "",
            '  IO.print("b");',
            "  ()",
        ], f"the blank between the two statements was swallowed:\n{out}"
        assert format_source(out) == out, "second pass differs"

    def test_a_blank_line_before_a_block_result_survives(self) -> None:
        """The `examples/file_io.vera` shape: `match ...;`, blank, `()`.

        The result expression is not a statement, so a fix that only
        walks `block.statements` leaves this one stripped.
        """
        out = _fmt("""
            public fn main(-> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match IO.read_file("a.txt") {
                Ok(@String) -> IO.print(@String.0),
                Err(@String) -> IO.print(@String.0)
              };

              ()
            }
        """)
        lines = out.splitlines()
        end = next(i for i, ln in enumerate(lines) if ln.strip() == "};")
        assert lines[end + 1] == "", (
            f"blank before the trailing `()` was swallowed:\n{out}"
        )
        assert lines[end + 2].strip() == "()", (
            f"expected `()` after the blank, got {lines[end + 2]!r}:\n{out}"
        )
        assert format_source(out) == out, "second pass differs"

    def test_consecutive_blank_lines_collapse_to_one(self) -> None:
        """However many the source had, the canonical form has one."""
        out = _fmt("""
            public fn main(-> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              IO.print("a");



              IO.print("b");
              ()
            }
        """)
        assert self._body_lines(out) == [
            '  IO.print("a");',
            "",
            '  IO.print("b");',
            "  ()",
        ], f"a run of blanks must collapse to exactly one:\n{out}"
        assert format_source(out) == out, "second pass differs"

    def test_no_blank_line_is_invented_where_source_had_none(self) -> None:
        """The anti-invention direction — what an over-eager fix breaks.

        Source with no gaps must format with no gaps: preserving a blank
        is a source-driven decision, not a per-statement default.
        """
        out = _fmt("""
            public fn main(-> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              let @Int = 1;
              IO.print("a");
              IO.print("b");
              match IO.read_file("a.txt") {
                Ok(@String) -> IO.print(@String.0),
                Err(@String) -> IO.print(@String.0)
              };
              ()
            }
        """)
        assert "" not in self._body_lines(out), (
            f"a blank line was invented where the source had none:\n{out}"
        )
        assert format_source(out) == out, "second pass differs"

    def test_no_blank_line_opens_or_closes_a_block(self) -> None:
        """A gap against a brace is padding, not a paragraph break.

        Rule 2 puts the braces on their own lines; a blank held against
        one separates nothing, so it is not reproduced even though the
        source line really was empty.
        """
        out = _fmt("""
            public fn main(-> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {

              IO.print("a");
              ()

            }
        """)
        body = self._body_lines(out)
        assert body and body[0] != "" and body[-1] != "", (
            f"a blank must not sit against a brace:\n{out}"
        )
        assert format_source(out) == out, "second pass differs"

    def test_no_blank_line_opens_a_block_holding_only_a_result(self) -> None:
        """The same rule where the result expression is the *first* thing.

        A block with no statements keeps its whole content in `expr`, so
        the gap-above-the-result rule reaches it with nothing before it
        and the gap it would reproduce is the one against the brace.
        """
        out = _fmt("""
            public fn main(-> @Unit)
              requires(true)
              ensures(true)
              effects(pure)
            {

              ()
            }
        """)
        assert self._body_lines(out) == ["  ()"], (
            f"a statements-free block must open flush with its brace:\n{out}"
        )
        assert format_source(out) == out, "second pass differs"

    def test_a_whitespace_only_line_counts_as_a_blank(self) -> None:
        """Source reaching the formatter is not canonical yet.

        Rule 9 strips trailing whitespace on the way *out*, so a
        separator carrying stray spaces on the way *in* is ordinary —
        and it is the same paragraph break as an empty line.  Testing
        for an empty string instead of a blank one would drop the gap
        from exactly the files that most need reformatting.  Written
        without `dedent`, which normalises such lines away.
        """
        out = format_source(
            'public fn main(-> @Unit)\n'
            '  requires(true)\n'
            '  ensures(true)\n'
            '  effects(<IO>)\n'
            '{\n'
            '  IO.print("a");\n'
            '     \n'  # the separator: whitespace, not empty
            '  IO.print("b");\n'
            '  ()\n'
            '}\n'
        )
        assert self._body_lines(out) == [
            '  IO.print("a");',
            "",
            '  IO.print("b");',
            "  ()",
        ], f"a whitespace-only line is a blank line:\n{out!r}"
        assert format_source(out) == out, "second pass differs"

    def test_top_level_declarations_always_get_exactly_one_blank(self) -> None:
        """Rule 13's second half: a separator, not a preserved gap.

        Unlike a gap inside a block this one does not read from source —
        none and three both come out as one — so extending gap
        preservation outward must not make the separator conditional.
        """
        fn = (
            "public fn {}(-> @Unit)\n  requires(true)\n  ensures(true)\n"
            "  effects(pure)\n{{\n  ()\n}}\n"
        )
        a, b = fn.format("a"), fn.format("b")
        for gap in ("", "\n", "\n\n\n"):
            out = format_source(a + gap + b)
            assert out.count("\n\n") == 1, (
                f"source gap {gap!r} must yield exactly one blank:\n{out}"
            )
            assert "}\n\npublic fn b" in out, (
                f"the separator must sit between the declarations:\n{out}"
            )

    def test_the_emitter_never_stacks_two_blank_lines(self) -> None:
        """Rule 13's "at most one" is enforced at the emitter, not per caller.

        Three call sites reproduce a gap — the declaration separator,
        the comment emitter for the space *below* a comment, the block
        emitter for the space *above* one — and no source arrangement
        currently puts two of them back to back, because the comment
        they bracket always lands between them.  Clamping here is what
        keeps that true for a fourth: a caller cannot open the output
        with a blank or stack one on another, whatever it knows about
        the others.
        """
        fmt = Formatter(_Attached(before={}, inline=[], header=[], footer=[]))
        fmt._blank()
        assert fmt._lines == [], "a blank must not open the output"
        fmt._line("x")
        fmt._blank()
        fmt._blank()
        fmt._blank()
        assert fmt._lines == ["x", ""], (
            f"blank lines must not stack: {fmt._lines!r}"
        )

    def test_a_blank_above_and_below_a_comment_both_survive(self) -> None:
        """Two independent gaps: one before the comment, one after it."""
        out = _fmt("""
            public fn main(-> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              IO.print("a");

              -- A note held off the statement below it.

              IO.print("b");
              ()
            }
        """)
        assert self._body_lines(out) == [
            '  IO.print("a");',
            "",
            "  -- A note held off the statement below it.",
            "",
            '  IO.print("b");',
            "  ()",
        ], f"both gaps must survive, each as one blank:\n{out}"
        assert format_source(out) == out, "second pass differs"

    def test_a_comment_with_a_blank_after_it_yields_exactly_one_blank(
        self,
    ) -> None:
        """The double-fire guard: two code paths, one blank line.

        `_emit_comments` reproduces the gap *below* a comment and the
        statement emitter reproduces the gap *above* one.  A fix that
        lets both fire on the same source blank emits two.
        """
        out = _fmt("""
            public fn main(-> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              IO.print("a");
              -- A note held off the statement below it.

              IO.print("b");
              ()
            }
        """)
        assert self._body_lines(out) == [
            '  IO.print("a");',
            "  -- A note held off the statement below it.",
            "",
            '  IO.print("b");',
            "  ()",
        ], f"exactly one blank, and only below the comment:\n{out}"
        assert format_source(out) == out, "second pass differs"

    # -- F6: rule 2 in value position ----------------------------------
    #
    # Rule 2 ("opening brace on the same line, closing brace on its own
    # line aligned with the construct") was implemented in statement
    # position, block-result position and match-arm-body position, but
    # not where a construct is the *value* of a binding.  So the same
    # `if` was written two ways depending on where it sat:
    #
    #     let @Int = if @Bool.0 then { 1 } else { 2 };   -- flat
    #     if @Bool.0 then { 1 } else { 2 }               -- five lines
    #
    # A position-dependent canonical form is two equivalent alternatives
    # for one construct, which DESIGN.md principle 3 forbids, and a
    # conditional rule a generator must evaluate per site, which
    # principle 6 rejects in favour of one unconditional rule.  Rule 2
    # holds in every position.

    @staticmethod
    def _no_line_holds_both_braces(out: str) -> None:
        """No emitted line may open a brace and close it again.

        `} else {` closes one brace before opening the next, which is
        the canonical `if` hinge rule 2 prescribes; the violation is an
        opening brace whose match arrives on the *same* line, so the
        test is that no `{` precedes a `}`.
        """
        offenders = [
            ln for ln in out.splitlines()
            if "{" in ln and "}" in ln and ln.index("{") < ln.rindex("}")
        ]
        assert not offenders, (
            "rule 2: a brace pair shares a line:\n  "
            + "\n  ".join(offenders)
            + f"\nfull output:\n{out}"
        )

    @staticmethod
    def _reparses_and_is_fixed_point(out: str) -> None:
        """Output must re-parse and be unchanged by a second pass."""
        pipeline.parse(out).program
        assert format_source(out) == out, (
            f"second pass differs.\nFirst:\n{out}\n"
            f"Second:\n{format_source(out)}"
        )

    def test_a_let_bound_if_takes_its_own_lines(self) -> None:
        """`let @T = if ...` expands exactly as statement position does."""
        out = _fmt("""
            public fn f(@Bool -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = if @Bool.0 then { 1 } else { 2 };
              @Int.0
            }
        """)
        assert self._body_lines(out) == [
            "  let @Int = if @Bool.0 then {",
            "    1",
            "  } else {",
            "    2",
            "  };",
            "  @Int.0",
        ], f"a let-bound `if` must obey rule 2:\n{out}"
        self._no_line_holds_both_braces(out)
        self._reparses_and_is_fixed_point(out)

    def test_a_let_bound_match_takes_its_own_lines(self) -> None:
        """The `match` sibling of the `if` case, same rule, same shape."""
        out = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = match @Int.0 { 0 -> 10, _ -> 20 };
              @Int.0
            }
        """)
        assert self._body_lines(out) == [
            "  let @Int = match @Int.0 {",
            "    0 -> 10,",
            "    _ -> 20",
            "  };",
            "  @Int.0",
        ], f"a let-bound `match` must obey rule 2:\n{out}"
        self._no_line_holds_both_braces(out)
        self._reparses_and_is_fixed_point(out)

    def test_a_let_destructure_of_a_match_takes_its_own_lines(self) -> None:
        """`LetDestruct` is a second value position with the same gap.

        It routes through the same `_fmt_expr` call as `LetStmt`, so a
        fix that covers only `let @T = ...` leaves the destructuring
        form flat — the sibling-miss this suite exists to catch.
        """
        out = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let Tuple<@Int, @Int> = match @Int.0 {
                0 -> Tuple(1, 2),
                _ -> Tuple(3, 4)
              };
              @Int.0 + @Int.1
            }
        """)
        assert self._body_lines(out) == [
            "  let Tuple<@Int, @Int> = match @Int.0 {",
            "    0 -> Tuple(1, 2),",
            "    _ -> Tuple(3, 4)",
            "  };",
            "  @Int.0 + @Int.1",
        ], f"a let-destructured `match` must obey rule 2:\n{out}"
        self._no_line_holds_both_braces(out)
        self._reparses_and_is_fixed_point(out)

    def test_a_let_bound_block_wrapped_match_does_not_flatten(self) -> None:
        """`let @T = { match ... };` unwraps rather than collapsing.

        The block holds its content in `expr` with `statements` empty,
        so a `statements`-only emptiness test reads it as flat and puts
        the whole construct on one line — the same hole the statement
        path closes with `_unwrap_redundant_block`.
        """
        out = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = { match @Int.0 { 0 -> 10, _ -> 20 } };
              @Int.0
            }
        """)
        assert self._body_lines(out) == [
            "  let @Int = match @Int.0 {",
            "    0 -> 10,",
            "    _ -> 20",
            "  };",
            "  @Int.0",
        ], f"a block-wrapped let value must not flatten:\n{out}"
        self._no_line_holds_both_braces(out)
        self._reparses_and_is_fixed_point(out)

    def test_a_let_bound_nested_construct_keeps_every_brace_apart(
        self,
    ) -> None:
        """Nesting inside a let value must not re-flatten one level in.

        The outer construct expanding is not evidence the inner one
        does: the arm body reaches a different emitter branch, and the
        flattening fallback lives there too.
        """
        out = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = match @Int.0 {
                0 -> if @Int.0 > 0 then { 1 } else { 2 },
                _ -> 20
              };
              @Int.0
            }
        """)
        assert self._body_lines(out) == [
            "  let @Int = match @Int.0 {",
            "    0 -> if @Int.0 > 0 then {",
            "      1",
            "    } else {",
            "      2",
            "    },",
            "    _ -> 20",
            "  };",
            "  @Int.0",
        ], f"the nested `if` must expand too:\n{out}"
        self._no_line_holds_both_braces(out)
        self._reparses_and_is_fixed_point(out)

    def test_a_comment_above_a_let_bound_construct_is_not_duplicated(
        self,
    ) -> None:
        """The unwrap must consume a comment once, not drop or repeat it.

        Expanding a let value changes which lines exist, and two
        anchors collapsing onto one line is what made a comment emit
        twice on the second pass earlier in this work.
        """
        out = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              -- Pick a branch.
              let @Int = { match @Int.0 { 0 -> 10, _ -> 20 } };
              @Int.0
            }
        """)
        assert out.count("-- Pick a branch.") == 1, (
            f"the comment must appear exactly once:\n{out}"
        )
        assert self._body_lines(out) == [
            "  -- Pick a branch.",
            "  let @Int = match @Int.0 {",
            "    0 -> 10,",
            "    _ -> 20",
            "  };",
            "  @Int.0",
        ], f"the comment must stay above its statement:\n{out}"
        self._reparses_and_is_fixed_point(out)

    # A statement's *value* was never walked for anchors, so every
    # position inside one — arms, handler clauses, branch statements —
    # was invisible to comment attachment and the comment fell through
    # to whatever came after the statement.  Expanding let values turns
    # those positions into real lines, which makes the misattribution
    # visible rather than merely latent.

    def test_a_comment_above_an_arm_of_a_let_bound_match_stays_there(
        self,
    ) -> None:
        """Position, not presence: the comment survives either way.

        Before the anchor walk descended into a statement's value, this
        comment was emitted *below* the whole `let`, documenting the
        next statement instead of the arm it was written above.  A
        count assertion passes in both worlds; only position separates
        them.
        """
        out = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = match @Int.0 {
                -- The zero case.
                0 -> 10,
                _ -> 20
              };
              @Int.0
            }
        """)
        assert self._body_lines(out) == [
            "  let @Int = match @Int.0 {",
            "    -- The zero case.",
            "    0 -> 10,",
            "    _ -> 20",
            "  };",
            "  @Int.0",
        ], f"the comment must stay on its arm:\n{out}"
        self._reparses_and_is_fixed_point(out)

    def test_a_comment_above_an_arm_of_a_statement_match_stays_there(
        self,
    ) -> None:
        """The `ExprStmt` sibling of the `let` case, same missing walk.

        Statement position already emitted its arms on their own lines,
        so this misattribution was reachable before the let-value
        change and is fixed by the same descent.
        """
        out = _fmt("""
            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                -- The zero case.
                0 -> IO.print("a"),
                _ -> IO.print("b")
              };
              IO.print("done")
            }
        """)
        assert self._body_lines(out) == [
            "  match @Int.0 {",
            "    -- The zero case.",
            '    0 -> IO.print("a"),',
            '    _ -> IO.print("b")',
            "  };",
            '  IO.print("done")',
        ], f"the comment must stay on its arm:\n{out}"
        self._reparses_and_is_fixed_point(out)

    # -- Adversarial-review fixes (PR #1138 review): comment deletion,
    # renderer fidelity, anchor gaps, and the structural backstop.
    #
    # Every test in this block began as a confirmed finding with an
    # exact repro.  The deletion cases are rule 11 violations (a
    # formatter MUST NOT discard a comment); the fidelity cases are
    # programs whose meaning or parseability the formatter destroyed.

    def test_comment_above_a_value_position_match_on_next_line_survives(
        self,
    ) -> None:
        """A match bound directly (no block) never flushed its bucket.

        `_collect_interior_anchors` files the comment under the match's
        own span line, but `_emit_value` popped that bucket only on the
        unwrap path — a value that IS the match deleted the comment.
        """
        out = _fmt("""
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int =
                -- KEEP ME
                match @Int.0 {
                  0 -> 1,
                  _ -> 2
                };
              @Int.0
            }
        """)
        assert out.count("KEEP ME") == 1, (
            f"COMMENT DELETED: count={out.count('KEEP ME')}\n{out}"
        )
        lines = out.splitlines()
        i = next(n for n, ln in enumerate(lines) if "KEEP ME" in ln)
        assert "let @Int = match" in lines[i + 1], (
            f"comment must sit above the let it documents:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_comment_inside_a_flattened_redundant_block_value_survives(
        self,
    ) -> None:
        """The plain-expression flatten path had no comment rescue.

        `let @Int = { -- keep me \\n 5 };` flattens to `let @Int = 5;`
        via `_emit_value`'s else branch, which never emitted the
        comment anchored at the inner expression's line.
        """
        out = _fmt("""
            public fn main(@Unit -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = {
                -- keep me
                5
              };
              @Int.0
            }
        """)
        assert out.count("keep me") == 1, (
            f"COMMENT LOST: appears {out.count('keep me')} times\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_comment_inside_a_flattened_match_arm_block_survives(
        self,
    ) -> None:
        """The arm loop's flatten branch is a distinct unfixed site.

        `pat -> { -- note \\n expr }` flattens to `pat -> expr` without
        the `_emit_comments` rescue the `_needs_own_lines` branch has.
        """
        out = _fmt("""
            public fn main(@Unit -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              match 1 {
                0 -> 0,
                _ -> {
                  -- important note about this arm
                  42
                }
              }
            }
        """)
        assert out.count("important note") == 1, (
            f"COMMENT LOST: appears {out.count('important note')} times\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_a_statement_bearing_block_as_a_let_value_renders_faithfully(
        self,
    ) -> None:
        """A block WITH statements in value position must keep braces.

        The flat path emitted `let @Int = let @Int = ...;` — output
        that no longer parses — and deleted the interior comment.
        """
        out = _fmt("""
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = {
                -- BLOCKDOC interior
                let @Int = @Int.0 + 1;
                @Int.0
              };
              @Int.0
            }
        """)
        assert "BLOCKDOC" in out, f"COMMENT LOST:\n{out}"
        self._reparses_and_is_fixed_point(out)

    def test_an_orphaned_before_bucket_relocates_not_deletes(self) -> None:
        """The structural backstop: no bucket may die unemitted.

        Every deletion in this block shared one mechanism — a
        `before` bucket keyed to a line no emitter visits.  Rule 11
        sanctions relocation to the end of the enclosing declaration;
        it forbids deletion.  This constructs the orphan directly, so
        the backstop is tested even after every known producer of
        orphans is fixed.
        """
        from vera.formatter import (
            Comment,
            _attach_comments,
            blank_source_lines,
        )
        src = dedent("""\
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """)
        program = parse_to_ast(src)
        attached = _attach_comments(extract_comments(src), program)
        # Key a bucket to the body's closing-brace line: inside the
        # declaration's span, never an anchor any emitter pops.
        orphan = Comment(
            kind="line", text="-- orphaned but not forgotten",
            line=6, column=1, end_line=6, inline=False,
        )
        attached.before[7] = [orphan]
        out = Formatter(attached, blank_source_lines(src)).format_program(
            program,
        )
        assert "-- orphaned but not forgotten" in out, (
            f"orphan bucket was deleted, not relocated:\n{out}"
        )
        parse_to_ast(out)

    def test_postcondition_rejects_comment_loss(self) -> None:
        """format_source must refuse to return comment-losing output."""
        from vera.formatter import (
            FormatterPostconditionError,
            _check_postconditions,
        )
        src = dedent("""\
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              -- documented
              @Int.0
            }
        """)
        lossy = src.replace("  -- documented\n", "")
        with pytest.raises(FormatterPostconditionError) as exc:
            _check_postconditions(src, lossy, None)
        assert "comment" in str(exc.value).lower()

    def test_postcondition_rejects_unparseable_output(self) -> None:
        """format_source must refuse to return destroyed output."""
        from vera.formatter import (
            FormatterPostconditionError,
            _check_postconditions,
        )
        src = dedent("""\
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """)
        with pytest.raises(FormatterPostconditionError) as exc:
            _check_postconditions(src, "let @Int = let @Int = 1;", None)
        assert "parse" in str(exc.value).lower()

    def test_postcondition_rejects_a_non_fixed_point(self) -> None:
        """Output a second pass would rewrite is not canonical."""
        from vera.formatter import (
            FormatterPostconditionError,
            _check_postconditions,
        )
        src = dedent("""\
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
                  @Int.0
            }
        """)
        # The source itself parses and holds its (zero) comments, but
        # is not canonical: handing it back as "output" must fail the
        # fixed-point invariant.
        with pytest.raises(FormatterPostconditionError) as exc:
            _check_postconditions(src, src, None)
        assert "fixed point" in str(exc.value).lower()

    def test_comment_above_a_value_position_if_stays_outside(self) -> None:
        """IfExpr needs the same self-anchor MatchExpr already has.

        Without it the comment attached to the first anchor *inside*
        the construct and was emitted inside the then-branch,
        documenting the branch result instead of the whole if.
        """
        out = _fmt("""
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int =
                -- ABOUT THE WHOLE IF
                if @Int.0 > 0 then {
                  1
                } else {
                  2
                };
              @Int.0
            }
        """)
        lines = out.splitlines()
        i = next(n for n, ln in enumerate(lines) if "ABOUT THE WHOLE IF" in ln)
        assert "let @Int = if" in lines[i + 1], (
            f"comment must sit above the let, not inside the if:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_comment_above_a_value_position_handle_stays_outside(
        self,
    ) -> None:
        """HandleExpr needs the same self-anchor as MatchExpr."""
        out = _fmt("""
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int =
                -- ABOUT THE WHOLE HANDLE
                handle[Exn<Int>] {
                  throw(@Int) -> { @Int.0 }
                } in {
                  @Int.1 + 1
                };
              @Int.0
            }
        """)
        lines = out.splitlines()
        i = next(
            n for n, ln in enumerate(lines) if "ABOUT THE WHOLE HANDLE" in ln
        )
        assert "let @Int = handle[Exn<Int>]" in lines[i + 1], (
            f"comment must sit above the let, not inside the handle:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_comment_between_arrow_and_next_line_body_stays_on_its_arm(
        self,
    ) -> None:
        """A plain next-line arm body is a position a comment precedes.

        Without a body anchor the comment fell through to the NEXT
        arm's line — and for the last arm, to the file footer.
        """
        out = _fmt("""
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              match @Int.0 {
                0 ->
                  -- ABOUT ARM ZERO
                  1,
                _ ->
                  -- ABOUT LAST ARM
                  3
              }
            }
        """)
        lines = out.splitlines()
        i = next(n for n, ln in enumerate(lines) if "ABOUT ARM ZERO" in ln)
        assert lines[i + 1].strip().startswith("0 -> 1"), (
            f"comment must stay on arm zero, not drift to the next:\n{out}"
        )
        j = next(n for n, ln in enumerate(lines) if "ABOUT LAST ARM" in ln)
        assert lines[j + 1].strip().startswith("_ -> 3"), (
            f"comment must stay on the last arm, not escape the fn:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_comment_inside_a_handler_clause_body_stays_on_its_clause(
        self,
    ) -> None:
        """Clause bodies render on one line; their comments must not
        migrate to the next clause (or into the in-block)."""
        out = _fmt("""
            private fn tally(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              handle[State<Int>](@Int = @Int.0) {
                get(@Unit) -> {
                  -- MARKA inside get clause
                  resume(@Int.0)
                },
                put(@Int) -> {
                  -- MARKB inside put clause
                  resume(())
                }
              } in {
                put(get(()) + 1);
                get(())
              }
            }
        """)
        lines = out.splitlines()
        ia = next(n for n, ln in enumerate(lines) if "MARKA" in ln)
        assert "get(@Unit) ->" in lines[ia + 1], (
            f"MARKA must stay on the get clause it documents:\n{out}"
        )
        ib = next(n for n, ln in enumerate(lines) if "MARKB" in ln)
        assert "put(@Int) ->" in lines[ib + 1], (
            f"MARKB must stay on the put clause it documents:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_small_and_large_float_literals_stay_lexable(self) -> None:
        """FLOAT_LIT has no exponent form; repr()'s `1e-05` destroys
        the program.  The emitted decimal must round-trip exactly."""
        tiny = "0." + "0" * 323 + "5"          # 5e-324, min subnormal
        huge = "1" + "0" * 300 + ".0"          # 1e300
        src = dedent(f"""\
            public fn f(@Unit -> @Float64)
              requires(true)
              ensures(true)
              effects(pure)
            {{
              let @Float64 = 0.00001;
              let @Float64 = 10000000000000000.0;
              let @Float64 = {huge};
              let @Float64 = {tiny};
              @Float64.0
            }}
        """)
        out = format_source(src)
        for ln in out.splitlines():
            if "let @Float64" in ln:
                assert "e" not in ln.split("=")[1], (
                    f"unlexable exponent form emitted: {ln!r}"
                )
        assert parse_to_ast(out) == parse_to_ast(src), (
            f"float values must round-trip identically:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_indexing_a_parenthesized_expression_keeps_the_parens(
        self,
    ) -> None:
        """`(x |> f())[0]` must not become `x |> f()[0]` — indexing
        binds tightest, so an operator collection needs parens."""
        src = dedent("""\
            private fn boxit(@Int -> @Array<Int>)
              requires(true)
              ensures(true)
              effects(pure)
            {
              [@Int.0, @Int.0 + 1]
            }

            public fn main(@Unit -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              (5 |> boxit())[0]
            }
        """)
        out = format_source(src)
        assert "(5 |> boxit())[0]" in out, (
            f"parens dropped — output is a different program:\n{out}"
        )
        assert parse_to_ast(out) == parse_to_ast(src), (
            f"formatted AST differs from the source AST:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_indexing_a_parenthesized_operator_expression_is_silent_safe(
        self,
    ) -> None:
        """`(0 - xs)[0]` reparsing as `0 - xs[0]` is the silent case."""
        src = dedent("""\
            public fn f(@Array<Int> -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              (0 - @Array<Int>.0)[0]
            }
        """)
        out = format_source(src)
        assert parse_to_ast(out) == parse_to_ast(src), (
            f"formatted AST differs from the source AST:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_a_block_statement_keeps_its_braces_and_its_scope(self) -> None:
        """`{ let @Int = 100; () };` must not leak its binding.

        Dropping the braces is check-clean both sides but changes
        which slot `@Int.0` resolves to — a silent runtime change.
        """
        src = dedent("""\
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              { let @Int = 100; () };
              @Int.0
            }
        """)
        out = format_source(src)
        assert parse_to_ast(out) == parse_to_ast(src), (
            f"braces lost — the binding leaks into the enclosing "
            f"scope:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_a_grouping_block_keeps_its_braces(self) -> None:
        """`{ 1 + 2 } * 3` is 9; `1 + 2 * 3` is 7."""
        src = dedent("""\
            public fn f(@Unit -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              { 1 + 2 } * 3
            }
        """)
        out = format_source(src)
        assert parse_to_ast(out) == parse_to_ast(src), (
            f"grouping braces lost — 9 became 7:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_a_statement_block_as_a_sub_expression_value_parses(
        self,
    ) -> None:
        """`let @Int = { let ...; ... };` must re-parse after fmt."""
        src = dedent("""\
            public fn g(@Unit -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = { let @Int = 1; @Int.0 + 1 };
              @Int.0
            }
        """)
        out = format_source(src)
        assert parse_to_ast(out) == parse_to_ast(src), (
            f"formatted AST differs from the source AST:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_a_blank_line_inside_a_block_comment_is_not_a_separator(
        self,
    ) -> None:
        """blank_source_lines must skip comment-interior lines.

        The docstring already promises this; the implementation was a
        raw whitespace scan that manufactured a paragraph break the
        author never wrote.
        """
        src = (
            "private fn f(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  let @Int = @Int.0 + 1;  {-\n"
            "\n"
            "  -} let @Int = @Int.0 + 2;\n"
            "  @Int.0\n"
            "}\n"
        )
        out = format_source(src)
        assert "" not in self._body_lines(out), (
            f"phantom blank line emitted between statements:\n{out}"
        )
        self._reparses_and_is_fixed_point(out)

    def test_the_corpus_gate_flags_crlf_files(self, tmp_path, monkeypatch,
                                              capsys) -> None:
        """Canonical form is LF; a CRLF corpus file must not pass."""
        import sys as _sys
        root = Path(__file__).parent.parent
        _sys.path.insert(0, str(root / "scripts"))
        import check_corpus_canonical as gate

        canonical = format_source(dedent("""\
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """))
        corpus = tmp_path / "corpus"
        corpus.mkdir()
        (corpus / "crlf.vera").write_bytes(
            canonical.replace("\n", "\r\n").encode("utf-8")
        )
        monkeypatch.setattr(gate, "_ROOT", tmp_path)
        monkeypatch.setattr(gate, "_CORPUS_DIRS", ("corpus",))
        assert gate.main() == 1, "CRLF file certified as canonical"
        err = capsys.readouterr().err
        assert "crlf.vera" in err
        assert "LF" in err, f"error must name the canonical line ending: {err}"

    def test_the_corpus_gate_reports_unreadable_files(self, tmp_path,
                                                      monkeypatch,
                                                      capsys) -> None:
        """Invalid UTF-8 joins the broken report; the sweep continues."""
        import sys as _sys
        root = Path(__file__).parent.parent
        _sys.path.insert(0, str(root / "scripts"))
        import check_corpus_canonical as gate

        corpus = tmp_path / "corpus"
        corpus.mkdir()
        (corpus / "bad_utf8.vera").write_bytes(
            b"fn f(@Int -> @Int)\n  requires(true)\n  \xff\xfe garbage\n"
        )
        # A second, stale file: the sweep must still reach and report it.
        (corpus / "stale.vera").write_text(
            "public fn f(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "      @Int.0\n"
            "}\n",
            encoding="utf-8",
        )
        monkeypatch.setattr(gate, "_ROOT", tmp_path)
        monkeypatch.setattr(gate, "_CORPUS_DIRS", ("corpus",))
        rc = gate.main()  # must not raise UnicodeDecodeError
        assert rc == 1
        err = capsys.readouterr().err
        assert "bad_utf8.vera" in err, f"unreadable file unreported: {err}"
        assert "stale.vera" in err, (
            f"sweep aborted before reaching later files: {err}"
        )

    def test_format_source_formats_the_passed_source_not_the_file(
        self,
    ) -> None:
        """`file` is a diagnostic label, not an alternate input."""
        src = dedent("""\
            fn triple(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 * 3
            }
        """)
        root = Path(__file__).parent.parent
        out = format_source(src, file=str(root / "examples/vera/math.vera"))
        assert "triple" in out, "the passed source was discarded"
        assert "vera.math" not in out, "the on-disk file was formatted"

    def test_where_span_serializes_as_a_structured_span(self) -> None:
        """`ast --json` must not emit two span encodings."""
        src = dedent("""\
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              g(@Int.0)
            }
            where {
              fn g(@Int -> @Int)
                requires(true)
                ensures(true)
                effects(pure)
              {
                @Int.0
              }
            }
        """)
        decl = parse_to_ast(src).declarations[0].decl
        d = decl.to_dict()
        assert isinstance(d["where_span"], dict), (
            f"where_span serialized as {type(d['where_span']).__name__}: "
            f"{d['where_span']!r}"
        )
        assert set(d["where_span"]) == {
            "line", "column", "end_line", "end_column",
        }

    def test_where_span_is_position_blind_like_every_other_span(
        self,
    ) -> None:
        """Node equality and repr must not leak source positions."""
        src = dedent("""\
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              g(@Int.0)
            }
            where {
              fn g(@Int -> @Int)
                requires(true)
                ensures(true)
                effects(pure)
              {
                @Int.0
              }
            }
        """)
        d1 = parse_to_ast(src).declarations[0].decl
        d2 = parse_to_ast("\n\n" + src).declarations[0].decl
        assert d1 == d2, (
            "byte-identical decls at different offsets must compare equal"
        )
        assert "where_span=" not in repr(d1), (
            "where_span leaks source position into repr"
        )

    def test_a_redundant_block_unwraps_at_block_result_position_too(
        self,
    ) -> None:
        """`{ match ... }` is canonical bare in every position."""
        out = _fmt("""
            private fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = @Int.0;
              { match @Int.0 { 0 -> 1, _ -> 2 } }
            }
        """)
        assert self._body_lines(out) == [
            "  let @Int = @Int.0;",
            "  match @Int.0 {",
            "    0 -> 1,",
            "    _ -> 2",
            "  }",
        ], f"the redundant wrapper must unwrap at result position:\n{out}"
        self._reparses_and_is_fixed_point(out)
