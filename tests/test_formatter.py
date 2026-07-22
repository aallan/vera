"""Tests for vera.formatter — canonical code formatter."""

from __future__ import annotations

import os
from pathlib import Path
from textwrap import dedent

import pytest

from vera.formatter import (
    extract_comments,
    format_source,
)
from vera.parser import parse_to_ast


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

    def test_own_line_comments_stay_above_contract_clauses(self) -> None:
        """Contract comments must not move into the function body (#1136)."""
        out = format_source(dedent("""\
            public fn demo(@Int -> @Int)
              -- before requires
              requires(true)
              ensures(true) -- after ensures
              -- before effects
              effects(pure)
            {
              @Int.0
            }
        """))
        assert out.splitlines() == [
            "public fn demo(@Int -> @Int)",
            "  -- before requires",
            "  requires(true)",
            "  ensures(true)  -- after ensures",
            "  -- before effects",
            "  effects(pure)",
            "{",
            "  @Int.0",
            "}",
        ]
        assert format_source(out) == out

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
            effect IO { op print(String -> Unit); }

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
            effect IO {
              op print(String -> Unit);
            }

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
            effect IO { op print(String -> Unit); }

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
            effect IO { op print(String -> Unit); }

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
            effect IO { op print(String -> Unit); }

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
            effect IO { op print(String -> Unit); }

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
            effect IO { op print(String -> Unit); }

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

    def test_match_arm_block_inline_context(self) -> None:
        """Match in let-binding position wraps block arm in braces inline."""
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
        # Block arm body must be wrapped in braces in inline form
        assert "{ let @Int = 10; @Int.0 + 1 }" in src

    def test_match_arm_block_in_exprstmt(self) -> None:
        """Match as ExprStmt preserves block arm braces in inline form."""
        src = _fmt("""
            effect IO { op print(String -> Unit); }

            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 { 0 -> { IO.print("a"); IO.print("b") }, _ -> IO.print("c") };
              IO.print("done")
            }
        """)
        # Block arm in inline match must have braces
        assert "{ IO.print(\"a\"); IO.print(\"b\") }" in src


# =====================================================================
# Interior comment positioning (#274)
# =====================================================================

class TestInteriorComments:
    """Comments inside function bodies must stay in position, not move to footer."""

    def test_comment_before_statement(self) -> None:
        """A comment before a let statement stays before it."""
        _fmt_check(
            """
            effect IO { op print(String -> Unit); }

            public fn main(@Unit -> @Unit)
              requires(true) ensures(true) effects(<IO>)
            {
              -- set up the value
              let @Int = 42;
              IO.print(int_to_string(@Int.0))
            }
            """,
            """
            effect IO {
              op print(String -> Unit);
            }

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
            effect IO { op print(String -> Unit); }

            public fn main(@Unit -> @Unit)
              requires(true) ensures(true) effects(<IO>)
            {
              let @Int = 42;
              -- now print it
              IO.print(int_to_string(@Int.0))
            }
            """,
            """
            effect IO {
              op print(String -> Unit);
            }

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
            effect IO { op print(String -> Unit); }

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
            effect IO {
              op print(String -> Unit);
            }

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
            effect IO { op print(String -> Unit); }

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
            effect IO {
              op print(String -> Unit);
            }

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
            effect IO { op print(String -> Unit); }

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
            effect IO { op print(String -> Unit); }

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
            effect IO { op print(String -> Unit); }

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
            effect IO {
              op print(String -> Unit);
            }

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

    ALL = {
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
