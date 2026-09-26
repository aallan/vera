"""Parser tests — verify that valid Vera programs parse without error."""

from pathlib import Path

import pytest

from vera.parser import (
    parse,
    parse_file,
    parse_to_ast,
    typecheck_file,
    verify_file,
)
from vera.errors import ParseError

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"


# =====================================================================
# Example file tests
# =====================================================================


@pytest.mark.parametrize(
    "filename",
    [f.name for f in sorted(EXAMPLES_DIR.glob("*.vera"))],
)
def test_example_files_parse(filename: str) -> None:
    """Every .vera file in examples/ must parse without error."""
    parse_file(EXAMPLES_DIR / filename)


# =====================================================================
# Individual construct tests
# =====================================================================


class TestExpressions:
    def test_integer_literal(self) -> None:
        tree = parse("private fn f(@Unit -> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert tree is not None

    def test_arithmetic(self) -> None:
        parse("private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 + 1 }")
        parse("private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 * 2 - 3 }")
        parse("private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 / 2 % 3 }")

    def test_comparison(self) -> None:
        parse("private fn f(@Int -> @Bool) requires(true) ensures(true) effects(pure) { @Int.0 > 0 }")
        parse("private fn f(@Int -> @Bool) requires(true) ensures(true) effects(pure) { @Int.0 <= 10 }")

    def test_boolean_operators(self) -> None:
        parse("private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) effects(pure) { @Bool.0 && @Bool.1 }")
        parse("private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) effects(pure) { @Bool.0 || @Bool.1 }")
        parse("private fn f(@Bool -> @Bool) requires(true) ensures(true) effects(pure) { !@Bool.0 }")

    def test_implies(self) -> None:
        parse("private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) effects(pure) { @Bool.0 ==> @Bool.1 }")

    def test_pipe(self) -> None:
        parse("private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 + 1 |> abs() }")

    def test_negation(self) -> None:
        parse("private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { -@Int.0 }")

    def test_parenthesized(self) -> None:
        parse("private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { (@Int.0 + 1) * 2 }")

    def test_array_literal(self) -> None:
        parse("private fn f(@Unit -> @Array<Int>) requires(true) ensures(true) effects(pure) { [1, 2, 3] }")

    def test_array_index(self) -> None:
        parse("private fn f(@Array<Int> -> @Int) requires(true) ensures(true) effects(pure) { @Array<Int>.0[0] }")

    def test_string_literal(self) -> None:
        parse('private fn f(@Unit -> @String) requires(true) ensures(true) effects(pure) { "hello" }')

    def test_unit_literal(self) -> None:
        parse("private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(pure) { () }")


class TestFunctions:
    def test_multiple_params(self) -> None:
        parse("private fn f(@Int, @Bool, @String -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 }")

    def test_multiple_requires(self) -> None:
        parse("private fn f(@Int -> @Int) requires(@Int.0 > 0) requires(@Int.0 < 100) ensures(true) effects(pure) { @Int.0 }")

    def test_multiple_ensures(self) -> None:
        parse("private fn f(@Int -> @Nat) requires(true) ensures(@Nat.result >= 0) ensures(@Nat.result <= @Int.0) effects(pure) { @Int.0 }")

    def test_decreases_clause(self) -> None:
        parse("private fn f(@Nat -> @Nat) requires(true) ensures(true) decreases(@Nat.0) effects(pure) { @Nat.0 }")

    def test_recursive_call(self) -> None:
        parse("""
        private fn f(@Nat -> @Nat)
          requires(true)
          ensures(true)
          decreases(@Nat.0)
          effects(pure)
        {
          if @Nat.0 == 0 then { 0 } else { f(@Nat.0 - 1) }
        }
        """)

    def test_where_block(self) -> None:
        parse("""
        private fn outer(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          helper(@Int.0)
        }
        where {
          fn helper(@Int -> @Int)
            requires(true)
            ensures(true)
            effects(pure)
          {
            @Int.0 + 1
          }
        }
        """)


class TestConditionals:
    def test_if_then_else(self) -> None:
        parse("""
        private fn f(@Bool -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          if @Bool.0 then { 1 } else { 0 }
        }
        """)


class TestPatternMatching:
    def test_match_constructors(self) -> None:
        parse("""
        private data Color { Red, Green, Blue }

        private fn to_int(@Color -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          match @Color.0 {
            Red -> 0,
            Green -> 1,
            Blue -> 2
          }
        }
        """)

    def test_match_with_binding(self) -> None:
        parse("""
        private data Maybe<T> { Nothing, Just(T) }

        private fn unwrap_or(@Maybe<Int>, @Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          match @Maybe<Int>.0 {
            Nothing -> @Int.0,
            Just(@Int) -> @Int.0
          }
        }
        """)

    def test_wildcard_pattern(self) -> None:
        parse("""
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          match @Int.0 {
            0 -> 1,
            _ -> 0
          }
        }
        """)


class TestEffects:
    def test_pure(self) -> None:
        parse("private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 }")

    def test_single_effect(self) -> None:
        parse("private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) { () }")

    def test_parameterized_effect(self) -> None:
        parse("private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<State<Int>>) { () }")

    def test_multiple_effects(self) -> None:
        parse("private fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<State<Int>, IO>) { () }")

    def test_effect_declaration(self) -> None:
        parse("""
        effect Console {
          op print(String -> Unit);
          op read_line(Unit -> String);
        }
        """)

    def test_handler(self) -> None:
        parse("""
        private fn f(@Unit -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          handle[State<Int>](@Int = 0) {
            get(@Unit) -> { resume(@Int.0) },
            put(@Int) -> { resume(()) }
          } in {
            put(42);
            get(())
          }
        }
        """)


class TestBlocks:
    def test_let_binding(self) -> None:
        parse("""
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let @Int = @Int.0 + 1;
          @Int.0
        }
        """)

    def test_multiple_statements(self) -> None:
        parse("""
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let @Int = @Int.0 + 1;
          let @Int = @Int.0 * 2;
          @Int.0
        }
        """)

    def test_expression_statement(self) -> None:
        parse("""
        private fn f(@Unit -> @Unit)
          requires(true)
          ensures(true)
          effects(<IO>)
        {
          print("hello");
          ()
        }
        """)


class TestContracts:
    def test_old_new_in_ensures(self) -> None:
        parse("""
        private fn f(@Unit -> @Unit)
          requires(true)
          ensures(new(State<Int>) == old(State<Int>) + 1)
          effects(<State<Int>>)
        {
          ()
        }
        """)

    def test_result_reference(self) -> None:
        parse("""
        private fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          @Int.0
        }
        """)


class TestDataTypes:
    def test_simple_adt(self) -> None:
        parse("private data Bool { True, False }")

    def test_parameterized_adt(self) -> None:
        parse("private data Option<T> { None, Some(T) }")

    def test_adt_with_invariant(self) -> None:
        parse("""
        private data Positive invariant(@Int.0 > 0) {
          MkPositive(Int)
        }
        """)

    def test_type_alias(self) -> None:
        parse("type Name = String;")


class TestModules:
    def test_module_declaration(self) -> None:
        parse("module vera.math;")

    def test_import(self) -> None:
        parse("import vera.math;")

    def test_import_list(self) -> None:
        parse("import vera.math(abs, max);")

    def test_import_types(self) -> None:
        parse("import vera.collections(List, Option);")

    def test_visibility(self) -> None:
        parse("""
        public fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }
        """)


class TestComments:
    def test_line_comment(self) -> None:
        parse("""
        -- this is a comment
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0 -- inline comment
        }
        """)

    def test_block_comment(self) -> None:
        parse("""
        {- block comment -}
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }
        """)

    def test_nested_block_comment(self) -> None:
        # Spec 1.3: block comments nest -- a `{-` inside a block comment
        # begins a nested comment that must be closed by its own `-}`
        # (#1112).  A non-greedy regex terminal closes at the FIRST `-}`,
        # leaving `still outer -}` as stray tokens.
        parse("""
        {- outer {- inner -} still outer -}
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }
        """)

    def test_deeply_nested_block_comment(self) -> None:
        parse("""
        {- one {- two {- three -} two -} one -}
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }
        """)

    def test_unterminated_block_comment_reports_e020(self) -> None:
        # The grammar only sees the wreckage a malformed comment leaves
        # behind.  For this input the old non-greedy regex matched through
        # the *inner* `-}`, so the failure surfaced as a missing-contract
        # complaint at end of input — lines away from the `{-` at fault
        # (#1112).  "Unexpected `{`" was the shape when no `-}` appeared
        # anywhere in the file.
        with pytest.raises(ParseError) as exc:
            parse("{- outer {- inner -}\nprivate fn f(@Int -> @Int)\n")
        assert exc.value.diagnostic.error_code == "E020"
        assert exc.value.diagnostic.location.line == 1

    def test_unterminated_annotation_comment_reports_e021(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse("/* never closed\nprivate fn f(@Int -> @Int)\n")
        assert exc.value.diagnostic.error_code == "E021"

    def test_nested_annotation_comment_reports_e023(self) -> None:
        # Annotation comments do not nest (spec 1.3): the span closes at
        # the first `*/`, so the diagnostic points at the INNER `/*` the
        # author expected to nest, not at the trailing `*/` the grammar
        # chokes on.
        with pytest.raises(ParseError) as exc:
            parse("/* a /* b */ */\nprivate fn f(@Int -> @Int)\n")
        assert exc.value.diagnostic.error_code == "E023"
        assert exc.value.diagnostic.location.column == 6

    def test_unterminated_nested_block_comment_is_rejected(self) -> None:
        # The inner comment closes, the outer never does.  Nesting must
        # not make an unbalanced comment silently swallow the rest of
        # the file -- it stays a parse error.
        with pytest.raises(ParseError):
            parse("""
        {- outer {- inner -}
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }
        """)

    def test_annotation_comment(self) -> None:
        parse("""
        private fn add(@Int /* left */, @Int /* right */ -> @Int /* sum */)
          requires(true)
          ensures(@Int.result == @Int.0 + @Int.1)
          effects(pure)
        {
          @Int.0 + @Int.1
        }
        """)

    def test_annotation_comment_standalone(self) -> None:
        parse("""
        /* Helper function */
        private fn id(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }
        """)

    def test_mixed_comments(self) -> None:
        parse("""
        -- Line comment
        {- Block comment -}
        /* Annotation comment */
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }
        """)


class TestAnnotationRetention:
    """Annotation comments survive into the AST (spec 1.3, #1112).

    Spec 1.3 calls annotation comments "optional human-readable labels
    for bindings" and states they are "preserved in the AST".  They are
    the readability that De Bruijn slot references give up: ``@Int.0``
    says *where* a value comes from but never *what it means*, so the
    label belongs to the slot's position, not to its type.
    """

    def test_params_carry_their_labels(self) -> None:
        ast = parse_to_ast("""
        private fn add(@Int /* left */, @Int /* right */ -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0 + @Int.1
        }
        """)
        fn = ast.declarations[0].decl
        assert fn.param_annotations == ("left", "right")

    def test_return_slot_carries_its_label(self) -> None:
        ast = parse_to_ast("""
        private fn add(@Int, @Int -> @Int /* sum */)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0 + @Int.1
        }
        """)
        fn = ast.declarations[0].decl
        assert fn.return_annotation == "sum"

    def test_unlabelled_slots_carry_no_label(self) -> None:
        """The negative direction, so a wrong-but-defaulted field cannot pass.

        Without this, an implementation that returned ``("left", "right")``
        unconditionally would be indistinguishable from a correct one on
        the positive tests alone.
        """
        ast = parse_to_ast("""
        private fn add(@Int, @Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0 + @Int.1
        }
        """)
        fn = ast.declarations[0].decl
        assert fn.param_annotations == (None, None)
        assert fn.return_annotation is None

    def test_partially_labelled_params_keep_their_positions(self) -> None:
        """A label belongs to a slot index, so gaps must not shift it.

        Labelling only the second parameter is the case that separates
        positional storage from "collect the labels in order" — the
        latter would report ``("right",)`` and mis-attribute it to slot 0.
        """
        ast = parse_to_ast("""
        private fn add(@Int, @Int /* right */ -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0 + @Int.1
        }
        """)
        fn = ast.declarations[0].decl
        assert fn.param_annotations == (None, "right")

    def test_two_labels_on_one_line_both_survive(self) -> None:
        """The spec's own example, and the case a line-keyed store cannot hold.

        ``_Attached.inline`` *was* ``dict[int, Comment]`` keyed by line,
        so it structurally admitted one comment per line; both labels here sit
        on the signature line.  Retention therefore cannot be built on
        that container (#1123).
        """
        ast = parse_to_ast("""
        private fn area(@Int /* width */, @Int /* height */ -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0 * @Int.1
        }
        """)
        fn = ast.declarations[0].decl
        assert fn.param_annotations == ("width", "height")

    def test_where_helper_slots_carry_their_labels(self) -> None:
        """Helpers are functions too, so the walk has to recurse.

        Without the ``where_fns`` recursion the outer function's labels
        still resolve, so every other test here passes while helpers
        silently lose theirs.
        """
        ast = parse_to_ast("""
        private fn outer(@Int /* outer_in */ -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          double(@Int.0)
        }
        where {
          fn double(@Int /* inner_in */ -> @Int /* doubled */)
            requires(true)
            ensures(true)
            effects(pure)
          {
            @Int.0 * 2
          }
        }
        """)
        fn = ast.declarations[0].decl
        assert fn.param_annotations == ("outer_in",)
        helper = fn.where_fns[0]
        assert helper.param_annotations == ("inner_in",)
        assert helper.return_annotation == "doubled"


# =====================================================================
# Tests for previously untested grammar constructs
# =====================================================================


class TestAnonymousFunctions:
    def test_closure_as_argument(self) -> None:
        parse("""
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          map(@Int.0, fn(@Int -> @Int) effects(pure) { @Int.0 * 2 })
        }
        """)

    def test_fn_type_alias(self) -> None:
        """Function types use type aliases for slot references."""
        parse("""
        type IntToInt = fn(Int -> Int) effects(pure);

        private fn apply(@IntToInt, @Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          apply_fn(@IntToInt.0, @Int.0)
        }
        """)

    def test_closure_in_let(self) -> None:
        """Anonymous functions can be bound in let statements."""
        parse("""
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let @Int = apply(fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }, @Int.0);
          @Int.0
        }
        """)


class TestGenerics:
    def test_forall_single_type_var(self) -> None:
        parse("""
        private forall<T> fn identity(@T -> @T)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @T.0
        }
        """)

    def test_forall_multiple_type_vars(self) -> None:
        parse("""
        private forall<A, B> fn const(@A, @B -> @A)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @A.0
        }
        """)

    def test_generic_data_type_multiple_params(self) -> None:
        parse("""
        private data Either<L, R> {
          Left(L),
          Right(R)
        }
        """)

    def test_generic_function_call(self) -> None:
        parse("""
        private forall<T> fn wrap(@T -> @Option<T>)
          requires(true)
          ensures(true)
          effects(pure)
        {
          Some(@T.0)
        }
        """)


class TestRefinementTypes:
    def test_refinement_type_alias(self) -> None:
        parse("type PosInt = { @Int | @Int.0 > 0 };")

    def test_refinement_via_type_alias(self) -> None:
        """Refined types in signatures use a type alias since @{...} isn't valid."""
        parse("""
        type NonNegInt = { @Int | @Int.0 >= 0 };

        private fn sqrt(@NonNegInt -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          @NonNegInt.0
        }
        """)

    def test_parameterized_refinement_alias(self) -> None:
        parse("type NonEmpty<T> = { @Array<T> | array_length(@Array<T>.0) > 0 };")


class TestTupleDestructuring:
    def test_basic_destruct(self) -> None:
        parse("""
        private fn swap(@Tuple<Int, String> -> @Tuple<String, Int>)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let Tuple<@Int, @String> = @Tuple<Int, String>.0;
          make_tuple(@String.0, @Int.0)
        }
        """)


class TestQuantifiers:
    def test_forall_expr(self) -> None:
        parse("""
        private fn all_positive(@Array<Int> -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        {
          forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
            @Array<Int>.0[@Int.0] > 0
          })
        }
        """)

    def test_exists_expr(self) -> None:
        parse("""
        private fn has_zero(@Array<Int> -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        {
          exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
            @Array<Int>.0[@Int.0] == 0
          })
        }
        """)


class TestAssertAssume:
    def test_assert(self) -> None:
        parse("""
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          assert(@Int.0 > 0);
          @Int.0
        }
        """)

    def test_assume(self) -> None:
        parse("""
        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          assume(@Int.0 > 0);
          @Int.0
        }
        """)


class TestQualifiedCalls:
    def test_effect_qualified_call(self) -> None:
        parse("""
        private fn f(@Unit -> @Int)
          requires(true)
          ensures(true)
          effects(<State<Int>>)
        {
          State.get(())
        }
        """)

    def test_import_and_direct_call(self) -> None:
        """After importing, call functions directly via bare calls."""
        parse("""
        import vera.math(abs);

        private fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          abs(@Int.0)
        }
        """)


class TestModuleQualifiedCalls:
    """Module-qualified calls use :: syntax (#95)."""

    def test_single_segment_module_call(self) -> None:
        """Single-segment path: math::abs(42)."""
        parse("""
        import math;
        private fn f(@Int -> @Int)
          requires(true) ensures(true) effects(pure)
        { math::abs(@Int.0) }
        """)

    def test_multi_segment_module_call(self) -> None:
        """Multi-segment path: vera.math::abs(42)."""
        parse("""
        import vera.math;
        private fn f(@Int -> @Int)
          requires(true) ensures(true) effects(pure)
        { vera.math::abs(@Int.0) }
        """)

    def test_module_call_no_args(self) -> None:
        """Module-qualified call with no arguments."""
        parse("""
        import util;
        private fn f(@Unit -> @Int)
          requires(true) ensures(true) effects(pure)
        { util::get_value() }
        """)

    def test_module_call_multiple_args(self) -> None:
        """Module-qualified call with multiple arguments."""
        parse("""
        import math;
        private fn f(@Int, @Int -> @Int)
          requires(true) ensures(true) effects(pure)
        { math::max(@Int.0, @Int.1) }
        """)

    def test_module_call_in_expression(self) -> None:
        """Module-qualified call nested in an expression."""
        parse("""
        import math;
        private fn f(@Int -> @Int)
          requires(true) ensures(true) effects(pure)
        { math::abs(@Int.0) + 1 }
        """)

    def test_old_dot_syntax_rejected(self) -> None:
        """Old dot syntax produces a 'did you mean ::' error (E008)."""
        with pytest.raises(ParseError, match="::"):
            parse("""
            import math;
            private fn f(@Int -> @Int)
              requires(true) ensures(true) effects(pure)
            { math.abs(@Int.0) }
            """)


class TestFunctionTypes:
    def test_fn_type_alias_in_signature(self) -> None:
        """Function types in signatures use type aliases."""
        parse("""
        type Mapper = fn(Int -> Int) effects(pure);

        private fn apply(@Mapper, @Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          apply_fn(@Mapper.0, @Int.0)
        }
        """)

    def test_fn_type_alias_with_effects(self) -> None:
        """Function types with effects use type aliases."""
        parse("""
        type Action = fn(Unit -> Unit) effects(<IO>);

        private fn run(@Action -> @Unit)
          requires(true)
          ensures(true)
          effects(<IO>)
        {
          run_action(@Action.0)
        }
        """)

    def test_fn_type_in_type_alias(self) -> None:
        """fn type expressions work in type alias declarations."""
        parse("type Predicate = fn(Int -> Bool) effects(pure);")
        parse("type Callback = fn(String -> Unit) effects(<IO>);")


class TestFloatLiterals:
    def test_float_in_expression(self) -> None:
        parse("""
        private fn f(@Unit -> @Float64)
          requires(true)
          ensures(true)
          effects(pure)
        {
          3.14
        }
        """)

    def test_float_arithmetic(self) -> None:
        parse("""
        private fn f(@Float64 -> @Float64)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Float64.0 * 2.0 + 1.5
        }
        """)


class TestNestedPatterns:
    def test_nested_constructor_pattern(self) -> None:
        parse("""
        private data Option<T> { None, Some(T) }
        private data List<T> { Nil, Cons(T, List<T>) }

        private fn head_or_zero(@List<Option<Int>> -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          match @List<Option<Int>>.0 {
            Cons(Some(@Int), @List<Option<Int>>) -> @Int.0,
            _ -> 0
          }
        }
        """)

    def test_literal_and_wildcard_patterns(self) -> None:
        parse("""
        private fn describe(@Int -> @String)
          requires(true)
          ensures(true)
          effects(pure)
        {
          match @Int.0 {
            0 -> "zero",
            1 -> "one",
            _ -> "other"
          }
        }
        """)


class TestHandlerVariations:
    def test_handler_without_state(self) -> None:
        parse("""
        private fn f(@Unit -> @Option<Int>)
          requires(true)
          ensures(true)
          effects(pure)
        {
          handle[Exn<String>] {
            throw(@String) -> { None }
          } in {
            let @Int = risky(());
            Some(@Int.0)
          }
        }
        """)

    def test_handler_multiple_clauses(self) -> None:
        parse("""
        private fn f(@Unit -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          handle[State<Int>](@Int = 0) {
            get(@Unit) -> { resume(@Int.0) },
            put(@Int) -> { resume(()) }
          } in {
            let @Int = State.get(());
            State.put(@Int.0 + 1);
            State.get(())
          }
        }
        """)

    def test_handler_with_qualified_effect(self) -> None:
        parse("""
        private fn f(@Unit -> @String)
          requires(true)
          ensures(true)
          effects(pure)
        {
          handle[Console] {
            print(@String) -> { resume(()) },
            read_line(@Unit) -> { resume("input") }
          } in {
            Console.print("hello");
            Console.read_line(())
          }
        }
        """)


    def test_handler_with_clause(self) -> None:
        """Handler clause with state update parses."""
        parse("""
        private fn f(@Unit -> @Int)
          requires(true) ensures(true) effects(pure)
        {
          handle[State<Int>](@Int = 0) {
            get(@Unit) -> { resume(@Int.0) },
            put(@Int) -> { resume(()) } with @Int = @Int.0
          } in {
            get(())
          }
        }
        """)

    def test_handler_with_clause_ast(self) -> None:
        """Handler with-clause populates state_update on HandlerClause."""
        from vera.parser import parse_to_ast
        prog = parse_to_ast("""
private fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    get(())
  }
}
""")
        fn = prog.declarations[0].decl
        clauses = fn.body.expr.clauses
        assert clauses[0].state_update is None
        assert clauses[1].state_update is not None
        upd_te, upd_expr = clauses[1].state_update
        assert upd_te.name == "Int"


class TestImpliesOperator:
    def test_implies_in_contract(self) -> None:
        parse("""
        private fn f(@Int -> @Int)
          requires(@Int.0 > 0 ==> @Int.0 < 100)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }
        """)

    def test_implies_right_associative(self) -> None:
        parse("""
        private fn f(@Bool, @Bool, @Bool -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Bool.0 ==> @Bool.1 ==> @Bool.2
        }
        """)


# =====================================================================
# Error case tests — verify that invalid programs produce ParseError
# =====================================================================


class TestParseErrors:
    def test_missing_contract_block(self) -> None:
        with pytest.raises(ParseError):
            parse("private fn f(@Int -> @Int) { @Int.0 }")

    def test_missing_effects(self) -> None:
        with pytest.raises(ParseError):
            parse("private fn f(@Int -> @Int) requires(true) ensures(true) { @Int.0 }")

    def test_missing_body(self) -> None:
        with pytest.raises(ParseError):
            parse("private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)")

    def test_unclosed_brace(self) -> None:
        with pytest.raises(ParseError):
            parse("private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0")

    def test_invalid_token(self) -> None:
        with pytest.raises(ParseError):
            parse("private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { $ }")


# =====================================================================
# old() / new() argument diagnostics (#1173)
# =====================================================================


def _bump(clauses: str) -> str:
    """A one-function program whose contract block is `clauses`."""
    return (
        "public fn bump(@Int -> @Int)\n"
        f"{clauses}\n"
        "  effects(pure)\n"
        "{ @Int.0 + 1 }\n"
    )


class TestOldNewArgumentDiagnostic:
    """`old(...)` / `new(...)` applied to an expression rather than an
    effect reference (#1173, VeraBench VB-T5-009).

    Vera's `old`/`new` take an *effect* reference — `old(State<Int>)`,
    spec 7.9.2 — not a Dafny-style arbitrary expression.  A model that
    reaches for `old(@Int.0)` used to get E005 "Unexpected @ ... Expected
    UPPER_IDENT" with the caret on the argument, which names neither the
    construct at fault nor the rule it breaks.
    """

    def test_old_slot_ref_reports_e030(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(@Int.0) > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E030"

    def test_caret_lands_on_old_not_its_argument(self) -> None:
        # The author's mistake is the `old(`, not the `@` two columns to
        # its right that the parser happens to choke on.
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(@Int.0) > 0)\n  ensures(true)"))
        loc = exc.value.diagnostic.location
        assert loc.line == 2
        assert loc.column == 12  # the `o` of `old`, not the `@` at 16

    def test_message_names_old_and_ensures(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(@Int.0) > 0)\n  ensures(true)"))
        diag = exc.value.diagnostic
        assert "old()" in diag.description
        assert "ensures()" in diag.description
        assert "effect reference" in diag.description
        # The fix must show the form that actually works.
        assert "State<Int>" in diag.fix

    def test_diagnostic_carries_every_field(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(@Int.0) > 0)\n  ensures(true)"))
        diag = exc.value.diagnostic
        assert diag.error_code == "E030"
        assert diag.description and diag.rationale and diag.fix
        assert diag.spec_ref and diag.error_code
        assert diag.source_line == "  requires(old(@Int.0) > 0)"

    def test_rationale_explains_pre_state(self) -> None:
        # requires()/decreases() are evaluated before the body runs, so
        # they already observe the pre-state.
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(@Int.0) > 0)\n  ensures(true)"))
        rationale = exc.value.diagnostic.rationale
        assert "requires()" in rationale
        assert "decreases()" in rationale

    def test_fires_inside_ensures_too(self) -> None:
        # The argument is wrong wherever it appears — moving it into
        # ensures() would not help, so the diagnostic must not be
        # conditioned on the enclosing clause.
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(true)\n  ensures(old(@Int.0) > 0)"))
        assert exc.value.diagnostic.error_code == "E030"
        assert exc.value.diagnostic.location.line == 3
        assert exc.value.diagnostic.location.column == 11

    def test_nested_in_a_larger_requires_expression(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(@Int.0) > 0 && true)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E030"
        assert exc.value.diagnostic.location.column == 12

    def test_in_decreases_clause(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump(
                "  requires(true)\n  ensures(true)\n  decreases(old(@Int.0))"
            ))
        assert exc.value.diagnostic.error_code == "E030"
        assert exc.value.diagnostic.location.line == 4
        assert exc.value.diagnostic.location.column == 13

    def test_arbitrary_expression_argument(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(@Int.0 + 1) > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E030"

    def test_call_argument(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(helper(())) > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E030"

    def test_result_ref_argument(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(true)\n  ensures(old(@Int.result) > 0)"))
        assert exc.value.diagnostic.error_code == "E030"

    def test_empty_argument(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old() > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E030"

    def test_whitespace_before_argument(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(  @Int.0) > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E030"
        assert exc.value.diagnostic.location.column == 12

    def test_whitespace_between_keyword_and_parenthesis(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old (@Int.0) > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E030"
        assert exc.value.diagnostic.location.column == 12

    def test_argument_on_a_later_line(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(\n    @Int.0) > 0)\n  ensures(true)"))
        diag = exc.value.diagnostic
        assert diag.error_code == "E030"
        # The caret follows `old` to line 2, not the argument on line 3.
        assert diag.location.line == 2
        assert diag.location.column == 12

    def test_invalid_character_argument(self) -> None:
        # `$` is not a Vera token at all, so Lark raises
        # UnexpectedCharacters rather than UnexpectedToken; the
        # diagnostic must be the same.
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old($x) > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E030"
        assert exc.value.diagnostic.location.column == 12

    def test_new_reports_e031(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(true)\n  ensures(new(@Int.0) > 0)"))
        diag = exc.value.diagnostic
        assert diag.error_code == "E031"
        assert "new()" in diag.description
        assert diag.location.column == 11

    # --- the detector must not over-fire ---

    def test_effect_reference_argument_still_parses(self) -> None:
        parse(
            "private fn tick(@Unit -> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result == old(State<Int>)"
            " && new(State<Int>) == old(State<Int>) + 1)\n"
            "  effects(<State<Int>>)\n"
            "{ let @Int = get(()); put(@Int.0 + 1); @Int.0 }\n"
        )

    def test_unclosed_effect_reference_is_not_attributed_to_old(self) -> None:
        # `State<Int>` parsed fine here; the failure is the missing `)`,
        # several tokens later.  A scan that walked back to the nearest
        # `(` would reach `old(` and blame it for someone else's typo, so
        # the detector fires only at the argument's *first* token.
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old(State<Int> > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E005"

    def test_unrelated_parse_error_still_reports_e005(self) -> None:
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(@Int.0 > > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E005"

    def test_identifier_ending_in_old_is_not_matched(self) -> None:
        # `keep_old(` ends in the same four characters as `old(` — and
        # the failure here IS on the first token of its argument list, so
        # only the identifier-boundary check separates the two.
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(keep_old(> 0) > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E005"

    def test_keyword_without_its_parenthesis_is_not_matched(self) -> None:
        # `old` with no argument list at all: there is no argument
        # position to diagnose, so this stays a generic parse error.
        with pytest.raises(ParseError) as exc:
            parse(_bump("  requires(old > 0)\n  ensures(true)"))
        assert exc.value.diagnostic.error_code == "E005"


# =====================================================================
# typecheck_file tests
# =====================================================================


class TestTypecheckFile:
    """Tests for the typecheck_file convenience function."""

    def test_typecheck_file_valid(self, tmp_path: Path) -> None:
        """typecheck_file returns empty diagnostics for valid code."""
        src = tmp_path / "ok.vera"
        src.write_text(
            "private fn f(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 }\n",
            encoding="utf-8",
        )
        diags = typecheck_file(src)
        errors = [d for d in diags if d.severity == "error"]
        assert errors == []

    def test_typecheck_file_with_error(self, tmp_path: Path) -> None:
        """typecheck_file reports type errors in the file."""
        src = tmp_path / "bad.vera"
        src.write_text(
            "private fn f(@Int -> @Bool)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 }\n",
            encoding="utf-8",
        )
        diags = typecheck_file(src)
        errors = [d for d in diags if d.severity == "error"]
        assert len(errors) >= 1

    def test_typecheck_file_accepts_str_path(self, tmp_path: Path) -> None:
        """typecheck_file also accepts a plain string path."""
        src = tmp_path / "str_path.vera"
        src.write_text(
            "private fn f(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 42 }\n",
            encoding="utf-8",
        )
        diags = typecheck_file(str(src))
        errors = [d for d in diags if d.severity == "error"]
        assert errors == []

    @staticmethod
    def _importing_pair(tmp_path: Path) -> Path:
        """An entry calling a function a sibling module exports."""
        (tmp_path / "tflib.vera").write_text(
            "module tflib;\n\n"
            "public fn twice(@Int -> @Int)\n"
            "  requires(true) ensures(@Int.result == @Int.0 * 2) "
            "effects(pure)\n"
            "{ @Int.0 * 2 }\n",
            encoding="utf-8",
        )
        entry = tmp_path / "entry.vera"
        entry.write_text(
            "import tflib(twice);\n\n"
            "public fn f(@Int -> @Int)\n"
            "  requires(true) ensures(@Int.result == @Int.0 * 2) "
            "effects(pure)\n"
            "{ twice(@Int.0) }\n",
            encoding="utf-8",
        )
        return entry

    def test_typecheck_file_resolves_imports(self, tmp_path: Path) -> None:
        """typecheck_file resolves imports as `vera check` does (#1513).

        An unresolved call is an error, so a module-blind check reported
        every imported name as one."""
        diags = typecheck_file(self._importing_pair(tmp_path))
        assert [d.error_code for d in diags] == []

    def test_verify_file_resolves_imports(self, tmp_path: Path) -> None:
        """verify_file resolves imports too, so the callee's postcondition
        proves the caller's (#1513); module-blind, the call was opaque and
        the `ensures` fell to Tier 3 with an E522."""
        result = verify_file(self._importing_pair(tmp_path))
        assert [d.error_code for d in result.diagnostics] == []
        ensures = [o.status for o in result.obligations
                   if o.fn_name == "f" and o.kind == "ensures"]
        assert ensures == ["verified"]


# =====================================================================
# verify_file tests
# =====================================================================


# One program per way `vera verify` stops before verifying: an import nothing
# resolves, a bare or module-qualified call to nothing, and a type error.  Each
# is (imports, body) of a function with a contract, so a verify_file that went
# on past the error would report obligations for it.
_VERIFY_REFUSED: dict[str, tuple[str, str]] = {
    "unresolved_import": ("import nosuch(g);\n\n", "1"),
    "unresolved_call": ("", "no_such_fn(1)"),
    "unresolved_module_call": ("", "nomod::g(1)"),
    "type_error": ("", "true"),
}


class TestVerifyFile:
    """Tests for the verify_file convenience function."""

    def test_verify_file_valid(self, tmp_path: Path) -> None:
        """verify_file returns a VerifyResult for valid code."""
        src = tmp_path / "ok.vera"
        src.write_text(
            "private fn f(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 }\n",
            encoding="utf-8",
        )
        result = verify_file(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Expected no errors, got: {[e.description for e in errors]}"
        assert result.summary is not None
        assert result.summary.total > 0

    def test_verify_file_accepts_str_path(self, tmp_path: Path) -> None:
        """verify_file also accepts a plain string path."""
        src = tmp_path / "str_path.vera"
        src.write_text(
            "private fn f(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 42 }\n",
            encoding="utf-8",
        )
        result = verify_file(str(src))
        assert result.summary is not None
        assert result.summary.total > 0

    @staticmethod
    def _vera_verify_errors(path: Path) -> list[str]:
        """The error codes `vera verify --json` stops with, run in process."""
        import contextlib
        import io
        import json

        from vera.cli import cmd_verify

        out = io.StringIO()
        with contextlib.redirect_stdout(out), \
                contextlib.redirect_stderr(io.StringIO()):
            rc = cmd_verify(str(path), as_json=True)
        assert rc == 1
        return [d["error_code"]
                for d in json.loads(out.getvalue())["diagnostics"]]

    @pytest.mark.parametrize("case", sorted(_VERIFY_REFUSED))
    def test_verify_file_stops_where_vera_verify_stops(
        self, case: str, tmp_path: Path,
    ) -> None:
        """verify_file returns the errors `vera verify` stops with, and
        verifies nothing past them.  It verified past them, so a program
        `vera verify` refuses came back verified, or with an E522 warning
        for the call it could not see (#1513)."""
        imports, body = _VERIFY_REFUSED[case]
        src = tmp_path / "prog.vera"
        src.write_text(
            imports
            + "public fn f(@Unit -> @Int)\n"
            "  requires(true) ensures(@Int.result == 1) effects(pure)\n"
            "{ " + body + " }\n",
            encoding="utf-8",
        )
        result = verify_file(src)
        errors = [d.error_code for d in result.diagnostics
                  if d.severity == "error"]
        assert errors, result.diagnostics
        assert errors == self._vera_verify_errors(src)
        assert result.obligations == []
        assert result.summary.total == 0

    def test_verify_file_returns_the_checkers_warnings(
        self, tmp_path: Path,
    ) -> None:
        """A program that checks with a warning is verified, and the
        warning comes back with the result, as `vera verify` reports it."""
        src = tmp_path / "warn.vera"
        src.write_text(
            "public fn f(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n  match 3 {\n    _ -> 1,\n    3 -> 2\n  }\n}\n",
            encoding="utf-8",
        )
        result = verify_file(src)
        assert [(d.severity, d.error_code) for d in result.diagnostics] == [
            ("warning", "E310")]
        assert result.summary.total > 0
