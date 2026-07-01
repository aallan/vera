"""Tests for the Vera type checker — types (primitive types, ADTs, generics, constructors, arrays, tuples, refinement, literal ranges).

Split from tests/test_checker.py (#420). Shared helpers live in tests/checker_helpers.py.
"""
from __future__ import annotations

from tests.checker_helpers import (
    _check_err,
    _check_ok,
    _errors,
    _warnings,
)


# =====================================================================
# Literals
# =====================================================================

class TestLiterals:

    def test_int_lit(self) -> None:
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
""")

    def test_negative_int_lit(self) -> None:
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 - 1 }
""")

    def test_float_lit(self) -> None:
        _check_ok("""
private fn foo(@Unit -> @Float64)
  requires(true) ensures(true) effects(pure)
{ 3.14 }
""")

    def test_string_lit(self) -> None:
        _check_ok("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }
""")

    def test_bool_lit(self) -> None:
        _check_ok("""
private fn foo(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ true }
""")

    def test_unit_lit(self) -> None:
        _check_ok("""
private fn foo(@Unit -> @Unit)
  requires(true) ensures(true) effects(pure)
{ () }
""")

    def test_float_alias_rejected(self) -> None:
        """'Float' is not a type — only 'Float64' is accepted (#76)."""
        _check_err("""
private fn foo(@Unit -> @Float)
  requires(true) ensures(true) effects(pure)
{ 3.14 }
""", "'Float' is not a type. Did you mean 'Float64'?")

    # --- Byte literal coercion (#241) ---

    def test_byte_lit_coercion(self) -> None:
        """Integer literal 0–255 accepted as Byte when expected type is Byte."""
        _check_ok("""
private fn foo(@Unit -> @Byte)
  requires(true) ensures(true) effects(pure)
{ 65 }
""")

    def test_byte_lit_zero(self) -> None:
        """Boundary: 0 accepted as Byte."""
        _check_ok("""
private fn foo(@Unit -> @Byte)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")

    def test_byte_lit_max(self) -> None:
        """Boundary: 255 accepted as Byte."""
        _check_ok("""
private fn foo(@Unit -> @Byte)
  requires(true) ensures(true) effects(pure)
{ 255 }
""")

    def test_byte_lit_overflow_rejected(self) -> None:
        """256 is out of Byte range — should be rejected."""
        _check_err("""
private fn foo(@Unit -> @Byte)
  requires(true) ensures(true) effects(pure)
{ 256 }
""", "body has type")

    def test_byte_lit_negative_rejected(self) -> None:
        """Negative integer is not a valid Byte."""
        _check_err("""
private fn foo(@Unit -> @Byte)
  requires(true) ensures(true) effects(pure)
{ 0 - 1 }
""", "body has type")


# =====================================================================
# Binary operators
# =====================================================================

class TestBinaryOps:

    def test_add_int(self) -> None:
        _check_ok("""
private fn foo(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }
""")

    def test_add_float(self) -> None:
        _check_ok("""
private fn foo(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ @Float64.0 + @Float64.1 }
""")

    def test_add_mixed_error(self) -> None:
        _check_err("""
private fn bad(@Int, @String -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @String.0 }
""", "requires numeric operands")

    def test_comparison(self) -> None:
        _check_ok("""
private fn foo(@Int, @Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 < @Int.1 }
""")

    def test_equality(self) -> None:
        _check_ok("""
private fn foo(@Int, @Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 == @Int.1 }
""")

    def test_logical_and(self) -> None:
        _check_ok("""
private fn foo(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 && @Bool.1 }
""")

    def test_logical_implies(self) -> None:
        _check_ok("""
private fn foo(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 ==> @Bool.1 }
""")

    def test_logical_not_bool_error(self) -> None:
        _check_err("""
private fn bad(@Int, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 && @Bool.0 }
""", "must be Bool")

    def test_modulo(self) -> None:
        _check_ok("""
private fn foo(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 % @Int.1 }
""")


# =====================================================================
# Unary operators
# =====================================================================

class TestUnaryOps:

    def test_not(self) -> None:
        _check_ok("""
private fn foo(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ !@Bool.0 }
""")

    def test_neg(self) -> None:
        _check_ok("""
private fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 - @Int.0 }
""")

    def test_not_non_bool_error(self) -> None:
        errs = _check_err("""
private fn bad(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ !@Int.0 }
""", "requires Bool operand")
        assert any(e.error_code == "E146" for e in errs)


# =====================================================================
# Generic functions
# =====================================================================

class TestGenerics:

    def test_identity(self) -> None:
        _check_ok("""
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }
""")

    def test_generic_call(self) -> None:
        _check_ok("""
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(@Int.0) }
""")

    # -- Rejection tests: TypeVar vs concrete should now fail ------

    def test_typevar_body_vs_concrete_return(self) -> None:
        """TypeVar body should NOT satisfy a concrete return type."""
        _check_err("""
private forall<T> fn bad(@T -> @Int)
  requires(true) ensures(true) effects(pure)
{ @T.0 }
""", "T")

    def test_concrete_body_vs_typevar_return(self) -> None:
        """Concrete body should NOT satisfy a TypeVar return type."""
        _check_err("""
private forall<T> fn bad(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ 42 }
""", "Nat")

    def test_typevar_in_let_binding(self) -> None:
        """TypeVar value should not bind to a concrete slot."""
        _check_err("""
private forall<T> fn bad(@T -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @T.0;
  @Int.0
}
""", "T")

    # -- Regression tests: legitimate generic patterns still work --

    def test_generic_calling_generic(self) -> None:
        _check_ok("""
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private forall<U> fn wrap(@U -> @U)
  requires(true) ensures(true) effects(pure)
{ identity(@U.0) }
""")

    def test_generic_constructor_wrapping(self) -> None:
        _check_ok("""
private data Box<T> { MkBox(T) }

private forall<T> fn wrap(@T -> @Box<T>)
  requires(true) ensures(true) effects(pure)
{ MkBox(@T.0) }
""")

    def test_generic_match_returns_typevar(self) -> None:
        _check_ok("""
private forall<T> fn unwrap_or(@Option<T>, @T -> @T)
  requires(true) ensures(true) effects(pure)
{
  match @Option<T>.0 {
    None -> @T.0,
    Some(@T) -> @T.0
  }
}
""")

    def test_generic_multi_typevar(self) -> None:
        _check_ok("""
private forall<A, B> fn const(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{ @A.0 }
""")

    def test_generic_option_some(self) -> None:
        _check_ok("""
private forall<T> fn wrap(@T -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{ Some(@T.0) }
""")

    # -- Regression tests for #293: bare None/Err in combinator calls --

    def test_none_as_first_arg_to_generic_fn(self) -> None:
        """option_unwrap_or(None, 99) must infer T=Int from the default arg."""
        _check_ok("""
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ option_unwrap_or(None, 99) }
""")

    def test_none_as_first_arg_to_option_map(self) -> None:
        """option_map(None, fn(@Int->@Int){...}) must infer A=Int, B=Int."""
        _check_ok("""
private fn test(@Unit -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ option_map(None, fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }) }
""")

    def test_err_as_first_arg_to_result_unwrap_or(self) -> None:
        """result_unwrap_or(Err("x"), false) must infer T=Bool, E=String."""
        _check_ok("""
private fn test(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ result_unwrap_or(Err("oops"), false) }
""")

    def test_ok_with_unresolvable_error_type(self) -> None:
        """result_unwrap_or(Ok(77), 0): E is genuinely unknown — must not crash."""
        _check_ok("""
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ result_unwrap_or(Ok(77), 0) }
""")

    def test_none_infers_from_second_arg_not_first(self) -> None:
        """When T is inferred from a later concrete arg, the fresh TypeVar
        placeholder from None must be overwritten, not kept."""
        _check_ok("""
private forall<T> fn pick_default(@Option<T>, @T -> @T)
  requires(true) ensures(true) effects(pure)
{
  match @Option<T>.0 {
    None -> @T.0,
    Some(@T) -> @T.0
  }
}

private fn test(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ pick_default(None, "hello") }
""")


# =====================================================================
# ADTs and constructors
# =====================================================================

class TestConstructors:

    def test_nullary_constructor(self) -> None:
        _check_ok("""
private data Color { Red, Green, Blue }

private fn foo(@Unit -> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }
""")

    def test_constructor_with_fields(self) -> None:
        _check_ok("""
private data Pair { MkPair(Int, String) }

private fn foo(@Int, @String -> @Pair)
  requires(true) ensures(true) effects(pure)
{ MkPair(@Int.0, @String.0) }
""")

    def test_constructor_arity_mismatch(self) -> None:
        errs = _check_err("""
private data Pair { MkPair(Int, String) }

private fn foo(@Int -> @Pair)
  requires(true) ensures(true) effects(pure)
{ MkPair(@Int.0) }
""", "expects 2 field")
        assert any(e.error_code == "E212" for e in errs)

    def test_parameterised_adt(self) -> None:
        _check_ok("""
private data Box<T> { MkBox(T) }

private fn foo(@Int -> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkBox(@Int.0) }
""")

    def test_unknown_constructor_call_warns_e210(self) -> None:
        """A call to an undeclared constructor warns E210, not just a message."""
        warns = _warnings("""
private data Option<T> { None, Some(T) }

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Bogus(42);
  @Int.0
}
""")
        e210 = [w for w in warns if w.error_code == "E210"]
        assert len(e210) == 1
        assert e210[0].severity == "warning"

    def test_nullary_constructor_given_args_is_e211(self) -> None:
        """Calling a nullary constructor with arguments reports E211."""
        errs = _check_err("""
private data Option<T> { None, Some(T) }

private fn f(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None(42) }
""", "nullary")
        assert any(e.error_code == "E211" for e in errs)

    def test_constructor_field_type_mismatch_is_e213(self) -> None:
        """A constructor argument of the wrong type reports E213."""
        errs = _check_err("""
private data Box { Wrap(Int) }

private fn f(@Int -> @Box)
  requires(true) ensures(true) effects(pure)
{ Wrap(true) }
""", "field 0 has type")
        assert any(e.error_code == "E213" for e in errs)

    def test_unknown_nullary_constructor_call_warns_e214(self) -> None:
        """A bare reference to an undeclared nullary constructor warns E214."""
        warns = _warnings("""
private data Option<T> { None, Some(T) }

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Bogus;
  @Int.0
}
""")
        e214 = [w for w in warns if w.error_code == "E214"]
        assert len(e214) == 1
        assert e214[0].severity == "warning"

    def test_constructor_used_as_nullary_is_e215(self) -> None:
        """Using a field-carrying constructor without arguments reports E215."""
        errs = _check_err("""
private data Option<T> { None, Some(T) }

private fn f(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some }
""", "used as nullary")
        assert any(e.error_code == "E215" for e in errs)

    def test_unresolved_qualified_call_warns_e220(self) -> None:
        """A qualified call resolving to neither effect-op nor module warns E220."""
        warns = _warnings("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = Foo.bar(42);
  @Int.0
}
""")
        e220 = [w for w in warns if w.error_code == "E220"]
        assert len(e220) == 1
        assert e220[0].severity == "warning"

    def test_data_invariant_non_bool_is_e120(self) -> None:
        """A data-type invariant whose body isn't Bool reports E120."""
        errs = _check_err("""
private data Pos invariant(42) { MkPos(Int) }

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "Invariant must be Bool")
        assert any(e.error_code == "E120" for e in errs)

    def test_data_invariant_bool_ok(self) -> None:
        """A Bool data-type invariant type-checks cleanly (no E120)."""
        _check_ok("""
private data Pos invariant(true) { MkPos(Int) }

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")


# =====================================================================
# Refinement types
# =====================================================================

class TestRefinementTypes:

    def test_refinement_alias(self) -> None:
        _check_ok("""
type PosInt = { @Int | @Int.0 > 0 };

private fn foo(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
""")

    def test_refinement_subtype_to_base(self) -> None:
        """Refinement type is subtype of its base type."""
        _check_ok("""
type PosInt = { @Int | @Int.0 > 0 };

private fn foo(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 + 1 }
""")

    def test_int_to_nat_allowed(self) -> None:
        """Int -> Nat allowed by checker; verifier enforces >= 0 via Z3."""
        _check_ok("""
private fn foo(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")


# =====================================================================
# Array operations
# =====================================================================

class TestArrays:

    def test_array_index(self) -> None:
        _check_ok("""
private fn first(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[0] }
""")

    def test_array_index_non_array_error(self) -> None:
        _check_err("""
private fn bad(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0[0] }
""", "Cannot index")

    # --- array_append (#242) ---

    def test_array_append_type_checks(self) -> None:
        """array_append(Array<T>, T) -> Array<T> type-checks cleanly."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(array_append([1, 2, 3], 4)) }
""")

    def test_array_append_string(self) -> None:
        """array_append works with String element type."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(array_append(["a", "b"], "c")) }
""")


# =====================================================================
# Array construction builtins (#209)
# =====================================================================

class TestArrayRange:

    def test_array_range_ok(self) -> None:
        """array_range(Int, Int) -> Array<Int> type-checks cleanly."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(array_range(0, 5)) }
""")

    def test_array_range_wrong_type(self) -> None:
        """array_range requires Int arguments."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(array_range("a", 5)) }
""", "type")


class TestArrayConcat:

    def test_array_concat_ok(self) -> None:
        """array_concat(Array<T>, Array<T>) -> Array<T> type-checks cleanly."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(array_concat([1, 2], [3, 4])) }
""")

    def test_array_concat_type_mismatch(self) -> None:
        """array_concat requires both arrays to have the same element type."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(array_concat([1, 2], ["a", "b"])) }
""", "type")


class TestTuple:
    """Tuple type construction, destructuring, and pattern matching."""

    def test_tuple_constructor_ok(self) -> None:
        """Tuple(42, 'hello') type-checks without E210 warning."""
        _check_ok("""
private fn f(-> @Tuple<Int, String>)
  requires(true) ensures(true) effects(pure)
{ Tuple(42, "hello") }
""")

    def test_tuple_constructor_int_int(self) -> None:
        """Tuple(1, 2) produces Tuple<Int, Int>."""
        _check_ok("""
private fn f(-> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(1, 2) }
""")

    def test_tuple_empty_error(self) -> None:
        """Tuple() with no fields is an error."""
        _check_err("""
private fn f(-> @Tuple<Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple() }
""", "at least one field")

    def test_tuple_let_destruct_ok(self) -> None:
        """let Tuple<@Int, @String> = ... type-checks."""
        _check_ok("""
private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Int, @String> = Tuple(42, "hello");
  @Int.0
}
""")

    def test_tuple_match_pattern_ok(self) -> None:
        """Tuple pattern in match binds slots correctly."""
        _check_ok("""
private fn f(@Tuple<Int, Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Tuple<Int, Int>.0 {
    Tuple(@Int, @Int) -> @Int.0 + @Int.1
  }
}
""")


# =====================================================================
# Return type checking
# =====================================================================

class TestReturnTypes:

    def test_return_type_mismatch(self) -> None:
        _check_err("""
private fn bad(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "body has type")

    def test_nat_return_from_int_body(self) -> None:
        """Int body with Nat return: allowed in C3."""
        _check_ok("""
private fn foo(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_if_nat_literal_return(self) -> None:
        """Non-negative literal should satisfy Nat return."""
        _check_ok("""
private fn foo(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 42 }
""")


# =====================================================================
# @Byte arithmetic rejection (regression for #551 disposition)
# =====================================================================

class TestByteArithmeticRejection551:
    """Pin the current convention that `@Byte` is excluded from arithmetic.

    `vera/types.py` defines `NUMERIC_TYPES = frozenset({INT, NAT,
    FLOAT64})` — `@Byte` is *deliberately* not in that set.  The
    arithmetic check in `vera/checker/expressions.py` (the
    `_check_binary` arithmetic branch and the `_check_unary` NEG
    branch) rejects any operand whose base type isn't in
    `NUMERIC_TYPES`, producing E140.

    This is the type-check-time guard that makes the runtime "@Byte
    underflow soundness hole" filed as #551 unreachable: there's no
    AST shape `BinaryExpr(SUB, @Byte, @Byte)` for the verifier or
    codegen to ever see.  #551 closed as not-a-bug; #564 captures
    the speculative *feature* (allow byte arithmetic with verified
    underflow + overflow guards) for if/when a real user driver
    emerges.

    These tests pin the current behaviour so a future widening of
    `NUMERIC_TYPES` (e.g. resolving #564 affirmatively) can't
    silently re-open the underflow hole without a corresponding
    extension of the verifier obligation + codegen guard from #520.
    """

    def test_byte_subtraction_rejected_e140(self):
        """`@Byte - @Byte` produces E140 at type-check time."""
        src = """
public fn byte_sub(@Byte, @Byte -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{ @Byte.0 - @Byte.1 }
"""
        errs = _check_err(src, "numeric")
        e140 = [e for e in errs if e.error_code == "E140"]
        assert len(e140) >= 1, (
            f"Expected E140 for @Byte - @Byte; got: "
            f"{[(e.error_code, e.description[:60]) for e in errs]}"
        )

    def test_byte_addition_rejected_e140(self):
        """`@Byte + @Byte` produces the same E140 — covers ADD."""
        src = """
public fn byte_add(@Byte, @Byte -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{ @Byte.0 + @Byte.1 }
"""
        errs = _check_err(src, "numeric")
        assert any(e.error_code == "E140" for e in errs)

    def test_byte_unary_negation_rejected_e147(self):
        """`-@Byte` produces E147 at type-check time (unary path)."""
        src = """
public fn byte_neg(@Byte -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ -@Byte.0 }
"""
        errs = _check_err(src, "numeric")
        e147 = [e for e in errs if e.error_code == "E147"]
        assert len(e147) >= 1, (
            f"Expected E147 for -@Byte; got: "
            f"{[(e.error_code, e.description[:60]) for e in errs]}"
        )

    def test_refinement_alias_does_not_bypass(self):
        """A refinement alias of @Byte still rejects arithmetic.

        `base_type()` strips refinements before the `NUMERIC_TYPES`
        check, so `type MyByte = { @Byte | true }` does not provide
        an escape hatch.  This pinning matters: if a future change
        moves the check to operate on the refined type rather than
        the base type, refinements would silently bypass the rule.
        """
        src = """
type MyByte = { @Byte | true };

public fn refined_sub(@MyByte, @MyByte -> @MyByte)
  requires(true)
  ensures(true)
  effects(pure)
{ @MyByte.0 - @MyByte.1 }
"""
        errs = _check_err(src, "numeric")
        assert any(e.error_code == "E140" for e in errs)

    def test_byte_to_int_then_arithmetic_works(self):
        """The canonical workaround: `byte_to_int` then arithmetic.

        Confirms the user-facing contract for byte-level work today:
        explicit conversion to `@Int`, do arithmetic in `@Int`, then
        (if needed) convert back via `int_to_byte`.  This is the
        idiom #564 would relax if/when adopted.
        """
        src = """
public fn byte_diff(@Byte, @Byte -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ byte_to_int(@Byte.1) - byte_to_int(@Byte.0) }
"""
        _check_ok(src)


class TestIntegerLiteralRange812:
    """#812 — integer literals must fit their target machine type (`@Int` = i64,
    `@Nat` = u64), checked at type-check time.

    Before this check the gap had two faces, both rooted in the verifier
    modeling a literal at its unbounded mathematical value while codegen emits a
    fixed-width `i64.const`:

      - LOUD: a literal >= 2^64 was accepted by `vera check`, then failed at
        codegen with an opaque `i64.const ... out of range` WAT error.
      - SILENT + UNSOUND: a literal in (i64.MAX, u64.MAX] used as `@Int` made
        `vera verify` prove `ensures(@Int.result == 18446744073709551615)` while
        the runtime returned `-1` (the i64 reinterpretation of the all-ones bit
        pattern) — the verifier proving a postcondition the runtime violates.

    Both are now a clean compile-time E149.
    """

    def _e149(self, source: str) -> None:
        errs = _errors(source)
        assert any(e.error_code == "E149" for e in errs), \
            f"expected E149, got {[(e.error_code, e.description) for e in errs]}"

    def test_literal_in_int_context_exceeding_i64_is_error(self) -> None:
        # The SILENT soundness bug: u64.MAX as @Int verified `== u64.MAX` but ran
        # to -1.  Now rejected at check time before it can reach that false proof.
        self._e149("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 18446744073709551615 }
""")

    def test_int_context_i64_max_plus_one_is_error(self) -> None:
        self._e149("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 9223372036854775808 }
""")

    def test_literal_exceeding_u64_is_error(self) -> None:
        # The LOUD case (#812 as filed): >= 2^64 previously reached codegen.
        self._e149("""
public fn f(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 18446744073709551616 }
""")

    def test_int_literal_at_i64_max_ok(self) -> None:
        _check_ok("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 9223372036854775807 }
""")

    def test_nat_literal_at_u64_max_ok(self) -> None:
        # u64.MAX is valid as @Nat — only the @Int context (and > u64.MAX) errors.
        _check_ok("""
public fn f(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 18446744073709551615 }
""")

    def test_call_arg_int_context_exceeding_i64_is_error(self) -> None:
        # The target type flows through a call argument too (bidirectional).
        self._e149("""
public fn g(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ g(18446744073709551615) }
""")

    def test_negated_i64_min_literal_ok(self) -> None:
        # i64.MIN = -(2^63): the magnitude 2^63 exceeds i64.MAX but is valid as
        # the operand of negation — the asymmetric i64 range [-2^63, 2^63-1].
        # `-N` parses as unary-minus over the magnitude literal, which is checked
        # against the u64 bound (2^63 <= u64.MAX), so i64.MIN is NOT falsely
        # rejected.  (Guards the asymmetric boundary against a future tightening.)
        _check_ok("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ -9223372036854775808 }
""")

    def test_negated_i64_min_minus_one_is_error(self) -> None:
        # SOUNDNESS: -(2^63 + 1) = -9223372036854775809 is one below i64.MIN, so
        # it is out of @Int range.  It parses as unary-minus over the magnitude
        # literal 9223372036854775809, which is <= u64.MAX — so without an
        # explicit unary-neg bound it slipped through and ran to a wrong POSITIVE
        # value (9223372036854775807), the same silent reinterpretation the
        # positive check closes.  Must be E149.
        self._e149("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ -9223372036854775809 }
""")

    def test_negated_literal_exceeding_u64_magnitude_is_error(self) -> None:
        # -(2^64): the magnitude itself exceeds u64.MAX, caught at the inner
        # literal regardless of the negation.
        self._e149("""
public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ -18446744073709551616 }
""")
