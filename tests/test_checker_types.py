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

    # --- Byte literal coercion through a refinement wrapper (#865) ---

    def test_byte_lit_coercion_refined_let(self) -> None:
        """#865 (E170 sibling): a 0..255 int literal is accepted when bound to
        a *refined* Byte let target (`{ @Byte | P }`).  Before the fix the
        coercion checked `isinstance(expected, PrimitiveType)` and did not see
        through the refinement, so the literal fell through to @Nat and the let
        binding was rejected with E170 — the same root gap as the #865
        call-argument site.  The predicate is deferred to the verifier, exactly
        as a `@Byte` value bound to a refined parameter already is."""
        _check_ok("""
private fn foo(@Unit -> @Byte)
  requires(true) ensures(true) effects(pure)
{
  let @{ @Byte | @Byte.0 < 10 } = 5;
  @Byte.0
}
""")

    def test_byte_lit_coercion_refined_let_out_of_range_rejected(self) -> None:
        """The refined-Byte coercion is bounded by the Byte range: `300` bound
        to `{ @Byte | @Byte.0 < 10 }` stays @Nat (not a Byte) and the let
        binding is rejected with E170 — proving the coercion is not a blanket
        literal→Byte acceptance."""
        _check_err("""
private fn foo(@Unit -> @Byte)
  requires(true) ensures(true) effects(pure)
{
  let @{ @Byte | @Byte.0 < 10 } = 300;
  @Byte.0
}
""", "Let binding expects")


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

    # -----------------------------------------------------------------
    # #861 — refinement predicates get contract-grade type-checking.
    # Before the fix these three passed `vera check` because the alias
    # predicate skipped well-formedness checking entirely.
    # -----------------------------------------------------------------

    def test_refinement_predicate_non_bool_rejected(self) -> None:
        """A bare value predicate (`@Int`, not a Bool) is rejected (E126).

        #861: `type T = { @Int | @Int.0 }` — the predicate types as Int,
        not Bool.  A refinement predicate must be a Bool the same way a
        `requires()` predicate must, so it gets the dedicated refinement code E126.
        """
        errs = _check_err("""
type Bad = { @Int | @Int.0 };

private fn foo(@Bad -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Bad.0 }
""", "predicate must be Bool")
        assert any(e.error_code == "E126" for e in errs), \
            f"Expected E126, got: {[e.error_code for e in errs]}"

    def test_refinement_predicate_non_bool_byte_rejected(self) -> None:
        """The issue's exact `{ @Byte | @Byte.0 }` non-Bool case (E126)."""
        errs = _check_err("""
type Bad = { @Byte | @Byte.0 };

private fn foo(@Bad -> @Bad)
  requires(true) ensures(true) effects(pure)
{ @Bad.0 }
""", "predicate must be Bool")
        assert any(e.error_code == "E126" for e in errs), \
            f"Expected E126, got: {[e.error_code for e in errs]}"

    def test_refinement_predicate_ill_typed_rejected(self) -> None:
        """A genuinely ill-typed predicate (String < Int) is rejected.

        #861: the predicate body is now type-checked, so an incompatible
        comparison surfaces (E142 — Cannot compare) instead of passing.
        """
        errs = _check_err("""
type Bad = { @String | @String.0 < 3 };

private fn foo(@Bad -> @Bad)
  requires(true) ensures(true) effects(pure)
{ @Bad.0 }
""", "compare")
        assert any(e.error_code == "E142" for e in errs), \
            f"Expected E142, got: {[e.error_code for e in errs]}"

    def test_refinement_predicate_nested_non_bool_rejected(self) -> None:
        """A non-Bool predicate NESTED in a type argument is also rejected.

        #861: refinements reach the checker through type args too
        (`Array<{ @Int | @Int.0 }>`), not only as a top-level alias body.
        """
        errs = _check_err("""
type Xs = Array<{ @Int | @Int.0 }>;

private fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "predicate must be Bool")
        assert any(e.error_code == "E126" for e in errs), \
            f"Expected E126, got: {[e.error_code for e in errs]}"

    def test_refinement_predicate_in_signature_non_bool_rejected(self) -> None:
        """A non-Bool refinement predicate written directly in a function
        signature (via a type argument) is rejected too — not only in a
        `type` alias.  #861.
        """
        errs = _check_err("""
private fn foo(@Array<{ @Int | @Int.0 }> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""", "predicate must be Bool")
        assert any(e.error_code == "E126" for e in errs), \
            f"Expected E126, got: {[e.error_code for e in errs]}"

    def test_refinement_predicate_byte_literal_comparison_ok(self) -> None:
        """`@Byte.0 < 10` stays well-typed inside a refinement predicate.

        #861 / #766: comparing a `@Byte` binder against an integer literal
        has a defined i32 runtime-guard lowering (#766's `_translate_byte_binop`),
        so the literal is typed against the Byte binder bidirectionally.  This
        must NOT regress to E142 — the ch02_byte_refinement conformance program
        depends on it.
        """
        _check_ok("""
type SmallByte = { @Byte | @Byte.0 < 10 };

private fn foo(@SmallByte -> @SmallByte)
  requires(true) ensures(true) effects(pure)
{ @SmallByte.0 }
""")

    def test_refinement_predicate_well_formed_ok(self) -> None:
        """A well-formed Bool predicate still passes (no false positives)."""
        _check_ok("""
type PosInt = { @Int | @Int.0 > 0 };
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 };

private fn foo(@PosInt -> @Percentage)
  requires(true) ensures(true) effects(pure)
{ if @PosInt.0 <= 100 then { @PosInt.0 } else { 100 } }
""")

    def test_refinement_predicate_alias_base_binder_ok(self) -> None:
        """The binder resolves through an alias base (`@Age` for `type Age = Nat`).

        #861: proves the predicate binder is bound under its *syntactic* name
        (`@Age.0`), not the resolved primitive — otherwise a well-formed
        predicate would spuriously fail to resolve its slot.
        """
        _check_ok("""
type Age = Nat;
type Adult = { @Age | @Age.0 >= 18 };

private fn f(@Adult -> @Age)
  requires(true) ensures(true) effects(pure)
{ @Adult.0 }
""")

    def test_refinement_predicate_generic_alias_ok(self) -> None:
        """A generic refinement alias's predicate checks with `T` in scope.

        #861: `type NonEmptyArray<T> = { @Array<T> | array_length(...) > 0 }`
        — the alias type param must be bound before checking the predicate.
        """
        _check_ok("""
type NonEmptyArray<T> = { @Array<T> | array_length(@Array<T>.0) > 0 };

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")

    def test_refinement_predicate_undefined_slot_rejected(self) -> None:
        """A predicate referencing a slot that is not the binder is rejected.

        #861: before the fix `{ @Int | @Foo.0 > 0 }` (no `@Foo` in scope)
        passed `vera check`; now the predicate is checked, so the dangling
        slot surfaces (E130).
        """
        errs = _check_err("""
type Bad = { @Int | @Foo.0 > 0 };

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""", "Foo")
        assert any(e.error_code == "E130" for e in errs), \
            f"Expected E130, got: {[e.error_code for e in errs]}"


class TestRefinementPredicateSites861:
    """#861 (PR #876 review): a `RefinementType` is grammatically legal at
    every `type_expr` position, and each position must route through the
    predicate well-formedness check.  The first-pass fix wired only alias
    bodies, constructor fields, and fn signatures — the ten positions below
    (let / destructure annotations, match binding patterns, anonymous-fn
    signatures, effect / ability op signatures, forall / exists binders,
    and the three handler positions) all let a non-Bool predicate escape
    `vera check`.  The let-annotation escape was the worst: check-green,
    then an uncaught `Z3Exception` inside `vera verify`'s refined-binding
    obligation (`z3.Not(<Int>)` on a non-Bool predicate sort).
    """

    @staticmethod
    def _assert_e126(source: str) -> None:
        errs = _check_err(source, "Refinement predicate must be Bool")
        assert any(e.error_code == "E126" for e in errs), \
            f"Expected E126, got: {[e.error_code for e in errs]}"

    def test_let_annotation_non_bool_rejected(self) -> None:
        """Site: `let @{ @Int | @Int.0 } = 5;` — pre-fix this passed check
        and then CRASHED `vera verify` with a raw Z3Exception."""
        self._assert_e126("""
private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @{ @Int | @Int.0 } = 5;
  0
}
""")

    def test_let_destructure_non_bool_rejected(self) -> None:
        """Site: tuple-destructure component annotation."""
        self._assert_e126("""
private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@{ @Int | @Int.0 }, @Int> = Tuple(1, 2);
  0
}
""")

    def test_match_binding_non_bool_rejected(self) -> None:
        """Site: `@{ @Int | @Int.0 } ->` match binding pattern."""
        self._assert_e126("""
private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match 5 {
    @{ @Int | @Int.0 } -> 0
  }
}
""")

    def test_anon_fn_param_non_bool_rejected(self) -> None:
        """Site: anonymous-fn parameter annotation."""
        self._assert_e126("""
private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(fn(@{ @Int | @Int.0 } -> @Int) effects(pure) { 1 }, 5)
}
""")

    def test_anon_fn_return_non_bool_rejected(self) -> None:
        """Site: anonymous-fn return annotation."""
        self._assert_e126("""
private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(fn(@Int -> @{ @Int | @Int.0 }) effects(pure) { 1 }, 5)
}
""")

    def test_effect_op_param_non_bool_rejected(self) -> None:
        """Site: effect-op parameter type.  The pre-fix comment claimed
        effect declarations "carry no refinement predicates to check" —
        wrong: `_register_effect` only resolves the base, stripping
        `RefinementType` layers without checking the predicate."""
        self._assert_e126("""
effect Log {
  op log({ @Int | @Int.0 } -> Unit);
}

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")

    def test_effect_op_return_non_bool_rejected(self) -> None:
        """Site: effect-op return type."""
        self._assert_e126("""
effect Gen {
  op next(Unit -> { @Int | @Int.0 });
}

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")

    def test_ability_op_non_bool_rejected(self) -> None:
        """Site: ability-op signature (param and return share the walker)."""
        self._assert_e126("""
ability Sized<T> {
  op size({ @Int | @Int.0 } -> { @Int | @Int.0 });
}

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")

    def test_forall_binder_non_bool_rejected(self) -> None:
        """Site: forall(...) binder type annotation."""
        self._assert_e126("""
private fn f(@Int -> @Bool)
  requires(true)
  ensures(forall(@{ @Int | @Int.0 }, [1, 2], fn(@Int -> @Bool) effects(pure) { true }))
  effects(pure)
{ true }
""")

    def test_exists_binder_non_bool_rejected(self) -> None:
        """Site: exists(...) binder type annotation."""
        self._assert_e126("""
private fn f(@Int -> @Bool)
  requires(true)
  ensures(exists(@{ @Int | @Int.0 }, [1, 2], fn(@Int -> @Bool) effects(pure) { true }))
  effects(pure)
{ true }
""")

    def test_handler_state_non_bool_rejected(self) -> None:
        """Site: handler initial-state annotation `handle[...](@T = e)`."""
        self._assert_e126("""
private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@{ @Int | @Int.0 } = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""")

    def test_handler_clause_param_non_bool_rejected(self) -> None:
        """Site: handler clause parameter annotation."""
        self._assert_e126("""
private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@{ @Int | @Int.0 }) -> { resume(()) }
  } in {
    get(())
  }
}
""")

    def test_handler_with_clause_non_bool_rejected(self) -> None:
        """Site: handler `with @T = e` state-update annotation."""
        self._assert_e126("""
private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @{ @Int | @Int.0 } = @Int.0
  } in {
    get(())
  }
}
""")

    def test_ctor_field_non_bool_rejected(self) -> None:
        """Site: constructor field type (PR #876 CR review).

        The walker covered constructor fields from the first pass — this
        pins the site against regression alongside the other site tests.
        """
        self._assert_e126("""
private data W {
  Mk({ @Int | @Int.0 })
}

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")

    def test_let_annotation_bool_refinement_ok(self) -> None:
        """A well-formed Bool predicate in a let annotation keeps passing."""
        _check_ok("""
private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @{ @Int | @Int.0 > 0 } = 5;
  0
}
""")

    def test_match_binding_bool_refinement_ok(self) -> None:
        """A well-formed Bool predicate in a match binding keeps passing."""
        _check_ok("""
private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match 5 {
    @{ @Int | @Int.0 > 0 } -> 0,
    _ -> 1
  }
}
""")

    def test_verify_rejects_at_check_before_z3_crash(
        self, tmp_path: object,
    ) -> None:
        """`vera verify` on the let-site program fails CLEANLY at check.

        Pre-fix repro: the program was check-green, so `cmd_verify` reached
        the verifier and `_check_refined_binding_obligation` handed the
        non-Bool predicate to `z3.Not(...)` — an uncaught
        `z3.z3types.Z3Exception` traceback.  Post-fix the checker rejects
        with E126 and `cmd_verify` returns before the verifier runs.
        """
        import subprocess
        import sys
        from pathlib import Path

        src = (
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  let @{ @Int | @Int.0 } = 5;\n"
            "  0\n"
            "}\n"
        )
        f = Path(str(tmp_path)) / "let_refine_crash.vera"
        f.write_text(src, encoding="utf-8")
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "verify", f.as_posix()],
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        combined = result.stdout + result.stderr
        assert result.returncode == 1, \
            f"expected exit 1, got {result.returncode}: {combined}"
        assert "E126" in combined, f"expected E126 diagnostic, got: {combined}"
        assert "Traceback" not in combined, \
            f"verifier crash leaked through: {combined}"
        assert "Z3Exception" not in combined, \
            f"verifier crash leaked through: {combined}"


class TestRefinementPredicateScopeIsolation861:
    """#861 (PR #876 CR review): the predicate binder `@T.0` is the SOLE
    slot in scope (spec §2.6).  The first-pass check pushed the binder with
    a plain `push_scope()`, leaving all enclosing scopes visible — so at
    any site with live bindings (a fn body, a where-helper body, a handler
    clause) the predicate could resolve slots beyond its binder:
    `let @{ @Int | @Int.0 > @Int.1 } = 5;` inside `fn f(@Int, @Int -> ...)`
    passed check with `@Int.1` resolving the enclosing parameter.  The
    check now runs the predicate in an isolated scope stack containing
    only the binder, so any other slot is E130.
    """

    def test_predicate_cannot_see_enclosing_fn_params(self) -> None:
        """`@Int.1` in a let-annotation predicate must NOT resolve the
        enclosing function's parameter — E130."""
        errs = _check_err("""
private fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @{ @Int | @Int.0 > @Int.1 } = 5;
  0
}
""", "Int.1")
        assert any(e.error_code == "E130" for e in errs), \
            f"Expected E130, got: {[e.error_code for e in errs]}"

    def test_predicate_cannot_see_where_helper_params(self) -> None:
        """The same leak through a where-helper body — E130."""
        errs = _check_err("""
private fn top(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  helper(@Int.0, 2)
}
where {
  fn helper(@Int, @Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    let @{ @Int | @Int.0 > @Int.1 } = 5;
    0
  }
}
""", "Int.1")
        assert any(e.error_code == "E130" for e in errs), \
            f"Expected E130, got: {[e.error_code for e in errs]}"

    def test_match_binding_predicate_cannot_see_outer_scope(self) -> None:
        """The leak through a match binding pattern — E130."""
        errs = _check_err("""
private fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match 5 {
    @{ @Int | @Int.0 > @Int.1 } -> 0
  }
}
""", "Int.1")
        assert any(e.error_code == "E130" for e in errs), \
            f"Expected E130, got: {[e.error_code for e in errs]}"

    def test_binder_still_resolves_with_outer_scopes_live(self) -> None:
        """Positive control: with enclosing Int params live, the binder
        `@Int.0` still resolves and a Bool predicate is accepted."""
        _check_ok("""
private fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @{ @Int | @Int.0 > 0 } = 5;
  @Int.2
}
""")

    def test_match_binding_predicate_ok_with_outer_scopes_live(self) -> None:
        """Positive control: match-binding predicate under live outer
        bindings."""
        _check_ok("""
private fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    @{ @Int | @Int.0 > 0 } -> 0,
    _ -> 1
  }
}
""")

    def test_handler_clause_predicate_ok_with_outer_scopes_live(self) -> None:
        """Positive control: handler-clause param predicate is checked with
        the clause / fn scopes live and still accepts a Bool predicate."""
        _check_ok("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@{ @Int | @Int.0 > 0 }) -> { resume(()) }
  } in {
    get(())
  }
}
""")

    def test_byte_allowance_still_works_under_isolation(self) -> None:
        """The Byte-literal allowance keeps working in the isolated scope
        (binder-only) — exercised at a match-binding site with enclosing
        Int / Byte bindings live."""
        _check_ok("""
private fn f(@Int, @Byte -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Byte.0 {
    @{ @Byte | @Byte.0 < 10 } -> 1,
    _ -> 0
  }
}
""")


class TestByteAllowanceBaseScoping861:
    """#861 (PR #876 CR review): the Byte-literal comparison allowance is
    scoped to predicates over a `@Byte` BASE (spec §2.6).  The first pass
    keyed it on a boolean "inside any refinement predicate" flag, so a
    Byte-typed operand in an `@Int`-based refinement
    (`{ @Int | b(@Int.0) < 10 }` with `b : Int -> Byte`) wrongly got the
    allowance instead of E142.  The flag is now a stack of the active
    refinement base types, and the allowance applies only when the
    innermost base resolves to Byte.
    """

    def test_byte_operand_under_int_base_rejected(self) -> None:
        """A Byte-returning call compared to a literal inside an
        `@Int`-based refinement is E142 — the allowance must not apply."""
        errs = _check_err("""
type T = { @Int | b(@Int.0) < 10 };

private fn b(@Int -> @Byte)
  requires(true) ensures(true) effects(pure)
{ 0 }

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""", "compare")
        assert any(e.error_code == "E142" for e in errs), \
            f"Expected E142, got: {[e.error_code for e in errs]}"

    def test_nested_inner_byte_base_allowed(self) -> None:
        """Nesting, allowance direction: an inner `@Byte`-based refinement
        (reached through a forall binder inside an `@Int`-based outer
        predicate) still gets the allowance."""
        _check_ok("""
type T = { @Int | forall(@{ @Byte | @Byte.0 < 10 }, [1], fn(@Byte -> @Bool) effects(pure) { true }) && @Int.0 > 0 };

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")

    def test_nested_inner_int_base_rejected(self) -> None:
        """Nesting, denial direction: an inner `@Int`-based refinement
        inside an `@Byte`-based outer predicate must NOT inherit the
        outer allowance — E142."""
        errs = _check_err("""
type U = { @Byte | forall(@{ @Int | b(@Int.0) < 10 }, [1], fn(@Int -> @Bool) effects(pure) { true }) && @Byte.0 < 10 };

private fn b(@Int -> @Byte)
  requires(true) ensures(true) effects(pure)
{ 0 }

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""", "compare")
        assert any(e.error_code == "E142" for e in errs), \
            f"Expected E142, got: {[e.error_code for e in errs]}"

    def test_byte_base_through_alias_allowed(self) -> None:
        """The Byte base resolves through an alias chain: a refinement over
        `@MyByte` (`type MyByte = Byte`) still gets the allowance."""
        _check_ok("""
type MyByte = Byte;
type Small = { @MyByte | @MyByte.0 < 10 };

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")

    def test_byte_fncall_operand_stays_allowed(self) -> None:
        """The #766 fn-call operand shape (`ident(@Byte.0) < 10`) under a
        `@Byte` base keeps the allowance."""
        _check_ok("""
type SmallVia = { @Byte | ident(@Byte.0) < 10 };

private fn ident(@Byte -> @Byte)
  requires(true) ensures(true) effects(pure)
{ @Byte.0 }

private fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
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
