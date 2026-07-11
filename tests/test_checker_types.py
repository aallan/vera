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


class TestForallNullaryCtorInference971:
    """#971: a bare nullary constructor (`None`) under `forall<T>` must
    unify its fresh constructor type variable with the declared forall var
    supplied by the surrounding type context — return type, let binding, or
    match arm — instead of minting a fresh `T$n` and then rejecting the
    program with a message describing two types that unify trivially.

    Each case below fails today (return -> E121, let -> E170, match -> E302)
    and must check clean once `_ctor_result_type` maps the fresh ctor var to
    an expected TypeVar.
    """

    def test_bare_none_return_position(self) -> None:
        """Shape (a): `None` returned where the declared type is Option<T>."""
        _check_ok("""
private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{
  None
}
""")

    def test_bare_none_return_position_alt_param_name(self) -> None:
        """Shape (a) with a param named E, not T — a fix keyed on the literal
        name "T" would leave this failing E121."""
        _check_ok("""
private forall<E> fn nothing_e(@Unit -> @Option<E>)
  requires(true) ensures(true) effects(pure)
{
  None
}
""")

    def test_bare_none_let_position(self) -> None:
        """Shape (b): `let @Option<T> = None` under forall<T>."""
        _check_ok("""
private forall<T> fn via_let(@Unit -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{
  let @Option<T> = None;
  @Option<T>.0
}
""")

    def test_bare_none_match_arm_position(self) -> None:
        """Shape (c): every match arm is `None` under forall<T>; the arms
        must agree at Option<T> instead of each minting its own T$n."""
        _check_ok("""
private forall<T> fn via_match(@Bool -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> None,
    false -> None
  }
}
""")

    def test_two_adts_share_param_no_cross_contamination(self) -> None:
        """The relaxed bidirectional fill must resolve each nullary ctor to
        ITS OWN parent: under forall<T>, `BNil` in a `let @Beta<T>` stays
        Beta<T> and the returned `ANil` stays Alpha<T>. If the fresh ctor var
        were mapped to the wrong parent's var the body would type as Beta<T>
        and re-raise E121 — so a clean check proves no cross-contamination."""
        _check_ok("""
private data Alpha<T> { ANil, ACons(T) }
private data Beta<T> { BNil, BCons(T) }

private forall<T> fn mix(@T -> @Alpha<T>)
  requires(true) ensures(true) effects(pure)
{
  let @Beta<T> = BNil;
  ANil
}
""")

    def test_two_adts_share_param_fresh_var_path_unchanged(self) -> None:
        """Regression guard for the fresh-var minting path the relaxation does
        NOT touch: two ADTs sharing "T" whose nullary ctors are resolved by
        cross-argument inference (expected concrete, not a forall var) still
        check clean. Green before and after — pins the invariant, not the fix.

        The same-ADT guard `expected.name == ci.parent_type` in
        `_ctor_result_type` is defense-in-depth masked downstream: removing it
        is caught by NO test, because the result type's name is always the
        constructor's own parent (`AdtType(ci.parent_type, ...)`), never
        `expected.name`, so a cross-ADT expected still mismatches on the
        nominal parent name (E121/E170/E302) regardless of which var the fill
        adopts. Verified empirically for PR #980 by removing the guard: an
        adversarial `ANil` returned where `@Beta<T>` is expected still reports
        E121, only the resolved type arg changes (`Alpha<T$1>` -> `Alpha<T>`).
        A vacuous pin would only assert that downstream check, so none is added.
        """
        _check_ok("""
private data Alpha<T> { ANil, ACons(T) }
private data Beta<T> { BNil, BCons(T) }

private forall<T> fn alpha_or(@Alpha<T>, @T -> @T)
  requires(true) ensures(true) effects(pure)
{
  match @Alpha<T>.0 { ACons(@T) -> @T.0, ANil -> @T.0 }
}

private forall<T> fn beta_or(@Beta<T>, @T -> @T)
  requires(true) ensures(true) effects(pure)
{
  match @Beta<T>.0 { BCons(@T) -> @T.0, BNil -> @T.0 }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = alpha_or(ANil, 7);
  let @Int = beta_or(BNil, 9);
  @Int.1 + @Int.0
}
""")

    # -----------------------------------------------------------------
    # Ill-typed direction pins: the relaxed bidirectional fill must not
    # over-admit.  When a payload-bearing sibling `Some(<Nat literal>)`
    # pins the body to Option<Nat>, the program is genuinely ill-typed
    # against the declared Option<T> and must still be rejected E121.  The
    # fresh-var adoption only ties a *bare nullary* ctor to the declared
    # forall var; it never launders a concrete Option<Nat> into Option<T>.
    # (The diagnostic names Option<Nat> because 5/3 are Nat literals.)
    # -----------------------------------------------------------------

    def test_some_literal_return_rejected(self) -> None:
        """Shape (a) ill-typed: `Some(5)` returned under forall<T> ->
        @Option<T> is Option<Nat>, not Option<T>, and must still fail E121."""
        errs = _check_err("""
private forall<T> fn bad_some(@Unit -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{
  Some(5)
}
""", "Option<Nat>")
        assert any(e.error_code == "E121" for e in errs), \
            f"Expected E121, got: {[e.error_code for e in errs]}"

    def test_mixed_if_arms_rejected(self) -> None:
        """Shape (b) ill-typed: `if @Bool.0 then None else Some(3)` types the
        whole `if` at Option<Nat> (the concrete arm wins), so against
        forall<T> -> @Option<T> it is E121 — None does not force Option<T>."""
        errs = _check_err("""
private forall<T> fn bad_mixed(@Bool -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { None } else { Some(3) }
}
""", "Option<Nat>")
        assert any(e.error_code == "E121" for e in errs), \
            f"Expected E121, got: {[e.error_code for e in errs]}"

    def test_mixed_match_arms_rejected(self) -> None:
        """Shape (c) ill-typed: a match with arms `None` / `Some(3)` unifies
        at Option<Nat>; against forall<T> -> @Option<T> that is E121."""
        errs = _check_err("""
private forall<T> fn bad_mixed_match(@Bool -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> None,
    false -> Some(3)
  }
}
""", "Option<Nat>")
        assert any(e.error_code == "E121" for e in errs), \
            f"Expected E121, got: {[e.error_code for e in errs]}"


class TestForallNullaryCtorNested979:
    """#979: a NESTED bare nullary constructor under `forall<T>` — `Some(None)`
    where the declared type is `Option<Option<T>>` — must thread the declared
    forall var through the nested-constructor FIELD propagation path, instead
    of the inner `None` minting an unrelated `T$n` one level down.  #971 fixed
    only the top-level result/let/match positions; the inner ctor's expected
    field type (`Option<T>`) still carries the declared var, and the
    field-propagation guard (`not contains_typevar(ft)`) suppressed it, so the
    inner `None` was typed with no expected and the well-typed program was
    rejected (return -> E121, let -> E170, match -> E302).
    """

    def test_nested_none_return_position(self) -> None:
        """`Some(None)` returned where the declared type is Option<Option<T>>."""
        _check_ok("""
private forall<T> fn pick(@Unit -> @Option<Option<T>>)
  requires(true) ensures(true) effects(pure)
{
  Some(None)
}
""")

    def test_nested_none_three_levels(self) -> None:
        """Deeper nesting: `Some(Some(None))` at Option<Option<Option<T>>> —
        the fill must descend through every level, not just one."""
        _check_ok("""
private forall<T> fn pick3(@Unit -> @Option<Option<Option<T>>>)
  requires(true) ensures(true) effects(pure)
{
  Some(Some(None))
}
""")

    def test_nested_none_alt_param_name(self) -> None:
        """The declared var is E, not T — a fix keyed on the literal name "T"
        (or on Option's own param name) would leave this failing E121."""
        _check_ok("""
private forall<E> fn pick_e(@Unit -> @Option<Option<E>>)
  requires(true) ensures(true) effects(pure)
{
  Some(None)
}
""")

    def test_nested_none_let_position(self) -> None:
        """`let @Option<Option<T>> = Some(None)` under forall<T> (was E170)."""
        _check_ok("""
private forall<T> fn pick_let(@Unit -> @Option<Option<T>>)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Option<T>> = Some(None);
  @Option<Option<T>>.0
}
""")

    def test_nested_none_match_arm_position(self) -> None:
        """Both match arms are `Some(None)`; they must agree at
        Option<Option<T>> instead of each minting its own T$n (was E302)."""
        _check_ok("""
private forall<T> fn pick_match(@Bool -> @Option<Option<T>>)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> Some(None),
    false -> Some(None)
  }
}
""")

    def test_nested_none_concrete_control(self) -> None:
        """Control — a monomorphic Option<Option<Int>> already checked clean
        before the fix (there is no declared var to adopt) and must stay OK."""
        _check_ok("""
private fn pick_concrete(@Unit -> @Option<Option<Int>>)
  requires(true) ensures(true) effects(pure)
{
  Some(None)
}
""")

    def test_nested_cross_adt_resolves_each_to_own_parent(self) -> None:
        """The nested fill must resolve each ctor to ITS OWN parent: `ACons`
        stays Alpha, the inner `BNil` stays Beta, and the shared param name T
        threads through both.  A miss would re-raise E121/E213."""
        _check_ok("""
private data Alpha<T> { ANil, ACons(T) }
private data Beta<T> { BNil, BCons(T) }

private forall<T> fn mix(@Unit -> @Alpha<Beta<T>>)
  requires(true) ensures(true) effects(pure)
{
  ACons(BNil)
}
""")

    def test_nested_cross_adt_no_cross_contamination(self) -> None:
        """Cross-contamination pin: the inner `BNil` (parent Beta) cannot adopt
        Alpha's var to satisfy an Alpha<Alpha<T>> field.  The per-level
        `expected.name == ci.parent_type` guard makes it mint fresh, and the
        field-type check then rejects the genuinely ill-typed nesting."""
        errs = _check_err("""
private data Alpha<T> { ANil, ACons(T) }
private data Beta<T> { BNil, BCons(T) }

private forall<T> fn bad(@Unit -> @Alpha<Alpha<T>>)
  requires(true) ensures(true) effects(pure)
{
  ACons(BNil)
}
""", "Alpha")
        assert any(e.error_code in ("E121", "E213") for e in errs), \
            f"Expected E121/E213, got: {[e.error_code for e in errs]}"

    def test_nested_some_literal_still_rejected(self) -> None:
        """Ill-typed pin: `Some(Some(5))` is Option<Option<Nat>>, not
        Option<Option<T>>; the fill ties only a bare nullary ctor to the
        declared var, never launders a concrete payload, so this stays E121."""
        errs = _check_err("""
private forall<T> fn bad2(@Unit -> @Option<Option<T>>)
  requires(true) ensures(true) effects(pure)
{
  Some(Some(5))
}
""", "Option<Option<Nat>>")
        assert any(e.error_code == "E121" for e in errs), \
            f"Expected E121, got: {[e.error_code for e in errs]}"


class TestForallNullaryCtorComparison981:
    """#981: a bare `None` used as a `==` / `!=` operand against a known Option
    type must adopt that type instead of minting a fresh `T$n`.  The
    comparison-synthesis path typed each operand with no expected type, so
    `@Option<T>.result == None` compared Option<T> with Option<T$1> and was
    rejected E142 — for BOTH operand orders, and (the bug is wider than the
    forall case) even at a concrete Option<Int>, which also failed at HEAD.
    """

    def test_eq_result_left(self) -> None:
        """`@Option<T>.result == None` in an ensures under forall<T> (was E142)."""
        _check_ok("""
private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true)
  ensures(@Option<T>.result == None)
  effects(pure)
{
  None
}
""")

    def test_eq_none_left(self) -> None:
        """Reversed operand order: `None == @Option<T>.result` (was E142)."""
        _check_ok("""
private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true)
  ensures(None == @Option<T>.result)
  effects(pure)
{
  None
}
""")

    def test_neq_result_left(self) -> None:
        """`!=` must also type-check (was E142).  The postcondition is FALSE
        here, so verify correctly defers it to a Tier-3 runtime check — this
        pins only that the comparison is well-typed."""
        _check_ok("""
private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true)
  ensures(@Option<T>.result != None)
  effects(pure)
{
  None
}
""")

    def test_neq_none_left(self) -> None:
        """Reversed order with `!=`: `None != @Option<T>.result` (was E142)."""
        _check_ok("""
private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true)
  ensures(None != @Option<T>.result)
  effects(pure)
{
  None
}
""")

    def test_requires_position(self) -> None:
        """A `requires` comparison over a parameter: `@Option<T>.0 == None`
        (was E142) — the fix point is operand typing, not the clause kind."""
        _check_ok("""
private forall<T> fn is_none(@Option<T> -> @Bool)
  requires(@Option<T>.0 == None)
  ensures(true)
  effects(pure)
{
  true
}
""")

    def test_concrete_option_int_eq_none(self) -> None:
        """Wider-than-forall: a monomorphic `@Option<Int>.result == None` ALSO
        failed E142 at HEAD (None mints a fresh var regardless of forall), so
        this is a RED->GREEN case, not a control."""
        _check_ok("""
private fn nothing_int(@Unit -> @Option<Int>)
  requires(true)
  ensures(@Option<Int>.result == None)
  effects(pure)
{
  None
}
""")

    def test_concrete_option_int_none_eq(self) -> None:
        """Reversed order at a concrete type: `None == @Option<Int>.result`."""
        _check_ok("""
private fn nothing_int(@Unit -> @Option<Int>)
  requires(true)
  ensures(None == @Option<Int>.result)
  effects(pure)
{
  None
}
""")

    def test_eq_option_vs_non_option_still_rejected(self) -> None:
        """Over-admission pin: comparing an Option against a non-Option value
        (`None == 5`) stays E142 — the re-synth only fires when the sibling is
        an AdtType, and `5` is Nat."""
        errs = _check_err("""
private forall<T> fn bad(@Unit -> @Bool)
  requires(None == 5)
  ensures(true)
  effects(pure)
{
  true
}
""", "compare")
        assert any(e.error_code == "E142" for e in errs), \
            f"Expected E142, got: {[e.error_code for e in errs]}"

    def test_eq_cross_adt_still_rejected(self) -> None:
        """Cross-ADT pin: `@Result<T, Int>.result == None` stays E142 — the
        `expected.name == ci.parent_type` guard blocks None (parent Option)
        from adopting Result's type args, so the operands never unify."""
        errs = _check_err("""
private forall<T> fn bad(@Unit -> @Result<T, Int>)
  requires(true)
  ensures(@Result<T, Int>.result == None)
  effects(pure)
{
  Err(0)
}
""", "compare")
        assert any(e.error_code == "E142" for e in errs), \
            f"Expected E142, got: {[e.error_code for e in errs]}"


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


# =====================================================================
# #898 — cross-argument type-argument merge for a generic bound by
# multiple sparse-multi-parameter constructor literals.
#
#   data Res<A, B> { MkOk(A), MkErr(B) }
#   forall<T> fn eq2(@T, @T -> @Bool)
#
# `eq2(MkErr(5), MkOk("x"))` is a fully-determined `Res<String, Int>` — arg 0
# (`MkErr(B)`) fixes `B = Int`, arg 1 (`MkOk(A)`) fixes `A = String` — but
# first-argument-wins binding used to reject it (E202): the checker bound `@T`
# to the first argument's whole `Res<A$1, Nat>` (with a fresh `A$1`) and the
# concrete second argument did not unify.  The checker now MERGES per-type-
# parameter information across the constructor arguments so a fully-determined
# multi-parameter ADT type-checks — while a genuine per-parameter CONFLICT
# (two arguments fixing the same parameter to different types) stays a clear
# error.
# =====================================================================

class TestCrossArgTypeArgMerge:

    _RES = "private data Res<A, B> { MkOk(A), MkErr(B) }\n"
    _EQ2 = (
        "private forall<T> fn eq2(@T, @T -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure) { true }\n"
    )

    def test_mergeable_cross_arg_accepts(self) -> None:
        # arg0 fixes B=Int, arg1 fixes A=String -> fully-determined Res<String,Int>
        _check_ok(
            self._RES + self._EQ2
            + "public fn main(@Unit -> @Bool)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ eq2(MkErr(5), MkOk(\"x\")) }\n"
        )

    def test_mergeable_cross_arg_reversed_order_accepts(self) -> None:
        # order independence: arg0 fixes A, arg1 fixes B
        _check_ok(
            self._RES + self._EQ2
            + "public fn main(@Unit -> @Bool)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ eq2(MkOk(\"x\"), MkErr(5)) }\n"
        )

    def test_conflicting_type_arg_rejected(self) -> None:
        # both args are MkOk (fix A), but to DIFFERENT types (String vs Int) —
        # a genuine conflict, must stay rejected (not silently merged) and get
        # the clear E205 conflict diagnostic (a subtype-check E202 is the
        # soundness backstop, but E205 is the actionable message).
        errs = _errors(
            self._RES + self._EQ2
            + "public fn main(@Unit -> @Bool)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ eq2(MkOk(\"x\"), MkOk(5)) }\n"
        )
        codes = {e.error_code for e in errs}
        assert "E205" in codes, f"conflict must be a clear E205, got {codes}"

    def test_conflicting_nested_type_arg_rejected(self) -> None:
        # nested conflict: arg0 gives A=String, arg1 gives A=Bool via MkOk
        errs = _errors(
            self._RES + self._EQ2
            + "public fn main(@Unit -> @Bool)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ eq2(MkOk(\"x\"), MkOk(true)) }\n"
        )
        codes = {e.error_code for e in errs}
        assert "E205" in codes, f"nested conflict must be a clear E205, got {codes}"

    def test_fully_determined_noneq_still_typechecks(self) -> None:
        # Res<Int, Array<Int>> is fully determined across args; it TYPE-CHECKS
        # (the Eq rejection is a codegen concern, not a checker concern here —
        # eq2 has no Eq bound in this fixture, so it must check cleanly).
        _check_ok(
            self._RES + self._EQ2
            + "public fn main(@Unit -> @Bool)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ eq2(MkErr([1]), MkOk(2)) }\n"
        )


class TestGenericOverUnitRejected900:
    """#900: a generic type parameter instantiated at the zero-size ``Unit``
    type is rejected at *check* time (E206) — but ONLY when the generic READS a
    ``@T``-typed slot somewhere that lowers to WASM (its body, or a ``requires``
    / ``ensures`` clause; #939), the exact condition that crashes in codegen.

    ``Unit`` is 0 bytes with no WASM representation (spec §11.2.2 / §11.3.1),
    so a monomorphized ``forall<T>``'s ``@T.n`` slot read resolves to no local
    (the dangling-slot codegen invariant).  A ``@T`` parameter that is never
    read erases cleanly from the WASM ABI, so a generic that does NOT read
    ``@T`` (``firstInt(@T, @Int){ @Int.0 }``, ``ignore(@T){ 0 }``) runs fine at
    ``T = Unit`` and MUST NOT be rejected — the discriminator is a ``@T.n``
    read, not merely ``T = Unit``.  The check must fire for every way ``T`` is
    pinned to ``Unit`` *when it is read*, not just the one repro shape from the
    issue.
    """

    _IDT = (
        "private forall<T> fn idt(@T -> @T)\n"
        "  requires(true) ensures(true) effects(pure) { @T.0 }\n"
    )
    _MKU = (
        "private fn mku(@Int -> @Unit)\n"
        "  requires(true) ensures(true) effects(pure) { () }\n"
    )

    def test_generic_over_unit_from_fn_return_rejected(self) -> None:
        # The issue's repro: a @Unit-returning fn feeds the generic arg.
        errs = _errors(
            self._MKU + self._IDT
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ let @Unit = idt(mku(5)); 7 }\n"
        )
        codes = {e.error_code for e in errs}
        assert "E206" in codes, \
            f"generic-over-Unit must be a clean E206, got {codes}"

    def test_generic_over_unit_from_unit_literal_rejected(self) -> None:
        # T bound to Unit by a bare () unit literal passed directly.
        errs = _errors(
            self._IDT
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ let @Unit = idt(()); 7 }\n"
        )
        codes = {e.error_code for e in errs}
        assert "E206" in codes, \
            f"() literal into generic must be E206, got {codes}"

    def test_generic_over_unit_one_of_several_params_rejected(self) -> None:
        # Unit pins T through one of several parameters (the others are Int).
        errs = _errors(
            self._MKU
            + "private forall<T> fn pair(@T, @Int -> @T)\n"
            "  requires(true) ensures(true) effects(pure) { @T.0 }\n"
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ let @Unit = pair(mku(5), 3); 7 }\n"
        )
        codes = {e.error_code for e in errs}
        assert "E206" in codes, \
            f"Unit pinning one of several params must be E206, got {codes}"

    def test_generic_over_unit_names_parameter_and_type(self) -> None:
        # The diagnostic must name the offending type parameter and Unit so
        # the message is actionable (checkability-over-correctness).
        errs = _errors(
            self._MKU + self._IDT
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ let @Unit = idt(mku(5)); 7 }\n"
        )
        e206 = [e for e in errs if e.error_code == "E206"]
        assert e206, "expected an E206 diagnostic"
        msg = e206[0].description
        assert "T" in msg and "Unit" in msg, \
            f"message must name the param and Unit, got: {msg!r}"

    def test_boxed_option_over_unit_still_ok(self) -> None:
        # Boundary: Option<Unit> is a *boxed* ADT (tag + pointer), not
        # zero-size, so instantiating a generic at Option<Unit> must remain
        # ACCEPTED — the rejection is keyed to *bare* Unit only.
        _check_ok(
            "private fn mko(@Int -> @Option<Unit>)\n"
            "  requires(true) ensures(true) effects(pure) { None }\n"
            + self._IDT
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ let @Option<Unit> = idt(mko(5)); 7 }\n"
        )

    def test_builtin_generic_over_unit_not_e206(self) -> None:
        # E206 is scoped to USER `forall<T>` fns the monomorphizer clones.
        # The built-in generic `async` has hand-written codegen, not a
        # `@T`-slot body, so `async(IO.print(...))` (a valid Future<Unit>
        # fire-and-forget) must NOT trip E206 — its W002 concurrency
        # warning path is preserved.
        errs = _errors(
            "private fn f(-> @Future<Unit>)\n"
            "  requires(true) ensures(true) effects(<IO, Async>)\n"
            "{ async(IO.print(\"hi\")) }\n"
        )
        codes = {e.error_code for e in errs}
        assert "E206" not in codes, \
            f"built-in async over Unit must not be E206, got {codes}"

    def test_user_override_of_prelude_name_over_unit_rejected(self) -> None:
        # Release review (CodeRabbit): a USER `forall<T>` override of a
        # prelude name (`option_map`) that READS `@T` is a genuine cloned
        # `@T`-slot body, so instantiating it at bare Unit must trip E206.
        # The pre-fix name-based built-in exclusion skipped any name in the
        # registry, letting this check-green program crash codegen with a
        # dangling-slot E699.  The discriminator is `forall_vars_read`
        # (empty for the hand-written built-in, populated for the override).
        errs = _errors(
            "private forall<T> fn option_map(@T -> @T)\n"
            "  requires(true) ensures(true) effects(pure) { @T.0 }\n"
            "public fn main(@Unit -> @Unit)\n"
            "  requires(true) ensures(true) effects(pure) { option_map(()) }\n"
        )
        codes = {e.error_code for e in errs}
        assert "E206" in codes, \
            f"user override of a prelude name over Unit must be E206, got {codes}"

    # ---- The @T-not-read cases: VALID at T=Unit, must be ACCEPTED ----
    # A `@T` parameter that the body never reads erases cleanly from the WASM
    # ABI, so these run on base and E206 must not fire (the round-2 fix).

    def test_generic_unread_typevar_extra_param_accepted(self) -> None:
        # firstInt(@T, @Int){ @Int.0 } never reads @T; runs 42 on base.
        _check_ok(
            self._MKU
            + "private forall<T> fn firstInt(@T, @Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure) { @Int.0 }\n"
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ firstInt(mku(5), 42) }\n"
        )

    def test_generic_unread_typevar_return_const_accepted(self) -> None:
        # ignore(@T){ 0 } never reads @T; monomorphizes to $ignore$Unit, runs 0.
        _check_ok(
            self._MKU
            + "private forall<T> fn ignore(@T -> @Int)\n"
            "  requires(true) ensures(true) effects(pure) { 0 }\n"
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ ignore(mku(5)) }\n"
        )

    def test_generic_unread_typevar_from_unit_literal_accepted(self) -> None:
        # Same discriminator via a bare () literal, no Unit-returning helper.
        _check_ok(
            "private forall<T> fn ignore(@T -> @Int)\n"
            "  requires(true) ensures(true) effects(pure) { 0 }\n"
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ ignore(()) }\n"
        )

    def test_generic_reads_typevar_as_match_scrutinee_rejected(self) -> None:
        # A `@T` read as a match scrutinee IS a materialization — E699 on base,
        # so it must stay an E206 rejection (not slip through the narrowing).
        errs = _errors(
            self._MKU
            + "private forall<T> fn matchT(@T, @Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ match @T.0 { @T -> @Int.0 } }\n"
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ matchT(mku(3), 8) }\n"
        )
        codes = {e.error_code for e in errs}
        assert "E206" in codes, \
            f"a @T match-scrutinee read must stay E206, got {codes}"

    def test_contract_requires_reads_typevar_over_unit_rejected(self) -> None:
        # #939: a `@T.n` read in a `requires(...)` clause ALSO lowers to a
        # `local.get` — `_compile_preconditions` emits the runtime precondition
        # check — so a contract-clause read at `T = Unit` dangles exactly like a
        # body read.  The body here never reads `@T` (returns `@Int.0`), so only
        # walking the contract clauses (not just the body) can catch it.
        # Pre-#939: `check` passed, then `vera run` crashed with a raw
        # CodegenInvariantError traceback (the dangling-slot invariant).
        errs = _errors(
            "private forall<T> fn ignore_pair(@T, @T, @Int -> @Int)\n"
            "  requires(@T.1 == @T.0) ensures(true) effects(pure)\n"
            "{ @Int.0 }\n"
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ ignore_pair((), (), 5) }\n"
        )
        codes = {e.error_code for e in errs}
        assert "E206" in codes, \
            f"a @T read in a requires clause must be E206 at Unit, got {codes}"

    def test_contract_ensures_reads_typevar_over_unit_rejected(self) -> None:
        # #939: the `ensures(...)` clause lowers to a runtime postcondition
        # check too, so a `@T.n` read there dangles at Unit identically.  (The
        # postcondition codegen path already degraded to a clean E699, but E206
        # at check is the correct, earlier diagnostic — and keeps requires and
        # ensures uniform under one discriminator.)
        errs = _errors(
            "private forall<T> fn ignore_pair(@T, @T, @Int -> @Int)\n"
            "  requires(true) ensures(@T.1 == @T.0) effects(pure)\n"
            "{ @Int.0 }\n"
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ ignore_pair((), (), 5) }\n"
        )
        codes = {e.error_code for e in errs}
        assert "E206" in codes, \
            f"a @T read in an ensures clause must be E206 at Unit, got {codes}"

    def test_generic_reads_typevar_over_future_unit_rejected(self) -> None:
        # #939 follow-up: `Future<Unit>` is a SECOND zero-size type.  Codegen
        # makes `Future<T>` transparent to `T` (#841), so `Future<Unit>` erases
        # to no WASM local exactly like bare `Unit`.  A `@T` BODY read at
        # `T = Future<Unit>` (pinned via `async(())`) dangles identically, so
        # E206 must fire — pre-fix `check` passed and codegen degraded to E699.
        # The discriminator now keys on `erases_to_unit`, not `base_type==UNIT`.
        errs = _errors(
            "private forall<T> fn idf(@T -> @T)\n"
            "  requires(true) ensures(true) effects(pure) { @T.0 }\n"
            + "public fn main(@Unit -> @Unit)\n"
            "  requires(true) ensures(true) effects(<Async>)\n"
            "{\n"
            "  let @Future<Unit> = async(());\n"
            "  let @Future<Unit> = idf(@Future<Unit>.0);\n"
            "  await(@Future<Unit>.0)\n"
            "}\n"
        )
        codes = {e.error_code for e in errs}
        assert "E206" in codes, \
            f"a @T body read at Future<Unit> must be E206, got {codes}"

    def test_contract_ensures_reads_typevar_over_future_unit_rejected(self) -> None:
        # #939 follow-up + the confirmed raw-traceback crash: a `@T` read in an
        # `ensures` clause at `T = Future<Unit>`.  Pre-fix this slipped BOTH the
        # E206 gate (keyed on bare `Unit`) AND the postcondition codegen net
        # (which lacked the `CodegenInvariantError` catch), crashing with a raw
        # Python traceback on a `check`-green + `verify`-green program.  Now
        # E206 at check (and the postcondition net is the defensive backstop).
        errs = _errors(
            "private forall<T> fn pf(@T, @Int -> @Int)\n"
            "  requires(true) ensures(@T.0 == @T.0) effects(pure) { @Int.0 }\n"
            + "public fn main(@Unit -> @Unit)\n"
            "  requires(true) ensures(true) effects(<Async>)\n"
            "{\n"
            "  let @Future<Unit> = async(());\n"
            "  let @Int = pf(@Future<Unit>.0, 5);\n"
            "  ()\n"
            "}\n"
        )
        codes = {e.error_code for e in errs}
        assert "E206" in codes, \
            f"a @T ensures-read at Future<Unit> must be E206, got {codes}"

    def test_generic_reads_typevar_over_future_int_accepted(self) -> None:
        # Non-regression for the `erases_to_unit` broadening: `Future<Int>` is
        # transparent to `Int` — a non-zero i32 — so a `@T` read at
        # `T = Future<Int>` erases cleanly and runs.  `erases_to_unit` must flag
        # ONLY `Future`-of-zero-size, never `Future<Int>` (nor a boxed
        # `Option<Unit>`, which is a tag+pointer i32).
        _check_ok(
            "private forall<T> fn firstT(@T, @Int -> @T)\n"
            "  requires(true) ensures(true) effects(pure) { @T.0 }\n"
            + "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(<Async>)\n"
            "{\n"
            "  let @Future<Int> = async(7);\n"
            "  let @Future<Int> = firstT(@Future<Int>.0, 3);\n"
            "  0\n"
            "}\n"
        )


class TestArrayZeroSizeElementRejected945:
    """#945: an ``Array<T>`` whose element type erases to zero-size (``Unit``,
    or a ``Future<Unit>`` that erases to it) has no valid WASM element layout.
    ``_element_mem_size`` fell through to the 4-byte ADT default, so the
    array-literal store (and the index load) emitted an ``i32.store`` /
    ``i32.load`` against an empty stack — a ``check``-green + ``verify``-green
    program that compiled to INVALID WASM (rejected by wasmtime at load).
    Rejected cleanly at check (E135) — a zero-size element has no runtime value
    to store, the same principle as the ``@T``-at-zero-size family (#900 / #939
    / #943).  An ``Array<Unit>`` is degenerate anyway (isomorphic to a ``Nat``
    count)."""

    def test_array_literal_of_unit_rejected(self) -> None:
        # Annotation + literal for ONE zero-size array: `_resolve_type` rejects
        # the `@Array<Unit>` annotation (E135), and the literal-level gate now
        # DEFERS to it (PR #938 review) rather than emitting a second E135 for
        # the same root cause — exactly one E135, not two.
        errs = _errors(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  let @Array<Unit> = [()];\n"
            "  nat_to_int(array_length(@Array<Unit>.0))\n"
            "}\n"
        )
        e135 = [e for e in errs if e.error_code == "E135"]
        assert len(e135) == 1, (
            "annotated Array<Unit> literal must emit E135 exactly once "
            f"(no double for one root cause), got {[e.error_code for e in errs]}"
        )
        # ...and the same when the annotation is REFINED (`{ @Array<Unit> | p }`):
        # `expected` is then a `RefinedType`, so the guard must strip to the base
        # (`base_type`) or the literal-level E135 double-fires again (PR #938
        # review; the E202 type-mismatch is a separate, expected diagnostic).
        refined = _errors(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  let @{ @Array<Unit> | true } = [()];\n"
            "  nat_to_int(array_length(@Array<Unit>.0))\n"
            "}\n"
        )
        refined_e135 = [e for e in refined if e.error_code == "E135"]
        assert len(refined_e135) == 1, (
            "refined Array<Unit> annotation + literal must also emit E135 "
            f"exactly once, got {[e.error_code for e in refined]}"
        )

    def test_array_unit_param_rejected(self) -> None:
        # No literal — the `@Array<Unit>` parameter type alone is rejected at
        # resolution, so an index read never reaches codegen either.  A
        # function's signature types are `_resolve_type`'d in BOTH the
        # registration and the check pass, so this once double-reported E135
        # at one location; the `_error` exact-duplicate dedup (PR #938)
        # collapses it to exactly one.
        errs = _errors(
            "public fn f(@Array<Unit> -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ nat_to_int(array_length(@Array<Unit>.0)) }\n"
        )
        e135 = [e for e in errs if e.error_code == "E135"]
        assert len(e135) == 1, (
            "Array<Unit> param must emit E135 exactly once (signature "
            f"double-resolution deduped), got {[e.error_code for e in errs]}"
        )

    def test_signature_diagnostics_deduplicated_per_location(self) -> None:
        # The exact-duplicate `_error` dedup (PR #938) is general, not
        # E135-specific: a signature with a zero-size `Array` in BOTH the
        # param and the return position emits exactly one E135 per DISTINCT
        # location — TWO total, not four (the registration- and check-pass
        # resolutions of each type collapse) and not one (the two positions
        # stay distinct, so the dedup keys on location, not just the code).
        errs = _errors(
            "public fn f(@Array<Unit> -> @Array<Unit>)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Array<Unit>.0 }\n"
        )
        e135 = [e for e in errs if e.error_code == "E135"]
        assert len(e135) == 2, (
            "param + return zero-size Array must emit E135 exactly twice "
            f"(once per location, not 4 un-deduped nor 1 over-collapsed), "
            f"got {[e.error_code for e in errs]}"
        )

    def test_bare_array_literal_of_unit_rejected(self) -> None:
        # A bare `[()]` with NO `@Array<Unit>` annotation never flows through
        # `_resolve_type`, so this isolates the `_check_array_lit` gate — which
        # must fire exactly once (its only gate; nothing else rejects it).
        errs = _errors(
            "public fn main(-> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ nat_to_int(array_length([()])) }\n"
        )
        e135 = [e for e in errs if e.error_code == "E135"]
        assert len(e135) == 1, (
            "bare [()] literal must emit E135 exactly once, "
            f"got {[e.error_code for e in errs]}"
        )

    def test_array_of_int_still_accepted(self) -> None:
        # Non-regression: a normal, non-zero-size element array is unaffected.
        _check_ok(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  let @Array<Int> = [1, 2, 3];\n"
            "  nat_to_int(array_length(@Array<Int>.0))\n"
            "}\n"
        )


class TestForallNullaryCtorCallArg993:
    """#993: a bare ``None`` in the remaining fresh-ctor-var positions must
    adopt the expected type instead of minting an unresolvable ``T$n``.
    Fifth mechanism of the family after #971 (return/let/match), #979
    (nested fields), and #981 (comparison operands): call arguments, ability
    op arguments, effect op arguments, constructor arguments under a bare
    forall var, and both-constructor comparisons.
    """

    def test_generic_call_arg_sibling_unresolved(self) -> None:
        """`option_unwrap_or(nothing(()), None)` — both arguments carry
        fresh/instantiation vars; the polymorphic None must not reject
        against the (still-generic) parameter type (was E202)."""
        _check_ok("""
private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{
  None
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(nothing(()), None);
  0
}
""")

    def test_eq_call_arg_concrete_expected(self) -> None:
        """`ensures(eq(@Option<Int>.result, None))` at a fully concrete
        expected type (was E241 — the operator form `== None` of the same
        comparison already checks clean via #981)."""
        _check_ok("""
private fn nothing(@Unit -> @Option<Int>)
  requires(true)
  ensures(eq(@Option<Int>.result, None))
  effects(pure)
{
  None
}
""")

    def test_eq_call_arg_under_forall(self) -> None:
        """The same eq-call shape under forall<T> (was E241)."""
        _check_ok("""
private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true)
  ensures(eq(@Option<T>.result, None))
  effects(pure)
{
  None
}
""")

    def test_effect_op_arg_adopts_state_type(self) -> None:
        """`handle[State<Option<Int>>](@Option<Int> = None)` with a
        `put(None)` in the body — the handler-state initializer synths with
        the declared state type (was E331; the effect-op argument loop
        already synthesizes against the resolved param type)."""
        _check_ok("""
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = None) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    put(None);
    0
  }
}
""")

    def test_ctor_arg_under_bare_forall_var(self) -> None:
        """`MkA(None)` where the field type is Option<T> with T the
        enclosing forall var (was E121; the concrete-nested-outer-arg form
        was fixed by #994/#979)."""
        _check_ok("""
private data A<T> { MkA(Option<T>) }

private forall<T> fn make(@Unit -> @A<T>)
  requires(true) ensures(true) effects(pure)
{
  MkA(None)
}
""")

    def test_both_ctor_comparison_concrete(self) -> None:
        """`Some(5) == None` — both sides constructors, one nullary-fresh;
        the fresh side must adopt the other side's type (was E142)."""
        _check_ok("""
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  Some(5) == None
}
""")

    def test_cross_adt_call_arg_still_rejected(self) -> None:
        """Guardrail: the typevar-wildcard skip is structural — a cross-ADT
        argument (Box vs Option) is still E202 even with unresolved vars on
        both sides and matching inner structure."""
        _check_err("""
private data Box<T> { MkBox(Option<T>) }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(MkBox(None), None);
  0
}
""", "Argument 0 of 'option_unwrap_or'")

    def test_none_eq_none_still_rejected(self) -> None:
        """Guardrail: two unresolved ctor operands have no side to adopt
        from — `None == None` stays rejected."""
        _check_err("""
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  None == None
}
""", "Cannot compare")

    # -- PR #1009 review round: reversed operand orders + rigidity ------

    def test_generic_call_arg_reversed(self) -> None:
        """The mirrored order `option_unwrap_or(None, nothing(()))` — the
        bare None first, the polymorphic sibling second."""
        _check_ok("""
private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{
  None
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(None, nothing(()));
  0
}
""")

    def test_eq_call_both_ctor(self) -> None:
        """`eq(None, Some(5))` — the ability mapping must not lock onto the
        first argument's fresh var; the concrete second argument re-anchors
        it and the None re-synths (was E241)."""
        _check_ok("""
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(None, Some(5))
}
""")

    def test_eq_call_arg_reversed_concrete(self) -> None:
        """`eq(None, @Option<Int>.result)` — bare None as the FIRST
        argument at a concrete sibling (was E241)."""
        _check_ok("""
private fn nothing(@Unit -> @Option<Int>)
  requires(true)
  ensures(eq(None, @Option<Int>.result))
  effects(pure)
{
  None
}
""")

    def test_eq_call_arg_reversed_forall(self) -> None:
        """The same reversed eq-call shape under forall<T> (was E241)."""
        _check_ok("""
private forall<T> fn nothing(@Unit -> @Option<T>)
  requires(true)
  ensures(eq(None, @Option<T>.result))
  effects(pure)
{
  None
}
""")

    def test_both_ctor_comparison_reversed(self) -> None:
        """`None == Some(5)` — the mirrored both-ctor comparison."""
        _check_ok("""
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  None == Some(5)
}
""")

    def test_both_ctor_rigid_forall_sibling(self) -> None:
        """`Some(@T.0) == None` under forall<T where Eq<T>> — the adopted-
        FROM ctor side carries only a RIGID var, which is a fully-resolved
        type inside its own body (was E142)."""
        _check_ok("""
public forall<T where Eq<T>> fn f(@T -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  Some(@T.0) == None
}
""")

    def test_rigid_forall_arg_still_rejected(self) -> None:
        """Guardrail: a RIGID forall var is not a wildcard — passing
        `@Option<T>.0` where `Option<Int>` is required must stay E202 (the
        body must be valid for EVERY T)."""
        _check_err("""
private fn g(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}

public forall<T> fn f(@Option<T> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  g(@Option<T>.0)
}
""", "Argument 0 of 'g'")

    def test_eq_none_none_still_rejected(self) -> None:
        """Guardrail: `eq(None, None)` — a param still carrying a fresh
        hole is not a resolved type to adopt, so the unresolvable
        comparison stays rejected."""
        _check_err("""
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(None, None)
}
""", "Argument 1 of 'eq'")

    def test_handler_init_intlit_coercion(self) -> None:
        """The init-expected change also enables IntLit coercion for
        non-ctor inits: `@Byte = 5` checks (bidirectional IntLit -> Byte,
        as at every other expected-type site); out-of-range stays E331."""
        _check_ok("""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Byte>](@Byte = 5) {
    get(@Unit) -> { resume(@Byte.0) },
    put(@Byte) -> { resume(()) }
  } in {
    0
  }
}
""")
        _check_err("""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Byte>](@Byte = 999) {
    get(@Unit) -> { resume(@Byte.0) },
    put(@Byte) -> { resume(()) }
  } in {
    0
  }
}
""", "Handler state initial value")

    def test_compat_fn_effect_row_not_wildcarded(self) -> None:
        """Unit-level guardrail on `_compatible_modulo_typevars`: a fresh
        var in a function type's params makes the STRUCTURE matchable, but
        the effect row is never wildcarded — `<IO>` cannot satisfy a pure
        formal.  (Not constructible from surface syntax today: builtin
        unresolved vars print as `?`/UnknownType, which bypasses the
        typevar-guarded compat path; user-generic fn params resolve their
        vars from the closure argument itself.)"""
        from vera.checker.calls import _compatible_modulo_typevars
        from vera.types import (
            INT,
            ConcreteEffectRow,
            EffectInstance,
            FunctionType,
            PureEffectRow,
            TypeVar,
        )
        io_row = ConcreteEffectRow(
            effects=frozenset({EffectInstance(name="IO", type_args=())}))
        arg = FunctionType(
            params=(INT,), return_type=INT, effect=io_row)
        param = FunctionType(
            params=(TypeVar("T$1"),), return_type=INT,
            effect=PureEffectRow())
        assert not _compatible_modulo_typevars(arg, param, frozenset())
        pure_arg = FunctionType(
            params=(INT,), return_type=INT, effect=PureEffectRow())
        assert _compatible_modulo_typevars(pure_arg, param, frozenset())
        # rigid discrimination: the same bare `T` is a wildcard outside a
        # forall<T> body but opaque inside one
        assert _compatible_modulo_typevars(TypeVar("T"), INT, frozenset())
        assert not _compatible_modulo_typevars(
            TypeVar("T"), INT, frozenset({"T"}))
