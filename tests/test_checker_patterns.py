"""Tests for the Vera type checker — patterns (pattern matching, exhaustiveness, match-arm typing, bidirectional inference, typed holes).

Split from tests/test_checker.py (#420). Shared helpers live in tests/checker_helpers.py.
"""
from __future__ import annotations

from tests.checker_helpers import (
    _check,
    _check_err,
    _check_ok,
    _errors,
    _warnings,
)


# =====================================================================
# Pattern matching
# =====================================================================

class TestPatterns:

    def test_constructor_pattern(self) -> None:
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn unwrap(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
""")

    def test_wildcard_pattern(self) -> None:
        _check_ok("""
private fn classify(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> "zero",
    1 -> "one",
    _ -> "other"
  }
}
""")

    def test_bool_pattern(self) -> None:
        _check_ok("""
private fn to_str(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> "yes",
    false -> "no"
  }
}
""")

    def test_nested_pattern(self) -> None:
        _check_ok("""
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

private fn first(@List<Option<Int>> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @List<Option<Int>>.0 {
    Cons(Some(@Int), @List<Option<Int>>) -> @Int.0,
    Cons(None, @List<Option<Int>>) -> first(@List<Option<Int>>.0),
    Nil -> 0
  }
}
""")

    def test_unknown_constructor_pattern_warns_e320(self) -> None:
        """A constructor pattern naming an unknown constructor warns E320."""
        warns = _warnings("""
private data Option<T> { None, Some(T) }

private fn f(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    Bogus(@Int) -> 0,
    None -> 0
  }
}
""")
        e320 = [w for w in warns if w.error_code == "E320"]
        assert len(e320) == 1
        assert e320[0].severity == "warning"

    def test_constructor_field_count_mismatch_is_e321(self) -> None:
        """A constructor pattern with the wrong sub-pattern count reports E321."""
        errs = _check_err("""
private data Pair { Both(Int, Int) }

private fn f(@Pair -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Pair.0 {
    Both(@Int) -> 0
  }
}
""", "field(s)")
        assert any(e.error_code == "E321" for e in errs)

    def test_unknown_nullary_constructor_warns_e322(self) -> None:
        """A nullary pattern naming an unknown constructor warns E322."""
        warns = _warnings("""
private data Option<T> { None, Some(T) }

private fn f(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    Bogus -> 0,
    None -> 0
  }
}
""")
        e322 = [w for w in warns if w.error_code == "E322"]
        assert len(e322) == 1
        assert e322[0].severity == "warning"


# =====================================================================
# Match arm-type unification
# =====================================================================

class TestMatchArmTypes:
    """Match arms must unify to a common type (E302)."""

    def test_incompatible_arm_types_carry_e302(self) -> None:
        # None -> Int and Some -> String: neither arm type is a subtype of
        # the other, so the unification must report E302 (kills the
        # is_subtype / types_equal / error_code mutants in _check_match).
        errs = _check_err("""
private data Option<T> { None, Some(T) }

private fn f(@Option<Int> -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> "ok"
  }
}
""", "incompatible")
        e302 = [e for e in errs if e.error_code == "E302"]
        assert len(e302) >= 1
        assert e302[0].rationale and e302[0].spec_ref


# =====================================================================
# Exhaustiveness checking
# =====================================================================

class TestExhaustiveness:

    # --- ADT exhaustiveness ---

    def test_adt_exhaustive(self) -> None:
        """All constructors covered → no error."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn unwrap(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
""")

    def test_adt_missing_constructor(self) -> None:
        """Missing None constructor → non-exhaustive error."""
        _check_err("""
private data Option<T> { None, Some(T) }

private fn unwrap(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0
  }
}
""", "Non-exhaustive")

    def test_adt_missing_multiple(self) -> None:
        """Missing both Err constructor → error mentions missing ones."""
        errs = _check_err("""
private data Result<T, E> { Ok(T), Err(E) }

private fn get(@Result<Int, String> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Result<Int, String>.0 {
    Ok(@Int) -> @Int.0
  }
}
""", "Non-exhaustive")
        desc = " ".join(e.description for e in errs)
        assert "Err" in desc

    def test_adt_missing_carries_e311(self) -> None:
        """The ADT non-exhaustive diagnostic carries E311, not just the text."""
        errs = _check_err("""
private data Option<T> { None, Some(T) }

private fn f(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0
  }
}
""", "Non-exhaustive")
        assert any(e.error_code == "E311" for e in errs)

    def test_unreachable_arm_after_catch_all_warns_e310(self) -> None:
        """An arm after a catch-all is the one (and only) E310 warning."""
        warns = _warnings("""
private data Option<T> { None, Some(T) }

private fn f(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    _ -> 0,
    Some(@Int) -> @Int.0
  }
}
""")
        e310 = [w for w in warns if w.error_code == "E310"]
        assert len(e310) == 1

    def test_bool_missing_carries_e312(self) -> None:
        """The Bool non-exhaustive diagnostic carries E312."""
        errs = _check_err("""
private fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> 1
  }
}
""", "Non-exhaustive")
        assert any(e.error_code == "E312" for e in errs)

    def test_int_match_without_catch_all_is_e313(self) -> None:
        """An infinite-domain (Int) match with no catch-all is E313."""
        errs = _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> 1
  }
}
""", "infinite domain")
        assert any(e.error_code == "E313" for e in errs)

    def test_exhaustiveness_diagnostics_are_well_formed(self) -> None:
        """Each exhaustiveness diagnostic carries the right severity and a
        populated rationale/fix/spec_ref (kills the =None / severity mutants)."""
        e311 = _check_err("""
private data Option<T> { None, Some(T) }

private fn f(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0
  }
}
""", "Non-exhaustive")[0]
        assert e311.severity == "error"
        assert e311.rationale and e311.fix and e311.spec_ref

        e310 = [w for w in _warnings("""
private data Option<T> { None, Some(T) }

private fn f(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    _ -> 0,
    Some(@Int) -> @Int.0
  }
}
""") if w.error_code == "E310"][0]
        assert e310.severity == "warning"
        assert e310.rationale and e310.fix

    def test_adt_with_wildcard(self) -> None:
        """Wildcard after Some covers None → exhaustive."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn unwrap(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    _ -> 0
  }
}
""")

    def test_adt_with_binding(self) -> None:
        """Binding pattern is a catch-all → exhaustive."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn unwrap(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    @Option<Int> -> 0
  }
}
""")

    # --- Bool exhaustiveness ---

    def test_bool_exhaustive(self) -> None:
        """Both true and false covered → no error."""
        _check_ok("""
private fn to_str(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> "yes",
    false -> "no"
  }
}
""")

    def test_bool_missing_true(self) -> None:
        """Only false covered → non-exhaustive."""
        _check_err("""
private fn to_str(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    false -> "no"
  }
}
""", "Non-exhaustive")

    def test_bool_missing_false(self) -> None:
        """Only true covered → non-exhaustive."""
        _check_err("""
private fn to_str(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> "yes"
  }
}
""", "Non-exhaustive")

    def test_bool_with_wildcard(self) -> None:
        """true + wildcard → exhaustive."""
        _check_ok("""
private fn to_str(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> "yes",
    _ -> "no"
  }
}
""")

    # --- Infinite type exhaustiveness ---

    def test_int_with_wildcard(self) -> None:
        """Int literals + wildcard → exhaustive."""
        _check_ok("""
private fn classify(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> "zero",
    1 -> "one",
    _ -> "other"
  }
}
""")

    def test_int_without_wildcard(self) -> None:
        """Int with only literals → non-exhaustive."""
        _check_err("""
private fn classify(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> "zero",
    1 -> "one"
  }
}
""", "Non-exhaustive")

    def test_string_without_wildcard(self) -> None:
        """String with only literals → non-exhaustive."""
        _check_err("""
private fn classify(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @String.0 {
    "hello" -> 1,
    "world" -> 2
  }
}
""", "Non-exhaustive")

    # --- Unreachable arms ---

    def test_unreachable_after_wildcard(self) -> None:
        """Arm after wildcard → unreachable warning."""
        warns = _warnings("""
private fn classify(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> "zero",
    _ -> "other",
    1 -> "one"
  }
}
""")
        assert any("Unreachable" in w.description for w in warns)

    def test_unreachable_after_binding(self) -> None:
        """Arm after binding pattern → unreachable warning."""
        warns = _warnings("""
private fn classify(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> "zero",
    @Int -> "other",
    1 -> "one"
  }
}
""")
        assert any("Unreachable" in w.description for w in warns)

    def test_multiple_unreachable(self) -> None:
        """Multiple arms after wildcard → multiple warnings."""
        warns = _warnings("""
private fn classify(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    _ -> "any",
    0 -> "zero",
    1 -> "one"
  }
}
""")
        unreachable = [w for w in warns if "Unreachable" in w.description]
        assert len(unreachable) == 2

    # --- Edge cases ---

    def test_wildcard_only(self) -> None:
        """Single wildcard arm → exhaustive."""
        _check_ok("""
private fn identity(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    _ -> @Int.0
  }
}
""")

    def test_refined_type_stripped(self) -> None:
        """Refined Int scrutinee still needs wildcard."""
        _check_err("""
private fn classify(@Int -> @String)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  match @Int.0 {
    1 -> "one",
    2 -> "two"
  }
}
""", "Non-exhaustive")


# =====================================================================
# Coverage: control.py — pattern checking branches
# =====================================================================

class TestPatternCoverage:
    """Cover missed lines in pattern type-checking."""

    # --- Line 272: fallthrough return [] (unknown pattern type) ---
    # This is architecturally unreachable from normal parsing, skip.

    # --- Lines 283-285: unknown constructor in pattern ---

    def test_unknown_constructor_pattern(self) -> None:
        """Unknown constructor in pattern produces a warning (lines 283-285)."""
        diags = _check("""
private data Color { Red, Green, Blue }

private fn foo(@Color -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Color.0 {
    Red -> 1,
    Green -> 2,
    Blue -> 3,
    Unknown(@Int) -> 4
  }
}
""")
        warnings = [d for d in diags if d.severity == "warning"]
        assert any("Unknown constructor" in w.description for w in warnings)

    # --- Lines 299-305: constructor arity mismatch in pattern ---

    def test_constructor_pattern_arity_mismatch(self) -> None:
        """Constructor pattern with wrong number of sub-patterns (lines 299-305)."""
        _check_err("""
private data Option<T> { None, Some(T) }

private fn foo(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int, @Int) -> @Int.0,
    None -> 0
  }
}
""", "1 field")

    # --- Lines 317-323: empty Tuple pattern ---
    # Marked as pragma: no cover — parser rejects Tuple() syntax.

    # --- Line 339: unknown nullary pattern ---

    def test_unknown_nullary_pattern(self) -> None:
        """Unknown nullary constructor in pattern produces a warning (line 339)."""
        diags = _check("""
private fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    FakeNullary -> 1,
    _ -> 0
  }
}
""")
        warnings = [d for d in diags if d.severity == "warning"]
        assert any("Unknown constructor" in w.description for w in warnings)


# =====================================================================
# Coverage: control.py — match-expression branches
# =====================================================================

class TestMatchExprCoverage:
    """Cover missed lines in match expression type-checking."""

    # --- Line 101: scrutinee_ty is None → return None ---

    def test_match_scrutinee_none(self) -> None:
        """Match on unresolvable scrutinee returns None (line 101)."""
        diags = _check("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match nonexistent_fn(()) {
    _ -> 42
  }
}
""")
        warnings = [d for d in diags if d.severity == "warning"]
        assert any("unresolved" in w.description.lower() for w in warnings)

    # --- Lines 117-118: arm_ty is None or UnknownType → continue ---

    def test_match_arm_unknown(self) -> None:
        """Match arm with unresolvable body → continue (lines 117-118)."""
        diags = _check("""
private data Color { Red, Green, Blue }

private fn foo(@Color -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Color.0 {
    Red -> some_unknown_fn(),
    Green -> 42,
    Blue -> 0
  }
}
""")
        warnings = [d for d in diags if d.severity == "warning"]
        assert any("unresolved" in w.description.lower() for w in warnings)

    # --- Line 122-123: result_type is Never, arm_ty is concrete ---

    def test_match_first_arm_never(self) -> None:
        """First arm is Never, second is concrete → use concrete (line 122-123)."""
        _check_ok("""
effect Exn<E> {
  op throw(E -> Never);
}

private fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(<Exn<String>>)
{
  match @Int.0 {
    0 -> throw("zero"),
    _ -> @Int.0
  }
}
""")

    # --- Lines 126-133: TypeVar re-synthesis in match arms ---

    # --- Lines 126-133: TypeVar re-synthesis in match arms ---
    # Marked as pragma: no cover — requires unresolved TypeVars in
    # match arm return types, which type inference normally resolves.

    # --- Line 137: incompatible arm types ---

    def test_match_arm_type_mismatch(self) -> None:
        """Arms with incompatible types produce E302 (line 137)."""
        _check_err("""
private fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> 42,
    _ -> "hello"
  }
}
""", "incompatible")


# =====================================================================
# Bidirectional type inference (issue #55)
# =====================================================================

class TestBidirectionalInference:
    """Bidirectional type checking: expected types resolve TypeVars in
    nullary constructors of parameterised ADTs."""

    def test_none_return_resolves_option(self) -> None:
        """None as function return resolves to Option<Int>."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn nothing(-> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None }
""")

    def test_if_none_some_resolves(self) -> None:
        """If-else with None/Some(42): None resolves from Some branch."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn maybe(@Bool -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { Some(42) } else { None }
}
""")

    def test_if_some_none_resolves(self) -> None:
        """If-else with Some(42)/None: None resolves from Some branch."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn maybe(@Bool -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { None } else { Some(42) }
}
""")

    def test_match_none_arm_resolves(self) -> None:
        """Match arm returning None resolves from expected return type."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn flip(@Option<Int> -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> None,
    None -> Some(0)
  }
}
""")

    def test_let_binding_resolves(self) -> None:
        """let @Option<Int> = None resolves TypeVar from declared type."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn f(-> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  @Option<Int>.0
}
""")

    def test_nil_resolves_list(self) -> None:
        """Nil resolves to List<Int> from return type context."""
        _check_ok("""
private data List<T> { Nil, Cons(T, List<T>) }

private fn empty(-> @List<Int>)
  requires(true) ensures(true) effects(pure)
{ Nil }
""")

    def test_err_resolves_result(self) -> None:
        """Err(msg) resolves T in Result<Int, String> from return type."""
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }

private fn fail(@String -> @Result<Int, String>)
  requires(true) ensures(true) effects(pure)
{ Err(@String.0) }
""")

    def test_nested_some_none_resolves(self) -> None:
        """Nested Some(None) resolves from Option<Option<Int>>."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn nested(-> @Option<Option<Int>>)
  requires(true) ensures(true) effects(pure)
{ Some(None) }
""")

    def test_none_as_fn_arg_resolves(self) -> None:
        """None passed as function argument resolves from param type."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn id(@Option<Int> -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ @Option<Int>.0 }

private fn test(-> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ id(None) }
""")

    def test_none_with_wrong_expected_errors(self) -> None:
        """None resolved to Option<Int> should not match Int return."""
        _check_err("""
private data Option<T> { None, Some(T) }

private fn bad(-> @Int)
  requires(true) ensures(true) effects(pure)
{ None }
""", "body has type")

    def test_block_threads_expected(self) -> None:
        """Expected type threads through block to tail expression."""
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn f(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0;
  None
}
""")

    def test_ok_resolves_result(self) -> None:
        """Ok(42) resolves E in Result<Int, String> from return type."""
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }

private fn succeed(-> @Result<Int, String>)
  requires(true) ensures(true) effects(pure)
{ Ok(42) }
""")

    # ---- Nested generic constructors (#243) ----------------------------

    def test_nested_generic_ctor_let_binding(self) -> None:
        """Cons(None, Nil) resolves via annotated let binding (#243)."""
        _check_ok("""
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

private fn f(-> @List<Option<Int>>)
  requires(true) ensures(true) effects(pure)
{
  let @List<Option<Int>> = Cons(None, Nil);
  @List<Option<Int>>.0
}
""")

    def test_nested_generic_ctor_fn_arg(self) -> None:
        """Cons(None, Nil) resolves as non-generic function argument (#243)."""
        _check_ok("""
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

private fn id(@List<Option<Int>> -> @List<Option<Int>>)
  requires(true) ensures(true) effects(pure)
{ @List<Option<Int>>.0 }

private fn test(-> @List<Option<Int>>)
  requires(true) ensures(true) effects(pure)
{ id(Cons(None, Nil)) }
""")

    def test_nested_generic_ctor_return_context(self) -> None:
        """Cons(None, Nil) resolves from return type context (#243)."""
        _check_ok("""
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

private fn f(-> @List<Option<Int>>)
  requires(true) ensures(true) effects(pure)
{ Cons(None, Nil) }
""")

    def test_deeper_nested_generic_ctor(self) -> None:
        """Cons(Some(None), Nil) resolves deeper nesting (#243)."""
        _check_ok("""
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

private fn f(-> @List<Option<Option<Int>>>)
  requires(true) ensures(true) effects(pure)
{ Cons(Some(None), Nil) }
""")


# =====================================================================
# Typed holes (#226)
# =====================================================================

class TestTypedHoles:
    """Typed hole expressions: ? placeholder with expected-type warning."""

    def test_hole_in_fn_body_warns(self):
        """A hole in a function body produces a W001 warning, not an error."""
        src = """
public fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ ? }
"""
        warnings = _warnings(src)
        errors = _errors(src)
        assert errors == [], f"Unexpected errors: {errors}"
        assert any("W001" in w.error_code for w in warnings)
        assert any("Int" in w.description for w in warnings)

    def test_hole_reports_expected_type(self):
        """The hole warning includes the expected return type."""
        src = """
public fn to_bool(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ ? }
"""
        warnings = _warnings(src)
        assert any("Bool" in w.description for w in warnings)

    def test_hole_fix_hint_includes_bindings(self):
        """The fix hint lists all available slot bindings in De Bruijn order."""
        src = """
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ ? }
"""
        warnings = _warnings(src)
        assert len(warnings) == 1
        fix = warnings[0].fix
        assert "@Int.0" in fix
        assert "@Int.1" in fix
        # De Bruijn order: @Int.0 (most recent) appears before @Int.1 in hint
        assert fix.find("@Int.0") < fix.find("@Int.1")

    def test_hole_with_no_int_bindings(self):
        """A hole in a function with no Int params has no @Int binding in the hint."""
        src = """
public fn zero(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ ? }
"""
        warnings = _warnings(src)
        assert len(warnings) == 1
        assert "Int" in warnings[0].description
        # No Int parameter, so @Int should not appear in the fix hint
        assert "@Int" not in warnings[0].fix

    def test_hole_is_warning_not_error(self):
        """vera check succeeds (ok=true) with holes; compile fails."""
        src = """
public fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ ? }
"""
        # check should have no errors
        assert _errors(src) == []

    def test_multiple_holes(self):
        """Multiple holes each get their own W001 warning."""
        src = """
public fn two_holes(@Int, @Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = ?;
  ?
}
"""
        warnings = _warnings(src)
        hole_warnings = [w for w in warnings if w.error_code == "W001"]
        assert len(hole_warnings) == 2
