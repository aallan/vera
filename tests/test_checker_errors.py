"""Tests for the Vera type checker — errors (error codes, resolution diagnostics, contracts, error accumulation).

Split from tests/test_checker.py (#420). Shared helpers live in tests/checker_helpers.py.
"""
from __future__ import annotations

from vera import ast

from tests.checker_helpers import (
    _check,
    _check_err,
    _check_ok,
    _errors,
)


# =====================================================================
# Error code tests
# =====================================================================

class TestErrorCodes:
    """Verify that diagnostics carry stable error codes."""

    def test_error_code_in_format_output(self) -> None:
        """Error codes appear in formatted diagnostic output."""
        from vera.errors import Diagnostic, SourceLocation
        d = Diagnostic(
            description="test error",
            location=SourceLocation(line=1, column=1),
            error_code="E130",
        )
        formatted = d.format()
        assert "[E130]" in formatted

    def test_error_code_in_json_output(self) -> None:
        """Error codes appear in to_dict() JSON output."""
        from vera.errors import Diagnostic, SourceLocation
        d = Diagnostic(
            description="test error",
            location=SourceLocation(line=1, column=1),
            error_code="E130",
        )
        data = d.to_dict()
        assert data["error_code"] == "E130"

    def test_no_error_code_omitted_from_format(self) -> None:
        """Diagnostics without codes don't show empty brackets."""
        from vera.errors import Diagnostic, SourceLocation
        d = Diagnostic(
            description="test error",
            location=SourceLocation(line=1, column=1),
        )
        formatted = d.format()
        assert "[" not in formatted.split("\n")[0]

    def test_no_error_code_omitted_from_json(self) -> None:
        """Diagnostics without codes don't include error_code in JSON."""
        from vera.errors import Diagnostic, SourceLocation
        d = Diagnostic(
            description="test error",
            location=SourceLocation(line=1, column=1),
        )
        data = d.to_dict()
        assert "error_code" not in data

    def test_error_codes_registry_valid(self) -> None:
        """All codes in ERROR_CODES are valid Exxx/Wxxx patterns and unique."""
        import re
        from vera.errors import ERROR_CODES
        pattern = re.compile(r"^[EW]\d{3}$")
        seen: set[str] = set()
        for code in ERROR_CODES:
            assert pattern.match(code), f"Invalid code format: {code}"
            assert code not in seen, f"Duplicate code: {code}"
            seen.add(code)
        assert len(ERROR_CODES) >= 70  # sanity: we defined ~80 codes

    def test_slot_ref_error_has_code_E130(self) -> None:
        """Unresolved slot reference produces E130."""
        src = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E130" for d in diags)

    def test_decimal_type_args_is_E134_not_E130(self) -> None:
        """`Decimal<...>` (a non-generic type given type arguments) is E134 —
        distinct from the E130 slot-resolution error it previously collided
        with (#826).  The `not E130` assertion is the collision-regression."""
        src = """\
private fn f(@Decimal<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E134" for d in diags)
        assert not any(d.error_code == "E130" for d in diags)

    def test_empty_tuple_is_E216_not_E210(self) -> None:
        """`Tuple()` with no fields is E216 — distinct from the E210
        unknown-constructor error it previously collided with (#826)."""
        src = """\
private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple = Tuple(); 0 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E216" for d in diags)
        assert not any(d.error_code == "E210" for d in diags)

    def test_body_type_mismatch_has_code_E121(self) -> None:
        """Function body type mismatch produces E121."""
        src = """\
private fn f(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E121" for d in diags)

    def test_if_condition_not_bool_has_code_E300(self) -> None:
        """If condition not Bool produces E300."""
        src = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 then { 1 } else { 0 } }
"""
        diags = _errors(src)
        assert any(d.error_code == "E300" for d in diags)

    def test_unresolved_function_has_code_E200(self) -> None:
        """Unresolved function produces E200 (warning)."""
        src = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ unknown_fn(@Int.0) }
"""
        diags = _check(src)
        assert any(d.error_code == "E200" for d in diags)

    def test_requires_not_bool_has_code_E123(self) -> None:
        """requires() with non-Bool predicate produces E123."""
        src = """\
private fn f(@Int -> @Int)
  requires(@Int.0) ensures(true) effects(pure)
{ @Int.0 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E123" for d in diags)

    def test_let_binding_mismatch_has_code_E170(self) -> None:
        """Let binding type mismatch produces E170."""
        src = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = @Int.0;
  @Int.0
}
"""
        diags = _errors(src)
        assert any(d.error_code == "E170" for d in diags)

    def test_assert_not_bool_has_code_E172(self) -> None:
        """assert() with non-Bool produces E172."""
        src = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  assert(@Int.0);
  @Int.0
}
"""
        diags = _errors(src)
        assert any(d.error_code == "E172" for d in diags)

    def test_arithmetic_non_numeric_has_code_E140(self) -> None:
        """Arithmetic on non-numeric produces E140."""
        src = """\
private fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 + 1 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E140" for d in diags)

    def test_E140_carries_a_fix_paragraph_682(self) -> None:
        """#682 AC5: the operator-type-mismatch diagnostic (E140) must
        carry a concrete `Fix:` paragraph, not just a description +
        rationale — this is the canonical example from the issue."""
        src = """\
private fn f(@Bool, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 + @Int.0 }
"""
        e140 = [d for d in _errors(src) if d.error_code == "E140"]
        assert e140, "expected an E140 diagnostic for `@Bool.0 + @Int.0`"
        assert e140[0].fix.strip(), "E140 must carry a non-empty fix"
        assert "Fix:" in e140[0].format()


# =====================================================================
# Resolution mixin — coverage for uncovered branches
# =====================================================================


class TestResolutionCoverage:
    """Tests targeting uncovered lines in checker/resolution.py."""

    # Line 48: _resolve_type returning UnknownType for unknown TypeExpr
    def test_resolve_type_unknown_type_expr(self) -> None:
        """Directly calling _resolve_type with an unrecognised TypeExpr
        node returns UnknownType."""
        from vera.checker.core import TypeChecker
        from vera.types import UnknownType
        from vera.environment import TypeEnv

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        # Create a TypeExpr subclass that is none of the known kinds
        bogus = ast.TypeExpr(span=None)
        result = checker._resolve_type(bogus)
        assert isinstance(result, UnknownType)

    # Lines 66-68: Type alias with type args (parameterised alias)
    def test_parameterised_type_alias(self) -> None:
        """A parameterised type alias resolves type args via substitution."""
        _check_ok("""
type Wrapper<T> = Option<T>;

private fn wrap(@Int -> @Wrapper<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(@Int.0) }
""")

    def test_alias_arity_mismatch_too_few_e133(self) -> None:
        """`#660` — `vera check` rejects `@Pair<Int>` when
        `Pair<A, B>` is declared with two type parameters.

        Pre-fix the checker silently accepted this and the `zip`
        in `_resolve_type` truncated, leaving the alias body's
        `B` unsubstituted.  Downstream codegen leaked literal
        `B` into mono suffixes (`option_map$Int_B`) → runtime
        `call_indirect` trap.  Post-fix the checker rejects with
        `[E133]` ("Type alias arity mismatch") at compile time.

        Pin both the message AND the error code so a future
        refactor that re-routes through a sibling diagnostic with
        the same text but a different code is caught.
        """
        errs = _check_err("""
type Pair<A, B> = fn(A -> B) effects(pure);

public fn main(@Pair<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
""", "expects 2 type argument(s) but 1 supplied")
        e133 = [e for e in errs if e.error_code == "E133"]
        assert e133, (
            f"Expected at least one diagnostic with error_code=E133; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    def test_alias_arity_mismatch_too_many_e133(self) -> None:
        """Symmetric case: too many type-args also rejected with E133."""
        errs = _check_err("""
type Single<T> = Option<T>;

public fn main(@Single<Int, Bool> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
""", "expects 1 type argument(s) but 2 supplied")
        e133 = [e for e in errs if e.error_code == "E133"]
        assert e133, (
            f"Expected at least one diagnostic with error_code=E133; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    def test_alias_zero_args_when_zero_expected_ok(self) -> None:
        """A non-parameterised alias accepts no type-args.  Pin
        the arity check doesn't false-positive on the
        zero-expected / zero-supplied case."""
        _check_ok("""
type Year = Int;

public fn current(@Unit -> @Year)
  requires(true) ensures(true) effects(pure)
{ 2026 }
""")

    # =================================================================
    # #648 — cyclic type aliases must produce [E132] at check time
    # =================================================================

    def test_cyclic_alias_two_way_e132(self) -> None:
        """`type A = B; type B = A` produces [E132] at check time
        instead of crashing codegen with RecursionError (#648).

        Also pins the diagnostic *payload* (cycle path + fix
        message) on this representative test — the other cyclic-
        alias tests below check error_code only, since the
        payload-shape contract is uniform across them.
        """
        errs = _check_err("""
type A = B;
type B = A;

public fn id(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  @A.0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )
        # Pin the cycle-path rendering in the description and the
        # `data`-as-alternative suggestion in the fix hint.  A
        # future refactor that changes the rendering would still
        # emit E132 but the payload contract these messages embody
        # — "you can tell *which* aliases form the cycle" and
        # "here's the alternative that supports self-reference" —
        # would silently regress without these assertions.
        assert "A -> B -> A" in e132[0].description, (
            f"Expected cycle path 'A -> B -> A' in description; "
            f"got: {e132[0].description!r}"
        )
        assert "data" in e132[0].fix, (
            f"Expected fix hint to suggest `data` as the alternative "
            f"for self-referential types; got: {e132[0].fix!r}"
        )

    def test_cyclic_alias_self_e132(self) -> None:
        """`type A = A` is the degenerate self-cycle case (#648)."""
        errs = _check_err("""
type A = A;

public fn id(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  @A.0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    def test_cyclic_alias_three_way_e132(self) -> None:
        """`A -> B -> C -> A` three-way cycle also flagged (#648)."""
        errs = _check_err("""
type A = B;
type B = C;
type C = A;

public fn id(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  @A.0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    def test_cyclic_alias_refinement_e132(self) -> None:
        """Cycles through a `RefinementType` wrapper (`type A = { @B
        | true }; type B = A`) also flagged.  Pins the
        `_alias_chain_target` helper's `RefinementType.base_type`
        peeling — codegen's `_type_expr_to_wasm_type` recurses
        through refinements unconditionally, so a cycle hidden
        behind one is still a codegen-crash cycle (#648)."""
        errs = _check_err("""
type A = { @B | true };
type B = A;

public fn id(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  @A.0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    def test_acyclic_alias_chain_ok(self) -> None:
        """`type IntAlias = Int; type Pair = IntAlias` is an
        acyclic chain — must pass without false-positive E132 (#648)."""
        _check_ok("""
type IntAlias = Int;
type Pair = IntAlias;

public fn id(@Pair -> @Pair)
  requires(true) ensures(true) effects(pure)
{
  @Pair.0
}
""")

    # Line 84: Array/Tuple without type_args
    def test_array_without_type_args(self) -> None:
        """Bare Array (no type args) is accepted as AdtType(Array, ())."""
        _check_ok("""
private fn f(@Array -> @Array)
  requires(true) ensures(true) effects(pure)
{ @Array.0 }
""")

    def test_tuple_without_type_args(self) -> None:
        """Bare Tuple (no type args) is accepted as AdtType(Tuple, ())."""
        _check_ok("""
private fn f(@Tuple -> @Tuple)
  requires(true) ensures(true) effects(pure)
{ @Tuple.0 }
""")

    # Lines 117-118: EffectSet with type variable (effect row variable)
    def test_effect_set_with_type_variable(self) -> None:
        """A forall type variable used in an effect set becomes a row var."""
        _check_ok("""
effect Console {
  op print(String -> Unit);
}

private forall<E> fn f(@Int -> @Int)
  requires(true) ensures(true) effects(<Console, E>)
{ @Int.0 }
""")

    # Lines 123-127: QualifiedEffectRef in effect set
    def test_qualified_effect_ref_in_effect_set(self) -> None:
        """Module-qualified effect ref in effects(<Mod.Effect>) is accepted."""
        _check_ok("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(<IO.Write>)
{ @Int.0 }
""")

    # Line 130: _resolve_effect_row fallback to PureEffectRow
    # This is a defensive branch for unknown EffectRow types.
    # Hard to trigger from source, so test via unit API.
    def test_resolve_effect_row_unknown_returns_pure(self) -> None:
        """Unknown EffectRow type falls back to PureEffectRow."""
        from vera.checker.core import TypeChecker
        from vera.environment import TypeEnv
        from vera.types import PureEffectRow

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        bogus_row = ast.EffectRow(span=None)
        result = checker._resolve_effect_row(bogus_row)
        assert isinstance(result, PureEffectRow)

    # Lines 139-144: QualifiedEffectRef in _resolve_effect_ref
    def test_resolve_effect_ref_qualified(self) -> None:
        """_resolve_effect_ref handles QualifiedEffectRef."""
        from vera.checker.core import TypeChecker
        from vera.environment import TypeEnv
        from vera.types import EffectInstance

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        ref = ast.QualifiedEffectRef(
            module="IO", name="Write", type_args=None, span=None,
        )
        result = checker._resolve_effect_ref(ref)
        assert isinstance(result, EffectInstance)
        assert result.name == "IO.Write"
        assert result.type_args == ()

    def test_resolve_effect_ref_unknown_returns_none(self) -> None:
        """_resolve_effect_ref returns None for unknown node types."""
        from vera.checker.core import TypeChecker
        from vera.environment import TypeEnv

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        bogus = ast.EffectRefNode(span=None)
        result = checker._resolve_effect_ref(bogus)
        assert result is None

    # Line 169: _slot_type_name with no type_args — returns bare name
    def test_slot_type_name_no_type_args(self) -> None:
        """_slot_type_name with no type_args returns the bare type name."""
        from vera.checker.core import TypeChecker
        from vera.environment import TypeEnv

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        assert checker._slot_type_name("Int", None) == "Int"
        assert checker._slot_type_name("Bool", ()) == "Bool"

    # Lines 187-189: FunctionType unification in _unify_for_inference
    def test_function_type_unification_inference(self) -> None:
        """_unify_for_inference with FunctionType patterns unifies
        parameter and return types."""
        from vera.checker.core import TypeChecker
        from vera.environment import TypeEnv
        from vera.types import (
            FunctionType, PureEffectRow, Type, TypeVar, PRIMITIVES,
        )

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        INT = PRIMITIVES["Int"]
        BOOL = PRIMITIVES["Bool"]

        tv_a = TypeVar("A")
        tv_b = TypeVar("B")
        pattern = FunctionType((tv_a,), tv_b, PureEffectRow())
        concrete = FunctionType((INT,), BOOL, PureEffectRow())

        mapping: dict[str, Type] = {}
        checker._unify_for_inference(pattern, concrete, mapping)
        assert mapping == {"A": INT, "B": BOOL}


# =====================================================================
# Contracts
# =====================================================================

class TestContracts:

    def test_requires_bool(self) -> None:
        _check_ok("""
private fn foo(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_requires_non_bool_error(self) -> None:
        _check_err("""
private fn bad(@Int -> @Int)
  requires(@Int.0) ensures(true) effects(pure)
{ @Int.0 }
""", "requires() predicate must be Bool")

    def test_ensures_bool(self) -> None:
        _check_ok("""
private fn foo(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ @Int.0 }
""")

    def test_ensures_non_bool_error(self) -> None:
        _check_err("""
private fn bad(@Int -> @Int)
  requires(true) ensures(@Int.result) effects(pure)
{ @Int.0 }
""", "ensures() predicate must be Bool")

    def test_decreases(self) -> None:
        _check_ok("""
private fn count(@Nat -> @Nat)
  requires(true) ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 }
  else { 1 + count(@Nat.0 - 1) }
}
""")

    def test_multiple_contracts(self) -> None:
        _check_ok("""
private fn clamp_to_range(@Int, @Int, @Int -> @Int)
  requires(@Int.1 <= @Int.2)
  ensures(@Int.result >= @Int.1)
  ensures(@Int.result <= @Int.2)
  effects(pure)
{
  if @Int.0 < @Int.1 then { @Int.1 }
  else {
    if @Int.0 > @Int.2 then { @Int.2 }
    else { @Int.0 }
  }
}
""")

    def test_old_new_in_ensures(self) -> None:
        _check_ok("""
private fn incr(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
""")

    def test_old_outside_ensures_error(self) -> None:
        _check_err("""
private fn bad(@Unit -> @Unit)
  requires(old(State<Int>) > 0)
  ensures(true)
  effects(<State<Int>>)
{ () }
""", "old() is only valid inside ensures")


# =====================================================================
# Error accumulation and edge cases
# =====================================================================

class TestErrorAccumulation:

    def test_multiple_errors(self) -> None:
        """Multiple type errors in one file are all reported."""
        errs = _errors("""
private fn bad(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = 42;
  @Int.0
}
""")
        # At least one error expected (let type mismatch or unresolved slot)
        assert len(errs) >= 1

    def test_empty_program(self) -> None:
        """An empty program type-checks cleanly."""
        _check_ok("")

    def test_data_only_program(self) -> None:
        """A program with only data declarations type-checks cleanly."""
        _check_ok("""
private data Color { Red, Green, Blue }
private data Option<T> { None, Some(T) }
""")

    def test_type_error_has_location(self) -> None:
        """Type errors include source location."""
        errs = _errors("""
private fn bad(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        assert len(errs) >= 1
        assert errs[0].location.line > 0
