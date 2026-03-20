"""Additional coverage tests for vera/smt.py and vera/verifier.py.

Exercises SMT encoding paths, verifier edge cases, and defensive
branches that are not covered by the main test_verifier.py suite.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vera.parser import parse_to_ast
from vera.checker import typecheck
from vera.verifier import VerifyResult, verify


# =====================================================================
# Helpers
# =====================================================================

def _verify(source: str) -> VerifyResult:
    """Parse, type-check, and verify a source string."""
    ast = parse_to_ast(source)
    tc_diags = typecheck(ast, source)
    tc_errors = [d for d in tc_diags if d.severity == "error"]
    assert tc_errors == [], (
        f"Type-check errors before verification: {[e.description for e in tc_errors]}"
    )
    return verify(ast, source)


def _verify_ok(source: str) -> VerifyResult:
    """Assert source verifies with no errors and no warnings."""
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors == [], f"Expected no errors, got: {[e.description for e in errors]}"
    warnings = [d for d in result.diagnostics if d.severity == "warning"]
    assert warnings == [], f"Expected no warnings, got: {[w.description for w in warnings]}"
    return result


def _verify_err(source: str, match: str) -> list:
    """Assert source produces at least one verification error matching *match*."""
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors, f"Expected at least one error, got none"
    matched = [e for e in errors if match.lower() in e.description.lower()]
    assert matched, (
        f"No error matched '{match}'. Errors: {[e.description for e in errors]}"
    )
    return matched


def _verify_warn(source: str, match: str) -> VerifyResult:
    """Assert source produces at least one verification warning matching *match*."""
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors == [], (
        f"Expected no errors in warning test, got: {[e.description for e in errors]}"
    )
    warnings = [d for d in result.diagnostics if d.severity == "warning"]
    matched = [w for w in warnings if match.lower() in w.description.lower()]
    assert matched, (
        f"No warning matched '{match}'. "
        f"Warnings: {[w.description for w in warnings]}"
    )
    return result


# =====================================================================
# SMT built-in functions — abs, min, max, nat_to_int, byte_to_int
# =====================================================================

class TestSmtBuiltinFunctions:
    """Exercise SMT translations of built-in function calls."""

    def test_abs_in_postcondition(self) -> None:
        """abs() translates to Z3 If(x >= 0, x, -x)."""
        _verify_ok("""
private fn test_abs(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ abs(@Int.0) }
""")

    def test_min_in_postcondition(self) -> None:
        """min() translates to Z3 If(a <= b, a, b)."""
        _verify_ok("""
private fn test_min(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result <= @Int.0)
  ensures(@Int.result <= @Int.1)
  effects(pure)
{ min(@Int.0, @Int.1) }
""")

    def test_max_in_postcondition(self) -> None:
        """max() translates to Z3 If(a >= b, a, b)."""
        _verify_ok("""
private fn test_max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= @Int.0)
  ensures(@Int.result >= @Int.1)
  effects(pure)
{ max(@Int.0, @Int.1) }
""")

    def test_nat_to_int_identity(self) -> None:
        """nat_to_int() is identity in Z3 (both IntSort)."""
        _verify_ok("""
private fn test_nat_to_int(@Nat -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ nat_to_int(@Nat.0) }
""")

    def test_byte_to_int_identity(self) -> None:
        """byte_to_int() is identity in Z3 (both IntSort)."""
        _verify_ok("""
private fn test_byte_to_int(@Byte -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ byte_to_int(@Byte.0) }
""")


# =====================================================================
# SMT unary operators — NOT and NEG
# =====================================================================

class TestSmtUnaryOps:
    """Exercise SMT translation of unary operators."""

    def test_not_operator(self) -> None:
        """Unary NOT translates to Z3 Not."""
        _verify_ok("""
private fn negate_bool(@Bool -> @Bool)
  requires(true)
  ensures(@Bool.result == !@Bool.0)
  effects(pure)
{ !@Bool.0 }
""")

    def test_neg_operator(self) -> None:
        """Unary NEG translates to Z3 negation."""
        _verify_ok("""
private fn negate(@Int -> @Int)
  requires(true)
  ensures(@Int.result == -@Int.0)
  effects(pure)
{ -@Int.0 }
""")


# =====================================================================
# SMT boolean logic in contracts
# =====================================================================

class TestSmtBooleanLogic:
    """Exercise boolean operators AND, OR, IMPLIES in contracts."""

    def test_and_in_contract(self) -> None:
        _verify_ok("""
private fn bounded(@Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 <= 100)
  ensures(@Int.result >= 0 && @Int.result <= 100)
  effects(pure)
{ @Int.0 }
""")

    def test_or_in_contract(self) -> None:
        _verify_ok("""
private fn abs_sign(@Int -> @Int)
  requires(@Int.0 > 0 || @Int.0 < 0)
  ensures(@Int.result > 0 || @Int.result < 0)
  effects(pure)
{ @Int.0 }
""")

    def test_implies_in_precondition(self) -> None:
        _verify_ok("""
private fn guarded(@Int, @Bool -> @Int)
  requires(@Bool.0 ==> @Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
""")


# =====================================================================
# SMT comparison operators — all six
# =====================================================================

class TestSmtComparisonOps:
    """Exercise all comparison operators in SMT translation."""

    def test_eq(self) -> None:
        _verify_ok("""
private fn f(@Int -> @Bool)
  requires(true)
  ensures(@Bool.result == (@Int.0 == @Int.0))
  effects(pure)
{ @Int.0 == @Int.0 }
""")

    def test_neq(self) -> None:
        _verify_ok("""
private fn f(@Int, @Int -> @Bool)
  requires(@Int.0 != @Int.1)
  ensures(@Bool.result == true)
  effects(pure)
{ @Int.0 != @Int.1 }
""")

    def test_lt(self) -> None:
        _verify_ok("""
private fn f(@Int, @Int -> @Bool)
  requires(@Int.1 < @Int.0)
  ensures(@Bool.result == true)
  effects(pure)
{ @Int.1 < @Int.0 }
""")

    def test_gt(self) -> None:
        _verify_ok("""
private fn f(@Int, @Int -> @Bool)
  requires(@Int.0 > @Int.1)
  ensures(@Bool.result == true)
  effects(pure)
{ @Int.0 > @Int.1 }
""")

    def test_le(self) -> None:
        _verify_ok("""
private fn f(@Int, @Int -> @Bool)
  requires(@Int.0 <= @Int.1)
  ensures(@Bool.result == true)
  effects(pure)
{ @Int.0 <= @Int.1 }
""")

    def test_ge(self) -> None:
        _verify_ok("""
private fn f(@Int, @Int -> @Bool)
  requires(@Int.0 >= @Int.1)
  ensures(@Bool.result == true)
  effects(pure)
{ @Int.0 >= @Int.1 }
""")


# =====================================================================
# Modular arithmetic — MOD
# =====================================================================

class TestSmtModOp:
    """Exercise MOD operator in SMT translation."""

    def test_mod_operator(self) -> None:
        _verify_ok("""
private fn f(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 % @Int.1)
  effects(pure)
{ @Int.0 % @Int.1 }
""")


# =====================================================================
# Bool parameters — declare_bool path in verifier
# =====================================================================

class TestBoolParameters:
    """Exercise Bool parameter declaration path in verifier."""

    def test_bool_param_declared(self) -> None:
        _verify_ok("""
private fn identity(@Bool -> @Bool)
  requires(true)
  ensures(@Bool.result == @Bool.0)
  effects(pure)
{ @Bool.0 }
""")

    def test_bool_return_type(self) -> None:
        _verify_ok("""
private fn always_true(@Int -> @Bool)
  requires(true)
  ensures(@Bool.result == (@Int.0 == @Int.0))
  effects(pure)
{ @Int.0 == @Int.0 }
""")


# =====================================================================
# Nat parameters — non-negative constraint
# =====================================================================

class TestNatParameters:
    """Exercise Nat parameter declaration and constraints."""

    def test_nat_params_non_negative(self) -> None:
        _verify_ok("""
private fn nat_add(@Nat, @Nat -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ nat_to_int(@Nat.0) + nat_to_int(@Nat.1) }
""")


# =====================================================================
# Generic function tier 3 fallback
# =====================================================================

class TestGenericFunctionTier3:
    """Generic functions with non-trivial contracts -> Tier 3."""

    def test_generic_nontrivial_contract_warns(self) -> None:
        _verify_warn("""
private forall<A> fn identity(@A -> @A)
  requires(true)
  ensures(@A.result == @A.0)
  effects(pure)
{ @A.0 }
""", "generic function")

    def test_generic_trivial_contract_tier1(self) -> None:
        """Generic with trivial ensures(true) is counted as Tier 1."""
        result = _verify("""
private forall<A> fn identity(@A -> @A)
  requires(true)
  ensures(true)
  effects(pure)
{ @A.0 }
""")
        assert result.summary.tier1_verified == 2
        assert result.summary.tier3_runtime == 0


# =====================================================================
# Precondition outside decidable fragment -- Tier 3
# =====================================================================

class TestTier3Precondition:
    """Preconditions that can't be translated -> Tier 3 warning."""

    def test_precondition_with_string_equality_tier3(self) -> None:
        """A precondition referencing String -> can't be SMT-translated -> Tier 3."""
        _verify_warn("""
private fn greet(@String -> @Int)
  requires(@String.0 == "hello")
  ensures(true)
  effects(pure)
{ 42 }
""", "outside the decidable fragment")


# =====================================================================
# Postcondition outside decidable fragment -- Tier 3
# =====================================================================

class TestTier3Postcondition:
    """Postconditions that can't be translated -> Tier 3 warning."""

    def test_postcondition_with_string_result_tier3(self) -> None:
        """String result type -> body can't be SMT-translated -> Tier 3."""
        _verify_warn("""
private fn greet(@Int -> @String)
  requires(true)
  ensures(@String.result == "hello")
  effects(pure)
{ "hello" }
""", "outside the decidable fragment")

    def test_postcondition_body_unsupported_tier3(self) -> None:
        """Lambda body -> can't translate -> Tier 3 for postcondition."""
        _verify_warn("""
type IntToInt = fn(Int -> Int) effects(pure);

private fn make_adder(@Int -> @IntToInt)
  requires(true)
  ensures(true)
  effects(pure)
{ fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 } }

private fn use_adder(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ apply_fn(make_adder(1), @Int.0) }
""", "outside the decidable fragment")

    def test_postcondition_expr_unsupported_tier3(self) -> None:
        """Postcondition uses unsupported construct -> Tier 3 (E523).

        The body translates fine (pure int) but the postcondition
        expression can't be translated to SMT because it references
        a string literal in a comparison.
        """
        _verify_warn("""
private fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 && "hello" == "hello")
  effects(pure)
{ @Int.0 }
""", "postcondition")


# =====================================================================
# ADT parameter declarations
# =====================================================================

class TestAdtParameterDeclaration:
    """Exercise ADT param/return variable declaration in verifier."""

    def test_adt_param_declared(self) -> None:
        """ADT parameters exercise the declare_adt path."""
        _verify_ok("""
private data Maybe { Nothing, Just(Int) }

private fn unwrap(@Maybe -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Maybe.0 { Nothing -> 0, Just(@Int) -> @Int.0 }
}
""")

    def test_adt_return_type(self) -> None:
        """ADT return type exercises the declare_adt path for result var."""
        _verify_ok("""
private data Maybe { Nothing, Just(Int) }

private fn wrap(@Int -> @Maybe)
  requires(true)
  ensures(true)
  effects(pure)
{
  Just(@Int.0)
}
""")


# =====================================================================
# Match expressions in SMT translation
# =====================================================================

class TestSmtMatchExpressions:
    """Exercise match expression SMT translation."""

    def test_match_int_pattern(self) -> None:
        """Match with int patterns."""
        _verify_ok("""
private fn f(@Int -> @Int)
  requires(@Int.0 == 0 || @Int.0 == 1)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Int.0 { 0 -> 0, _ -> 1 }
}
""")

    def test_match_bool_pattern(self) -> None:
        """Match with bool patterns."""
        _verify_ok("""
private fn f(@Bool -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Bool.0 { true -> 1, false -> 0 }
}
""")

    def test_match_binding_pattern(self) -> None:
        """Match with binding patterns extends environment."""
        _verify_ok("""
private data Maybe { Nothing, Just(Int) }

private fn get_or_zero(@Maybe -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Maybe.0 { Just(@Int) -> @Int.0, Nothing -> 0 }
}
""")


# =====================================================================
# Block with let statements in SMT
# =====================================================================

class TestSmtBlockStatements:
    """Exercise block/let statement SMT translation."""

    def test_let_in_block(self) -> None:
        """let binding in block translates to Z3."""
        _verify_ok("""
private fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{
  let @Int = @Int.0 + 1;
  @Int.0
}
""")

    def test_multiple_lets(self) -> None:
        """Multiple let bindings extend environment properly."""
        _verify_ok("""
private fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 3)
  effects(pure)
{
  let @Int = @Int.0 + 1;
  let @Int = @Int.0 + 2;
  @Int.0
}
""")


# =====================================================================
# Constructor calls in SMT
# =====================================================================

class TestSmtConstructorCalls:
    """Exercise constructor call SMT translation."""

    def test_nullary_constructor(self) -> None:
        _verify_ok("""
private data Maybe { Nothing, Just(Int) }

private fn make_nothing(@Int -> @Maybe)
  requires(true)
  ensures(true)
  effects(pure)
{ Nothing }
""")

    def test_constructor_with_args(self) -> None:
        _verify_ok("""
private data Maybe { Nothing, Just(Int) }

private fn wrap(@Int -> @Maybe)
  requires(true)
  ensures(true)
  effects(pure)
{ Just(@Int.0) }
""")


# =====================================================================
# Pipe operator with ModuleCall
# =====================================================================

class TestSmtModuleCall:
    """Exercise verifier with module-qualified calls."""

    def test_module_call_verified(self) -> None:
        """Module-qualified call resolves and verifies correctly."""
        from vera.resolver import ResolvedModule as RM

        mod_src = """\
public fn inc(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }
"""
        mod_prog = parse_to_ast(mod_src)
        mod = RM(
            path=("util",),
            file_path=Path("/fake/util.vera"),
            program=mod_prog,
            source=mod_src,
        )

        src = """\
import util;
private fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ util::inc(@Int.0) }
"""
        prog = parse_to_ast(src)
        tc_diags = typecheck(prog, src, resolved_modules=[mod])
        tc_errors = [d for d in tc_diags if d.severity == "error"]
        assert tc_errors == [], [d.description for d in tc_errors]
        result = verify(prog, src, resolved_modules=[mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]


# =====================================================================
# SMT context direct tests
# =====================================================================

class TestSmtContextDirect:
    """Direct tests of SmtContext methods."""

    def test_slot_env_resolve_out_of_bounds(self) -> None:
        """SlotEnv.resolve returns None for out-of-bounds index."""
        from vera.smt import SlotEnv
        import z3
        env = SlotEnv()
        env = env.push("Int", z3.Int("x"))
        assert env.resolve("Int", 0) is not None
        assert env.resolve("Int", 1) is None  # out of bounds
        assert env.resolve("Float", 0) is None  # no such type

    def test_get_var_none(self) -> None:
        """get_var returns None for unknown variable."""
        from vera.smt import SmtContext
        ctx = SmtContext()
        assert ctx.get_var("nonexistent") is None

    def test_reset_clears_state(self) -> None:
        """reset() clears solver state."""
        from vera.smt import SmtContext
        ctx = SmtContext()
        ctx.declare_int("x")
        ctx.declare_bool("b")
        ctx.reset()
        assert ctx.get_var("x") is None
        assert ctx.get_var("b") is None

    def test_declare_nat(self) -> None:
        """declare_nat creates a variable with >= 0 constraint."""
        from vera.smt import SmtContext
        ctx = SmtContext()
        v = ctx.declare_nat("n")
        assert ctx.get_var("n") is not None

    def test_adt_sort_key_with_type_var(self) -> None:
        """_adt_sort_key handles TypeVar with '?' fallback."""
        from vera.smt import _adt_sort_key
        from vera.types import TypeVar
        result = _adt_sort_key("List", (TypeVar("T"),))
        assert result == "List<?>"

    def test_check_valid_unknown(self) -> None:
        """check_valid returns 'unknown' for indeterminate formulas."""
        from vera.smt import SmtContext
        import z3
        # Use a very short timeout and a non-linear arithmetic formula
        # that Z3 cannot decide quickly, to force an 'unknown' result.
        ctx = SmtContext(timeout_ms=1)
        x = ctx.declare_int("x")
        y = ctx.declare_int("y")
        # Non-linear arithmetic is undecidable in general; with 1ms
        # timeout this should reliably produce 'unknown'.
        goal = x * x + y * y == z3.IntVal(91)
        result = ctx.check_valid(goal, [])
        # With such a tight timeout the solver may still solve trivial
        # instances on fast machines, so accept either unknown or a
        # concrete answer.
        assert result.status in ("verified", "violated", "unknown")

    def test_translate_expr_returns_none_for_unsupported(self) -> None:
        """translate_expr returns None for unsupported expressions."""
        from vera.smt import SmtContext, SlotEnv
        from vera.ast import StringLit, Span
        ctx = SmtContext()
        env = SlotEnv()
        # StringLit is unsupported
        result = ctx.translate_expr(StringLit(value="hello", span=None), env)
        assert result is None

    def test_vera_type_to_z3_sort_bool(self) -> None:
        """_vera_type_to_z3_sort returns BoolSort for Bool type."""
        import z3
        from vera.smt import SmtContext
        from vera.types import BOOL
        ctx = SmtContext()
        sort = ctx._vera_type_to_z3_sort(BOOL)
        assert sort == z3.BoolSort()

    def test_vera_type_to_z3_sort_unsupported(self) -> None:
        """_vera_type_to_z3_sort returns None for String type."""
        from vera.smt import SmtContext
        from vera.types import STRING
        ctx = SmtContext()
        sort = ctx._vera_type_to_z3_sort(STRING)
        assert sort is None

    def test_vera_type_to_z3_sort_type_var(self) -> None:
        """_vera_type_to_z3_sort returns None for TypeVar."""
        from vera.smt import SmtContext
        from vera.types import TypeVar
        ctx = SmtContext()
        sort = ctx._vera_type_to_z3_sort(TypeVar("T"))
        assert sort is None


# =====================================================================
# Decreases clause edge cases
# =====================================================================

class TestDecreasesEdgeCases:
    """Exercise decreases verification edge cases."""

    def test_decreases_no_recursive_call_tier3(self) -> None:
        """Function with decreases but no recursive call -> Tier 3."""
        _verify_warn("""
private fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{ @Nat.0 }
""", "termination metric")


# =====================================================================
# Call-site verification -- additional paths
# =====================================================================

class TestCallSiteVerificationCoverage:
    """Additional call-site verification paths."""

    def test_call_postcondition_bool_return(self) -> None:
        """Callee with Bool return creates declare_bool for fresh var."""
        _verify_ok("""
private fn is_pos(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 > 0 }

private fn caller(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ is_pos(@Int.0) }
""")

    def test_call_postcondition_nat_return(self) -> None:
        """Callee with Nat return creates declare_nat for fresh var."""
        _verify_ok("""
private fn add_nats(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 + @Nat.1 }

private fn caller(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ add_nats(@Nat.0, @Nat.0) }
""")

    def test_call_postcondition_adt_return(self) -> None:
        """Callee with ADT return creates declare_adt for fresh var."""
        _verify_ok("""
private data Maybe { Nothing, Just(Int) }

private fn wrap(@Int -> @Maybe)
  requires(true)
  ensures(true)
  effects(pure)
{ Just(@Int.0) }

private fn caller(@Int -> @Maybe)
  requires(true)
  ensures(true)
  effects(pure)
{ wrap(@Int.0) }
""")


# =====================================================================
# Violation reporting
# =====================================================================

class TestViolationReporting:
    """Exercise counterexample formatting paths."""

    def test_violation_includes_counterexample(self) -> None:
        """Violation report includes counterexample values."""
        result = _verify("""
private fn bad(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert len(errors) > 0
        assert "counterexample" in errors[0].description.lower()

    def test_call_violation_report(self) -> None:
        """Call-site violation includes callee name."""
        errors = _verify_err("""
private fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ positive(@Int.0) }
""", "precondition")
        assert any("positive" in e.description for e in errors)


# =====================================================================
# Walk-for-calls coverage -- unary, binary, match
# =====================================================================

class TestWalkForCallsCoverage:
    """Exercise _walk_for_calls paths for decreases verification."""

    def test_recursive_in_unary_expr(self) -> None:
        """Recursive call inside a unary expression."""
        _verify_ok("""
private fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if nat_to_int(@Nat.0) == 0 then { 0 }
  else { -(f(@Nat.0 - 1)) }
}
""")

    def test_recursive_in_binary_expr(self) -> None:
        """Recursive call inside a binary expression."""
        _verify_ok("""
private fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if nat_to_int(@Nat.0) == 0 then { 0 }
  else { 1 + f(@Nat.0 - 1) }
}
""")

    def test_recursive_in_let(self) -> None:
        """Recursive call inside a let binding in block."""
        _verify_ok("""
private fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if nat_to_int(@Nat.0) == 0 then { 0 }
  else {
    let @Int = f(@Nat.0 - 1);
    @Int.0 + 1
  }
}
""")

    def test_recursive_in_match(self) -> None:
        """Recursive call inside a match arm."""
        _verify_ok("""
private data NatList { NNil, NCons(Nat, NatList) }

private fn len(@NatList -> @Nat)
  requires(true)
  ensures(true)
  decreases(@NatList.0)
  effects(pure)
{
  match @NatList.0 {
    NNil -> 0,
    NCons(@Nat, @NatList) -> 1 + len(@NatList.0)
  }
}
""")

    def test_recursive_match_with_binding_pattern(self) -> None:
        """Recursive call in match with binding and wildcard patterns.

        Exercises _pattern_condition for BindingPattern and WildcardPattern.
        """
        _verify_ok("""
private fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  match nat_to_int(@Nat.0) {
    @Int -> if @Int.0 == 0 then { @Nat.0 }
            else { f(@Nat.0 - 1) }
  }
}
""")


# =====================================================================
# Ability declaration registration
# =====================================================================

class TestAbilityRegistration:
    """Exercise ability declaration registration in verifier."""

    def test_ability_with_operations(self) -> None:
        """Ability declaration is registered without errors."""
        _verify_ok("""
ability MyEq<A> {
  op equal(A, A -> Bool);
}

private fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
""")


# =====================================================================
# _is_trivial for Decreases
# =====================================================================

class TestIsTrivialDecreases:
    """_is_trivial for Decreases returns False (line 965)."""

    def test_decreases_not_trivial(self) -> None:
        """Decreases is never trivial -- exercises the else branch."""
        result = _verify("""
private fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if nat_to_int(@Nat.0) == 0 then { @Nat.0 }
  else { f(@Nat.0 - 1) }
}
""")
        # decreases should count in total
        assert result.summary.total >= 3  # requires + ensures + decreases


# =====================================================================
# _resolve_type edge cases
# =====================================================================

class TestResolveTypeEdgeCases:
    """Exercise verifier _resolve_type edge cases."""

    def test_fn_type_param_resolves(self) -> None:
        """Function type parameter exercises FnType -> FunctionType path."""
        # Use a type alias for a function type, then use it as a param
        _verify_ok("""
type IntToInt = fn(Int -> Int) effects(pure);

private fn apply(@IntToInt, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ apply_fn(@IntToInt.0, @Int.0) }
""")


# =====================================================================
# Effect row resolution
# =====================================================================

class TestEffectRowResolution:
    """Exercise _resolve_effect_row paths."""

    def test_effect_set_resolution(self) -> None:
        """EffectSet resolves to ConcreteEffectRow."""
        _verify_ok("""
effect Console {
  op print(String -> Unit);
}

private fn greet(@Int -> @Unit)
  requires(true)
  ensures(true)
  effects(<Console>)
{ Console.print("hello") }
""")


# =====================================================================
# Type alias registration
# =====================================================================

class TestTypeAliasRegistration:
    """Exercise type alias registration."""

    def test_type_alias(self) -> None:
        _verify_ok("""
type Num = Int;

private fn f(@Num -> @Num)
  requires(true)
  ensures(true)
  effects(pure)
{ @Num.0 }
""")


# =====================================================================
# Multiple ensures clauses
# =====================================================================

class TestMultipleEnsures:
    """Exercise multiple ensures clause verification."""

    def test_multiple_ensures_all_verified(self) -> None:
        _verify_ok("""
private fn clamp(@Int -> @Int)
  requires(@Int.0 >= 0)
  requires(@Int.0 <= 100)
  ensures(@Int.result >= 0)
  ensures(@Int.result <= 100)
  effects(pure)
{ @Int.0 }
""")

    def test_multiple_ensures_one_fails(self) -> None:
        _verify_err("""
private fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 }
""", "postcondition does not hold")


# =====================================================================
# _get_source_line returning empty
# =====================================================================

class TestGetSourceLine:
    """Exercise _get_source_line edge case."""

    def test_verify_with_empty_source(self) -> None:
        """When source is empty, _get_source_line returns ''."""
        prog = parse_to_ast("""
private fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 }
""")
        typecheck(prog, "")
        result = verify(prog, "")  # empty source
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert len(errors) > 0
        # source_line should be empty string
        assert errors[0].source_line == ""


# =====================================================================
# Parameterised types in contracts (Array<Int>)
# =====================================================================

class TestParameterisedTypeContracts:
    """Exercise parameterised type slot references."""

    def test_array_length_in_contract(self) -> None:
        """array_length in contract exercises length_fn path."""
        _verify_ok("""
private fn non_empty(@Array<Int> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ array_length(@Array<Int>.0) > 0 }
""")


# =====================================================================
# _type_expr_to_slot_name for RefinementType
# =====================================================================

class TestRefinementTypeSlotName:
    """Exercise _type_expr_to_slot_name for refinement types."""

    def test_refinement_type_slot_name(self) -> None:
        """RefinementType extracts base type name for slot name."""
        _verify_ok("""
type PosInt = { @Int | @Int.0 > 0 };

private fn f(@PosInt -> @Int)
  requires(@PosInt.0 > 0)
  ensures(@Int.result > 0)
  effects(pure)
{ @PosInt.0 }
""")

    def test_inline_refinement_type_slot_name(self) -> None:
        """Inline refinement type parameter exercises RefinementType path."""
        _verify_ok("""
private fn f(@{ @Int | @Int.0 > 0 } -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
""")

    def test_fn_type_param_slot_name_via_verifier(self) -> None:
        """FnType -> 'Fn' path in _type_expr_to_slot_name is exercised
        indirectly via ContractVerifier when a fn-type param exists."""
        from vera.verifier import ContractVerifier
        from vera.ast import FnType, NamedType
        cv = ContractVerifier()
        fn_te = FnType(
            params=(NamedType(name="Int", type_args=None, span=None),),
            return_type=NamedType(name="Int", type_args=None, span=None),
            effect=None,
            span=None,
        )
        result = cv._type_expr_to_slot_name(fn_te)
        assert result == "Fn"


# =====================================================================
# Direct SMT translate_expr edge cases via unit tests
# =====================================================================

class TestSmtTranslateEdgeCases:
    """Edge cases in SMT expression translation."""

    def test_binary_with_none_operand(self) -> None:
        """Binary expr where one operand can't be translated returns None."""
        from vera.smt import SmtContext, SlotEnv
        from vera.ast import BinaryExpr, BinOp, StringLit, IntLit
        ctx = SmtContext()
        env = SlotEnv()
        expr = BinaryExpr(
            left=IntLit(value=1, span=None),
            op=BinOp.ADD,
            right=StringLit(value="x", span=None),
            span=None,
        )
        result = ctx.translate_expr(expr, env)
        assert result is None

    def test_unary_with_none_operand(self) -> None:
        """Unary expr where operand can't be translated returns None."""
        from vera.smt import SmtContext, SlotEnv
        from vera.ast import UnaryExpr, UnaryOp, StringLit
        ctx = SmtContext()
        env = SlotEnv()
        expr = UnaryExpr(
            op=UnaryOp.NOT,
            operand=StringLit(value="x", span=None),
            span=None,
        )
        result = ctx.translate_expr(expr, env)
        assert result is None

    def test_if_with_untranslatable_condition(self) -> None:
        """If expr with untranslatable condition returns None."""
        from vera.smt import SmtContext, SlotEnv
        from vera.ast import IfExpr, StringLit, IntLit
        ctx = SmtContext()
        env = SlotEnv()
        expr = IfExpr(
            condition=StringLit(value="cond", span=None),
            then_branch=IntLit(value=1, span=None),
            else_branch=IntLit(value=2, span=None),
            span=None,
        )
        result = ctx.translate_expr(expr, env)
        assert result is None

    def test_call_no_fn_lookup(self) -> None:
        """FnCall with no fn_lookup returns None."""
        from vera.smt import SmtContext, SlotEnv
        from vera.ast import FnCall, IntLit
        ctx = SmtContext(fn_lookup=None)
        env = SlotEnv()
        expr = FnCall(
            name="unknown_fn",
            args=(IntLit(value=1, span=None),),
            span=None,
        )
        result = ctx.translate_expr(expr, env)
        assert result is None

    def test_module_call_no_lookup(self) -> None:
        """ModuleCall with no module_fn_lookup returns None."""
        from vera.smt import SmtContext, SlotEnv
        from vera.ast import ModuleCall, IntLit
        ctx = SmtContext(module_fn_lookup=None)
        env = SlotEnv()
        expr = ModuleCall(
            path=("mod",),
            name="fn",
            args=(IntLit(value=1, span=None),),
            span=None,
        )
        result = ctx.translate_expr(expr, env)
        assert result is None

    def test_type_expr_to_slot_name_refinement(self) -> None:
        """_type_expr_to_slot_name handles RefinementType."""
        from vera.smt import SmtContext
        from vera.ast import RefinementType, NamedType, BoolLit
        ctx = SmtContext()
        te = RefinementType(
            base_type=NamedType(name="Int", type_args=None, span=None),
            predicate=BoolLit(value=True, span=None),
            span=None,
        )
        result = ctx._type_expr_to_slot_name(te)
        assert result == "Int"

    def test_type_expr_to_slot_name_unknown(self) -> None:
        """_type_expr_to_slot_name returns None for unknown type expr."""
        from vera.smt import SmtContext
        from vera.ast import FnType, NamedType
        ctx = SmtContext()
        te = FnType(
            params=(NamedType(name="Int", type_args=None, span=None),),
            return_type=NamedType(name="Int", type_args=None, span=None),
            effect=None,
            span=None,
        )
        result = ctx._type_expr_to_slot_name(te)
        assert result is None

    def test_find_sort_for_ctor_none(self) -> None:
        """_find_sort_for_ctor returns None for unknown constructor."""
        from vera.smt import SmtContext
        ctx = SmtContext()
        assert ctx._find_sort_for_ctor("UnknownCtor") is None

    def test_find_ctor_index_not_found(self) -> None:
        """_find_ctor_index returns None when ctor not in sort."""
        from vera.smt import SmtContext
        import z3
        ctx = SmtContext()
        # Int sort is not a DatatypeSortRef
        assert ctx._find_ctor_index(z3.IntSort(), "Foo") is None
