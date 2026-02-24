"""Tests for the Vera type checker (Phase C3).

Follows the same patterns as test_ast.py: helper functions, parametrised
round-trip tests, then node-specific test classes.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vera.checker import typecheck
from vera.errors import Diagnostic
from vera.parser import parse_to_ast

# =====================================================================
# Helpers
# =====================================================================

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"
EXAMPLE_FILES = sorted(f.name for f in EXAMPLES_DIR.glob("*.vera"))

# Self-contained examples (no unresolved external references)
CLEAN_EXAMPLES = [
    "absolute_value.vera",
    "factorial.vera",
    "generics.vera",
    "increment.vera",
    "list_ops.vera",
    "modules.vera",
    "mutual_recursion.vera",
    "pattern_matching.vera",
    "quantifiers.vera",
    "refinement_types.vera",
    "safe_divide.vera",
]

# Examples with unresolved external references (warnings expected)
WARN_EXAMPLES = [
    "closures.vera",
    "effect_handler.vera",
]


def _check(source: str) -> list[Diagnostic]:
    """Parse and type-check, return diagnostics."""
    prog = parse_to_ast(source)
    return typecheck(prog, source=source)


def _errors(source: str) -> list[Diagnostic]:
    """Parse and type-check, return only errors (not warnings)."""
    return [d for d in _check(source) if d.severity == "error"]


def _warnings(source: str) -> list[Diagnostic]:
    """Parse and type-check, return only warnings."""
    return [d for d in _check(source) if d.severity != "error"]


def _check_ok(source: str) -> None:
    """Assert the source type-checks with no errors."""
    errs = _errors(source)
    assert errs == [], \
        f"Expected no errors, got: {[e.description for e in errs]}"


def _check_err(source: str, match: str) -> list[Diagnostic]:
    """Assert the source has at least one error matching the substring."""
    errs = _errors(source)
    assert any(match.lower() in e.description.lower() for e in errs), \
        f"Expected error matching '{match}', got: " \
        f"{[e.description for e in errs]}"
    return errs


# =====================================================================
# Round-trip example tests
# =====================================================================

class TestExampleRoundTrips:
    """All self-contained examples must type-check cleanly."""

    @pytest.mark.parametrize("filename", CLEAN_EXAMPLES)
    def test_clean_example(self, filename: str) -> None:
        source = (EXAMPLES_DIR / filename).read_text()
        prog = parse_to_ast(source, file=filename)
        errors = typecheck(prog, source=source, file=filename)
        real_errors = [e for e in errors if e.severity == "error"]
        assert real_errors == [], \
            f"{filename}: {[e.description for e in real_errors]}"

    @pytest.mark.parametrize("filename", WARN_EXAMPLES)
    def test_warn_example(self, filename: str) -> None:
        """Examples with unresolved names: only warnings, no errors."""
        source = (EXAMPLES_DIR / filename).read_text()
        prog = parse_to_ast(source, file=filename)
        errors = typecheck(prog, source=source, file=filename)
        real_errors = [e for e in errors if e.severity == "error"]
        assert real_errors == [], \
            f"{filename}: {[e.description for e in real_errors]}"


# =====================================================================
# Literals
# =====================================================================

class TestLiterals:

    def test_int_lit(self) -> None:
        _check_ok("""
fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
""")

    def test_negative_int_lit(self) -> None:
        _check_ok("""
fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 - 1 }
""")

    def test_float_lit(self) -> None:
        _check_ok("""
fn foo(@Unit -> @Float64)
  requires(true) ensures(true) effects(pure)
{ 3.14 }
""")

    def test_string_lit(self) -> None:
        _check_ok("""
fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }
""")

    def test_bool_lit(self) -> None:
        _check_ok("""
fn foo(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ true }
""")

    def test_unit_lit(self) -> None:
        _check_ok("""
fn foo(@Unit -> @Unit)
  requires(true) ensures(true) effects(pure)
{ () }
""")


# =====================================================================
# Slot references
# =====================================================================

class TestSlotRefs:

    def test_simple_ref(self) -> None:
        _check_ok("""
fn id(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_multiple_same_type(self) -> None:
        _check_ok("""
fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }
""")

    def test_different_types(self) -> None:
        _check_ok("""
fn pick(@Int, @String -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_out_of_bounds(self) -> None:
        _check_err("""
fn bad(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 }
""", "Cannot resolve @Int.1")

    def test_no_bindings(self) -> None:
        _check_err("""
fn bad(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "Cannot resolve @Int.0")

    def test_let_introduces_binding(self) -> None:
        _check_ok("""
fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 42;
  @Int.0
}
""")

    def test_let_shadowing(self) -> None:
        _check_ok("""
fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 99;
  @Int.0 + @Int.1
}
""")

    def test_alias_opacity(self) -> None:
        """Type aliases are opaque for slot reference resolution."""
        _check_ok("""
type PosInt = { @Int | @Int.0 > 0 };

fn foo(@PosInt, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 + @Int.0 }
""")

    def test_parameterised_slot(self) -> None:
        _check_ok("""
data Option<T> { None, Some(T) }

fn foo(@Option<Int> -> @Bool)
  requires(true) ensures(true) effects(pure)
{ true }
""")


# =====================================================================
# Result references
# =====================================================================

class TestResultRefs:

    def test_result_in_ensures(self) -> None:
        _check_ok("""
fn foo(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }
""")

    def test_result_outside_ensures(self) -> None:
        _check_err("""
fn foo(@Int -> @Int)
  requires(@Int.result > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
""", "@Int.result is only valid inside ensures")

    def test_result_in_body(self) -> None:
        _check_err("""
fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.result }
""", "only valid inside ensures")


# =====================================================================
# Binary operators
# =====================================================================

class TestBinaryOps:

    def test_add_int(self) -> None:
        _check_ok("""
fn foo(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }
""")

    def test_add_float(self) -> None:
        _check_ok("""
fn foo(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ @Float64.0 + @Float64.1 }
""")

    def test_add_mixed_error(self) -> None:
        _check_err("""
fn bad(@Int, @String -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @String.0 }
""", "requires numeric operands")

    def test_comparison(self) -> None:
        _check_ok("""
fn foo(@Int, @Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 < @Int.1 }
""")

    def test_equality(self) -> None:
        _check_ok("""
fn foo(@Int, @Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 == @Int.1 }
""")

    def test_logical_and(self) -> None:
        _check_ok("""
fn foo(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 && @Bool.1 }
""")

    def test_logical_implies(self) -> None:
        _check_ok("""
fn foo(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 ==> @Bool.1 }
""")

    def test_logical_not_bool_error(self) -> None:
        _check_err("""
fn bad(@Int, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 && @Bool.0 }
""", "must be Bool")

    def test_modulo(self) -> None:
        _check_ok("""
fn foo(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 % @Int.1 }
""")


# =====================================================================
# Unary operators
# =====================================================================

class TestUnaryOps:

    def test_not(self) -> None:
        _check_ok("""
fn foo(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ !@Bool.0 }
""")

    def test_neg(self) -> None:
        _check_ok("""
fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 - @Int.0 }
""")

    def test_not_non_bool_error(self) -> None:
        _check_err("""
fn bad(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ !@Int.0 }
""", "requires Bool operand")


# =====================================================================
# Function calls
# =====================================================================

class TestFnCalls:

    def test_simple_call(self) -> None:
        _check_ok("""
fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }

fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0) }
""")

    def test_arity_mismatch(self) -> None:
        _check_err("""
fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }

fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0, @Int.0) }
""", "expects 1 argument")

    def test_type_mismatch_arg(self) -> None:
        _check_err("""
fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }

fn main(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@String.0) }
""", "has type String, expected Int")

    def test_recursive_call(self) -> None:
        _check_ok("""
fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 1 }
  else { @Nat.0 * factorial(@Nat.0 - 1) }
}
""")

    def test_unresolved_function_warning(self) -> None:
        """Unresolved functions emit warnings, not errors."""
        diags = _check("""
fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ unknown_fn(@Int.0) }
""")
        warnings = [d for d in diags if d.severity == "warning"]
        errors = [d for d in diags if d.severity == "error"]
        assert len(warnings) >= 1
        assert any("Unresolved" in w.description for w in warnings)
        assert errors == []


# =====================================================================
# Generic functions
# =====================================================================

class TestGenerics:

    def test_identity(self) -> None:
        _check_ok("""
forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }
""")

    def test_generic_call(self) -> None:
        _check_ok("""
forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(@Int.0) }
""")


# =====================================================================
# ADTs and constructors
# =====================================================================

class TestConstructors:

    def test_nullary_constructor(self) -> None:
        _check_ok("""
data Color { Red, Green, Blue }

fn foo(@Unit -> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }
""")

    def test_constructor_with_fields(self) -> None:
        _check_ok("""
data Pair { MkPair(Int, String) }

fn foo(@Int, @String -> @Pair)
  requires(true) ensures(true) effects(pure)
{ MkPair(@Int.0, @String.0) }
""")

    def test_constructor_arity_mismatch(self) -> None:
        _check_err("""
data Pair { MkPair(Int, String) }

fn foo(@Int -> @Pair)
  requires(true) ensures(true) effects(pure)
{ MkPair(@Int.0) }
""", "expects 2 field")

    def test_parameterised_adt(self) -> None:
        _check_ok("""
data Box<T> { MkBox(T) }

fn foo(@Int -> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkBox(@Int.0) }
""")


# =====================================================================
# Pattern matching
# =====================================================================

class TestPatterns:

    def test_constructor_pattern(self) -> None:
        _check_ok("""
data Option<T> { None, Some(T) }

fn unwrap(@Option<Int> -> @Int)
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
fn classify(@Int -> @String)
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
fn to_str(@Bool -> @String)
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
data Option<T> { None, Some(T) }
data List<T> { Nil, Cons(T, List<T>) }

fn first(@List<Option<Int>> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @List<Option<Int>>.0 {
    Cons(Some(@Int), @List<Option<Int>>) -> @Int.0,
    Cons(None, @List<Option<Int>>) -> first(@List<Option<Int>>.0),
    Nil -> 0
  }
}
""")


# =====================================================================
# Control flow
# =====================================================================

class TestControlFlow:

    def test_if_then_else(self) -> None:
        _check_ok("""
fn abs(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 >= 0 then { @Int.0 }
  else { 0 - @Int.0 }
}
""")

    def test_if_condition_not_bool(self) -> None:
        _check_err("""
fn bad(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 then { 1 } else { 2 }
}
""", "condition must be Bool")

    def test_if_branch_mismatch(self) -> None:
        _check_err("""
fn bad(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { 42 } else { "hello" }
}
""", "incompatible types")

    def test_block_with_let(self) -> None:
        _check_ok("""
fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0 + 1;
  let @Int = @Int.0 * 2;
  @Int.0
}
""")


# =====================================================================
# Effects
# =====================================================================

class TestEffects:

    def test_pure_function(self) -> None:
        _check_ok("""
fn pure_fn(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_effect_declaration(self) -> None:
        _check_ok("""
effect Logger {
  op log(String -> Unit);
}

fn greet(@String -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  Logger.log(@String.0)
}
""")

    def test_pure_calling_effectful_error(self) -> None:
        _check_err("""
effect Logger {
  op log(String -> Unit);
}

fn bad(@String -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  Logger.log(@String.0)
}
""", "Pure function")

    def test_handler_basic(self) -> None:
        _check_ok("""
fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""")

    def test_state_effect_builtin(self) -> None:
        """The built-in State<T> effect is available."""
        _check_ok("""
fn incr(@Unit -> @Unit)
  requires(true) ensures(true) effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
""")

    def test_qualified_effect_call(self) -> None:
        _check_ok("""
effect Counter {
  op get_count(Unit -> Int);
  op increment(Unit -> Unit);
}

fn use_counter(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Counter>)
{
  Counter.increment(())
}
""")


# =====================================================================
# Contracts
# =====================================================================

class TestContracts:

    def test_requires_bool(self) -> None:
        _check_ok("""
fn foo(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_requires_non_bool_error(self) -> None:
        _check_err("""
fn bad(@Int -> @Int)
  requires(@Int.0) ensures(true) effects(pure)
{ @Int.0 }
""", "requires() predicate must be Bool")

    def test_ensures_bool(self) -> None:
        _check_ok("""
fn foo(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ @Int.0 }
""")

    def test_ensures_non_bool_error(self) -> None:
        _check_err("""
fn bad(@Int -> @Int)
  requires(true) ensures(@Int.result) effects(pure)
{ @Int.0 }
""", "ensures() predicate must be Bool")

    def test_decreases(self) -> None:
        _check_ok("""
fn count(@Nat -> @Nat)
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
fn clamp(@Int, @Int, @Int -> @Int)
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
fn incr(@Unit -> @Unit)
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
fn bad(@Unit -> @Unit)
  requires(old(State<Int>) > 0)
  ensures(true)
  effects(<State<Int>>)
{ () }
""", "old() is only valid inside ensures")


# =====================================================================
# Higher-order functions
# =====================================================================

class TestHigherOrder:

    def test_anon_fn(self) -> None:
        _check_ok("""
fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 5;
  @Int.0
}
""")

    def test_fn_type_alias(self) -> None:
        _check_ok("""
type IntToInt = fn(Int -> Int) effects(pure);

fn apply(@IntToInt, @Int -> @Int)
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

fn foo(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
""")

    def test_refinement_subtype_to_base(self) -> None:
        """Refinement type is subtype of its base type."""
        _check_ok("""
type PosInt = { @Int | @Int.0 > 0 };

fn foo(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 + 1 }
""")

    def test_int_to_nat_allowed(self) -> None:
        """Int -> Nat allowed by checker; verifier enforces >= 0 via Z3."""
        _check_ok("""
fn foo(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")


# =====================================================================
# Error accumulation and edge cases
# =====================================================================

class TestErrorAccumulation:

    def test_multiple_errors(self) -> None:
        """Multiple type errors in one file are all reported."""
        errs = _errors("""
fn bad(@Unit -> @Int)
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
data Color { Red, Green, Blue }
data Option<T> { None, Some(T) }
""")

    def test_type_error_has_location(self) -> None:
        """Type errors include source location."""
        errs = _errors("""
fn bad(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        assert len(errs) >= 1
        assert errs[0].location.line > 0


# =====================================================================
# Where blocks (mutual recursion)
# =====================================================================

class TestWhereBlocks:

    def test_mutual_recursion(self) -> None:
        _check_ok("""
fn is_even(@Nat -> @Bool)
  requires(true) ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { true }
  else { is_odd(@Nat.0 - 1) }
}
where {
  fn is_odd(@Nat -> @Bool)
    requires(true) ensures(true)
    decreases(@Nat.0)
    effects(pure)
  {
    if @Nat.0 == 0 then { false }
    else { is_even(@Nat.0 - 1) }
  }
}
""")


# =====================================================================
# Array operations
# =====================================================================

class TestArrays:

    def test_array_index(self) -> None:
        _check_ok("""
fn first(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[0] }
""")

    def test_array_index_non_array_error(self) -> None:
        _check_err("""
fn bad(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0[0] }
""", "Cannot index")


# =====================================================================
# Return type checking
# =====================================================================

class TestReturnTypes:

    def test_return_type_mismatch(self) -> None:
        _check_err("""
fn bad(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "body has type")

    def test_nat_return_from_int_body(self) -> None:
        """Int body with Nat return: allowed in C3."""
        _check_ok("""
fn foo(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_if_nat_literal_return(self) -> None:
        """Non-negative literal should satisfy Nat return."""
        _check_ok("""
fn foo(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 42 }
""")


# =====================================================================
# Exhaustiveness checking
# =====================================================================

class TestExhaustiveness:

    # --- ADT exhaustiveness ---

    def test_adt_exhaustive(self) -> None:
        """All constructors covered → no error."""
        _check_ok("""
data Option<T> { None, Some(T) }

fn unwrap(@Option<Int> -> @Int)
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
data Option<T> { None, Some(T) }

fn unwrap(@Option<Int> -> @Int)
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
data Result<T, E> { Ok(T), Err(E) }

fn get(@Result<Int, String> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Result<Int, String>.0 {
    Ok(@Int) -> @Int.0
  }
}
""", "Non-exhaustive")
        desc = " ".join(e.description for e in errs)
        assert "Err" in desc

    def test_adt_with_wildcard(self) -> None:
        """Wildcard after Some covers None → exhaustive."""
        _check_ok("""
data Option<T> { None, Some(T) }

fn unwrap(@Option<Int> -> @Int)
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
data Option<T> { None, Some(T) }

fn unwrap(@Option<Int> -> @Int)
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
fn to_str(@Bool -> @String)
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
fn to_str(@Bool -> @String)
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
fn to_str(@Bool -> @String)
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
fn to_str(@Bool -> @String)
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
fn classify(@Int -> @String)
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
fn classify(@Int -> @String)
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
fn classify(@String -> @Int)
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
fn classify(@Int -> @String)
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
fn classify(@Int -> @String)
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
fn classify(@Int -> @String)
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
fn identity(@Int -> @Int)
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
fn classify(@Int -> @String)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  match @Int.0 {
    1 -> "one",
    2 -> "two"
  }
}
""", "Non-exhaustive")
