"""Tests for the Vera type checker (Phase C3).

Follows the same patterns as test_ast.py: helper functions, parametrised
round-trip tests, then node-specific test classes.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vera import ast
from vera.checker import typecheck
from vera.errors import Diagnostic
from vera.parser import parse_to_ast
from vera.resolver import ResolvedModule

# =====================================================================
# Helpers
# =====================================================================

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"
EXAMPLE_FILES = sorted(f.name for f in EXAMPLES_DIR.glob("*.vera"))

# Self-contained examples (no unresolved external references)
CLEAN_EXAMPLES = [
    "absolute_value.vera",
    "effect_handler.vera",
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


def _check_clean(source: str) -> None:
    """Assert the source type-checks with no errors AND no warnings."""
    diags = _check(source)
    assert diags == [], \
        f"Expected no diagnostics, got: {[d.description for d in diags]}"


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
# Slot references
# =====================================================================

class TestSlotRefs:

    def test_simple_ref(self) -> None:
        _check_ok("""
private fn id(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_multiple_same_type(self) -> None:
        _check_ok("""
private fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }
""")

    def test_different_types(self) -> None:
        _check_ok("""
private fn pick(@Int, @String -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_out_of_bounds(self) -> None:
        _check_err("""
private fn bad(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 }
""", "Cannot resolve @Int.1")

    def test_no_bindings(self) -> None:
        _check_err("""
private fn bad(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "Cannot resolve @Int.0")

    def test_let_introduces_binding(self) -> None:
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 42;
  @Int.0
}
""")

    def test_let_shadowing(self) -> None:
        _check_ok("""
private fn foo(@Int -> @Int)
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

private fn foo(@PosInt, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 + @Int.0 }
""")

    def test_parameterised_slot(self) -> None:
        _check_ok("""
private data Option<T> { None, Some(T) }

private fn foo(@Option<Int> -> @Bool)
  requires(true) ensures(true) effects(pure)
{ true }
""")


# =====================================================================
# Result references
# =====================================================================

class TestResultRefs:

    def test_result_in_ensures(self) -> None:
        _check_ok("""
private fn foo(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }
""")

    def test_result_outside_ensures(self) -> None:
        _check_err("""
private fn foo(@Int -> @Int)
  requires(@Int.result > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
""", "@Int.result is only valid inside ensures")

    def test_result_in_body(self) -> None:
        _check_err("""
private fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.result }
""", "only valid inside ensures")


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
        _check_err("""
private fn bad(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ !@Int.0 }
""", "requires Bool operand")


# =====================================================================
# Function calls
# =====================================================================

class TestFnCalls:

    def test_simple_call(self) -> None:
        _check_ok("""
private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }

private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0) }
""")

    def test_arity_mismatch(self) -> None:
        _check_err("""
private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }

private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0, @Int.0) }
""", "expects 1 argument")

    def test_type_mismatch_arg(self) -> None:
        _check_err("""
private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }

private fn main(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@String.0) }
""", "has type String, expected Int")

    def test_recursive_call(self) -> None:
        _check_ok("""
private fn factorial(@Nat -> @Nat)
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
private fn foo(@Int -> @Int)
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
        _check_err("""
private data Pair { MkPair(Int, String) }

private fn foo(@Int -> @Pair)
  requires(true) ensures(true) effects(pure)
{ MkPair(@Int.0) }
""", "expects 2 field")

    def test_parameterised_adt(self) -> None:
        _check_ok("""
private data Box<T> { MkBox(T) }

private fn foo(@Int -> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkBox(@Int.0) }
""")


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


# =====================================================================
# Control flow
# =====================================================================

class TestControlFlow:

    def test_if_then_else(self) -> None:
        _check_ok("""
private fn abs(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 >= 0 then { @Int.0 }
  else { 0 - @Int.0 }
}
""")

    def test_if_condition_not_bool(self) -> None:
        _check_err("""
private fn bad(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 then { 1 } else { 2 }
}
""", "condition must be Bool")

    def test_if_branch_mismatch(self) -> None:
        _check_err("""
private fn bad(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { 42 } else { "hello" }
}
""", "incompatible types")

    def test_block_with_let(self) -> None:
        _check_ok("""
private fn foo(@Int -> @Int)
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
private fn pure_fn(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_effect_declaration(self) -> None:
        _check_ok("""
effect Logger {
  op log(String -> Unit);
}

private fn greet(@String -> @Unit)
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

private fn bad(@String -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  Logger.log(@String.0)
}
""", "Pure function")

    def test_handler_basic(self) -> None:
        """Handler with resume produces no errors or warnings."""
        _check_clean("""
private fn foo(@Unit -> @Int)
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

    def test_resume_wrong_arg_type(self) -> None:
        """resume() type-checks its argument against operation return type."""
        # get(Unit) -> Int, so resume expects Int; passing Unit is a mismatch
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(()) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""", "has type Unit, expected Int")

    def test_resume_wrong_arity(self) -> None:
        """resume() takes exactly one argument."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0, @Int.1) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""", "expects 1 argument")

    def test_resume_outside_handler(self) -> None:
        """resume() outside a handler scope is unresolved."""
        diags = _check("""
private fn foo(@Unit -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  resume(42)
}
""")
        warns = [d for d in diags if d.severity == "warning"]
        assert any("Unresolved function 'resume'" in w.description
                    for w in warns), \
            f"Expected unresolved resume warning, got: " \
            f"{[w.description for w in warns]}"

    def test_with_clause_valid(self) -> None:
        """Handler with-clause with correct type produces no errors."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    put(42);
    get(())
  }
}
""")

    def test_with_clause_type_mismatch(self) -> None:
        """Handler with-clause value must match state type."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = true
  } in {
    get(())
  }
}
""", "expected Int")

    def test_with_clause_no_state(self) -> None:
        """Handler with-clause without handler state is an error."""
        _check_err("""
effect Exn<E> {
  op throw(E -> Never);
}
private fn bar(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> { 0 } with @String = @String.0
  } in {
    42
  }
}
""", "no state declaration")

    def test_with_clause_wrong_slot_type(self) -> None:
        """Handler with-clause type must match handler state type."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Bool = true
  } in {
    get(())
  }
}
""", "does not match handler state type")

    def test_state_effect_builtin(self) -> None:
        """The built-in State<T> effect is available."""
        _check_ok("""
private fn incr(@Unit -> @Unit)
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

private fn use_counter(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Counter>)
{
  Counter.increment(())
}
""")

    # ----- Diverge (built-in marker effect, Chapter 7 §7.7.3) --------

    def test_diverge_type_checks(self) -> None:
        """effects(<Diverge>) is a recognised built-in effect."""
        _check_ok("""
private fn loop(@Unit -> @Int)
  requires(true) ensures(true) effects(<Diverge>)
{ 0 }
""")

    def test_diverge_combined_with_io(self) -> None:
        """Diverge composes with other effects in the same row."""
        _check_ok("""
private fn serve(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Diverge, IO>)
{
  IO.print("running");
  ()
}
""")

    def test_diverge_no_operations(self) -> None:
        """Diverge has no operations — qualified calls produce a warning."""
        warns = _warnings("""
private fn bad(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Diverge>)
{
  Diverge.stop(())
}
""")
        assert any("Unresolved qualified call" in w.description for w in warns), \
            f"Expected unresolved call warning, got: {[w.description for w in warns]}"

    def test_diverge_registered_in_env(self) -> None:
        """Diverge is present in the environment's effect registry."""
        from vera.environment import TypeEnv
        env = TypeEnv()
        info = env.lookup_effect("Diverge")
        assert info is not None
        assert info.name == "Diverge"
        assert info.type_params is None
        assert info.operations == {}


# =====================================================================
# Abilities (Spec §9.8) — PR 2: registration + constraint validation
# =====================================================================

class TestAbilities:
    """Ability declarations, constraint validation, and operation resolution."""

    def test_ability_decl_accepted(self) -> None:
        """Ability declaration is accepted without errors."""
        _check_ok("""
        ability Eq<T> {
          op eq(T, T -> Bool);
        }

        private fn main(@Unit -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        { 0 }
        """)

    def test_forall_with_constraint_accepted(self) -> None:
        """Function with forall constraint is accepted."""
        _check_ok("""
        private forall<T where Eq<T>> fn contains(@Array<T>, @T -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        { true }
        """)

    def test_ability_with_builtin_eq(self) -> None:
        """Built-in Eq ability: eq() call in constrained function resolves."""
        _check_ok("""
        private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        { eq(@T.1, @T.0) }
        """)

    def test_ability_op_resolves_return_type(self) -> None:
        """eq() returns Bool, usable in if condition."""
        _check_ok("""
        private forall<T where Eq<T>> fn check(@T, @T -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          if eq(@T.1, @T.0) then { 1 } else { 0 }
        }
        """)

    def test_user_defined_ability_op_call(self) -> None:
        """User-defined ability operation resolves in constrained function."""
        _check_ok("""
        ability Show<T> {
          op show(T -> String);
        }

        private forall<T where Show<T>> fn display(@T -> @String)
          requires(true)
          ensures(true)
          effects(pure)
        { show(@T.0) }
        """)

    def test_unknown_ability_in_constraint(self) -> None:
        """Unknown ability in constraint → E180."""
        _check_err("""
        private forall<T where Unknown<T>> fn f(@T -> @T)
          requires(true)
          ensures(true)
          effects(pure)
        { @T.0 }
        """, "Unknown ability 'Unknown'")

    def test_undeclared_typevar_in_constraint(self) -> None:
        """Constraint references undeclared type variable → E181."""
        _check_err("""
        private forall<T where Eq<X>> fn f(@T -> @T)
          requires(true)
          ensures(true)
          effects(pure)
        { @T.0 }
        """, "undeclared type variable 'X'")

    def test_ability_op_wrong_arity(self) -> None:
        """Ability operation with wrong argument count → E240."""
        _check_err("""
        private forall<T where Eq<T>> fn bad(@T -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        { eq(@T.0) }
        """, "expects 2 argument(s), got 1")

    def test_ability_op_type_mismatch(self) -> None:
        """Ability operation with mismatched argument types → E241."""
        _check_err("""
        private fn bad(@Int, @String -> @Bool)
          requires(true)
          ensures(true)
          effects(pure)
        { eq(@Int.0, @String.0) }
        """, "Argument 1 of 'eq'")


# =====================================================================
# Effect Subtyping (Spec §7.8)
# =====================================================================

class TestEffectSubtyping:
    """Call-site effect checking — functions can only call functions
    whose effects are a subset of the caller's effect row."""

    def test_pure_calling_effectful_fn_error(self) -> None:
        """Pure function calling an effectful *function* (not an op) → E125."""
        _check_err("""
effect Logger {
  op log(String -> Unit);
}

private fn effectful(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  Logger.log("hi")
}

private fn bad(@Unit -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  effectful(())
}
""", "requires effects(<Logger>) but call site only allows effects(pure)")

    def test_effectful_calling_same_effect_ok(self) -> None:
        """Calling a function with the same effect row is fine."""
        _check_ok("""
effect Logger {
  op log(String -> Unit);
}

private fn effectful(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  Logger.log("hi")
}

private fn caller(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  effectful(())
}
""")

    def test_effectful_calling_subset_ok(self) -> None:
        """Calling a function whose effects are a subset of the caller's."""
        _check_ok("""
effect Logger {
  op log(String -> Unit);
}

effect Tracer {
  op trace(String -> Unit);
}

private fn log_only(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  Logger.log("hi")
}

private fn caller(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger, Tracer>)
{
  log_only(())
}
""")

    def test_effectful_calling_superset_error(self) -> None:
        """Calling a function that needs more effects than the caller has."""
        _check_err("""
effect Logger {
  op log(String -> Unit);
}

effect Tracer {
  op trace(String -> Unit);
}

private fn needs_both(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger, Tracer>)
{
  Logger.log("hi");
  Tracer.trace("t")
}

private fn caller(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{
  needs_both(())
}
""", "requires effects(<Logger, Tracer>) but call site only allows effects(<Logger>)")

    def test_handler_discharges_effect_ok(self) -> None:
        """Handler body can use effects — handler discharges them."""
        _check_ok("""
private fn run(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
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

    def test_pure_calling_pure_fn_ok(self) -> None:
        """Pure calling pure is always fine."""
        _check_ok("""
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

private fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  helper(@Int.0)
}
""")

    def test_io_calling_pure_fn_ok(self) -> None:
        """An IO context can call a pure function (pure <: IO)."""
        _check_ok("""
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

private fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  helper(@Int.0)
}
""")


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
private fn clamp(@Int, @Int, @Int -> @Int)
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
# Higher-order functions
# =====================================================================

class TestHigherOrder:

    def test_anon_fn(self) -> None:
        _check_ok("""
private fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 5;
  @Int.0
}
""")

    def test_fn_type_alias(self) -> None:
        _check_ok("""
type IntToInt = fn(Int -> Int) effects(pure);

private fn apply(@IntToInt, @Int -> @Int)
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


# =====================================================================
# Where blocks (mutual recursion)
# =====================================================================

class TestWhereBlocks:

    def test_mutual_recursion(self) -> None:
        _check_ok("""
private fn is_even(@Nat -> @Bool)
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


# =====================================================================
# Map collection (#62)
# =====================================================================

class TestMapCollection:

    def test_map_insert_and_size(self) -> None:
        """map_insert + map_size type-check cleanly."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), "hello", 42)) }
""")

    def test_map_get_returns_option(self) -> None:
        """map_get returns Option<V>."""
        _check_ok("""
private fn foo(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ option_unwrap_or(map_get(map_insert(map_new(), "k", 7), "k"), 0) }
""")

    def test_map_contains_returns_bool(self) -> None:
        """map_contains returns Bool."""
        _check_ok("""
private fn foo(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ map_contains(map_insert(map_new(), "k", 1), "k") }
""")

    def test_map_remove_returns_map(self) -> None:
        """map_remove returns Map<K, V>."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_remove(map_insert(map_new(), "k", 1), "k")) }
""")

    def test_map_keys_returns_array(self) -> None:
        """map_keys returns Array<K>."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_keys(map_insert(map_new(), "k", 1))) }
""")

    def test_map_values_returns_array(self) -> None:
        """map_values returns Array<V>."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_values(map_insert(map_new(), "k", 1))) }
""")

    def test_map_int_keys(self) -> None:
        """Map with Int keys type-checks cleanly."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), 1, "hello")) }
""")

    def test_map_let_binding(self) -> None:
        """Map can be bound with let @Map<K, V>."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_insert(map_new(), "k", 42);
  map_size(@Map<String, Nat>.0)
}
""")

    def test_map_wrong_arity(self) -> None:
        """map_insert with wrong number of args produces error."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), "k")) }
""", "expects")

    def test_map_new_infers_from_let(self) -> None:
        """Bare map_new() resolves type vars from let binding context."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_new();
  map_size(@Map<String, Nat>.0)
}
""")

    def test_map_insert_wrong_value_type(self) -> None:
        """map_insert rejects a value whose type does not match V."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_new();
  map_size(map_insert(@Map<String, Nat>.0, "k", "oops"))
}
""", "type")


class TestSetChecker:

    def test_set_new_type_checks(self) -> None:
        """set_new() in a let binding with Set<Int> type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_new();
  set_size(@Set<Int>.0)
}
""")

    def test_set_add_type_checks(self) -> None:
        """set_add(set_new(), 1) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_new(), 1)) }
""")

    def test_set_contains_type_checks(self) -> None:
        """set_contains returns Bool."""
        _check_ok("""
private fn foo(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ set_contains(set_add(set_new(), 1), 1) }
""")

    def test_set_remove_type_checks(self) -> None:
        """set_remove type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_remove(set_add(set_new(), 1), 1)) }
""")

    def test_set_size_type_checks(self) -> None:
        """set_size returns Int."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_new(), 42)) }
""")

    def test_set_to_array_type_checks(self) -> None:
        """set_to_array type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(set_to_array(set_add(set_new(), 1))) }
""")

    def test_set_wrong_arity(self) -> None:
        """set_add with wrong number of args produces error."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_new())) }
""", "expects")

    def test_set_new_infers_from_let(self) -> None:
        """let @Set<String> = set_new() infers correctly."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<String> = set_new();
  set_size(@Set<String>.0)
}
""")

    def test_set_add_wrong_element_type(self) -> None:
        """set_add rejects an element whose type does not match T."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Nat> = set_new();
  set_size(set_add(@Set<Nat>.0, "oops"))
}
""", "expected Nat")


class TestDecimalChecker:

    def test_decimal_from_int(self) -> None:
        """decimal_from_int(@Int -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_from_int(42) }
""")

    def test_decimal_add(self) -> None:
        """decimal_add(@Decimal, @Decimal -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_add(decimal_from_int(1), decimal_from_int(2)) }
""")

    def test_decimal_eq(self) -> None:
        """decimal_eq(@Decimal, @Decimal -> @Bool) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ decimal_eq(decimal_from_int(1), decimal_from_int(1)) }
""")

    def test_decimal_to_string(self) -> None:
        """decimal_to_string(@Decimal -> @String) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ decimal_to_string(decimal_from_int(42)) }
""")

    def test_decimal_to_float(self) -> None:
        """decimal_to_float(@Decimal -> @Float64) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Float64)
  requires(true) ensures(true) effects(pure)
{ decimal_to_float(decimal_from_int(42)) }
""")

    def test_decimal_wrong_arity(self) -> None:
        """decimal_add with 1 arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_add(decimal_from_int(1)) }
""", "expects")

    def test_decimal_wrong_type(self) -> None:
        """decimal_add with Int args produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_add(1, 2) }
""", "type")

    def test_decimal_from_string(self) -> None:
        """decimal_from_string(@String -> @Option<Decimal>) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ decimal_from_string("3.14") }
""")

    def test_decimal_div(self) -> None:
        """decimal_div(@Decimal, @Decimal -> @Option<Decimal>) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ decimal_div(decimal_from_int(10), decimal_from_int(3)) }
""")

    def test_decimal_compare(self) -> None:
        """decimal_compare(@Decimal, @Decimal -> @Ordering) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Ordering)
  requires(true) ensures(true) effects(pure)
{ decimal_compare(decimal_from_int(1), decimal_from_int(2)) }
""")

    def test_decimal_round(self) -> None:
        """decimal_round(@Decimal, @Int -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_round(decimal_from_int(3), 2) }
""")

    def test_decimal_neg(self) -> None:
        """decimal_neg(@Decimal -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_neg(decimal_from_int(42)) }
""")

    def test_decimal_abs(self) -> None:
        """decimal_abs(@Decimal -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_abs(decimal_from_int(42)) }
""")

    # Happy-path tests for remaining operations
    def test_decimal_from_float(self) -> None:
        """decimal_from_float(@Float64 -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_from_float(3.14) }
""")

    def test_decimal_sub(self) -> None:
        """decimal_sub(@Decimal, @Decimal -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_sub(decimal_from_int(5), decimal_from_int(3)) }
""")

    def test_decimal_mul(self) -> None:
        """decimal_mul(@Decimal, @Decimal -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_mul(decimal_from_int(2), decimal_from_int(3)) }
""")

    # Wrong-type tests
    def test_decimal_from_float_wrong_type(self) -> None:
        """decimal_from_float with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_from_float(42) }
""", "type")

    def test_decimal_sub_wrong_type(self) -> None:
        """decimal_sub with Int args produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_sub(1, 2) }
""", "type")

    def test_decimal_mul_wrong_type(self) -> None:
        """decimal_mul with Int args produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_mul(1, 2) }
""", "type")

    def test_decimal_neg_wrong_type(self) -> None:
        """decimal_neg with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_neg(42) }
""", "type")

    def test_decimal_abs_wrong_type(self) -> None:
        """decimal_abs with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_abs(42) }
""", "type")

    def test_decimal_round_wrong_type(self) -> None:
        """decimal_round with wrong arg types produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_round("2", 2) }
""", "type")

    def test_decimal_compare_wrong_type(self) -> None:
        """decimal_compare with Int args produces error."""
        _check_err("""
private fn foo(@Unit -> @Ordering)
  requires(true) ensures(true) effects(pure)
{ decimal_compare(1, 2) }
""", "type")

    def test_decimal_div_wrong_type(self) -> None:
        """decimal_div with Int args produces error."""
        _check_err("""
private fn foo(@Unit -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ decimal_div(1, 2) }
""", "type")

    def test_decimal_from_string_wrong_type(self) -> None:
        """decimal_from_string with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ decimal_from_string(42) }
""", "type")

    def test_decimal_rejects_type_args(self) -> None:
        """Decimal<Int> is rejected — Decimal is not parameterised."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ let @Decimal<Int> = decimal_from_int(1); @Decimal.0 }
""", "type arg")


class TestJsonChecker:
    """Json ADT and built-in function type checking."""

    def test_json_null(self) -> None:
        """JNull constructor type-checks as Json."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JNull }
""")

    def test_json_bool(self) -> None:
        """JBool(Bool) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JBool(true) }
""")

    def test_json_number(self) -> None:
        """JNumber(Float64) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JNumber(3.14) }
""")

    def test_json_string(self) -> None:
        """JString(String) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JString("hello") }
""")

    def test_json_array(self) -> None:
        """JArray(Array<Json>) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JArray([JNull, JBool(false)]) }
""")

    def test_json_object(self) -> None:
        """JObject(Map<String, Json>) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JObject(map_insert(map_new(), "key", JNull)) }
""")

    def test_json_parse(self) -> None:
        """json_parse returns Result<Json, String>."""
        _check_ok("""
private fn foo(@Unit -> @Result<Json, String>)
  requires(true) ensures(true) effects(pure)
{ json_parse("{}") }
""")

    def test_json_stringify(self) -> None:
        """json_stringify returns String."""
        _check_ok("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ json_stringify(JNull) }
""")

    def test_json_get(self) -> None:
        """json_get returns Option<Json>."""
        _check_ok("""
private fn foo(@Json -> @Option<Json>)
  requires(true) ensures(true) effects(pure)
{ json_get(@Json.0, "key") }
""")

    def test_json_has_field(self) -> None:
        """json_has_field returns Bool."""
        _check_ok("""
private fn foo(@Json -> @Bool)
  requires(true) ensures(true) effects(pure)
{ json_has_field(@Json.0, "key") }
""")

    def test_json_type_fn(self) -> None:
        """json_type returns String."""
        _check_ok("""
private fn foo(@Json -> @String)
  requires(true) ensures(true) effects(pure)
{ json_type(@Json.0) }
""")

    def test_json_array_get(self) -> None:
        """json_array_get returns Option<Json>."""
        _check_ok("""
private fn foo(@Json -> @Option<Json>)
  requires(true) ensures(true) effects(pure)
{ json_array_get(@Json.0, 0) }
""")

    def test_json_array_length(self) -> None:
        """json_array_length returns Int."""
        _check_ok("""
private fn foo(@Json -> @Int)
  requires(true) ensures(true) effects(pure)
{ json_array_length(@Json.0) }
""")

    def test_json_keys(self) -> None:
        """json_keys returns Array<String>."""
        _check_ok("""
private fn foo(@Json -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ json_keys(@Json.0) }
""")

    def test_json_parse_wrong_type(self) -> None:
        """json_parse with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Result<Json, String>)
  requires(true) ensures(true) effects(pure)
{ json_parse(42) }
""", "type")

    def test_json_stringify_wrong_type(self) -> None:
        """json_stringify with String arg produces error."""
        _check_err("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ json_stringify("not json") }
""", "type")

    def test_json_array_length_wrong_type(self) -> None:
        """json_array_length with non-Json arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ json_array_length(42) }
""", "type")

    def test_json_keys_wrong_type(self) -> None:
        """json_keys with non-Json arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ json_keys(42) }
""", "type")

    def test_json_array_get_wrong_index_type(self) -> None:
        """json_array_get with String index produces error."""
        _check_err("""
private fn foo(@Json -> @Option<Json>)
  requires(true) ensures(true) effects(pure)
{ json_array_get(@Json.0, "0") }
""", "type")

    def test_json_get_wrong_type(self) -> None:
        """json_get with non-Json first arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Option<Json>)
  requires(true) ensures(true) effects(pure)
{ json_get(42, "key") }
""", "type")

    def test_json_has_field_wrong_type(self) -> None:
        """json_has_field with non-Json first arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ json_has_field(42, "key") }
""", "type")

    def test_json_type_wrong_type(self) -> None:
        """json_type with non-Json arg produces error."""
        _check_err("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ json_type(42) }
""", "type")

    def test_json_custom_data_shadows_prelude(self) -> None:
        """User-defined data Json with non-standard constructors shadows prelude."""
        _check_ok("""
private data Json { MyNode(Int) }
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ MyNode(42) }
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
# Module call diagnostics (C7a)
# =====================================================================

class TestModuleCallDiagnostics:
    """Test improved module-call diagnostic messages (C7a).

    These tests construct AST nodes manually to exercise the checker
    logic in isolation from the parser.
    """

    @staticmethod
    def _make_program_with_module_call(
        mod_path: tuple[str, ...],
        fn_name: str,
    ) -> ast.Program:
        """Build a minimal Program with a module call in the body."""
        call = ast.ModuleCall(
            path=mod_path,
            name=fn_name,
            args=(ast.IntLit(value=42),),
        )
        fn = ast.FnDecl(
            name="main",
            forall_vars=None,
            forall_constraints=None,
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        tld = ast.TopLevelDecl(visibility="private", decl=fn)
        return ast.Program(
            module=None,
            imports=(),
            declarations=(tld,),
        )

    def test_module_not_found_warning(self) -> None:
        """ModuleCall without resolved_modules gives 'not found' warning."""
        prog = self._make_program_with_module_call(("foo",), "bar")
        diags = typecheck(prog, source="")
        warns = [d for d in diags if d.severity == "warning"]
        assert any("not found" in w.description for w in warns)

    def test_module_resolved_fn_not_found(self) -> None:
        """ModuleCall with resolved empty module gives 'not found in module'."""
        from vera.resolver import ResolvedModule

        prog = self._make_program_with_module_call(("foo",), "bar")
        fake_mod = ResolvedModule(
            path=("foo",),
            file_path=Path("/fake/foo.vera"),
            program=ast.Program(
                module=None, imports=(), declarations=(),
            ),
            source="",
        )
        diags = typecheck(prog, source="", resolved_modules=[fake_mod])
        warns = [d for d in diags if d.severity == "warning"]
        assert any("not found in module" in w.description for w in warns)


# =====================================================================
# C7b: Cross-module type checking
# =====================================================================


class TestCrossModuleTyping:
    """Test cross-module type merging (C7b).

    These tests verify that imported function signatures are registered
    and used for type-checking.  Manual-AST ModuleCall tests are retained
    for checker isolation; parse-from-source tests in TestModuleCallParsed
    verify end-to-end parsing with :: syntax.
    """

    # Reusable module sources
    MATH_MODULE = """\
public fn abs(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }

public fn max(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ if @Int.0 >= @Int.1 then { @Int.0 } else { @Int.1 } }
"""

    GENERIC_MODULE = """\
public forall<T> fn identity(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }
"""

    COLLECTIONS_MODULE = """\
public data List<T> { Nil, Cons(T, List<T>) }
public data Option<T> { None, Some(T) }
"""

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> ResolvedModule:
        """Build a ResolvedModule from source text."""
        from vera.resolver import ResolvedModule as RM
        prog = parse_to_ast(source)
        return RM(
            path=path,
            file_path=Path(f"/fake/{'/'.join(path)}.vera"),
            program=prog,
            source=source,
        )

    # -- Bare calls (parsed normally) -----------------------------------

    def test_bare_call_resolves_type(self) -> None:
        """import m(abs); abs(42) -> no errors."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        prog = parse_to_ast("""\
import math(abs);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_bare_call_arity_mismatch(self) -> None:
        """abs(1, 2) where abs takes 1 arg -> arity error."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        prog = parse_to_ast("""\
import math(abs);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(@Int.0, @Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("expects 1" in e.description for e in errors)

    def test_bare_call_type_mismatch(self) -> None:
        """abs(true) where abs expects Int -> type error."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        prog = parse_to_ast("""\
import math(abs);
private fn main(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(@Bool.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("Bool" in e.description and "Int" in e.description
                    for e in errors)

    def test_bare_call_generic_inference(self) -> None:
        """import m(identity); identity(42) -> infers Int, no errors."""
        mod = self._resolved(("gen",), self.GENERIC_MODULE)
        prog = parse_to_ast("""\
import gen(identity);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_wildcard_import_allows_all(self) -> None:
        """import math (no names) -> all functions available."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        prog = parse_to_ast("""\
import math;
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ max(@Int.0, abs(@Int.0)) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_local_shadows_import(self) -> None:
        """Local fn abs shadows imported abs."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        prog = parse_to_ast("""\
import math(abs);
private fn abs(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_imported_adt_constructors(self) -> None:
        """import m(List) -> Cons and Nil constructors available."""
        mod = self._resolved(("col",), self.COLLECTIONS_MODULE)
        prog = parse_to_ast("""\
import col(List);
private fn main(@Int -> @List<Int>)
  requires(true) ensures(true) effects(pure)
{ Cons(@Int.0, Nil) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Module-qualified calls (manual AST) ----------------------------

    def test_module_call_resolves_type(self) -> None:
        """ModuleCall to resolved function -> correct type, no errors."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        call = ast.ModuleCall(
            path=("math",), name="abs",
            args=(ast.IntLit(value=42),),
        )
        imp = ast.ImportDecl(path=("math",), names=("abs",))
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Int", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        warns = [d for d in diags if d.severity == "warning"]
        assert errors == [], [e.description for e in errors]
        assert not any("not found" in w.description for w in warns)

    def test_module_call_arity_mismatch(self) -> None:
        """Module-qualified call with wrong arity -> error."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        call = ast.ModuleCall(
            path=("math",), name="abs",
            args=(ast.IntLit(value=1), ast.IntLit(value=2)),
        )
        imp = ast.ImportDecl(path=("math",), names=("abs",))
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Int", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("expects 1" in e.description for e in errors)

    def test_selective_import_rejects_unimported(self) -> None:
        """Module call to name not in selective import -> error."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        call = ast.ModuleCall(
            path=("math",), name="max",
            args=(ast.IntLit(value=1), ast.IntLit(value=2)),
        )
        # Only import "abs", not "max"
        imp = ast.ImportDecl(path=("math",), names=("abs",))
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Int", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("not imported" in e.description for e in errors)

    def test_fn_not_in_module(self) -> None:
        """Module call to nonexistent function -> warning with available list."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        call = ast.ModuleCall(
            path=("math",), name="nonexistent",
            args=(ast.IntLit(value=42),),
        )
        imp = ast.ImportDecl(path=("math",), names=None)  # wildcard
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        warns = [d for d in diags if d.severity == "warning"]
        assert any("not found in module" in w.description for w in warns)
        assert any("abs" in w.description for w in warns)  # available list

    def test_multi_segment_path(self) -> None:
        """Multi-segment module path (vera.math) works."""
        mod = self._resolved(("vera", "math"), self.MATH_MODULE)
        call = ast.ModuleCall(
            path=("vera", "math"), name="abs",
            args=(ast.IntLit(value=42),),
        )
        imp = ast.ImportDecl(path=("vera", "math"), names=("abs",))
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Int", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]


# =====================================================================
# C7c: Visibility enforcement
# =====================================================================

class TestVisibilityEnforcement:
    """Test visibility enforcement (C7c).

    Verifies that the checker:
    - Requires explicit public/private on every fn/data declaration
    - Prevents importing private declarations across module boundaries
    - Allows calling own file's private declarations freely
    """

    # Reusable module sources
    MIXED_MODULE = """\
public fn pub_fn(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

private fn priv_fn(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

public data Color { Red, Green, Blue }

private data Secret { Hidden }
"""

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> ResolvedModule:
        """Build a ResolvedModule from source text."""
        from vera.resolver import ResolvedModule as RM
        prog = parse_to_ast(source)
        return RM(
            path=path,
            file_path=Path(f"/fake/{'/'.join(path)}.vera"),
            program=prog,
            source=source,
        )

    # -- Mandatory visibility -------------------------------------------

    def test_missing_visibility_on_fn(self) -> None:
        """Bare fn (no public/private) -> error."""
        _check_err("""
fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "Missing visibility on 'foo'")

    def test_missing_visibility_on_data(self) -> None:
        """Bare data (no public/private) -> error."""
        _check_err("""
data Color { Red, Green, Blue }
""", "Missing visibility on 'Color'")

    def test_private_fn_ok(self) -> None:
        """Explicit private fn -> no error."""
        _check_ok("""
private fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_public_fn_ok(self) -> None:
        """Explicit public fn -> no error."""
        _check_ok("""
public fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    # -- Cross-module visibility (bare calls) ---------------------------

    def test_public_fn_importable(self) -> None:
        """Public fn from module can be imported and called."""
        mod = self._resolved(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod(pub_fn);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ pub_fn(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_private_fn_not_importable(self) -> None:
        """Selective import of private fn -> error."""
        mod = self._resolved(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod(priv_fn);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ priv_fn(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("private" in e.description for e in errors), (
            [e.description for e in errors]
        )

    def test_public_data_importable(self) -> None:
        """Public data type and constructors can be imported."""
        mod = self._resolved(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod(Color);
private fn main(@Unit -> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_private_data_not_importable(self) -> None:
        """Selective import of private data type -> error."""
        mod = self._resolved(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod(Secret);
private fn main(@Unit -> @Secret)
  requires(true) ensures(true) effects(pure)
{ Hidden }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("private" in e.description for e in errors), (
            [e.description for e in errors]
        )

    def test_wildcard_import_skips_private(self) -> None:
        """Wildcard import only injects public names."""
        mod = self._resolved(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod;
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ pub_fn(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_wildcard_import_private_fn_unresolved(self) -> None:
        """Wildcard import: calling private fn -> unresolved warning."""
        mod = self._resolved(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod;
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ priv_fn(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        warns = [d for d in diags if d.severity == "warning"]
        assert any("Unresolved" in w.description or "not found" in w.description
                    for w in warns), [d.description for d in diags]

    # -- Module-qualified call visibility (C7c + ModuleCall AST) --------

    def test_module_call_private_fn_rejected(self) -> None:
        """ModuleCall to private function -> error."""
        mod = self._resolved(("mod",), self.MIXED_MODULE)
        call = ast.ModuleCall(
            path=("mod",), name="priv_fn",
            args=(ast.IntLit(value=42),),
        )
        imp = ast.ImportDecl(path=("mod",), names=None)
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Int", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("private" in e.description for e in errors), (
            [e.description for e in errors]
        )

    # -- Own file's declarations always accessible ----------------------

    def test_own_private_fn_callable(self) -> None:
        """Private fn in own file -> callable, no errors."""
        _check_ok("""
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ helper(@Int.0) }
""")

    # -- Error message quality ------------------------------------------

    def test_visibility_error_mentions_private(self) -> None:
        """Error message includes 'private', fn name, and module name."""
        mod = self._resolved(("mymod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mymod(priv_fn);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ priv_fn(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        msg = " ".join(e.description for e in errors)
        assert "private" in msg.lower()
        assert "priv_fn" in msg
        assert "mymod" in msg


# =====================================================================
# Module-qualified call parse tests (#95)
# =====================================================================

class TestModuleCallParsed:
    """Module-qualified call tests using parsed :: syntax (#95)."""

    MATH_MODULE = """\
public fn abs(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }

public fn max(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ if @Int.0 > @Int.1 then { @Int.0 } else { @Int.1 } }
"""

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str
    ) -> "ResolvedModule":
        from vera.resolver import ResolvedModule
        prog = parse_to_ast(source)
        return ResolvedModule(
            path=path, file_path=Path("/fake"), program=prog, source=source,
        )

    def test_parsed_module_call_typechecks(self) -> None:
        """Parsed :: syntax produces ModuleCall that type-checks."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        source = """\
import math(abs);
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ math::abs(@Int.0) }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_parsed_multi_segment_path(self) -> None:
        """Multi-segment path vera.math::abs type-checks."""
        mod = self._resolved(("vera", "math"), self.MATH_MODULE)
        source = """\
import vera.math(abs);
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ vera.math::abs(@Int.0) }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_parsed_module_call_arity_error(self) -> None:
        """Parsed :: call with wrong arity produces error."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        source = """\
import math(abs);
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ math::abs(@Int.0, @Int.0) }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("argument" in e.description.lower() for e in errors)


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
        """All codes in ERROR_CODES are valid Exxx patterns and unique."""
        import re
        from vera.errors import ERROR_CODES
        pattern = re.compile(r"^E\d{3}$")
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


# =====================================================================
# String built-in operations
# =====================================================================


class TestStringBuiltins:
    def test_string_length_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(@String.0) }
""")

    def test_string_concat_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_concat(@String.0, @String.1) }
""")

    def test_string_slice_ok(self) -> None:
        _check_ok("""
private fn f(@String, @Nat, @Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ string_slice(@String.0, @Nat.0, @Nat.1) }
""")

    def test_string_length_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(@Int.0) }
""", "type")

    def test_string_concat_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String, @Int -> @String)
  requires(true) ensures(true) effects(pure)
{ string_concat(@String.0, @Int.0) }
""", "type")

    def test_string_char_code_ok(self) -> None:
        _check_ok("""
private fn f(@String, @Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ string_char_code(@String.0, @Int.0) }
""")

    def test_string_char_code_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String, @Bool -> @Nat)
  requires(true) ensures(true) effects(pure)
{ string_char_code(@String.0, @Bool.0) }
""", "type")

    def test_parse_nat_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @Result<Nat, String>)
  requires(true) ensures(true) effects(pure)
{ parse_nat(@String.0) }
""")

    def test_parse_nat_bare_nat_mismatch(self) -> None:
        _check_err("""
private fn f(@String -> @Nat)
  requires(true) ensures(true) effects(pure)
{ parse_nat(@String.0) }
""", "expected Nat")

    def test_parse_float64_ok(self) -> None:
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<Float64, String>)
  requires(true) ensures(true) effects(pure)
{ parse_float64(@String.0) }
""")

    def test_parse_float64_bare_mismatch(self) -> None:
        _check_err("""
private fn f(@String -> @Float64)
  requires(true) ensures(true) effects(pure)
{ parse_float64(@String.0) }
""", "expected Float64")

    def test_parse_int_ok(self) -> None:
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<Int, String>)
  requires(true) ensures(true) effects(pure)
{ parse_int(@String.0) }
""")

    def test_parse_int_bare_mismatch(self) -> None:
        _check_err("""
private fn f(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ parse_int(@String.0) }
""", "expected Int")

    def test_parse_bool_ok(self) -> None:
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<Bool, String>)
  requires(true) ensures(true) effects(pure)
{ parse_bool(@String.0) }
""")

    def test_parse_bool_bare_mismatch(self) -> None:
        _check_err("""
private fn f(@String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ parse_bool(@String.0) }
""", "expected Bool")

    def test_base64_encode_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ base64_encode(@String.0) }
""")

    def test_base64_encode_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ base64_encode(@Int.0) }
""", "expected String")

    def test_base64_decode_ok(self) -> None:
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(pure)
{ base64_decode(@String.0) }
""")

    def test_base64_decode_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ base64_decode(@Int.0) }
""", "expected String")

    def test_url_encode_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ url_encode(@String.0) }
""")

    def test_url_encode_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ url_encode(@Int.0) }
""", "expected String")

    def test_url_decode_ok(self) -> None:
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(pure)
{ url_decode(@String.0) }
""")

    def test_url_decode_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ url_decode(@Int.0) }
""", "expected String")

    def test_url_parse_ok(self) -> None:
        _check_ok("""
private data UrlParts { UrlParts(String, String, String, String, String) }
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<UrlParts, String>)
  requires(true) ensures(true) effects(pure)
{ url_parse(@String.0) }
""")

    def test_url_parse_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ url_parse(@Int.0) }
""", "expected String")

    def test_url_join_ok(self) -> None:
        _check_ok("""
private data UrlParts { UrlParts(String, String, String, String, String) }
private fn f(@UrlParts -> @String)
  requires(true) ensures(true) effects(pure)
{ url_join(@UrlParts.0) }
""")

    def test_url_join_wrong_type(self) -> None:
        _check_err("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ url_join(@String.0) }
""", "expected UrlParts")

    def test_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ to_string(@Int.0) }
""")

    def test_string_strip_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_strip(@String.0) }
""")

    def test_string_strip_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ string_strip(@Int.0) }
""", "type")

    def test_bool_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{ bool_to_string(@Bool.0) }
""")

    def test_bool_to_string_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ bool_to_string(@Int.0) }
""", "type")

    def test_nat_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ nat_to_string(@Nat.0) }
""")

    def test_nat_to_string_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{ nat_to_string(@Bool.0) }
""", "type")

    def test_byte_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Byte -> @String)
  requires(true) ensures(true) effects(pure)
{ byte_to_string(@Byte.0) }
""")

    def test_byte_to_string_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ byte_to_string(@Int.0) }
""", "type")

    def test_int_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ int_to_string(@Int.0) }
""")

    def test_int_to_string_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{ int_to_string(@Bool.0) }
""", "type")

    def test_float_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @String)
  requires(true) ensures(true) effects(pure)
{ float_to_string(@Float64.0) }
""")

    def test_float_to_string_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ float_to_string(@Int.0) }
""", "type")


# =====================================================================
# Numeric math builtins (issue #199)
# =====================================================================

class TestNumericBuiltins:
    """Type checking for numeric math built-in functions."""

    def test_abs_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ abs(@Int.0) }
""")

    def test_abs_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @Nat)
  requires(true) ensures(true) effects(pure)
{ abs(@String.0) }
""", "type")

    def test_min_ok(self) -> None:
        _check_ok("""
private fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ min(@Int.0, @Int.1) }
""")

    def test_min_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Int)
  requires(true) ensures(true) effects(pure)
{ min(@Int.0, @String.0) }
""", "type")

    def test_max_ok(self) -> None:
        _check_ok("""
private fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ max(@Int.0, @Int.1) }
""")

    def test_floor_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Int)
  requires(true) ensures(true) effects(pure)
{ floor(@Float64.0) }
""")

    def test_floor_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ floor(@Int.0) }
""", "type")

    def test_ceil_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Int)
  requires(true) ensures(true) effects(pure)
{ ceil(@Float64.0) }
""")

    def test_round_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Int)
  requires(true) ensures(true) effects(pure)
{ round(@Float64.0) }
""")

    def test_sqrt_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ sqrt(@Float64.0) }
""")

    def test_sqrt_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @Float64)
  requires(true) ensures(true) effects(pure)
{ sqrt(@Int.0) }
""", "type")

    def test_pow_ok(self) -> None:
        _check_ok("""
private fn f(@Float64, @Int -> @Float64)
  requires(true) ensures(true) effects(pure)
{ pow(@Float64.0, @Int.0) }
""")

    def test_pow_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ pow(@Float64.0, @Float64.1) }
""", "type")


# =====================================================================
# Numeric type conversions (issue #208)
# =====================================================================

class TestTypeConversionBuiltins:
    """Type-checking for numeric type conversion builtins."""

    def test_int_to_float_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @Float64)
  requires(true) ensures(true) effects(pure)
{ int_to_float(@Int.0) }
""")

    def test_int_to_float_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @Float64)
  requires(true) ensures(true) effects(pure)
{ int_to_float(@String.0) }
""", "type")

    def test_float_to_int_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Int)
  requires(true) ensures(true) effects(pure)
{ float_to_int(@Float64.0) }
""")

    def test_float_to_int_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ float_to_int(@Int.0) }
""", "type")

    def test_nat_to_int_ok(self) -> None:
        _check_ok("""
private fn f(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(@Nat.0) }
""")

    def test_nat_to_int_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(@String.0) }
""", "type")

    def test_int_to_nat_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match int_to_nat(@Int.0) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0
  }
}
""")

    def test_int_to_nat_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Float64 -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{ int_to_nat(@Float64.0) }
""", "type")

    def test_byte_to_int_ok(self) -> None:
        _check_ok("""
private fn f(@Byte -> @Int)
  requires(true) ensures(true) effects(pure)
{ byte_to_int(@Byte.0) }
""")

    def test_byte_to_int_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ byte_to_int(@String.0) }
""", "type")

    def test_int_to_byte_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match int_to_byte(@Int.0) {
    Some(@Byte) -> byte_to_int(@Byte.0),
    None -> 0
  }
}
""")

    def test_int_to_byte_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Float64 -> @Option<Byte>)
  requires(true) ensures(true) effects(pure)
{ int_to_byte(@Float64.0) }
""", "type")


# =====================================================================
# Float64 predicate builtins (issue #212)
# =====================================================================

class TestFloatPredicateBuiltins:
    """Type-checking for Float64 predicate and constant builtins."""

    def test_float_is_nan_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{ float_is_nan(@Float64.0) }
""")

    def test_float_is_nan_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ float_is_nan(@Int.0) }
""", "type")

    def test_float_is_infinite_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{ float_is_infinite(@Float64.0) }
""")

    def test_float_is_infinite_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ float_is_infinite(@String.0) }
""", "type")

    def test_nan_ok(self) -> None:
        _check_ok("""
private fn f(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ nan() }
""")

    def test_nan_wrong_arity(self) -> None:
        _check_err("""
private fn f(@Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ nan(@Float64.0) }
""", "argument")

    def test_infinity_ok(self) -> None:
        _check_ok("""
private fn f(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ infinity() }
""")

    def test_infinity_wrong_arity(self) -> None:
        _check_err("""
private fn f(@Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ infinity(@Float64.0) }
""", "argument")


# =====================================================================
# Removed legacy names (must fail after #288 naming audit)
# =====================================================================


class TestRemovedLegacyNames:
    """Assert that pre-#288 function names are no longer resolvable."""

    @pytest.mark.parametrize("src, match", [
        ("""
private fn f(@Int -> @Float64)
  requires(true) ensures(true) effects(pure)
{ to_float(@Int.0) }
""", "Unresolved"),
        ("""
private fn f(@Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{ is_nan(@Float64.0) }
""", "Unresolved"),
        ("""
private fn f(@Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{ is_infinite(@Float64.0) }
""", "Unresolved"),
        ("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ starts_with(@String.0, @String.1) }
""", "Unresolved"),
        ("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ ends_with(@String.0, @String.1) }
""", "Unresolved"),
        ("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ contains(@String.0, @String.1) }
""", "Unresolved"),
        ("""
private fn f(@String, @String -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{ index_of(@String.0, @String.1) }
""", "Unresolved"),
        ("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ strip(@String.0) }
""", "Unresolved"),
        ("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ upper(@String.0) }
""", "Unresolved"),
        ("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ lower(@String.0) }
""", "Unresolved"),
        ("""
private fn f(@String, @String, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ replace(@String.0, @String.1, @String.2) }
""", "Unresolved"),
        ("""
private fn f(@String, @String -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ split(@String.0, @String.1) }
""", "Unresolved"),
        ("""
private fn f(@Array<String>, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ join(@Array<String>.0, @String.0) }
""", "Unresolved"),
        ("""
private fn f(@String, @Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ char_code(@String.0, @Int.0) }
""", "Unresolved"),
        ("""
private fn f(@Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ from_char_code(@Nat.0) }
""", "Unresolved"),
    ])
    def test_removed_builtin_names_fail(self, src: str, match: str) -> None:
        """Pre-#288 names must not resolve after the naming audit."""
        _check_ok(src)  # must produce no errors (warning-only)
        warns = _warnings(src)
        assert any(match.lower() in w.description.lower() for w in warns), \
            f"Expected warning matching '{match}', got: " \
            f"{[w.description for w in warns]}"


# =====================================================================
# String search and transformation builtins
# =====================================================================

class TestStringSearchBuiltins:
    """Type-checking for string search and transformation builtins."""

    # -- string_contains --

    def test_string_contains_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_contains(@String.0, @String.1) }
""")

    def test_string_contains_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_contains(@Int.0, @String.0) }
""", "type")

    # -- string_starts_with --

    def test_string_starts_with_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_starts_with(@String.0, @String.1) }
""")

    def test_string_starts_with_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_starts_with(@Int.0, @String.0) }
""", "type")

    # -- string_ends_with --

    def test_string_ends_with_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_ends_with(@String.0, @String.1) }
""")

    def test_string_ends_with_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_ends_with(@Int.0, @String.0) }
""", "type")

    # -- string_index_of --

    def test_string_index_of_ok(self) -> None:
        _check_ok("""
private data Option<T> { Some(T), None }
private fn f(@String, @String -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{ string_index_of(@String.0, @String.1) }
""")

    def test_string_index_of_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_index_of(@Int.0, @String.0) }
""", "type")

    # -- string_upper --

    def test_string_upper_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_upper(@String.0) }
""")

    def test_string_upper_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ string_upper(@Int.0) }
""", "type")

    # -- string_lower --

    def test_string_lower_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_lower(@String.0) }
""")

    def test_string_lower_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ string_lower(@Int.0) }
""", "type")

    # -- string_replace --

    def test_string_replace_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_replace(@String.0, @String.1, @String.2) }
""")

    def test_string_replace_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_replace(@Int.0, @String.0, @String.1) }
""", "type")

    # -- string_split --

    def test_string_split_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ string_split(@String.0, @String.1) }
""")

    def test_string_split_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ string_split(@Int.0, @String.0) }
""", "type")

    # -- string_join --

    def test_string_join_ok(self) -> None:
        _check_ok("""
private fn f(@Array<String>, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_join(@Array<String>.0, @String.0) }
""")

    def test_string_join_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Array<Int>, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_join(@Array<Int>.0, @String.0) }
""", "type")

    # -- string_from_char_code --

    def test_string_from_char_code_ok(self) -> None:
        _check_ok("""
private fn f(@Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ string_from_char_code(@Nat.0) }
""")

    def test_string_from_char_code_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_from_char_code(@String.0) }
""", "type")

    # -- string_repeat --

    def test_string_repeat_ok(self) -> None:
        _check_ok("""
private fn f(@String, @Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ string_repeat(@String.0, @Nat.0) }
""")

    def test_string_repeat_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String, @Bool -> @String)
  requires(true) ensures(true) effects(pure)
{ string_repeat(@String.0, @Bool.0) }
""", "type")


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
# IO built-in operations (C8.5 — #135)
# =====================================================================

class TestIOOperations:
    """Type checking for built-in IO operations."""

    def test_io_print_type_checks_clean(self) -> None:
        """IO.print should type-check cleanly (no E220 warning)."""
        _check_clean("""
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello") }
""")

    def test_io_print_wrong_arg_type(self) -> None:
        """IO.print(42) should fail: expected String, got Int."""
        _check_err("""
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(42) }
""", "expected String")

    def test_io_print_wrong_arity(self) -> None:
        """IO.print("a", "b") should fail: wrong arity."""
        _check_err("""
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("a", "b") }
""", "expects 1 argument")

    def test_io_read_line_type_checks(self) -> None:
        """IO.read_line(()) should type-check cleanly."""
        _check_clean("""
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(@String.0)
}
""")

    def test_io_read_file_returns_result(self) -> None:
        """IO.read_file returns Result<String, String>."""
        _check_clean("""
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_file("test.txt") {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  };
  ()
}
""")

    def test_io_write_file_returns_result(self) -> None:
        """IO.write_file returns Result<Unit, String>."""
        _check_clean("""
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.write_file("out.txt", "data") {
    Ok(@Unit) -> IO.print("ok"),
    Err(@String) -> IO.print(@String.0)
  };
  ()
}
""")

    def test_io_args_returns_array(self) -> None:
        """IO.args(()) returns Array<String>."""
        _check_clean("""
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  ()
}
""")

    def test_io_exit_returns_never(self) -> None:
        """IO.exit(0) has type Never — match arms propagate."""
        _check_clean("""
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.exit(0)
}
""")

    def test_io_get_env_returns_option(self) -> None:
        """IO.get_env("HOME") returns Option<String>."""
        _check_clean("""
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.get_env("HOME") {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("not set")
  };
  ()
}
""")

    def test_io_in_pure_function_error(self) -> None:
        """IO operations in effects(pure) should fail."""
        _check_err("""
public fn main(-> @Unit)
  requires(true) ensures(true) effects(pure)
{ IO.print("hello") }
""", "Pure function")

    def test_io_user_declared_override(self) -> None:
        """User-declared effect IO should override built-in."""
        # This declares only print — read_line should be unresolved (E220)
        diags = _check("""
effect IO {
  op print(String -> Unit);
}

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.read_line(()) }
""")
        warnings = [d for d in diags if d.severity == "warning"]
        assert any("read_line" in w.description for w in warnings), \
            f"Expected warning about read_line, got: " \
            f"{[w.description for w in warnings]}"


# =====================================================================
# String interpolation
# =====================================================================


class TestStringInterpolation:
    """String interpolation type checking."""

    def test_interp_string_ok(self) -> None:
        """Interpolating a String expression is allowed."""
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ "hello \\(@String.0)" }
""")

    def test_interp_int_auto_convert(self) -> None:
        """Int expressions are auto-converted to String."""
        _check_ok("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ "x = \\(@Int.0)" }
""")

    def test_interp_bool_auto_convert(self) -> None:
        """Bool expressions are auto-converted to String."""
        _check_ok("""
private fn f(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{ "flag: \\(@Bool.0)" }
""")

    def test_interp_nat_auto_convert(self) -> None:
        """Nat expressions are auto-converted to String."""
        _check_ok("""
private fn f(@Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ "n = \\(@Nat.0)" }
""")

    def test_interp_float_auto_convert(self) -> None:
        """Float64 expressions are auto-converted to String."""
        _check_ok("""
private fn f(@Float64 -> @String)
  requires(true) ensures(true) effects(pure)
{ "f = \\(@Float64.0)" }
""")

    def test_interp_byte_auto_convert(self) -> None:
        """Byte expressions are auto-converted to String."""
        _check_ok("""
private fn f(@Byte -> @String)
  requires(true) ensures(true) effects(pure)
{ "b = \\(@Byte.0)" }
""")

    def test_interp_multiple_exprs(self) -> None:
        """Multiple interpolated expressions in one string."""
        _check_ok("""
private fn f(@Int, @Bool -> @String)
  requires(true) ensures(true) effects(pure)
{ "a=\\(@Int.0) b=\\(@Bool.0)" }
""")

    def test_interp_no_interp_still_works(self) -> None:
        """A plain string without interpolation still works as StringLit."""
        _check_ok("""
private fn f(-> @String)
  requires(true) ensures(true) effects(pure)
{ "plain string" }
""")

    def test_interp_unsupported_type(self) -> None:
        """ADT types without to_string produce E148."""
        _check_err("""
private data Color { Red, Green, Blue }

private fn f(-> @String)
  requires(true) ensures(true) effects(pure)
{ "color: \\(Red)" }
""", "cannot be automatically converted to String")


# =====================================================================
# Async effect
# =====================================================================


class TestAsyncEffect:
    """Async effect and Future<T> type checking."""

    def test_async_ok(self) -> None:
        """async(expr) in a function with effects(<Async>) type-checks."""
        _check_ok("""
private fn f(-> @Future<Int>)
  requires(true) ensures(true) effects(<Async>)
{ async(42) }
""")

    def test_await_ok(self) -> None:
        """await(future) in a function with effects(<Async>) type-checks."""
        _check_ok("""
private fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(42);
  await(@Future<Int>.0)
}
""")

    def test_async_requires_effect(self) -> None:
        """async(expr) in effects(pure) function produces an error."""
        _check_err("""
private fn f(-> @Future<Int>)
  requires(true) ensures(true) effects(pure)
{ async(42) }
""", "effect")

    def test_await_requires_effect(self) -> None:
        """await(future) in effects(pure) function produces an error."""
        _check_err("""
private fn f(@Future<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ await(@Future<Int>.0) }
""", "effect")

    def test_async_wrong_arity(self) -> None:
        """async() with no arguments is an error."""
        _check_err("""
private fn f(-> @Future<Int>)
  requires(true) ensures(true) effects(<Async>)
{ async() }
""", "expects 1 argument")

    def test_await_wrong_type(self) -> None:
        """await(42) where 42 is Int not Future<T> is an error."""
        _check_err("""
private fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ await(42) }
""", "expected Future")

    def test_async_with_io(self) -> None:
        """Async composes with IO in the same effect set."""
        _check_ok("""
private fn f(-> @Unit)
  requires(true) ensures(true) effects(<IO, Async>)
{
  let @Future<Int> = async(42);
  IO.print(to_string(await(@Future<Int>.0)));
  ()
}
""")


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


class TestMarkdownBuiltins:
    """Type-checking for md_parse, md_render, md_has_heading, etc."""

    def test_md_parse_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @Result<MdBlock, String>)
  requires(true) ensures(true) effects(pure)
{ md_parse(@String.0) }
""")

    def test_md_parse_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ md_parse(@Int.0) }
""", "expected String")

    def test_md_render_ok(self) -> None:
        _check_ok("""
private fn f(@MdBlock -> @String)
  requires(true) ensures(true) effects(pure)
{ md_render(@MdBlock.0) }
""")

    def test_md_has_heading_ok(self) -> None:
        _check_ok("""
private fn f(@MdBlock, @Nat -> @Bool)
  requires(true) ensures(true) effects(pure)
{ md_has_heading(@MdBlock.0, @Nat.0) }
""")

    def test_md_has_code_block_ok(self) -> None:
        _check_ok("""
private fn f(@MdBlock, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ md_has_code_block(@MdBlock.0, @String.0) }
""")

    def test_md_extract_code_blocks_ok(self) -> None:
        _check_ok("""
private fn f(@MdBlock, @String -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ md_extract_code_blocks(@MdBlock.0, @String.0) }
""")


class TestRegexBuiltins:
    """Type-checking for regex_match, regex_find, regex_find_all,
    regex_replace."""

    def test_regex_match_ok(self) -> None:
        _check_ok(r"""
private fn f(@String -> @Result<Bool, String>)
  requires(true) ensures(true) effects(pure)
{ regex_match(@String.0, "\\d+") }
""")

    def test_regex_match_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ regex_match(@Int.0, @Int.0) }
""", "expected String")

    def test_regex_find_ok(self) -> None:
        _check_ok(r"""
private fn f(@String -> @Result<Option<String>, String>)
  requires(true) ensures(true) effects(pure)
{ regex_find(@String.0, "\\d+") }
""")

    def test_regex_find_all_ok(self) -> None:
        _check_ok(r"""
private fn f(@String -> @Result<Array<String>, String>)
  requires(true) ensures(true) effects(pure)
{ regex_find_all(@String.0, "\\d+") }
""")

    def test_regex_replace_ok(self) -> None:
        _check_ok(r"""
private fn f(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(pure)
{ regex_replace(@String.0, "\\d+", "X") }
""")

    def test_regex_replace_wrong_arity(self) -> None:
        _check_err(r"""
private fn f(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(pure)
{ regex_replace(@String.0, "\\d+") }
""", "expects 3 argument")


# =====================================================================
# Coverage: control.py — if-expression branches
# =====================================================================

class TestControlFlowCoverage:
    """Cover missed lines in vera/checker/control.py."""

    # --- Line 50: then_ty is None or else_ty is None → return other ---

    def test_if_one_branch_none(self) -> None:
        """When one if-branch cannot be synthesised, return the other."""
        # Trigger by having one branch contain an unresolvable call
        # (warning, not error) so _synth_expr returns None.
        diags = _check("""
private fn foo(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { unknown_fn(1) }
  else { 42 }
}
""")
        # Should still produce some result type (no crash).
        # The warning about unresolved function is expected.
        warnings = [d for d in diags if d.severity == "warning"]
        assert any("unresolved" in w.description.lower() for w in warnings)

    # --- Lines 57-60: Never propagation in if-branches ---

    def test_if_then_never_propagates(self) -> None:
        """If then-branch is Never, result is else-branch type (line 58)."""
        _check_ok("""
effect Exn<E> {
  op throw(E -> Never);
}

private fn checked(@Int -> @Int)
  requires(true) ensures(true) effects(<Exn<String>>)
{
  if @Int.0 < 0 then { throw("negative") }
  else { @Int.0 }
}
""")

    def test_if_else_never_propagates(self) -> None:
        """If else-branch is Never, result is then-branch type (line 60)."""
        _check_ok("""
effect Exn<E> {
  op throw(E -> Never);
}

private fn checked(@Int -> @Int)
  requires(true) ensures(true) effects(<Exn<String>>)
{
  if @Int.0 >= 0 then { @Int.0 }
  else { throw("negative") }
}
""")

    # --- Lines 63-66: subtype checks between branches ---

    def test_if_else_subtype_of_then(self) -> None:
        """When else-branch is subtype of then, return then type (line 66)."""
        # Never is subtype of everything; IO.exit returns Never.
        _check_ok("""
public fn foo(@Bool -> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  if @Bool.0 then { 42 }
  else { IO.exit(1) }
}
""")

    # --- Lines 70-82: TypeVar re-synthesis in if-expressions ---
    # Marked as pragma: no cover — requires unresolved TypeVars in
    # if-branch return types, which type inference normally resolves.

    # --- Lines 51-54: UnknownType propagation ---

    def test_if_then_unknown_returns_else(self) -> None:
        """When then-branch has UnknownType, return else type (line 52)."""
        # An unresolved function call produces UnknownType.
        diags = _check("""
private fn foo(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { completely_unknown() }
  else { 42 }
}
""")
        # Should produce a warning about unresolved function, not crash
        errors = [d for d in diags if d.severity == "error"]
        assert errors == []
        warnings = [d for d in diags if d.severity == "warning"]
        assert any("unresolved" in w.description.lower() for w in warnings)

    def test_if_else_unknown_returns_then(self) -> None:
        """When else-branch has UnknownType, return then type (line 54)."""
        diags = _check("""
private fn foo(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { 42 }
  else { completely_unknown() }
}
""")
        errors = [d for d in diags if d.severity == "error"]
        assert errors == []
        warnings = [d for d in diags if d.severity == "warning"]
        assert any("unresolved" in w.description.lower() for w in warnings)


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
# Coverage: control.py — handler type-checking
# =====================================================================

class TestHandlerCoverage:
    """Cover missed lines in handler type-checking."""

    # --- Lines 359, 363-368: unknown effect in handler ---

    def test_handle_unknown_effect(self) -> None:
        """Handler with unknown effect returns UnknownType (lines 363-368)."""
        diags = _check("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[NoSuchEffect] {
    some_op(@Int) -> { resume(()) }
  } in {
    42
  }
}
""")
        # Should produce a diagnostic mentioning the unknown effect
        assert any(
            "NoSuchEffect" in d.description for d in diags
        ), f"Expected diagnostic mentioning 'NoSuchEffect', got: {[d.description for d in diags]}"

    # --- Lines 400-406: unknown operation in handler clause ---

    def test_handle_unknown_operation(self) -> None:
        """Handler clause for non-existent operation produces E332 (lines 400-406)."""
        _check_err("""
effect Logger {
  op log(String -> Unit);
}

private fn foo(@Unit -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  handle[Logger] {
    nonexistent(@String) -> { resume(()) }
  } in {
    Logger.log("hi")
  }
}
""", "has no operation")

    # --- Line 470: restore saved_resume (when resume was previously bound) ---

    def test_nested_handlers_resume_restore(self) -> None:
        """Nested handlers restore outer resume binding (line 470)."""
        _check_ok("""
effect Inner {
  op inner_op(Unit -> Int);
}

effect Outer {
  op outer_op(Unit -> Int);
}

private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Outer] {
    outer_op(@Unit) -> {
      handle[Inner] {
        inner_op(@Unit) -> { resume(0) }
      } in {
        resume(inner_op(()))
      }
    }
  } in {
    outer_op(())
  }
}
""")

    # --- Lines 484-485: ConcreteEffectRow merging ---

    def test_handler_merges_effect_rows(self) -> None:
        """Handler body adds effect to existing ConcreteEffectRow (lines 484-485)."""
        _check_ok("""
effect Logger {
  op log(String -> Unit);
}

private fn foo(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  handle[Logger] {
    log(@String) -> { resume(()) }
  } in {
    Logger.log("inside handler");
    IO.print("also IO");
    ()
  }
}
""")

    def test_handler_state_init_type_mismatch(self) -> None:
        """Handler state initial value type doesn't match declared type (line 382)."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = "wrong") {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""", "expected Int")


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
