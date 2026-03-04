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
            name="main", forall_vars=None, params=(),
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
            name="main", forall_vars=None, params=(),
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
            name="main", forall_vars=None, params=(),
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
            name="main", forall_vars=None, params=(),
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
            name="main", forall_vars=None, params=(),
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
            name="main", forall_vars=None, params=(),
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

    def test_char_code_ok(self) -> None:
        _check_ok("""
private fn f(@String, @Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ char_code(@String.0, @Int.0) }
""")

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
private fn f(@String -> @Float64)
  requires(true) ensures(true) effects(pure)
{ parse_float64(@String.0) }
""")

    def test_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ to_string(@Int.0) }
""")

    def test_strip_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ strip(@String.0) }
""")

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
