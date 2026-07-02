"""Tests for the Vera type checker — functions (function signatures, slot references, calls, control flow, where-blocks, IO, interpolation).

Split from tests/test_checker.py (#420). Shared helpers live in tests/checker_helpers.py.
"""
from __future__ import annotations

import pytest

from vera.checker import typecheck
from vera.parser import parse_to_ast

from tests.checker_helpers import (
    CLEAN_EXAMPLES,
    EXAMPLES_DIR,
    _check,
    _check_clean,
    _check_err,
    _check_ok,
)


# =====================================================================
# Round-trip example tests
# =====================================================================

class TestExampleRoundTrips:
    """All self-contained examples must type-check cleanly."""

    @pytest.mark.parametrize("filename", CLEAN_EXAMPLES)
    def test_clean_example(self, filename: str) -> None:
        source = (EXAMPLES_DIR / filename).read_text(encoding="utf-8")
        prog = parse_to_ast(source, file=filename)
        errors = typecheck(prog, source=source, file=filename)
        real_errors = [e for e in errors if e.severity == "error"]
        assert real_errors == [], \
            f"{filename}: {[e.description for e in real_errors]}"


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
# Control flow
# =====================================================================

class TestControlFlow:

    def test_if_then_else(self) -> None:
        _check_ok("""
private fn magnitude(@Int -> @Int)
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
# Expression diagnostics (#387 fix-core)
# =====================================================================

class TestExpressionDiagnostics:
    """Error-code assertions for expression-level checks."""

    def test_array_index_non_int_is_e160(self) -> None:
        """A non-integer array index reports E160."""
        errs = _check_err("""
private fn f(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[true] }
""", "index must be Int")
        assert any(e.error_code == "E160" for e in errs)

    def test_index_non_array_is_e161(self) -> None:
        """Indexing a non-Array value reports E161."""
        errs = _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0[0] }
""", "indexing requires Array")
        assert any(e.error_code == "E161" for e in errs)

    def test_assume_non_bool_is_e173(self) -> None:
        """assume() with a non-Bool argument reports E173."""
        errs = _check_err("""
private fn f(@Int -> @Unit)
  requires(true) ensures(true) effects(pure)
{ assume(42); () }
""", "assume() requires Bool")
        assert any(e.error_code == "E173" for e in errs)

    def test_old_outside_ensures_is_e174(self) -> None:
        """old() used outside an ensures clause reports E174."""
        errs = _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Int = old(State<Int>); @Int.0 }
""", "old() is only valid")
        assert any(e.error_code == "E174" for e in errs)

    def test_new_outside_ensures_is_e175(self) -> None:
        """new() used outside an ensures clause reports E175."""
        errs = _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Int = new(State<Int>); @Int.0 }
""", "new() is only valid")
        assert any(e.error_code == "E175" for e in errs)


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
