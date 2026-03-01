"""Tests for vera.codegen — Runtime contract insertion.

Covers preconditions, postconditions, combined contracts,
contract failure messages, and old()/new() state contracts.
"""

from __future__ import annotations

import pytest
import wasmtime

from vera.codegen import (
    CompileResult,
    ConstructorLayout,
    ExecuteResult,
    _align_up,
    _wasm_type_align,
    _wasm_type_size,
    compile,
    execute,
)
from vera.parser import parse_file
from vera.transform import transform


# =====================================================================
# Helpers
# =====================================================================


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    # Write to a temp source and parse
    import tempfile
    from pathlib import Path

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False
    ) as f:
        f.write(source)
        f.flush()
        path = f.name

    tree = parse_file(path)
    ast = transform(tree)
    return compile(ast, source=source, file=path)


def _compile_ok(source: str) -> CompileResult:
    """Compile and assert no errors."""
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected errors: {errors}"
    return result


def _run(source: str, fn: str | None = None, args: list[int] | None = None) -> int:
    """Compile, execute, and return the integer result."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _run_float(
    source: str, fn: str | None = None, args: list[int | float] | None = None
) -> float:
    """Compile, execute, and return the float result."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None, "Expected a return value"
    assert isinstance(exec_result.value, float), (
        f"Expected float, got {type(exec_result.value).__name__}"
    )
    return exec_result.value


def _run_io(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> str:
    """Compile, execute, and return captured stdout."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    return exec_result.stdout


def _run_trap(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> None:
    """Compile, execute, and assert a WASM trap."""
    result = _compile_ok(source)
    with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
        execute(result, fn_name=fn, args=args)


# =====================================================================
# 5f: Runtime contract insertion
# =====================================================================


class TestPreconditions:
    def test_requires_holds(self) -> None:
        """Non-trivial precondition that holds — no trap."""
        source = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        assert _run(source, fn="positive", args=[5]) == 5

    def test_requires_traps(self) -> None:
        """Non-trivial precondition violated — WASM trap."""
        source = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        _run_trap(source, fn="positive", args=[0])

    def test_requires_boundary(self) -> None:
        """Precondition with exact boundary value."""
        source = """\
public fn nonneg(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        assert _run(source, fn="nonneg", args=[0]) == 0
        _run_trap(source, fn="nonneg", args=[-1])

    def test_requires_neq_zero(self) -> None:
        """Precondition: denominator != 0."""
        source = """\
public fn safe_div(@Int, @Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.1 / @Int.0 }
"""
        assert _run(source, fn="safe_div", args=[10, 2]) == 5
        _run_trap(source, fn="safe_div", args=[10, 0])

    def test_trivial_requires_no_overhead(self) -> None:
        """requires(true) should not produce any trap instructions."""
        source = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        result = _compile_ok(source)
        # No unreachable in WAT (no contract checks needed)
        assert "unreachable" not in result.wat

    def test_multiple_requires(self) -> None:
        """Multiple preconditions — all must hold."""
        source = """\
public fn bounded(@Int -> @Int)
  requires(@Int.0 >= 0)
  requires(@Int.0 <= 100)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        assert _run(source, fn="bounded", args=[50]) == 50
        _run_trap(source, fn="bounded", args=[-1])
        _run_trap(source, fn="bounded", args=[101])


class TestPostconditions:
    def test_ensures_holds(self) -> None:
        """Postcondition that holds — no trap."""
        source = """\
public fn double(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ @Int.0 * 2 }
"""
        assert _run(source, fn="double", args=[5]) == 10

    def test_ensures_traps(self) -> None:
        """Postcondition violated — WASM trap."""
        source = """\
public fn negate(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ -@Int.0 }
"""
        # negate(5) returns -5, which violates ensures(result > 0)
        _run_trap(source, fn="negate", args=[5])

    def test_ensures_with_params(self) -> None:
        """Postcondition referencing both result and parameters."""
        source = """\
public fn inc(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 + 1 }
"""
        assert _run(source, fn="inc", args=[5]) == 6

    def test_ensures_result_eq(self) -> None:
        """Postcondition checking exact result value."""
        source = """\
public fn always_zero(-> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{ 0 }
"""
        assert _run(source, fn="always_zero") == 0

    def test_ensures_result_traps(self) -> None:
        """Postcondition checking exact value — wrong result traps."""
        source = """\
public fn buggy(-> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{ 42 }
"""
        _run_trap(source, fn="buggy")

    def test_trivial_ensures_no_overhead(self) -> None:
        """ensures(true) should not produce any trap instructions."""
        source = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        result = _compile_ok(source)
        assert "unreachable" not in result.wat

    def test_ensures_bool_result(self) -> None:
        """Postcondition on a Bool-returning function."""
        source = """\
public fn is_pos(@Int -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{ @Int.0 > 0 }
"""
        assert _run(source, fn="is_pos", args=[5]) == 1
        # is_pos(-1) returns false, violating ensures(result == true)
        _run_trap(source, fn="is_pos", args=[-1])


class TestCombinedContracts:
    def test_both_hold(self) -> None:
        """Both requires and ensures hold — normal execution."""
        source = """\
public fn safe_inc(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 + 1 }
"""
        assert _run(source, fn="safe_inc", args=[0]) == 1
        assert _run(source, fn="safe_inc", args=[10]) == 11

    def test_requires_fails_first(self) -> None:
        """Precondition fails before postcondition is checked."""
        source = """\
public fn safe_inc(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 + 1 }
"""
        _run_trap(source, fn="safe_inc", args=[-1])

    def test_contracts_with_recursion(self) -> None:
        """Runtime contracts on a recursive function."""
        source = """\
public fn factorial(@Nat -> @Nat)
  requires(@Nat.0 >= 0)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 <= 1 then { 1 }
  else { @Nat.0 * factorial(@Nat.0 - 1) }
}
"""
        assert _run(source, fn="factorial", args=[5]) == 120
        assert _run(source, fn="factorial", args=[0]) == 1


# =====================================================================
# Contract failure messages (#112)
# =====================================================================

class TestContractFailMessages:
    """Verify that contract violations produce informative error messages."""

    def test_precondition_wat_has_contract_fail(self) -> None:
        """WAT should call contract_fail before unreachable for requires."""
        source = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        result = _compile_ok(source)
        assert "call $vera.contract_fail" in result.wat
        assert "unreachable" in result.wat

    def test_postcondition_wat_has_contract_fail(self) -> None:
        """WAT should call contract_fail before unreachable for ensures."""
        source = """\
public fn negate(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ -@Int.0 }
"""
        result = _compile_ok(source)
        assert "call $vera.contract_fail" in result.wat

    def test_trivial_contract_no_contract_fail(self) -> None:
        """Trivial contracts should not generate contract_fail calls."""
        source = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        result = _compile_ok(source)
        assert "contract_fail" not in result.wat

    def test_precondition_violation_message(self) -> None:
        """Precondition violation should produce an informative error."""
        source = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        result = _compile_ok(source)
        with pytest.raises(RuntimeError, match="Precondition violation"):
            execute(result, fn_name="positive", args=[0])

    def test_postcondition_violation_message(self) -> None:
        """Postcondition violation should produce an informative error."""
        source = """\
public fn negate(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ -@Int.0 }
"""
        result = _compile_ok(source)
        with pytest.raises(RuntimeError, match="Postcondition violation"):
            execute(result, fn_name="negate", args=[5])

    def test_violation_includes_function_name(self) -> None:
        """Error message should include the function name."""
        source = """\
public fn safe_div(@Int, @Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.1 / @Int.0 }
"""
        result = _compile_ok(source)
        with pytest.raises(RuntimeError, match="safe_div"):
            execute(result, fn_name="safe_div", args=[10, 0])

    def test_violation_includes_contract_text(self) -> None:
        """Error message should include the contract expression."""
        source = """\
public fn bounded(@Int -> @Int)
  requires(@Int.0 >= 0)
  requires(@Int.0 <= 100)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        result = _compile_ok(source)
        with pytest.raises(RuntimeError, match=r"requires\(@Int.0 >= 0\)"):
            execute(result, fn_name="bounded", args=[-1])

    def test_postcondition_includes_ensures_text(self) -> None:
        """Postcondition message should include the ensures expression."""
        source = """\
public fn double(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ @Int.0 * 2 }
"""
        result = _compile_ok(source)
        with pytest.raises(RuntimeError, match=r"ensures\(@Int.result >= 0\)"):
            execute(result, fn_name="double", args=[-1])

    def test_precondition_full_message_format(self) -> None:
        """Full message should have kind, signature, and clause."""
        source = """\
public fn clamp(@Int, @Int, @Int -> @Int)
  requires(@Int.0 <= @Int.1)
  ensures(true)
  effects(pure)
{ @Int.2 }
"""
        result = _compile_ok(source)
        try:
            execute(result, fn_name="clamp", args=[5, 3, 4])
            assert False, "Expected RuntimeError"
        except RuntimeError as exc:
            msg = str(exc)
            assert "Precondition violation" in msg
            assert "clamp" in msg
            assert "requires(" in msg
            assert "@Int.0 <= @Int.1" in msg
            assert "failed" in msg

    def test_unit_postcondition_violation(self) -> None:
        """Postcondition on Unit-returning function should report correctly."""
        source = """\
public fn bad_put(@Int -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 2);
  ()
}
"""
        result = _compile_ok(source)
        with pytest.raises(RuntimeError, match="Postcondition violation"):
            execute(result, fn_name="bad_put", args=[0],
                    initial_state={"State_Int": 5})


# =====================================================================
# 6.5f: old()/new() state expressions in postconditions
# =====================================================================


class TestOldNewContracts:
    """Tests for old()/new() state expression compilation in postconditions."""

    def test_old_new_postcondition_compiles(self) -> None:
        """Function with old()/new() in ensures clause compiles to WASM."""
        src = """
public fn increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
"""
        result = _compile_ok(src)
        assert "increment" in result.exports

    def test_old_new_postcondition_passes(self) -> None:
        """Postcondition holds — no trap when new == old + 1."""
        src = """
public fn increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
"""
        result = _compile_ok(src)
        exec_result = execute(
            result, fn_name="increment",
            initial_state={"State_Int": 10},
        )
        # Should complete without trap
        assert exec_result.value is None  # Unit return

    def test_old_new_postcondition_traps(self) -> None:
        """Postcondition violated — traps when increment is wrong."""
        src = """
public fn bad_increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 2);
  ()
}
"""
        result = _compile_ok(src)
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
            execute(
                result, fn_name="bad_increment",
                initial_state={"State_Int": 5},
            )

    def test_trivial_ensures_no_snapshot(self) -> None:
        """ensures(true) with State effect does NOT emit a snapshot."""
        src = """
public fn inc(@Unit -> @Unit)
  requires(true) ensures(true)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
"""
        result = _compile_ok(src)
        wat = result.wat
        assert "inc" in result.exports
        # Body should call state_get for the let binding,
        # but no snapshot local.set before the body
        lines = wat.split("\n")
        # Find the function body — there should be exactly one
        # state_get call (the let binding), not two (snapshot + let)
        state_get_count = sum(
            1 for l in lines if "call $vera.state_get_Int" in l
        )
        # Only the body's get() call — no snapshot
        assert state_get_count == 1

    def test_old_new_wat_structure(self) -> None:
        """WAT contains state_get snapshot before body and new() in postcondition."""
        src = """
public fn increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
"""
        result = _compile_ok(src)
        wat = result.wat
        lines = wat.split("\n")
        state_get_count = sum(
            1 for l in lines if "call $vera.state_get_Int" in l
        )
        # 3 calls: snapshot (old), body get(), postcondition new()
        assert state_get_count == 3

    def test_new_reads_current_state(self) -> None:
        """new(State<T>) reads the current value, not the snapshot."""
        # Increment by 5 but claim increment by 5 in postcondition
        src = """
public fn add_five(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 5)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 5);
  ()
}
"""
        result = _compile_ok(src)
        exec_result = execute(
            result, fn_name="add_five",
            initial_state={"State_Int": 100},
        )
        assert exec_result.value is None  # Unit, no trap
