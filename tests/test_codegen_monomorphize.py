"""Tests for vera.codegen — Monomorphization of generic (forall<T>) functions."""

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
# C6i: Monomorphization of generic (forall<T>) functions
# =====================================================================


class TestMonomorphization:
    """Tests for monomorphization of forall<T> functions."""

    def test_identity_int(self) -> None:
        """forall<T> fn identity instantiated with Int."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        assert _run(source, fn="main") == 42

    def test_identity_bool(self) -> None:
        """forall<T> fn identity instantiated with Bool."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ identity(true) }
"""
        assert _run(source, fn="main") == 1

    def test_identity_two_instantiations(self) -> None:
        """Same generic function instantiated with both Int and Bool."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_int(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }

public fn test_bool(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ identity(false) }
"""
        result = _compile_ok(source)
        # Private generic -> monomorphized variants not exported
        assert "identity$Int" not in result.exports
        assert "identity$Bool" not in result.exports
        # Public callers are exported
        assert "test_int" in result.exports
        assert "test_bool" in result.exports
        # Run both
        exec_int = execute(result, fn_name="test_int")
        assert exec_int.value == 42
        exec_bool = execute(result, fn_name="test_bool")
        assert exec_bool.value == 0

    def test_identity_slot_ref_arg(self) -> None:
        """Generic function called with a slot reference argument."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(@Int.0) }
"""
        assert _run(source, fn="main", args=[99]) == 99

    def test_const_function(self) -> None:
        """forall<A, B> fn const with two type parameters."""
        source = """\
private forall<A, B> fn const(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{ @A.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ const(42, true) }
"""
        assert _run(source, fn="main") == 42

    def test_generic_with_adt_match(self) -> None:
        """forall<T> fn is_some with ADT match (Some case)."""
        source = """\
private data Option<T> { None, Some(T) }

private forall<T> fn is_some(@Option<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match @Option<T>.0 {
    None -> false,
    Some(@T) -> true
  }
}

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ is_some(Some(1)) }
"""
        assert _run(source, fn="main") == 1

    def test_generic_with_adt_match_none(self) -> None:
        """forall<T> fn is_some with ADT match (None case)."""
        source = """\
private data Option<T> { None, Some(T) }

private forall<T> fn is_some(@Option<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match @Option<T>.0 {
    None -> false,
    Some(@T) -> true
  }
}

public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  is_some(@Option<Int>.0)
}
"""
        assert _run(source, fn="main") == 0

    def test_generic_fn_wat_has_mangled_name(self) -> None:
        """WAT output contains mangled function name."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        result = _compile_ok(source)
        assert "$identity$Int" in result.wat

    def test_generic_fn_mangled_in_exports(self) -> None:
        """Private generic's mangled names not exported; public caller is."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        result = _compile_ok(source)
        # Private generic -> monomorphized variants not exported
        assert "identity$Int" not in result.exports
        assert "identity" not in result.exports
        # Public caller is exported
        assert "main" in result.exports

    def test_non_generic_fn_unaffected(self) -> None:
        """Non-generic functions compile normally alongside generic ones."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ double(identity(21)) }
"""
        assert _run(source, fn="main") == 42

    def test_generic_identity_in_let_binding(self) -> None:
        """Generic call result used in a let binding."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = identity(10);
  @Int.0 + 5
}
"""
        assert _run(source, fn="main") == 15

    def test_generic_chained_calls(self) -> None:
        """Generic function called with result of another generic call."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(identity(99)) }
"""
        assert _run(source, fn="main") == 99

    def test_generic_in_if_branch(self) -> None:
        """Generic call inside an if-then-else branch."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { identity(1) } else { identity(2) }
}
"""
        assert _run(source, fn="main", args=[1]) == 1
        assert _run(source, fn="main", args=[0]) == 2

    def test_generic_with_arithmetic_arg(self) -> None:
        """Generic function called with arithmetic expression as argument."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(3 + 4) }
"""
        assert _run(source, fn="main") == 7

    def test_generic_no_callers_skipped(self) -> None:
        """Generic function with no callers is gracefully skipped."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "main" in result.exports
        # identity has no callers -> no monomorphized version -> not in exports
        assert "identity" not in result.exports

    def test_generics_example_file(self) -> None:
        """examples/generics.vera compiles without errors."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "generics.vera"
        source = path.read_text()
        result = _compile(source)
        assert result.ok

    def test_list_ops_example_file(self) -> None:
        """examples/list_ops.vera compiles and runs correctly (#154)."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "list_ops.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_list")
        assert exec_result.value == 60
