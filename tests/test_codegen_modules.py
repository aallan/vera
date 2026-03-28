"""Tests for vera.codegen — Cross-module codegen.

Covers the cross-module guard rail and cross-module function compilation
via flattening.
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
# Cross-module guard rail
# =====================================================================


class TestCrossModuleGuardRail:
    """Calls to undefined functions produce a proper diagnostic."""

    def test_undefined_fn_call_diagnostic(self) -> None:
        """Calling a function not defined in this module emits a diagnostic."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ unknown_fn(42) }
"""
        result = _compile(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert len(errors) == 1
        assert "unknown_fn" in errors[0].description
        assert "not defined in this module" in errors[0].description
        assert "not found in any imported module" in errors[0].description
        assert result.ok is False

    def test_undefined_fn_no_raw_wasmtime_error(self) -> None:
        """No raw WAT compilation error -- guard rail catches it first."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ missing(1) }
"""
        result = _compile(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert all("WAT compilation failed" not in e.description for e in errors)

    def test_locally_defined_fn_compiles(self) -> None:
        """Calls to locally defined functions still work."""
        source = """\
public fn helper(-> @Int) requires(true) ensures(true) effects(pure) { 1 }
public fn f(-> @Int) requires(true) ensures(true) effects(pure) { helper() }
"""
        result = _compile_ok(source)
        assert result.ok is True


# =====================================================================
# Cross-module codegen (C7e)
# =====================================================================


class TestCrossModuleCodegen:
    """Imported functions are compiled into the WASM module via flattening."""

    # Reusable module sources
    MATH_MODULE = """\
public fn abs(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }

public fn max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= @Int.0)
  ensures(@Int.result >= @Int.1)
  effects(pure)
{ if @Int.0 >= @Int.1 then { @Int.0 } else { @Int.1 } }
"""

    HELPER_MODULE = """\
public fn double(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ internal(@Int.0) + internal(@Int.0) }

private fn internal(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> "ResolvedModule":
        """Build a ResolvedModule from source text."""
        import tempfile
        from pathlib import Path

        from vera.resolver import ResolvedModule as RM

        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            f.flush()
            fpath = f.name

        tree = parse_file(fpath)
        prog = transform(tree)
        return RM(
            path=path,
            file_path=Path(fpath),
            program=prog,
            source=source,
        )

    @classmethod
    def _compile_mod(
        cls, source: str, modules: list,
    ) -> CompileResult:
        """Compile with resolved modules."""
        import tempfile

        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            f.flush()
            path = f.name

        tree = parse_file(path)
        ast = transform(tree)
        return compile(
            ast, source=source, file=path, resolved_modules=modules,
        )

    @classmethod
    def _run_mod(
        cls, source: str, modules: list,
        fn: str | None = None, args: list[int] | None = None,
    ) -> int:
        """Compile with modules, execute, and return the integer result."""
        result = cls._compile_mod(source, modules)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, f"Unexpected errors: {[e.description for e in errors]}"
        exec_result = execute(result, fn_name=fn, args=args)
        assert exec_result.value is not None, "Expected a return value"
        return exec_result.value

    # -- Basic compilation --------------------------------------------------

    def test_imported_function_compiles(self) -> None:
        """Imported function produces valid WASM."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._compile_mod("""\
import math(abs);
public fn wrap(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(@Int.0) }
""", [mod])
        assert result.ok, [d.description for d in result.diagnostics]
        assert "$abs" in result.wat

    def test_imported_function_executes(self) -> None:
        """abs(-5) returns 5 via cross-module call."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        val = self._run_mod("""\
import math(abs);
public fn wrap(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(@Int.0) }
""", [mod], fn="wrap", args=[-5])
        assert val == 5

    def test_multiple_imports_execute(self) -> None:
        """abs(max(x, y)) compiles and runs correctly."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        val = self._run_mod("""\
import math(abs, max);
public fn abs_max(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(max(@Int.0, @Int.1)) }
""", [mod], fn="abs_max", args=[-3, -5])
        assert val == 3  # abs(max(-3, -5)) = abs(-3) = 3

    # -- Export / visibility -------------------------------------------------

    def test_imported_functions_not_exported(self) -> None:
        """Imported functions are internal, not WASM exports."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._compile_mod("""\
import math(abs);
public fn wrap(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(@Int.0) }
""", [mod])
        assert result.ok
        # Only local public functions are exported
        assert "wrap" in result.exports
        assert "abs" not in result.exports

    def test_local_shadows_import(self) -> None:
        """Local definition of abs shadows the imported one."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        val = self._run_mod("""\
import math(abs);
public fn abs(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 999 }
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(42) }
""", [mod], fn="main")
        assert val == 999  # local abs, not imported

    # -- Guard rail ----------------------------------------------------------

    def test_guard_rail_still_catches_unknowns(self) -> None:
        """Unknown function still produces an error even with modules."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._compile_mod("""\
import math(abs);
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ totally_undefined(1) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert len(errors) == 1
        assert "totally_undefined" in errors[0].description
        assert result.ok is False

    # -- Private helper compilation ------------------------------------------

    def test_private_helper_compiled(self) -> None:
        """Public fn calling private helper works across modules."""
        mod = self._resolved(("util",), self.HELPER_MODULE)
        val = self._run_mod("""\
import util(double);
public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0) }
""", [mod], fn="main", args=[7])
        assert val == 14  # double(7) = internal(7) + internal(7) = 14

    # -- Data imports --------------------------------------------------------

    def test_data_imports_dont_break_codegen(self) -> None:
        """Importing data types alongside functions compiles fine."""
        data_mod_source = """\
public data Color { Red, Green, Blue }
public fn pick(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        mod = self._resolved(("colors",), data_mod_source)
        val = self._run_mod("""\
import colors(pick);
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ pick() }
""", [mod], fn="main")
        assert val == 42


# =====================================================================
# Name collision detection (#110)
# =====================================================================


class TestNameCollisionDetection:
    """Name collisions across imported modules produce diagnostics."""

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> "ResolvedModule":
        """Build a ResolvedModule from source text."""
        return TestCrossModuleCodegen._resolved(path, source)

    @classmethod
    def _compile_mod(
        cls, source: str, modules: list,
    ) -> CompileResult:
        """Compile with resolved modules."""
        return TestCrossModuleCodegen._compile_mod(source, modules)

    def test_fn_collision_two_modules(self) -> None:
        """Same function name in two imported modules produces E608."""
        mod_a = self._resolved(("mod_a",), """\
public fn process(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }
""")
        mod_b = self._resolved(("mod_b",), """\
public fn process(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 2 }
""")
        result = self._compile_mod("""\
import mod_a(process);
import mod_b(process);
public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ process(@Int.0) }
""", [mod_a, mod_b])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert len(errors) >= 1
        assert "process" in errors[0].description
        assert "mod_a" in errors[0].description
        assert "mod_b" in errors[0].description
        assert errors[0].error_code == "E608"
        assert result.ok is False

    def test_private_helper_collision(self) -> None:
        """Private helpers with same name across modules produce E608."""
        mod_a = self._resolved(("mod_a",), """\
public fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ helper(@Int.0) + helper(@Int.0) }
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        mod_b = self._resolved(("mod_b",), """\
public fn triple(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ helper(@Int.0) + helper(@Int.0) + helper(@Int.0) }
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        result = self._compile_mod("""\
import mod_a(double);
import mod_b(triple);
public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0) + triple(@Int.0) }
""", [mod_a, mod_b])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(
            e.error_code == "E608" and "helper" in e.description
            for e in errors
        )

    def test_adt_type_collision(self) -> None:
        """Same ADT name in two modules produces E609."""
        mod_a = self._resolved(("mod_a",), """\
public data Color { Red, Green, Blue }
""")
        mod_b = self._resolved(("mod_b",), """\
public data Color { Cyan, Magenta, Yellow }
""")
        result = self._compile_mod("""\
import mod_a(Color);
import mod_b(Color);
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""", [mod_a, mod_b])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(
            e.error_code == "E609" and "Color" in e.description
            for e in errors
        )

    def test_prelude_types_not_flagged_as_collision(self) -> None:
        """Builtin ADTs (Option, Result, etc.) shared across two imported modules
        must NOT produce E609. Regression test for #360.

        Both modules explicitly return builtin ADTs so that Option and Result
        appear in each module's _adt_layouts when the temp CodeGenerators are
        built — this is the exact scenario that triggered the false positive.
        """
        mod_a = self._resolved(("mod_a",), """\
public fn maybe_double(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(@Int.0 * 2) }
""")
        mod_b = self._resolved(("mod_b",), """\
public fn safe_triple(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(@Int.0 * 3) }
""")
        result = self._compile_mod("""\
import mod_a(maybe_double);
import mod_b(safe_triple);
public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = maybe_double(@Int.0);
  match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> 0 }
}
""", [mod_a, mod_b])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        # Option, Result, Ordering, UrlParts, Tuple, MdInline, MdBlock are
        # builtins registered in every CodeGenerator — must not collide.
        assert not any(
            e.error_code == "E609" for e in errors
        ), f"False E609 for builtin ADTs: {[e.description for e in errors if e.error_code == 'E609']}"
        assert result.ok is True

    def test_ctor_collision_across_adts(self) -> None:
        """Same constructor name in different ADTs produces E610."""
        mod_a = self._resolved(("colors",), """\
public data Color { Red, Green, Blue }
""")
        mod_b = self._resolved(("shapes",), """\
public data Shape { Red, Green, Triangle }
""")
        result = self._compile_mod("""\
import colors(Color);
import shapes(Shape);
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""", [mod_a, mod_b])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(
            e.error_code == "E610" and "Red" in e.description
            for e in errors
        )
        assert any(
            e.error_code == "E610" and "Green" in e.description
            for e in errors
        )

    def test_local_shadows_import_no_collision(self) -> None:
        """Local definition shadowing an import is NOT a collision."""
        mod = self._resolved(("math",), TestCrossModuleCodegen.MATH_MODULE)
        result = self._compile_mod("""\
import math(abs);
public fn abs(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 999 }
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(42) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, (
            f"Local shadow should not produce collision: {errors}"
        )

    def test_same_module_no_collision(self) -> None:
        """Same module path in resolved list twice is not a collision."""
        mod = self._resolved(("math",), TestCrossModuleCodegen.MATH_MODULE)
        result = self._compile_mod("""\
import math(abs);
public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(@Int.0) }
""", [mod, mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors

    def test_collision_message_includes_both_modules(self) -> None:
        """Collision diagnostic mentions both conflicting module paths."""
        mod_a = self._resolved(("alpha",), """\
public fn compute(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        mod_b = self._resolved(("beta",), """\
public fn compute(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        result = self._compile_mod("""\
import alpha(compute);
import beta(compute);
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""", [mod_a, mod_b])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert len(errors) >= 1
        desc = errors[0].description
        assert "alpha" in desc and "beta" in desc
