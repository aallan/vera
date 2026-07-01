"""Tests for vera.codegen — infrastructure (module assembly, execute error paths, unsupported-construct skips, builtin shadowing, typed holes, E602 reasons, example round-trips).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import pytest

from vera.codegen import (
    CompileResult,
    execute,
)
from vera.codegen.api import WasmTrapError

from tests.codegen_helpers import (
    _IO_PRELUDE,
    _compile,
    _compile_example,
    _compile_ok,
    _run,
)


# =====================================================================
# Unsupported constructs
# =====================================================================


class TestUnsupportedSkipped:
    def test_adt_function_compiles(self) -> None:
        """Functions with ADT types now compile (not skipped)."""
        source = """\
private data Option<T> { None, Some(T) }

public fn make_none(-> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None }

public fn simple(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 1 }
"""
        result = _compile(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors
        # Both functions should be compiled
        assert "make_none" in result.exports
        assert "simple" in result.exports

    def test_unsupported_effect_skipped(self) -> None:
        """Functions with non-IO effects produce warnings, not errors."""
        source = """\
effect Counter {
  op tick(Unit -> Unit);
}

public fn count(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Counter>)
{
  Counter.tick(())
}

public fn simple(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert not errors
        assert len(warnings) > 0
        # Unsupported effect function is skipped
        assert "count" not in result.exports
        # Pure function still compiles
        assert "simple" in result.exports


# =====================================================================
# Example round-trips — compile and run actual .vera example files
# =====================================================================


class TestExampleRoundTrips:
    """Compile and execute the .vera example files that fall within
    the compilable subset (Int, Nat, Bool, Unit, String, IO)."""

    def test_absolute_value_positive(self) -> None:
        """absolute_value(5) returns 5."""
        result = _compile_example("absolute_value.vera")
        assert result.ok
        assert "absolute_value" in result.exports
        exec_result = execute(result, fn_name="absolute_value", args=[5])
        assert exec_result.value == 5

    def test_absolute_value_negative(self) -> None:
        """absolute_value(-7) returns 7."""
        result = _compile_example("absolute_value.vera")
        exec_result = execute(result, fn_name="absolute_value", args=[-7])
        assert exec_result.value == 7

    def test_absolute_value_zero(self) -> None:
        """absolute_value(0) returns 0."""
        result = _compile_example("absolute_value.vera")
        exec_result = execute(result, fn_name="absolute_value", args=[0])
        assert exec_result.value == 0

    def test_safe_divide(self) -> None:
        """safe_divide(3, 10) returns 3 (body: @Int.0/@Int.1 = 10/3)."""
        result = _compile_example("safe_divide.vera")
        assert result.ok
        assert "safe_divide" in result.exports
        # De Bruijn: @Int.1 = first param (divisor), @Int.0 = second param
        # Body: @Int.0 / @Int.1 = second / first = 10 / 3 = 3
        exec_result = execute(result, fn_name="safe_divide", args=[3, 10])
        assert exec_result.value == 3

    def test_safe_divide_trap_on_zero(self) -> None:
        """safe_divide(0, 10) traps: requires(@Int.1 != 0) violated."""
        result = _compile_example("safe_divide.vera")
        # First param (divisor) is 0 → precondition @Int.1 != 0 violated
        with pytest.raises(WasmTrapError) as excinfo:
            execute(result, fn_name="safe_divide", args=[0, 10])
        assert excinfo.value.kind == "contract_violation"

    def test_mutual_recursion_is_even(self) -> None:
        """Where-block mutual recursion: is_even(4) returns true."""
        result = _compile_example("mutual_recursion.vera")
        assert result.ok
        assert "is_even" in result.exports
        # is_even(4) → true (1)
        exec_result = execute(result, fn_name="is_even", args=[4])
        assert exec_result.value == 1
        # is_even(3) → false (0)
        exec_result = execute(result, fn_name="is_even", args=[3])
        assert exec_result.value == 0

    def test_mutual_recursion_zero(self) -> None:
        """is_even(0) returns true (base case)."""
        result = _compile_example("mutual_recursion.vera")
        exec_result = execute(result, fn_name="is_even", args=[0])
        assert exec_result.value == 1

    def test_factorial_example_file(self) -> None:
        """The actual examples/factorial.vera compiles and runs."""
        result = _compile_example("factorial.vera")
        assert result.ok
        exec_result = execute(result, fn_name="factorial", args=[5])
        assert exec_result.value == 120


# =====================================================================
# Module assembly — import/memory conditionals
# =====================================================================


class TestModuleAssembly:
    """Verify that module-level constructs are conditional."""

    def test_pure_no_io_import(self) -> None:
        """Pure functions should not import vera.print."""
        result = _compile_ok(
            "public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }"
        )
        assert "vera.print" not in result.wat

    def test_pure_no_memory(self) -> None:
        """Pure functions without strings should not declare memory."""
        result = _compile_ok(
            "public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }"
        )
        assert "(memory" not in result.wat

    def test_io_has_import_and_memory(self) -> None:
        """IO functions import vera.print and declare memory."""
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello") }
"""
        result = _compile_ok(source)
        assert 'import "vera" "print"' in result.wat
        assert "(memory" in result.wat
        assert "(data" in result.wat

    def test_multiple_exports(self) -> None:
        """Multiple compilable functions are all exported."""
        source = """\
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }

public fn mul(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 * @Int.0 }

public fn neg(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ -@Int.0 }
"""
        result = _compile_ok(source)
        assert "add" in result.exports
        assert "mul" in result.exports
        assert "neg" in result.exports
        assert len(result.exports) == 3


# =====================================================================
# Execute error paths
# =====================================================================


class TestExecuteErrors:
    """Test error handling in the execute() function."""

    def test_function_not_found(self) -> None:
        """execute() with unknown function name raises RuntimeError."""
        result = _compile_ok(
            "public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }"
        )
        with pytest.raises(RuntimeError, match="not found"):
            execute(result, fn_name="nonexistent")

    def test_compilation_error_blocks_execute(self) -> None:
        """execute() refuses to run if compilation had errors."""
        from vera.errors import Diagnostic, SourceLocation
        result = CompileResult(
            wat="",
            wasm_bytes=b"",
            exports=[],
            diagnostics=[
                Diagnostic(
                    description="test error",
                    location=SourceLocation(),
                    severity="error",
                )
            ],
        )
        with pytest.raises(RuntimeError, match="compilation had errors"):
            execute(result)

    def test_first_export_used_when_no_main(self) -> None:
        """When no 'main' function, the first exported function is called."""
        source = """\
public fn compute(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 99 }
"""
        result = _compile_ok(source)
        assert "main" not in result.exports
        exec_result = execute(result)  # no fn_name specified
        assert exec_result.value == 99


# =====================================================================
# User-defined functions shadow built-in intrinsics (#154)
# =====================================================================


class TestBuiltinShadowing:
    """User-defined functions take priority over built-in intrinsics."""

    def test_user_length_over_adt(self) -> None:
        """User-defined length() over a recursive ADT compiles and runs."""
        src = """
private data List<T> { Nil, Cons(T, List<T>) }

private fn length(@List<Int> -> @Nat)
  requires(true) ensures(@Nat.result >= 0)
  decreases(@List<Int>.0) effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @List<Int> = Cons(1, Cons(2, Cons(3, Nil)));
  length(@List<Int>.0)
}
"""
        assert _run(src) == 3

    def test_user_length_single_element(self) -> None:
        """User-defined length returns 1 for a single-element list."""
        src = """
private data List<T> { Nil, Cons(T, List<T>) }

private fn length(@List<Int> -> @Nat)
  requires(true) ensures(@Nat.result >= 0)
  decreases(@List<Int>.0) effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  length(Cons(42, Nil))
}
"""
        assert _run(src) == 1

    def test_builtin_array_length_still_works(self) -> None:
        """Array length built-in works when no user-defined length exists."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  array_length(@Array<Int>.0)
}
"""
        assert _run(src) == 3


class TestTypedHoles:
    """Typed holes: compile rejects programs with ? placeholders."""

    def test_hole_compile_rejected(self) -> None:
        """Programs with holes produce E614 and cannot compile."""
        src = """\
public fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ ? }
"""
        result = _compile(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(d.error_code == "E614" for d in errors), \
            f"Expected E614, got: {[d.error_code for d in errors]}"
        assert result.wasm_bytes == b""

    def test_hole_nested_compile_rejected(self) -> None:
        """Holes in non-root positions (let bindings) also produce E614."""
        src = """\
public fn bar(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = ?;
  @Int.0 + 1
}
"""
        result = _compile(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(d.error_code == "E614" for d in errors), \
            f"Expected E614, got: {[d.error_code for d in errors]}"
        assert result.wasm_bytes == b""


class TestE602NodeLevelReasons626Layer3:
    """`#626` Layer 3 (PR #658) — `[E602]` diagnostics now carry a
    node-level span and a specific reason string, rather than the
    pre-Layer-3 generic enclosing-function-level message.

    Pre-Layer-3 the diagnostic looked like::

        [E602] Function 'main' body contains unsupported expressions
        — skipped.   ← span: declaration of `main` (line N)

    Post-Layer-3::

        [E602] Function 'main' body contains unsupported FnCall:
        Map/Set with Array-typed key, value, or element is not
        supported — function skipped.   ← span: the offending
        map_insert(...) call (line N+M)

    These two tests pin the user-visible contract:

    1. the diagnostic's ``description`` includes the specific reason
       text that the ``raise CodegenSkip(node, reason)`` site passed
       — preventing a future refactor from dropping back to a generic
       message.
    2. the diagnostic's ``location.line`` matches the offending node
       (the FnCall), not the enclosing function declaration — preventing
       a future refactor from dropping the per-node span.

    See `vera/codegen/functions.py::_compile_fn` for the catch handler
    that turns ``CodegenSkip(node, reason)`` into the user-visible
    ``[E602]`` shape.
    """

    _MAP_OF_ARRAY_SRC = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<Nat, Array<Nat>> = map_insert(map_new(), 1, [1, 2, 3]);
  IO.print("ok")
}
"""

    def test_e602_description_contains_node_specific_reason(self) -> None:
        """The `[E602]` description for `Map<Nat, Array<Nat>>` carries
        the specific reason text from the `_translate_map_insert`
        raise site, not just the generic ``"unsupported expressions"``.

        Locks in the user-visible improvement from PR #658:
        ``CodegenSkip(call, "Map/Set with Array-typed key, value, or
        element is not supported")`` flows through the catch handler
        as ``f"Function '{decl.name}' body contains unsupported
        {type(skip.node).__name__}: {skip.reason}"``.
        """
        result = _compile(self._MAP_OF_ARRAY_SRC)
        e602 = [
            d for d in result.diagnostics
            if d.error_code == "E602" and "main" in d.description
        ]
        assert e602, (
            f"Expected an [E602] for `main`; diagnostics: "
            f"{result.diagnostics}"
        )
        # The reason string from `vera/wasm/calls_containers.py`'s
        # CodegenSkip raise should appear verbatim in the diagnostic.
        assert "Array-typed" in e602[0].description, (
            f"Expected node-specific reason in [E602] description; "
            f"got: {e602[0].description!r}"
        )
        # And the AST-node-type label too — confirms the catch handler
        # is composing from `type(skip.node).__name__`.
        assert "FnCall" in e602[0].description, (
            f"Expected FnCall node-type label in [E602] description; "
            f"got: {e602[0].description!r}"
        )

    def test_e602_location_points_at_offending_call_not_fn_header(
        self,
    ) -> None:
        """The `[E602]` source location points at the offending
        `map_insert(...)` call (line 5 of the test source), not the
        `public fn main(...)` declaration (line 2).

        Pre-Layer-3 the legacy `_warning(decl, ...)` call attached
        the function-declaration span; Post-Layer-3 the catch handler
        passes `skip.node` (the FnCall), giving a per-node span.
        """
        result = _compile(self._MAP_OF_ARRAY_SRC)
        e602 = [
            d for d in result.diagnostics
            if d.error_code == "E602" and "main" in d.description
        ]
        assert e602, (
            f"Expected an [E602] for `main`; got: {result.diagnostics}"
        )
        # `public fn main(@Unit -> @Unit)` is line 2 in _MAP_OF_ARRAY_SRC;
        # the offending `map_insert(...)` is line 5, column 31.  The
        # diagnostic must point exactly at the call, not the declaration
        # (line 2) or any later statement.  Pin the line precisely so
        # any future refactor that drops back to enclosing-function
        # span (line 2) OR drifts to the `IO.print` on line 6 fails
        # the test.
        loc_line = e602[0].location.line
        assert loc_line == 5, (
            f"Expected [E602] location at line 5 (the "
            f"`map_insert(...)` call); got line {loc_line}.  "
            f"Pre-#658 this would have been line 2 (legacy "
            f"enclosing-fn span).  Any other line means the catch "
            f"handler drifted off the offending FnCall node."
        )
