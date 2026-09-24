"""Tests for vera.codegen — Cross-module codegen.

Covers the cross-module guard rail and cross-module function compilation
via flattening.
"""

from __future__ import annotations

from pathlib import Path
from typing import ClassVar

import pytest
import wasmtime

from vera import ast
from vera.codegen import (
    CompileResult,
    compile,
    execute,
)
from vera.parser import parse_file
from vera.transform import transform
from vera.monomorphize import resolve_fn_type_alias
from vera.symbols import module_symbol

from tests.module_fixture_helpers import resolved_module


# =====================================================================
# Helpers
# =====================================================================


def _parse_from_temp_file(source: str) -> tuple[ast.Program, str]:
    """Parse *source* through a real temp file: ``(program, path)``.

    These tests need a real file because they exercise the module
    pipeline through ``parse_file``, but nothing downstream re-reads the
    path — codegen works off the returned program and the in-memory
    source string, and keeps the path only as a diagnostic label.  So
    the file is removed the moment it has been parsed.  ``delete=False``
    plus a manual unlink is the Windows-portable pattern (an open
    ``NamedTemporaryFile`` cannot be reopened there); see TESTING.md's
    Test Fixture Conventions.  Six sites in this file each wrote the
    temp file and never removed it, leaking one per call (#1228
    adversarial round).
    """
    import tempfile

    # Same shape as `tests/module_fixture_helpers.resolved_module`, and
    # for the same two reasons: the `try` is entered before anything that
    # can fail (a write error would otherwise strand the file, since
    # `delete=False` outlives the block), and the single unlink sits
    # AFTER the `with` has closed the handle — Windows cannot delete an
    # open one (PR #1282 review).
    tmp = tempfile.NamedTemporaryFile(  # noqa: SIM115 — closed by the `with`
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    )
    path = tmp.name
    try:
        with tmp as f:
            f.write(source)
            f.flush()
        return transform(parse_file(path)), path
    finally:
        Path(path).unlink(missing_ok=True)


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    prog, path = _parse_from_temp_file(source)
    return compile(prog, source=source, file=path)


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

    _resolved = staticmethod(resolved_module)

    @classmethod
    def _compile_mod(
        cls, source: str, modules: list,
    ) -> CompileResult:
        """Compile with resolved modules."""
        prog, path = _parse_from_temp_file(source)
        return compile(
            prog, source=source, file=path, resolved_modules=modules,
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
        # `abs` is a built-in, which holds its name in every namespace
        # (§8.5.2.2): the checker resolves the entry's bare `abs` to it and
        # never to an import, so math's declaration owns no bare name and is
        # emitted under its own module's symbol (#1494).
        assert f"(func ${module_symbol(('math',), 'abs')} " in result.wat

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

    def test_qualified_call_bypasses_local_shadow(self) -> None:
        """§8.5.3: a module-qualified call bypasses a local shadow.

        Regression for #814: codegen desugared ModuleCall to a bare FnCall,
        dropping the module path, so ``m::hundred`` wrongly resolved to the
        shadowing local instead of the module's function.  A non-builtin name
        keeps the verifier/codegen built-in models (abs/min/max) from
        confounding the test.
        """
        mod = self._resolved(("m",), """\
public fn hundred(@Int -> @Int)
  requires(true) ensures(@Int.result == 100) effects(pure)
{ 100 }
""")
        val = self._run_mod("""\
import m(hundred);
public fn hundred(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ m::hundred(0) }
""", [mod], fn="main")
        assert val == 100  # module's hundred() = 100, NOT the local 0

    def test_qualified_call_verifier_codegen_agree(self) -> None:
        """#814 differential: the verifier and codegen resolve a module-
        qualified call to the SAME function (cross-component soundness).

        For a program where the module's ``hundred`` returns 100 and a local
        shadow returns 0, the verifier proves ``ensures(== 100)`` via the
        module's contract while codegen must *run* the module's body (100).
        A desync in either direction fails here: if codegen ran the local,
        ``run`` returns 0 ≠ 100; if the verifier used the local, it could not
        prove ``== 100`` and emits an error.
        """
        import tempfile
        from pathlib import Path

        from vera.checker import typecheck
        from vera.verifier import verify

        mod = self._resolved(("m",), """\
public fn hundred(@Int -> @Int)
  requires(true) ensures(@Int.result == 100) effects(pure)
{ 100 }
""")
        main_src = """\
import m(hundred);
public fn hundred(@Int -> @Int)
  requires(true) ensures(@Int.result == 0) effects(pure)
{ 0 }
public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 100) effects(pure)
{ m::hundred(0) }
"""
        # Codegen side: runs the module's body, returning 100 (not local 0).
        assert self._run_mod(main_src, [mod], fn="main") == 100

        # Verifier side: proves ensures(== 100) via the module's contract.
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(main_src)
            f.flush()
            path = f.name
        try:
            prog = transform(parse_file(path))
            # Assert the check stage is clean too, so a check-stage module-
            # resolution regression is caught independently of verify
            # (typecheck returns the diagnostics list directly).
            check_diags = typecheck(prog, main_src, resolved_modules=[mod])
            check_errors = [d for d in check_diags if d.severity == "error"]
            assert check_errors == [], [e.description for e in check_errors]
            vres = verify(prog, main_src, resolved_modules=[mod])
            errors = [d for d in vres.diagnostics if d.severity == "error"]
            assert errors == [], [e.description for e in errors]
        finally:
            Path(path).unlink(missing_ok=True)

    def test_qualified_call_body_reaches_module_siblings(self) -> None:
        """#814 C2: inside a qualified-reached qualified body, an intra-module
        call lands on the module's sibling, not a local shadow of its name.

        Module ``outer`` calls ``inner``; the importer shadows BOTH locally.
        ``m::outer`` runs the module's ``outer``, whose ``inner(...)`` must in
        turn reach the module's ``inner`` (100), not the local shadow (7).
        """
        mod = self._resolved(("m",), """\
public fn inner(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 100 }
public fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ inner(@Int.0) }
""")
        val = self._run_mod("""\
import m(inner, outer);
public fn inner(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 7 }
public fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ m::outer(0) }
""", [mod], fn="main")
        assert val == 100  # module inner via module outer, NOT local inner (7)

    def test_wildcard_qualified_and_bare_calls_coexist(self) -> None:
        """#814: under a wildcard ``import m;``, a qualified call and a bare
        call to the same shadowed name resolve independently within one
        expression — qualified → module (100), bare → local (7).
        """
        mod = self._resolved(("m",), """\
public fn hundred(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 100 }
""")
        val = self._run_mod("""\
import m;
public fn hundred(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 7 }
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ m::hundred(0) + hundred(0) }
""", [mod], fn="main")
        assert val == 107  # 100 (qualified -> module) + 7 (bare -> local)

    def test_imported_body_reaches_module_sibling_over_local_shadow(
        self,
    ) -> None:
        """#814 C2 (Pass 2.5 mirror): a NON-shadowed imported fn whose body
        calls a sibling reaches the module's sibling, not a local shadow of
        that name.

        ``outer`` is imported (not locally shadowed, so it compiles in Pass
        2.5 under its bare name) and calls ``inner``; the importer shadows
        only ``inner``.  A bare ``outer()`` must run the module's ``outer``,
        whose ``inner(...)`` reaches the module's ``inner`` (100) via the
        intra-rename map — not the local shadow (7).
        """
        mod = self._resolved(("m",), """\
public fn inner(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 100 }
public fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ inner(@Int.0) }
""")
        val = self._run_mod("""\
import m(inner, outer);
public fn inner(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 7 }
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ outer(0) }
""", [mod], fn="main")
        assert val == 100  # module inner via module outer (Pass 2.5), not local 7

    def test_imported_where_fn_reaches_module_helper_over_local_shadow(
        self,
    ) -> None:
        """#814 C2 (where-fn mirror): an imported fn's `where` helper resolves
        to the module's helper even when the importer locally shadows that
        helper's name.

        ``outer`` (imported, not shadowed) calls its `where` helper ``helper``;
        the importer defines a local ``helper``.  ``outer()`` must reach the
        module's helper (100) via the intra-rename map, not the local shadow
        (7) — the where-fns go through the same shadow wiring as top-level fns.
        """
        mod = self._resolved(("m",), """\
public fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ helper(@Int.0) }
where {
  fn helper(@Int -> @Int) requires(true) ensures(true) effects(pure) { 100 }
}
""")
        val = self._run_mod("""\
import m(outer);
public fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 7 }
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ outer(0) }
""", [mod], fn="main")
        assert val == 100  # module's where-helper, NOT the local shadow (7)

    def test_local_where_fn_shadows_imported_name(self) -> None:
        """#814: a LOCAL `where`-fn shadowing an imported name must not produce
        a duplicate bare WASM function.

        The importer's `main` has a `where` helper `helper`, and the module
        also exports `helper`.  A `where`-fn flattens to a bare ``$helper``, so
        the imported `helper` must be recognized as shadowed (emitted only
        under its ``<path>::…`` name, never a second bare ``$helper``).  Before the
        fix, `local_fn_names` collected only top-level names, so the imported
        `helper` was emitted bare too → a duplicate-`$helper` WASM module that
        wasmtime rejects.
        """
        mod = self._resolved(("m",), """\
public fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 100 }
""")
        val = self._run_mod("""\
import m(helper);
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ helper(0) }
where {
  fn helper(@Int -> @Int) requires(true) ensures(true) effects(pure) { 7 }
}
""", [mod], fn="main")
        assert val == 7  # local where-helper; no duplicate-$helper WASM error

    def test_unit_returning_qualified_call_in_statement_position(self) -> None:
        """#814: a `@Unit`-returning module-qualified call in non-tail
        statement position must not emit a stray `drop`.

        The drop-classifier (`_is_void_expr`) inspects the raw `ModuleCall`
        node before it is desugared, so it must resolve the qualified target
        and recognize a `@Unit` return — otherwise `m::noop(); 42` appends a
        `drop` for a value that was never pushed, and wasmtime rejects the
        module ("expected a type but nothing on stack").  Same class as the
        user-`@Unit`-fn statement-position case (#584).
        """
        mod = self._resolved(("m",), """\
public fn noop(@Int -> @Unit)
  requires(true) ensures(true) effects(pure)
{ () }
""")
        val = self._run_mod("""\
import m;
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  m::noop(0);
  42
}
""", [mod], fn="main")
        assert val == 42  # unit ModuleCall dropped cleanly; no stray-drop WASM error

    def test_pair_returning_qualified_call_in_statement_position(self) -> None:
        """#814: a `@String`/`@Array`-returning module-qualified call in
        non-tail statement position must drop BOTH stack values (i32 ptr +
        i32 len), not one.

        Sibling of ``test_unit_returning_qualified_call_in_statement_position``
        for the *pair* result shape.  The drop-classifier
        (``_is_pair_result_expr``) inspects the raw ``ModuleCall`` node and
        must resolve the qualified target through ``_module_qualified_targets``
        to recognize a pair-returning (``@String`` / ``@Array``) callee.  The
        local ``make_str`` where-shadow forces resolution through the mangled
        ``<path>::…`` target (not the bare-name fallback), so this also pins the
        shadowed branch of the classifier.  If the ModuleCall clause is
        missing, only one of the two i32 values is dropped and wasmtime
        rejects the module as invalid WASM.
        """
        mod = self._resolved(("m",), """\
public fn make_str(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ "hi" }
""")
        val = self._run_mod("""\
import m;
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  m::make_str(0);
  42
}
where {
  fn make_str(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { 7 }
}
""", [mod], fn="main")
        assert val == 42  # pair ModuleCall dropped cleanly; no invalid-WASM error

    def test_nat_param_guard_mirrored_on_shadowed_qualified_call(self) -> None:
        """#814: the @Nat-parameter narrowing guard is mirrored onto a
        shadowed module fn's mangled ``<path>::…`` target.

        A qualified call ``m::f(0 - 1)`` to a *shadowed* module fn whose
        parameter is ``@Nat`` must still emit the call-site ``value >= 0``
        narrowing guard, which keys on the resolved ``<path>::…`` target via
        ``_fn_nat_params``.  The ``0 - 1`` underflow idiom is Tier-3-deferred
        by the verifier (so ``vera verify`` is clean) and must TRAP at
        runtime.  If the guard bitmap is *not* mirrored onto the mangled name
        (``vera/codegen/modules.py``), the negative value is passed unchecked
        — verified: the program then returns ``-1`` with no trap, an unsound
        @Nat.  The local ``f`` where-shadow forces resolution through the
        mangled target rather than the bare name.
        """
        mod = self._resolved(("m",), """\
public fn f(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError),
        ):
            self._run_mod("""\
import m;
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  m::f(0 - 1)
}
where {
  fn f(@Nat -> @Int)
    requires(true) ensures(true) effects(pure)
  { @Nat.0 }
}
""", [mod], fn="main")

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

    # -- #628 cross-module return-type-expression harvest -----------------

    def test_cross_module_index_of_fncall(self) -> None:
        """`make_arr(())[0]` where `make_arr` is defined in another
        module compiles and returns the first element.

        `#628` regression: pre-fix `_fn_ret_type_exprs` was populated
        only for in-module functions, so the IndexExpr translator's
        element-type inference returned None for `make_arr(())[0]`,
        the enclosing `main` got dropped via `[E602]`, and `vera run`
        reported "No exported functions to call".  Post-fix the
        cross-module harvest in `vera/codegen/modules.py` populates
        `_fn_ret_type_exprs` alongside `_fn_sigs`.
        """
        arr_mod_source = """\
public fn make_arr(@Unit -> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{
  [1, 2, 3]
}
"""
        mod = self._resolved(("arr",), arr_mod_source)
        val = self._run_mod("""\
import arr(make_arr);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  make_arr(())[0]
}
""", [mod], fn="main")
        assert val == 1, (
            f"Expected make_arr(())[0] == 1 cross-module; got {val!r}.  "
            "Pre-#628-fix this would have failed with main dropped via "
            "[E602] and no exported function to call."
        )

    def test_cross_module_string_interpolation_of_fncall(self) -> None:
        """Interpolating a `String`-returning cross-module call inside
        a string literal compiles and prints correctly.

        Pre-fix: `_fn_ret_type_exprs` lookup returned None for
        cross-module `make_str`, the interpolation segment fell through
        to the `to_string(...)` silent wrapper, the i32_pair value
        tripped `expected i64, found i32` at WASM validation, and
        the enclosing function was dropped.
        """
        str_mod_source = """\
public fn make_str(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{
  "hello"
}
"""
        mod = self._resolved(("strs",), str_mod_source)
        result = self._compile_mod("""\
import strs(make_str);

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make_str(()))!\\n")
}
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, (
            f"Expected no errors after #628 fix; got: "
            f"{[d.description for d in errors]}"
        )
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "hello!\n", (
            f"Expected 'hello!\\n'; got {exec_result.stdout!r}"
        )


# =====================================================================
# #774 — cross-module generic monomorphization
# =====================================================================


class TestCrossModuleGenerics774:
    """`#774` — an imported generic instantiated only by the importer must be
    monomorphized by the importer (its clone emitted into the flat module) and
    verified in lockstep, for both the bare and module-qualified call forms.

    Pre-fix: the importer's mono discovery built from its own
    ``program.declarations`` (the imported generic isn't there) and the defining
    module only monomorphized its own instantiations, so the clone was emitted
    NOWHERE — ``vera check`` passed but ``vera run`` failed WASM validation at
    ``call $gid`` (both call forms).  The #814 asymmetric variant (a generic
    shadowed by a local AND qualified-called) false-Tier-1'd instead: verify
    resolved the module generic's contract while codegen fell back to the local
    shadow.
    """

    # Reuse the sibling class's module-compilation helpers.  Wrapped in
    # ``staticmethod(...)`` so ``self._resolved(path, src)`` doesn't bind ``self``
    # as an extra positional argument (the underlying methods are static/class
    # methods of ``TestCrossModuleCodegen`` and take no ``self``).
    _resolved = staticmethod(TestCrossModuleCodegen._resolved)
    _compile_mod = staticmethod(TestCrossModuleCodegen._compile_mod)
    _run_mod = staticmethod(TestCrossModuleCodegen._run_mod)

    GEN_MODULE = """\
public forall<T> fn gid(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ @T.0 }
"""

    def test_imported_generic_bare_call_executes(self) -> None:
        """`gid(42)` (bare) runs, returning 42 — the importer emits gid$Int.

        Pre-fix this failed WASM validation at ``call $gid`` (no clone).  The
        observable output (42) cannot coincide with the phantom-var default
        (Bool/i32), so a discovery miss can't masquerade as a pass.
        """
        mod = self._resolved(("genmod",), self.GEN_MODULE)
        val = self._run_mod("""\
import genmod;
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ gid(42) }
""", [mod], fn="main")
        assert val == 42

    def test_imported_generic_qualified_call_executes(self) -> None:
        """`genmod::gid(42)` (qualified ModuleCall) runs, returning 42.

        The qualified form is an ``ast.ModuleCall`` the shared discovery now
        walks; it desugars to the bare mono target at codegen.  Pre-fix it
        crashed identically at ``call $gid``.
        """
        mod = self._resolved(("genmod",), self.GEN_MODULE)
        val = self._run_mod("""\
import genmod;
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ genmod::gid(42) }
""", [mod], fn="main")
        assert val == 42

    def test_imported_generic_two_instantiations_execute(self) -> None:
        """Two distinct instantiations (`gid<Int>`, `gid<Bool>`) both emit and
        run — the importer's worklist covers each concrete type it uses."""
        mod = self._resolved(("genmod",), self.GEN_MODULE)
        # gid(true) → true (1); if it wrongly shared gid<Int>'s i64 clone the
        # bool result would still read 1 here, so also exercise the Int arm to
        # pin that both symbols exist (a missing gid$Bool fails WASM validation).
        val = self._run_mod("""\
import genmod;
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = gid(true);
  gid(41) + 1
}
""", [mod], fn="main")
        assert val == 42

    def test_imported_generic_verify_and_run_agree(self) -> None:
        """The importer's ``verify`` and ``run`` agree on the imported generic's
        contract — no false Tier-1.  ``bad_id`` has a real ``ensures`` and the
        emitted clone carries the runtime postcondition guard.
        """
        import tempfile
        from pathlib import Path

        from vera.verifier import verify

        mod = self._resolved(("lib",), self.GEN_MODULE.replace("gid", "bad_id"))
        main_src = """\
import lib;
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ bad_id(42) }
"""
        assert self._run_mod(main_src, [mod], fn="main") == 42
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(main_src)
            f.flush()
            path = f.name
        try:
            prog = transform(parse_file(path))
            vres = verify(prog, main_src, resolved_modules=[mod])
            errors = [d for d in vres.diagnostics if d.severity == "error"]
            assert errors == [], [e.description for e in errors]
        finally:
            Path(path).unlink(missing_ok=True)

    def test_shadowed_imported_generic_qualified_call_no_false_tier1(
        self,
    ) -> None:
        """`#814` asymmetric variant: an imported generic (`gen`, identity)
        shadowed by a LOCAL non-generic `gen` (adds 100) AND module-qualified
        called must run the MODULE generic — matching what verify proves — not
        the local shadow.

        Pre-fix: verify proved ``m::gen(5) == 5`` via the module's contract while
        codegen fell back to the local shadow (`5 + 100 == 105`) — a false
        Tier-1 (verify clean, runtime violates).  The local's ``+ 100`` (not
        identity) makes the shadow's wrong answer (105) impossible to mistake for
        the module generic's (5), and a bare ``gen(5)`` must STILL reach the
        local shadow (§8.5.2), proving the qualified fix didn't hijack the bare
        namespace.
        """
        import tempfile
        from pathlib import Path

        from vera.verifier import verify

        gen_mod = """\
public forall<T> fn gen(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ @T.0 }
"""
        mod = self._resolved(("g",), gen_mod)
        main_src = """\
import g;
private fn gen(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 100 }
public fn qual_probe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ g::gen(5) }
public fn bare_probe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ gen(5) }
"""
        # Codegen: qualified reaches the module identity generic (5); bare stays
        # on the local shadow (105).
        assert self._run_mod(main_src, [mod], fn="qual_probe") == 5
        assert self._run_mod(main_src, [mod], fn="bare_probe") == 105

        # Verifier: proving `qual_probe`'s value through the module generic's
        # contract must be consistent with the run (no false Tier-1).
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(main_src)
            f.flush()
            path = f.name
        try:
            prog = transform(parse_file(path))
            vres = verify(prog, main_src, resolved_modules=[mod])
            errors = [d for d in vres.diagnostics if d.severity == "error"]
            assert errors == [], [e.description for e in errors]
        finally:
            Path(path).unlink(missing_ok=True)

    def test_shadowed_generic_calling_another_generic_transitive(self) -> None:
        """`#774` review (CR 3518737014): a SHADOWED imported generic whose body
        calls ANOTHER generic must get that transitive clone emitted too.

        `outer<T>` (identity via `inner(@T.0)`) is shadowed by a local
        non-generic `outer` (adds 100); `inner<T>` is an unshadowed sibling.
        `g::outer(7)` must run the module generic — `inner(7) == 7` — so the
        transitive `inner$Int` clone MUST be emitted.  Pre-fix the shadowed path
        appended `g::outer$Int` without scanning its body, so `inner$Int` was
        never emitted and the run failed WASM validation at
        `unknown func $g::outer$Int` (the clone body couldn't compile its
        missing `inner$Int` call).  A bare `outer(7)` must still hit the local
        shadow (107), proving the qualified transitive fix didn't leak.
        """
        gen_mod = """\
module g;
public forall<T> fn inner(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ @T.0 }
public forall<T> fn outer(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ inner(@T.0) }
"""
        mod = self._resolved(("g",), gen_mod)
        main_src = """\
import g;
private fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 100 }
public fn qual_probe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ g::outer(7) }
public fn bare_probe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ outer(7) }
"""
        assert self._run_mod(main_src, [mod], fn="qual_probe") == 7
        assert self._run_mod(main_src, [mod], fn="bare_probe") == 107

    def test_shadowed_generic_deep_transitive_chain(self) -> None:
        """A three-deep transitive chain through a shadowed generic
        (`outer` → `inner` → `helper`, all identity) resolves end-to-end: the
        closure must chase past the first transitive hop.  `g::outer(9) == 9`.
        """
        gen_mod = """\
module g;
public forall<T> fn helper(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ @T.0 }
public forall<T> fn inner(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ helper(@T.0) }
public forall<T> fn outer(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ inner(@T.0) }
"""
        mod = self._resolved(("g",), gen_mod)
        main_src = """\
import g;
private fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 100 }
public fn probe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ g::outer(9) }
"""
        assert self._run_mod(main_src, [mod], fn="probe") == 9

    def test_shadowed_generic_calling_shadowed_sibling(self) -> None:
        """When a shadowed generic's body calls a SAME-MODULE shadowed sibling,
        the intra-module call must reach the sibling's `<path>::…` clone, not the
        importer's local shadow of that name.

        Both `outer` and `inner` are shadowed by locals (adding 100 / 200).
        `g::outer(9)` runs the module `outer`, whose body calls the module
        `inner` (identity) — so the result is `9`, NOT `9 + 200 == 209` (the
        local `inner` shadow).  Pre-fix the clone body's bare `inner` resolved to
        the local shadow and the postcondition `result == arg` failed at run.
        """
        gen_mod = """\
module g;
public forall<T> fn inner(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ @T.0 }
public forall<T> fn outer(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ inner(@T.0) }
"""
        mod = self._resolved(("g",), gen_mod)
        main_src = """\
import g;
private fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 100 }
private fn inner(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 200 }
public fn probe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ g::outer(9) }
"""
        assert self._run_mod(main_src, [mod], fn="probe") == 9

    def test_shadowed_generic_pair_result_in_statement_position(self) -> None:
        """`#774` review (CR 3518737022): the statement-position result-shape
        predicates (`_is_void_expr` / `_is_pair_result_expr`) must resolve a
        shadowed-generic `m::gen(...)` to its per-instantiation clone, the same
        way the desugar does.

        `mkstr<T>` (shadowed) returns `@String` (an i32_pair — two stack values);
        its LOCAL shadow returns `@Int` (one).  In statement position
        (`g::mkstr(5); 42`) the result must be dropped as a PAIR.  Pre-fix the
        predicate resolved the ModuleCall via `_module_qualified_targets` only —
        seeing the local `@Int` shadow — so it dropped one value, leaving one on
        the stack: a WASM `type mismatch: values remaining on stack` at run on a
        check-green program.  Runs to `42`.
        """
        gen_mod = """\
module g;
public forall<T> fn mkstr(@T -> @String)
  requires(true) ensures(true) effects(pure)
{ "hi" }
"""
        mod = self._resolved(("g",), gen_mod)
        main_src = """\
import g;
private fn mkstr(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
public fn probe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  g::mkstr(5);
  42
}
"""
        assert self._run_mod(main_src, [mod], fn="probe") == 42

    def test_shadowed_generic_scalar_result_with_pair_local_shadow(
        self,
    ) -> None:
        """The dual of the pair case: a shadowed generic returning a SCALAR whose
        local shadow returns a pair.  The predicate must resolve to the clone's
        scalar shape (drop ONE), not the local's pair (drop two) — else a value
        is under-dropped.  `g::f(5); 42` runs to `42`.
        """
        gen_mod = """\
module g;
public forall<T> fn f(@T -> @Int)
  requires(true) ensures(true) effects(pure)
{ 1 }
"""
        mod = self._resolved(("g",), gen_mod)
        main_src = """\
import g;
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ "x" }
public fn probe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  g::f(5);
  42
}
"""
        assert self._run_mod(main_src, [mod], fn="probe") == 42

    # -- #774 review (CR 3519156263): the imported-generic false Tier-1 --

    @pytest.mark.parametrize("local_shadow", [
        "",  # unshadowed imported generic
        (  # a same-named LOCAL GENERIC shadows it (the unhandled twin)
            "private forall<T> fn tag(@T -> @Int)\n"
            "  requires(true) ensures(@Int.result == 0) effects(pure)\n"
            "{ 0 }\n\n"
        ),
        (  # a same-named LOCAL NON-generic shadows it (#814 family)
            "private fn tag(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 100 }\n\n"
        ),
    ], ids=["unshadowed", "generic_shadow", "nongeneric_shadow"])
    def test_imported_generic_with_lying_contract_is_caught_at_verify(
        self, local_shadow: str,
    ) -> None:
        """A cross-module generic whose clone RUNS in the importer must have its
        MODULE contract verified by the importer — else a LYING module contract
        is a false Tier-1 (verify clean, run violates the clone's postcondition).

        The module `tag<T>` returns `0` but claims `ensures(@Int.result == 9)`.
        The module itself never instantiates `tag`, so it only Tier-3s the
        uninstantiated generic — the importer is the only site that instantiates
        it.  Pre-fix, verify passed clean (`ok: True`, all Tier-1) while `vera
        run` trapped the clone's postcondition; the fix verifies the imported
        generic's clone at the importer's instantiation, turning it into an
        honest E500 at verify time.  Covers all three shadow shapes: unshadowed,
        a same-named local GENERIC shadow (the unhandled twin that absorbed the
        module instance into the local key), and a local non-generic shadow.
        """
        from vera.verifier import verify

        mod = self._resolved(("g",), (
            "module g;\n"
            "public forall<T> fn tag(@T -> @Int)\n"
            "  requires(true) ensures(@Int.result == 9) effects(pure)\n"
            "{ 0 }\n"
        ))
        call = "tag(5)" if local_shadow == "" else "g::tag(5)"
        main_src = (
            "import g;\n\n"
            f"{local_shadow}"
            "public fn probe(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            f"{{ {call} }}\n"
        )
        import tempfile
        from pathlib import Path
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(main_src)
            f.flush()
            path = f.name
        try:
            prog = transform(parse_file(path))
            vres = verify(prog, main_src, resolved_modules=[mod])
            errors = [d for d in vres.diagnostics if d.severity == "error"]
            assert any(e.error_code == "E500" for e in errors), (
                f"the lying module generic's clone must be caught at verify "
                f"(E500), got diagnostics {[e.error_code for e in errors]}"
            )
        finally:
            Path(path).unlink(missing_ok=True)

    def test_imported_generic_honest_contract_verifies_and_runs(self) -> None:
        """The dual of the lying-contract test: an HONEST imported generic
        (`tag` returns `0`, `ensures(@Int.result == 0)`) with a local generic
        shadow verifies clean AND runs — the fix must not over-reject the
        common honest case.  `g::tag(5)` runs the module (0); a bare `tag(5)`
        runs the local generic shadow (which here also returns 0 but with a
        distinct contract, verified independently).
        """
        from vera.verifier import verify

        mod = self._resolved(("g",), (
            "module g;\n"
            "public forall<T> fn tag(@T -> @Int)\n"
            "  requires(true) ensures(@Int.result == 0) effects(pure)\n"
            "{ 0 }\n"
        ))
        main_src = (
            "import g;\n\n"
            "private forall<T> fn tag(@T -> @Int)\n"
            "  requires(true) ensures(@Int.result == 7) effects(pure)\n"
            "{ 7 }\n\n"
            "public fn qual(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ g::tag(5) }\n"
            "public fn bare(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ tag(5) }\n"
        )
        # Module tag → 0; local generic tag → 7. Distinct clones, both honest.
        assert self._run_mod(main_src, [mod], fn="qual") == 0
        assert self._run_mod(main_src, [mod], fn="bare") == 7
        import tempfile
        from pathlib import Path
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(main_src)
            f.flush()
            path = f.name
        try:
            prog = transform(parse_file(path))
            vres = verify(prog, main_src, resolved_modules=[mod])
            errors = [d for d in vres.diagnostics if d.severity == "error"]
            assert errors == [], [e.description for e in errors]
        finally:
            Path(path).unlink(missing_ok=True)

    def test_unshadowed_generic_calling_shadowed_sibling(self) -> None:
        """`#774` review (CR 3519063445): the REVERSE of the shadowed→normal
        transitive case — an UNSHADOWED (normal) local generic whose body
        qualified-calls a SHADOWED generic must emit that shadowed clone.

        `caller<T>` (local, unshadowed) calls `g::gen(@T.0)` where `gen` is
        shadowed by a local non-generic (+100).  `caller(5)` → its clone
        `caller$Int` calls `g::gen` → the MODULE generic (identity) → `5`.
        Pre-fix the shadowed emission seeded only from `program.declarations`
        non-generic bodies, never from the emitted `caller$Int` clone, so
        `g::gen$Int` was missing → `unknown func $caller$Int` at run.  A
        lying module `gen` reached this way is caught at verify (E500), and
        both sides discover `g::gen<Int>` (the differential pins it).
        """
        from vera.verifier import verify

        mod = self._resolved(("g",), (
            "module g;\n"
            "public forall<T> fn gen(@T -> @T)\n"
            "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
            "{ @T.0 }\n"
        ))
        main_src = (
            "import g;\n\n"
            "private fn gen(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 + 100 }\n\n"
            "private forall<T> fn caller(@T -> @T)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ g::gen(@T.0) }\n\n"
            "public fn probe(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ caller(5) }\n"
        )
        assert self._run_mod(main_src, [mod], fn="probe") == 5
        import tempfile
        from pathlib import Path
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(main_src)
            f.flush()
            path = f.name
        try:
            prog = transform(parse_file(path))
            vres = verify(prog, main_src, resolved_modules=[mod])
            errors = [d for d in vres.diagnostics if d.severity == "error"]
            assert errors == [], [e.description for e in errors]
        finally:
            Path(path).unlink(missing_ok=True)

    def test_imported_generic_via_pipe_executes(self) -> None:
        """`#913`: an imported generic invoked through the `|>` pipe
        (`42 |> genmod::gid()`) is discovered and monomorphized.

        The pipe RHS is an ``ast.ModuleCall`` — the ``ModuleCall`` arm of the
        #913 pipe-discovery branch (`Monomorphizer._collect_calls`) must
        reconstruct the pipe-desugared argument list `(42,)` so `gid$Int` is
        emitted; pre-#913 the bare RHS `ModuleCall` (empty args) bound nothing
        and no clone existed, dropping the caller.  42 cannot coincide with the
        phantom-var Bool/i32 default, so a discovery miss can't masquerade.
        """
        mod = self._resolved(("genmod",), self.GEN_MODULE)
        val = self._run_mod("""\
import genmod;
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 |> genmod::gid() }
""", [mod], fn="main")
        assert val == 42


# =====================================================================
# #661 — cross-module name collision in template-warning suppression
# =====================================================================


class TestCrossModuleNameCollision661:
    """`#661` — pin the invariant that bare-name keying in
    `compile_program`'s template-warning suppression set
    (`compiled_mono_bases` / `forall_decl_names`) cannot
    cross-suppress between modules.

    The original concern: if two modules both declare
    `forall<T> fn shared_name(...)`, the suppression set keys on
    the bare base name `"shared_name"` and could mask a real
    diagnostic on the imported version when only the local one
    compiles.  Investigation in #661 showed the scenario is not
    reachable today because:

    1. Pass 2.5 in `compile_program` skips imported FnDecls whose
       names are already in `fn_visibility` (= local
       declarations).  An imported forall with the same name as a
       local one is dropped before its template warning could be
       emitted.
    2. `forall_decl_names` is built from `program.declarations`
       only, never from imports.  Only local forall decls are
       eligible for suppression.

    So at most one template warning per base name lands in
    `self.diagnostics`, and bare-name matching in the suppression
    filter cannot cross-suppress.  This test compiles a
    name-shadowing fixture to pin both invariants.  If Pass 2.5's
    dedup ever loosens, or the mono pipeline starts carrying
    module attribution, this test will flag the change.
    """

    _resolved = staticmethod(resolved_module)

    def test_cross_module_forall_name_shadow_compiles_and_runs(
        self,
    ) -> None:
        """Two modules with the same `forall<T> fn shared_name`
        compile and run correctly — the local one shadows the
        import (no [E608] collision, no missing-function trap)."""
        a_source = """\
public forall<T> fn shared_name(@T -> @T)
  requires(true) ensures(true) effects(pure)
{
  @T.0
}
"""
        main_source = """\
import a;

private forall<T> fn shared_name(@T -> @T)
  requires(true) ensures(true) effects(pure)
{
  @T.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  shared_name(42)
}
"""
        mod = self._resolved(("a",), a_source)
        import tempfile
        from pathlib import Path
        # Explicit utf-8 + try/finally cleanup (CR-2 on PR #664).
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False,
            encoding="utf-8",
        ) as f:
            f.write(main_source)
            f.flush()
            path = f.name
        try:
            tree = parse_file(path)
            ast_program = transform(tree)
            result = compile(
                ast_program, source=main_source, file=path,
                resolved_modules=[mod],
            )
            errors = [d for d in result.diagnostics if d.severity == "error"]
            assert not errors, (
                f"Cross-module forall shadow should not produce errors; "
                f"got: {[e.description for e in errors]}"
            )
            exec_result = execute(result, fn_name="main")
            assert exec_result.value == 42
        finally:
            Path(path).unlink(missing_ok=True)

    def test_suppression_does_not_cross_modules(self) -> None:
        """Compile the shadow fixture and verify the suppression
        filter doesn't accidentally drop a diagnostic that would
        belong to an unrelated imported function."""
        # Same fixture as the test above, but check the warnings
        # surface: the only template warnings should be on the
        # prelude generics that aren't called here (which is the
        # pre-existing behaviour); there should be no warning
        # about `shared_name` since the local mono clone compiles
        # and suppresses correctly.
        a_source = """\
public forall<T> fn shared_name(@T -> @T)
  requires(true) ensures(true) effects(pure)
{
  @T.0
}
"""
        main_source = """\
import a;

private forall<T> fn shared_name(@T -> @T)
  requires(true) ensures(true) effects(pure)
{
  @T.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  shared_name(42)
}
"""
        mod = self._resolved(("a",), a_source)
        import tempfile
        from pathlib import Path
        # Explicit utf-8 + try/finally cleanup (CR-2 on PR #664).
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False,
            encoding="utf-8",
        ) as f:
            f.write(main_source)
            f.flush()
            path = f.name
        try:
            tree = parse_file(path)
            ast_program = transform(tree)
            result = compile(
                ast_program, source=main_source, file=path,
                resolved_modules=[mod],
            )
            # Guard against silent pass-on-failure: if compile errored,
            # the warning filter below would be empty and the assertion
            # would incorrectly succeed.  Pin compilation success first.
            errors = [d for d in result.diagnostics if d.severity == "error"]
            assert result.ok, (
                f"Compilation failed; suppression-filter assertion below "
                f"would silently pass on empty warning list.  Errors: "
                f"{[e.description for e in errors]}"
            )
            warnings = [d for d in result.diagnostics if d.severity == "warning"]
            # No template warning on `shared_name` — its mono clone
            # compiled, so the suppression correctly filtered it.
            shared_warnings = [
                d for d in warnings
                if d.error_code in {"E602", "E604", "E605"}
                and d.description.startswith("Function 'shared_name' ")
            ]
            assert not shared_warnings, (
                f"Expected no [E602]/[E604]/[E605] warnings about "
                f"`shared_name` (mono clone compiled, suppression "
                f"should fire); got: "
                f"{[d.description for d in shared_warnings]}"
            )
        finally:
            Path(path).unlink(missing_ok=True)


# =====================================================================
# Name collision detection (#110)
# =====================================================================


class TestNameCollisionDetection:
    """Name collisions across imported modules produce diagnostics."""

    _resolved = staticmethod(resolved_module)

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

    def test_private_helpers_of_one_name_each_run_their_own(self) -> None:
        """Two modules' private ``helper`` each keep their own symbol (#1498).

        Neither owns the entry's bare name, so each is emitted as
        ``<path>::helper`` and each module's bare call reaches its own.
        This was E608, although spec §11.16 says two declarations neither of
        which owns the bare name cannot overwrite each other.  The two bodies
        differ, so a call bound to the other module's helper shows.
        """
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
{ @Int.0 * 10 }
""")
        result = self._compile_mod("""\
import mod_a(double);
import mod_b(triple);
public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0) + triple(@Int.0) }
""", [mod_a, mod_b])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == []
        # double(2) = 2 + 2 via mod_a's helper; triple(2) = 3 * 20 via mod_b's.
        assert execute(result, fn_name="main", args=[2]).value == 4 + 60

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


class TestCrossModuleFusedAwait841:
    """#841: an await of a cross-module call returning
    Future<Result<String, String>> must get the fused-handle runtime
    check.  Pre-fix, ``compute_future_ret_fns`` scanned only the local
    program (missing imported fns for the FnCall arm) and
    ``await_needs_check`` had no ModuleCall arm — so the await lowered
    to identity, the kind-4 wrapper flowed into the match's
    unconditional last arm, and the future was silently never awaited
    (PR #842 review, critical finding)."""

    FETCHER_MODULE = """\
public fn grab(@String -> @Future<Result<String, String>>)
  requires(true) ensures(true) effects(<Http, Async>)
{ async(Http.get(@String.0)) }
"""

    _MAIN_TEMPLATE = """\
import fetcher(grab);

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{{
  let @Result<String, String> = await({call});
  match @Result<String, String>.0 {{
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }}
}}
"""

    def _run_await_of(self, call: str) -> None:
        fetcher = TestCrossModuleCodegen._resolved(
            ("fetcher",), self.FETCHER_MODULE,
        )
        source = self._MAIN_TEMPLATE.format(call=call)
        result = TestCrossModuleCodegen._compile_mod(source, [fetcher])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, [e.description for e in errors]
        assert '(import "vera" "async_await"' in result.wat, (
            "await of a cross-module future must import async_await")
        exec_result = execute(result)
        assert exec_result.value == 1, (
            "the awaited Err must carry the real fetch outcome — a raw "
            "wrapper smuggled into the match reads a zero-length string "
            "and returns 0")

    def test_await_of_unqualified_imported_call(self) -> None:
        """`await(grab(...))` — FnCall arm via the cross-module
        return-type registry."""
        self._run_await_of('grab("ftp://blocked.invalid/x")')

    def test_await_of_qualified_module_call(self) -> None:
        """`await(fetcher::grab(...))` — the ModuleCall arm."""
        self._run_await_of('fetcher::grab("ftp://blocked.invalid/x")')

    def test_qualified_await_not_confused_by_colliding_local(self) -> None:
        """PR #842 review round 2: `await(fetcher::grab(...))` classifies
        by the RESOLVED module target, not the bare name — a local
        `grab` returning a different Future shape (here Future<Int>)
        must not make the qualified await lower to identity (bare-name
        registry follows local-shadows-import) or vice versa."""
        fetcher = TestCrossModuleCodegen._resolved(
            ("fetcher",), self.FETCHER_MODULE,
        )
        source = """\
import fetcher(grab);

private fn grab(@Int -> @Future<Int>)
  requires(true) ensures(true) effects(<Async>)
{ async(@Int.0 + 1) }

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Result<String, String> = await(fetcher::grab("ftp://collide.invalid/x"));
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }
}
"""
        result = TestCrossModuleCodegen._compile_mod(source, [fetcher])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, [e.description for e in errors]
        assert '(import "vera" "async_await"' in result.wat
        exec_result = execute(result)
        assert exec_result.value == 1


class TestIndirectClosureFusedAwait843:
    """#843: an inline ``await`` of an INDIRECTLY-called closure (an
    ``apply_fn`` on a fn-typed slot or an inline ``AnonFn``) whose declared
    return is ``Future<Result<String, String>>`` must get the fused-handle
    runtime check.  Pre-fix, ``await_needs_check`` had no ``apply_fn`` arm —
    the await lowered to identity, the kind-4 fused wrapper flowed into the
    match's unconditional last arm, the ``Err`` payload came out as a
    zero-length string, and the request outcome was silently discarded (the
    #842 failure shape, one call-indirection further out).

    The ceiling classifies the shape correctly by consulting the closure's
    declared return type (via the type-alias / AnonFn signature), so the
    program runs correctly rather than merely failing loudly."""

    # A fn-typed slot whose return is the fused future type.
    _FETCHER_ALIAS = (
        "type Fetcher = fn(String -> Future<Result<String, String>>) "
        "effects(<Http, Async>);"
    )

    _SLOT_SOURCE = (
        _FETCHER_ALIAS
        + """

private fn run_fetch(@Fetcher, @String -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Result<String, String> = await(apply_fn(@Fetcher.0, @String.0));
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }
}

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  run_fetch(
    fn(@String -> @Future<Result<String, String>>) effects(<Http, Async>) {
      async(Http.get(@String.0))
    },
    "ftp://blocked.invalid/x"
  )
}
"""
    )

    # The inline-AnonFn form of the same indirect await.
    _ANON_SOURCE = (
        _FETCHER_ALIAS
        + """

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Result<String, String> = await(apply_fn(
    fn(@String -> @Future<Result<String, String>>) effects(<Http, Async>) {
      async(Http.get(@String.0))
    },
    "ftp://blocked.invalid/x"
  ));
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }
}
"""
    )

    # A GENERIC fn-type alias instantiated to the fused future type at
    # the slot (PR #868 panel, critical): the alias's raw return is the
    # bare type param `T`, so classification must substitute the slot's
    # bound type args — exactly as `_infer_apply_fn_return_type` does
    # when it builds the (valid!) call_indirect signature.  Without the
    # substitution the two consultors diverge: no E616, no WASM trap,
    # identity await, silent wrong value — check+verify+run all green,
    # returns 0 where the non-generic equivalent returns 1, and the WAT
    # has zero `async_await` references instead of the import + call.
    _GENERIC_ALIAS_SOURCE = """\
type Producer<T> = fn(String -> T) effects(<Http, Async>);

private fn run_fetch(@Producer<Future<Result<String, String>>>, @String -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Result<String, String> = await(apply_fn(@Producer<Future<Result<String, String>>>.0, @String.0));
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }
}

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  run_fetch(
    fn(@String -> @Future<Result<String, String>>) effects(<Http, Async>) {
      async(Http.get(@String.0))
    },
    "ftp://blocked.invalid/x"
  )
}
"""

    # Control: the let-bind workaround (bind to a @Future slot before
    # awaiting) has always classified via the slot arm.
    _WORKAROUND_SOURCE = (
        _FETCHER_ALIAS
        + """

private fn run_fetch(@Fetcher, @String -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Future<Result<String, String>> = apply_fn(@Fetcher.0, @String.0);
  let @Result<String, String> = await(@Future<Result<String, String>>.0);
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }
}

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  run_fetch(
    fn(@String -> @Future<Result<String, String>>) effects(<Http, Async>) {
      async(Http.get(@String.0))
    },
    "ftp://blocked.invalid/x"
  )
}
"""
    )

    def _assert_awaited_correctly(self, source: str) -> None:
        result = _compile_ok(source)
        assert '(import "vera" "async_await"' in result.wat, (
            "await of an indirect closure future must import async_await — "
            "otherwise the fused wrapper is smuggled past an identity await")
        exec_result = execute(result)
        assert exec_result.value == 1, (
            "the awaited Err must carry the real fetch outcome — a raw "
            "wrapper read as the ADT yields a zero-length string and "
            "returns 0, silently discarding the request outcome (#843)")

    def test_await_of_apply_fn_slot(self) -> None:
        """`await(apply_fn(@Fetcher.0, url))` — the fn-typed-slot arm."""
        self._assert_awaited_correctly(self._SLOT_SOURCE)

    def test_await_of_apply_fn_anon(self) -> None:
        """`await(apply_fn(fn(...){...}, url))` — the inline-AnonFn arm."""
        self._assert_awaited_correctly(self._ANON_SOURCE)

    def test_let_bind_workaround_still_correct(self) -> None:
        """Control: the documented let-bind workaround is unaffected."""
        self._assert_awaited_correctly(self._WORKAROUND_SOURCE)

    def test_unresolvable_closure_return_fails_loud(self) -> None:
        """FLOOR: an ``apply_fn`` whose closure comes from a nested
        ``FnCall`` — a shape whose declared return type is not statically
        resolvable — must fail LOUDLY ([E616], function skipped) rather
        than silently mis-lower the await to identity.  This is the
        soundness backstop: the classification arm returns ``False`` for
        this shape, but the ``apply_fn`` translation already rejects it,
        so a fused wrapper can never reach an identity await."""
        source = (
            self._FETCHER_ALIAS
            + """

private fn make_fetcher(@Unit -> @Fetcher)
  requires(true) ensures(true) effects(<Http, Async>)
{
  fn(@String -> @Future<Result<String, String>>) effects(<Http, Async>) {
    async(Http.get(@String.0))
  }
}

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Result<String, String> = await(apply_fn(make_fetcher(()), "ftp://blocked.invalid/x"));
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }
}
"""
        )
        result = _compile(source)
        codes = {d.error_code for d in result.diagnostics}
        assert "E616" in codes, (
            "the unresolvable-closure apply_fn must be rejected loudly by "
            "[E616], not silently identity-lowered")
        # main is dropped, so the fused wrapper is never read as an ADT —
        # no silent zero-length-Err wrong value escapes.
        assert "$main" not in result.wat

    def test_await_of_apply_fn_generic_alias(self) -> None:
        """`await(apply_fn(@Producer<Future<Result<String, String>>>.0,
        url))` — a GENERIC alias instantiated to the fused type must
        classify via type-arg substitution (PR #868 panel, critical).
        WAT-level discriminator pinned network-free: pre-fix the WAT has
        zero `async_await` references (identity await); post-fix it has
        the import and the tag-probe call."""
        result = _compile_ok(self._GENERIC_ALIAS_SOURCE)
        assert '(import "vera" "async_await"' in result.wat, (
            "generic-alias apply_fn await must import async_await — "
            "an unsubstituted bare `T` return classifies as None while "
            "_infer_apply_fn_return_type substitutes and builds a VALID "
            "call_indirect signature: no E616, no trap, silent wrong value")
        assert "call $vera.async_await" in result.wat, (
            "the fused-handle tag probe must be emitted at the await site")
        exec_result = execute(result)
        assert exec_result.value == 1, (
            "the awaited Err must carry the real fetch outcome — identity "
            "lowering reads the fused wrapper as the ADT and returns 0")

    # An alias-of-alias fn-typed slot (`type Fetcher = InnerFetcher;`)
    # where `InnerFetcher` is the fused future fn type — the #867
    # transitive-alias case.  Pre-#867 both consultors resolved only one
    # alias hop: the await classified as unresolvable (identity lowering
    # smuggled the fused wrapper past the await) AND
    # `_infer_apply_fn_return_type` fell to its `i64` default while the
    # closure returns an i32 fused pointer, so the call_indirect signature
    # mismatched and trapped at WASM validation.  Post-#867 the shared
    # transitive resolver follows the chain to the terminal FnType in BOTH
    # consultors, so the program classifies and runs correctly.
    _NESTED_ALIAS_SLOT_SOURCE = """\
type InnerFetcher = fn(String -> Future<Result<String, String>>) effects(<Http, Async>);
type Fetcher = InnerFetcher;

private fn run_fetch(@Fetcher, @String -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Result<String, String> = await(apply_fn(@Fetcher.0, @String.0));
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }
}

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  run_fetch(
    fn(@String -> @Future<Result<String, String>>) effects(<Http, Async>) {
      async(Http.get(@String.0))
    },
    "ftp://blocked.invalid/x"
  )
}
"""

    # A THREE-hop chain (`Fetcher = B = A = fn(...)`) — the transitive
    # resolver must follow depth-N, not just depth-2.  A single-level
    # unwrap resolves `Fetcher` to `B` (still a NamedType, not a FnType)
    # and bails; a two-level unwrap would resolve to `A` and still bail.
    _THREE_HOP_ALIAS_SLOT_SOURCE = """\
type A = fn(String -> Future<Result<String, String>>) effects(<Http, Async>);
type B = A;
type Fetcher = B;

private fn run_fetch(@Fetcher, @String -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  let @Result<String, String> = await(apply_fn(@Fetcher.0, @String.0));
  match @Result<String, String>.0 {
    Ok(@String) -> false,
    Err(@String) -> string_contains(@String.0, "refusing non-HTTP(S)")
  }
}

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(<Http, Async>)
{
  run_fetch(
    fn(@String -> @Future<Result<String, String>>) effects(<Http, Async>) {
      async(Http.get(@String.0))
    },
    "ftp://blocked.invalid/x"
  )
}
"""

    def test_nested_alias_slot_awaited_correctly(self) -> None:
        """#867 (two-hop): `type Fetcher = InnerFetcher;` where
        `InnerFetcher` is the fused future fn type — the await must import
        `async_await` and deliver the real fetch outcome.  Flipped from the
        pre-#867 `_still_fails_loud` pin once the shared transitive resolver
        landed in both consultors."""
        self._assert_awaited_correctly(self._NESTED_ALIAS_SLOT_SOURCE)

    def test_three_hop_alias_slot_awaited_correctly(self) -> None:
        """#867 (three-hop): `Fetcher = B = A = fn(...)` — the transitive
        resolver must follow the chain to depth-N, not just one or two
        hops."""
        self._assert_awaited_correctly(self._THREE_HOP_ALIAS_SLOT_SOURCE)


class TestResolveFnTypeAliasCycleGuard867:
    """#867: the shared transitive resolver ``resolve_fn_type_alias`` must
    TERMINATE on a malformed cyclic alias chain, returning ``None`` (the
    caller then falls to its loud backstop) rather than spinning forever.

    Circular aliases are rejected upstream by the type checker
    (``[E132]``, #648), so a cycle only reaches codegen through malformed
    input, but the resolver — reached before any such check on a raw
    ``type_aliases`` map — must be self-guarding.  A watchdog (SIGALRM)
    proves termination: a resolver without the ``seen`` guard hangs and
    the alarm fires."""

    @staticmethod
    def _resolve_with_watchdog(
        te: ast.NamedType,
        aliases: dict[str, ast.TypeExpr],
    ) -> ast.FnType | None:
        import signal

        if not hasattr(signal, "SIGALRM"):
            pytest.skip("SIGALRM unavailable on this platform")

        def _timeout(_sig: int, _frm: object) -> None:
            raise TimeoutError("resolve_fn_type_alias did not terminate")

        old = signal.signal(signal.SIGALRM, _timeout)
        signal.alarm(5)
        try:
            return resolve_fn_type_alias(te, aliases, {})
        finally:
            signal.alarm(0)
            signal.signal(signal.SIGALRM, old)

    def test_two_node_cycle_terminates_none(self) -> None:
        """`type A = B; type B = A;` — resolver returns None, no hang."""
        aliases: dict[str, ast.TypeExpr] = {
            "A": ast.NamedType(name="B", type_args=None),
            "B": ast.NamedType(name="A", type_args=None),
        }
        result = self._resolve_with_watchdog(
            ast.NamedType(name="A", type_args=None), aliases)
        assert result is None

    def test_self_cycle_terminates_none(self) -> None:
        """`type A = A;` — resolver returns None, no hang."""
        aliases: dict[str, ast.TypeExpr] = {
            "A": ast.NamedType(name="A", type_args=None),
        }
        result = self._resolve_with_watchdog(
            ast.NamedType(name="A", type_args=None), aliases)
        assert result is None

    def test_prefix_into_cycle_terminates_none(self) -> None:
        """`type X = A; type A = B; type B = A;` — X leads into an A<->B
        cycle that does not include X; resolver still terminates None."""
        aliases: dict[str, ast.TypeExpr] = {
            "X": ast.NamedType(name="A", type_args=None),
            "A": ast.NamedType(name="B", type_args=None),
            "B": ast.NamedType(name="A", type_args=None),
        }
        result = self._resolve_with_watchdog(
            ast.NamedType(name="X", type_args=None), aliases)
        assert result is None


class TestTransitiveModuleImport890:
    """#890: a transitive module import (``main`` imports ``mid``, ``mid``
    imports ``base``) must compile and run.

    Codegen compiles the DIRECTLY-imported module's bodies (Pass 2.5), but
    the importer's flat WASM module must ALSO include every module reachable
    through the import graph — otherwise ``mid``'s body (which calls
    ``base::wrap40``) is left with a dangling call and ``vera run`` fails at
    WAT validation with ``unknown func``.  The fix makes
    ``ModuleResolver.resolve_imports`` return the transitive closure of
    reachable modules (each tagged ``direct``), and the codegen /
    checker / verifier only inject the DIRECT imports into the importer's
    callable namespace (spec §8.6.4: transitive declarations are not visible
    to the original importer).

    These tests drive the REAL on-disk resolver end-to-end so the resolver's
    "return only direct imports" defect is exercised, not papered over by a
    hand-built module list.
    """

    @staticmethod
    def _compile_run_chain(
        tmp_path: Path,
        files: dict[str, str],
        fn: str = "main",
        args: list[int] | None = None,
    ) -> int:
        """Write ``files`` (rel path -> source), resolve ``main.vera`` with the
        real resolver, compile, execute, and return the integer result."""
        from vera.resolver import ModuleResolver

        main_file: Path | None = None
        for rel, content in files.items():
            p = tmp_path / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(content, encoding="utf-8")
            if rel == "main.vera":
                main_file = p
        assert main_file is not None, "files must include 'main.vera'"

        resolver = ModuleResolver(_root=tmp_path)
        tree = parse_file(str(main_file))
        prog = transform(tree)
        resolved = resolver.resolve_imports(prog, main_file)
        assert not resolver.errors, (
            f"resolution errors: {[e.description for e in resolver.errors]}"
        )
        result = compile(
            prog,
            source=main_file.read_text(encoding="utf-8"),
            file=str(main_file),
            resolved_modules=resolved,
        )
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, (
            f"compile errors: {[e.description for e in errors]}"
        )
        exec_result = execute(result, fn_name=fn, args=args)
        assert exec_result.value is not None, "Expected a return value"
        return exec_result.value

    BASE = """\
module base;
public fn wrap40(@Int -> @Int)
  requires(true) ensures(true) effects(pure) { @Int.0 + 40 }
"""

    MID = """\
module mid;
import base;
public fn via_mid(@Int -> @Int)
  requires(true) ensures(true) effects(pure) { wrap40(@Int.0) }
"""

    def test_transitive_chain_runs(self, tmp_path: Path) -> None:
        """main -> mid -> base: ``via_mid(2)`` returns 42.

        Pre-fix this failed at WAT validation with
        ``unknown func: failed to find name $via_mid`` because ``base`` was
        dropped from the resolved-module list, so ``mid``'s body could not be
        compiled with ``wrap40`` in scope.  42 is not a compiler default for
        any type, so a stray success can't masquerade as a pass.
        """
        val = self._compile_run_chain(
            tmp_path,
            {
                "base.vera": self.BASE,
                "mid.vera": self.MID,
                "main.vera": """\
import mid;
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure) { via_mid(2) }
""",
            },
        )
        assert val == 42

    def test_transitive_base_not_bare_visible_to_main(
        self, tmp_path: Path,
    ) -> None:
        """spec §8.6.4: ``base``'s ``wrap40`` is NOT bare-callable from
        ``main`` — only ``mid``'s public declarations are visible to the
        top-level importer.  A bare ``wrap40(...)`` in ``main`` must fail to
        compile even though ``base`` is now in the resolved-module closure."""
        from vera.resolver import ModuleResolver

        (tmp_path / "base.vera").write_text(self.BASE, encoding="utf-8")
        (tmp_path / "mid.vera").write_text(self.MID, encoding="utf-8")
        main_file: Path = tmp_path / "main.vera"
        main_file.write_text(
            """\
import mid;
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure) { wrap40(2) }
""",
            encoding="utf-8",
        )
        resolver = ModuleResolver(_root=tmp_path)
        tree = parse_file(str(main_file))
        prog = transform(tree)
        resolved = resolver.resolve_imports(prog, main_file)
        assert not resolver.errors
        result = compile(
            prog,
            source=main_file.read_text(encoding="utf-8"),
            file=str(main_file),
            resolved_modules=resolved,
        )
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, (
            "expected a cross-module error: base::wrap40 must not be "
            "bare-callable from main (spec §8.6.4)"
        )

    def test_diamond_transitive_runs(self, tmp_path: Path) -> None:
        """main -> {left, right} -> base (diamond): the shared transitive
        ``base`` is included once and both branches resolve.  ``main`` sums
        ``via_left(1)`` (wrap40(1)+1 = 42) and ``via_right(0)`` (wrap40(0) =
        40) → 82, guarding both the shared-module dedup and multi-branch
        reachability."""
        val = self._compile_run_chain(
            tmp_path,
            {
                "base.vera": self.BASE,
                "left.vera": """\
module left;
import base;
public fn via_left(@Int -> @Int)
  requires(true) ensures(true) effects(pure) { wrap40(@Int.0) + 1 }
""",
                "right.vera": """\
module right;
import base;
public fn via_right(@Int -> @Int)
  requires(true) ensures(true) effects(pure) { wrap40(@Int.0) }
""",
                "main.vera": """\
import left;
import right;
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ via_left(1) + via_right(0) }
""",
            },
        )
        assert val == 82


class TestModuleCallInConstructorField905(TestCrossModuleCodegen):
    """#905: a non-void cross-module call (``ModuleCall``) used *directly* as a
    constructor argument (a ``Tuple``/ADT field) must compile and run.

    This is the non-void sibling of #902 (which fixed only the ``Unit``-valued
    field case via ``_is_void_expr``).  Before the fix, ``_infer_expr_wasm_type``
    returned ``None`` for a ``ModuleCall`` argument, so
    ``_translate_constructor_call`` raised ``CodegenSkip``; the enclosing
    function was silently dropped and any call to it dangled at run with
    ``unknown func: failed to find name $mkt``.

    All programs here pass ``vera check`` (the checker resolves the module
    call's return type fine); the gap was purely codegen-time WASM-type
    inference at the constructor-arg site.
    """

    # A module exporting a NON-void @Int-returning function (magnitude) plus a
    # @Unit-returning one (log) so we can compose with the #902 Unit-field case.
    MAG_MODULE = """\
public fn magnitude(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }
"""

    def test_module_call_in_tuple_field_runs(self) -> None:
        """``Tuple(m::magnitude(@Int.0), 9)`` — the canonical #905 repro.

        Extracts the trailing (literal ``9``) field so the assertion is
        decoupled from the module-call value; the point is that the function
        compiles at all (before the fix it was dropped and ``mkt`` dangled).
        De Bruijn: ``@Int.0`` = LAST field (the ``9``), ``@Int.1`` = first.
        """
        mod = self._resolved(("m",), self.MAG_MODULE)
        val = self._run_mod("""\
import m(magnitude);
private fn mkt(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(m::magnitude(@Int.0), 9) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = mkt(-5); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 } }
""", [mod], fn="main")
        assert val == 9

    def test_module_call_in_tuple_field_value_correct(self) -> None:
        """Extract the FIRST field (the module-call result) itself: it must be
        the actual ``magnitude(-5) == 5``, not garbage — proves the field is laid
        out at the right offset with the right WASM type, not merely that the
        function compiles.  De Bruijn: ``@Int.1`` = first field (the module
        call)."""
        mod = self._resolved(("m",), self.MAG_MODULE)
        val = self._run_mod("""\
import m(magnitude);
private fn mkt(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(m::magnitude(@Int.0), 9) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = mkt(-5); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 } }
""", [mod], fn="main")
        assert val == 5  # magnitude(-5)

    def test_module_call_in_dotted_path_tuple_field_runs(self) -> None:
        """The dotted-path form ``vera.math::magnitude(...)`` (as in the issue
        repro) is the same ``ModuleCall`` AST node and must also work.  Extracts
        the module-call field (``@Int.1`` = first field)."""
        mod = self._resolved(("vera", "math"), self.MAG_MODULE)
        val = self._run_mod("""\
import vera.math(magnitude);
private fn mkt(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(vera.math::magnitude(@Int.0), 9) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = mkt(-5); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 } }
""", [mod], fn="main")
        assert val == 5

    def test_module_call_non_final_field_with_unit_field(self) -> None:
        """#905 composed with #902: a module-call field in NON-final position,
        mixed with a zero-size ``Unit`` field — ``Tuple(m::magnitude(-5), (), 7)``.

        The Unit field advances no offset, so extracting the trailing ``7``
        checks the module-call field's WASM type feeds correct offsets for the
        fields after it."""
        mod = self._resolved(("m",), self.MAG_MODULE)
        val = self._run_mod("""\
import m(magnitude);
private fn mkt(@Int -> @Tuple<Int, Unit, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(m::magnitude(@Int.0), (), 7) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Unit, Int> = mkt(-5); match @Tuple<Int, Unit, Int>.0 { Tuple(@Int, @Unit, @Int) -> @Int.0 } }
""", [mod], fn="main")
        assert val == 7  # trailing field extracted past the module-call + Unit

    def test_module_call_in_adt_constructor_field(self) -> None:
        """A user ADT (non-Tuple) constructor with a module-call field shares
        ``_translate_constructor_call``, so it must be fixed too."""
        mod = self._resolved(("m",), self.MAG_MODULE)
        val = self._run_mod("""\
import m(magnitude);
public data Boxed { Box(Int) }
private fn mk(@Int -> @Boxed)
  requires(true) ensures(true) effects(pure)
{ Box(m::magnitude(@Int.0)) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Boxed = mk(-8); match @Boxed.0 { Box(@Int) -> @Int.0 } }
""", [mod], fn="main")
        assert val == 8  # magnitude(-8)

    def test_module_call_in_array_literal_element(self) -> None:
        """#905 array-literal sibling: a ModuleCall as the FIRST element of an
        array literal reaches ``_infer_array_element_type`` → ``_infer_vera_type``,
        which also returned None for ModuleCall.  The symptom was quieter than
        the constructor crash — ``compile`` reported ``ok`` but the enclosing
        function was dropped from the exports (its array-let binding was
        skipped).  ``[m::magnitude(-5), 9]`` indexed at 0 must be
        ``magnitude(-5) == 5``."""
        mod = self._resolved(("m",), self.MAG_MODULE)
        val = self._run_mod("""\
import m(magnitude);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [m::magnitude(-5), 9]; @Array<Int>.0[0] }
""", [mod], fn="main")
        assert val == 5

    def test_module_call_in_array_literal_trailing_element(self) -> None:
        """The same array-literal, indexed at the trailing literal element (9),
        confirms the module-call element sized the array correctly."""
        mod = self._resolved(("m",), self.MAG_MODULE)
        val = self._run_mod("""\
import m(magnitude);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [m::magnitude(-5), 9]; @Array<Int>.0[1] }
""", [mod], fn="main")
        assert val == 9

    # -- Regressions: paths that already worked must be unaffected -----------

    def test_same_file_fncall_in_field_still_runs(self) -> None:
        """A SAME-FILE ``FnCall`` in a constructor field already worked (its
        return type is resolved); the fix must not disturb it.  Extracts the
        same-file-call field (``@Int.1`` = first field)."""
        val = _run("""\
private fn magnitude(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }
private fn mkt(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(magnitude(@Int.0), 9) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = mkt(-5); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 } }
""", fn="main")
        assert val == 5

    def test_plain_literal_field_still_runs(self) -> None:
        """A plain-literal constructor field must NOT take the new module-call
        path — guards against the fix over-firing.  De Bruijn: ``@Int.0`` = LAST
        field (the literal ``9``)."""
        val = _run("""\
private fn mkt(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(@Int.0, 9) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = mkt(4); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 } }
""", fn="main")
        assert val == 9


class TestUserShowHashInField908(TestCrossModuleCodegen):
    """#908: a user-defined function literally named ``show`` or ``hash`` used
    in a constructor field / array-literal element must be laid out at the WIDTH
    of ITS declared return type, not the ability-op width special-case.

    ``vera/wasm/inference.py`` name-special-cases the ability operations
    (``show`` → ``i32_pair`` / String, ``hash`` → ``i64`` / Int) by bare name in
    ``_infer_expr_wasm_type`` / ``_infer_fncall_wasm_type`` (WASM width) and
    ``_infer_fncall_vera_type`` (Vera-type-name).  The type checker rejects
    user redefinition of registry builtins (E151) but NOT the ability ops
    ``show``/``hash``, so a user helper named ``show`` (returning ``@Int``) or
    ``hash`` (returning ``@String``) was mis-sized: the constructor-field
    inference reported the ability-op width while ``_translate_call`` (gated on
    ``call.name not in self._known_fns``) correctly emitted a call to the USER
    function.  The two disagreed → an ``expected i32, found i64`` WASM
    translation error on a ``vera check``-green program.

    A GENUINE ability op (``show``/``hash`` on a value whose type derives
    ``Show``/``Hash``) has NO user-fn registry entry, so it still falls back to
    the special-case width — the load-bearing regression at the bottom of this
    class.
    """

    # A module exporting a user function named ``show`` that returns @Int
    # (NOT the String the ability op returns) — the mis-width trigger.
    SHOW_INT_MODULE = """\
public fn show(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 + 1 }
"""

    # -- User-fn show/hash mis-sizing (the bug) ------------------------------

    def test_module_user_show_in_tuple_field_runs(self) -> None:
        """``Tuple(m::show(@Int.0), 9)`` where ``m::show`` returns @Int (i64) —
        the canonical #908 repro.  Before the fix, the field was sized as the
        ability-op ``i32_pair`` while the emitted ``call $show`` returned i64.
        Extracts the trailing literal ``9`` (De Bruijn ``@Int.0`` = LAST)."""
        mod = self._resolved(("m",), self.SHOW_INT_MODULE)
        val = self._run_mod("""\
import m(show);
private fn mkt(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(m::show(@Int.0), 9) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = mkt(5); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 } }
""", [mod], fn="main")
        assert val == 9

    def test_module_user_show_in_tuple_field_value_correct(self) -> None:
        """Extract the module-call field itself (``@Int.1`` = FIRST field): it
        must be ``show(5) == 6`` (the user fn's ``@Int.0 + 1``), proving the
        field is laid out at the right offset with the i64 (not i32_pair)
        width."""
        mod = self._resolved(("m",), self.SHOW_INT_MODULE)
        val = self._run_mod("""\
import m(show);
private fn mkt(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(m::show(@Int.0), 9) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = mkt(5); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 } }
""", [mod], fn="main")
        assert val == 6  # user show(5) = 5 + 1

    def test_dotted_path_user_show_in_tuple_field_runs(self) -> None:
        """The dotted-path form ``vera.util::show(...)`` (the issue repro) is the
        same ``ModuleCall`` node and must also work."""
        mod = self._resolved(("vera", "util"), self.SHOW_INT_MODULE)
        val = self._run_mod("""\
import vera.util(show);
private fn mkt(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(vera.util::show(@Int.0), 9) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = mkt(5); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 } }
""", [mod], fn="main")
        assert val == 9

    def test_same_file_user_show_in_tuple_field_runs(self) -> None:
        """A SAME-FILE ``fn show(@Int -> @Int)`` used bare in a field
        (``Tuple(show(x), 9)``) hits the same bug via the same-file ``FnCall``
        path in ``_infer_expr_wasm_type``.  Extracts the trailing ``9``
        (De Bruijn ``@Int.0`` = LAST field)."""
        val = _run("""\
private fn show(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }
private fn mkt(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(show(@Int.0), 9) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = mkt(5); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 } }
""", fn="main")
        assert val == 9

    def test_same_file_user_hash_string_in_tuple_field_runs(self) -> None:
        """A user ``fn hash(@Int -> @String)`` returns a NON-Int type (i32_pair)
        — the opposite mis-width from ``show``.  The ability-op special-case
        would size the field as ``i64``; the user fn emits an ``i32_pair``.
        Extracts the trailing Int ``7`` (De Bruijn ``@Int.0`` = last field)."""
        val = _run("""\
private fn hash(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ "n" }
private fn mkt(@Int -> @Tuple<String, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(hash(@Int.0), 7) }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<String, Int> = mkt(5); match @Tuple<String, Int>.0 { Tuple(@String, @Int) -> @Int.0 } }
""", fn="main")
        assert val == 7

    def test_module_user_show_in_array_literal_element(self) -> None:
        """A user ``m::show`` (returns @Int) as the FIRST element of an array
        literal reaches ``_infer_array_element_type`` → ``_infer_vera_type`` →
        ``_infer_fncall_vera_type``, which name-special-cased ``show`` → String.
        ``[m::show(-5), 9]`` indexed at 1 (the literal) must be ``9``."""
        mod = self._resolved(("m",), self.SHOW_INT_MODULE)
        val = self._run_mod("""\
import m(show);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [m::show(5), 9]; @Array<Int>.0[1] }
""", [mod], fn="main")
        assert val == 9

    def test_same_file_user_show_in_array_literal_element(self) -> None:
        """The same-file ``fn show(@Int -> @Int)`` as an array-literal element.
        Indexed at 0 it must be the user ``show(5) == 6``."""
        val = _run("""\
private fn show(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [show(5), 9]; @Array<Int>.0[0] }
""", fn="main")
        assert val == 6

    # -- CRITICAL regression: genuine ability dispatch must still work -------

    def test_genuine_show_in_tuple_field_still_runs(self) -> None:
        """LOAD-BEARING: a GENUINE ability ``show(42)`` (no user fn; Int derives
        Show) in a constructor field must STILL be sized as the ability-op
        ``i32_pair`` (String).  ``Tuple(show(42), 9)`` indexed at the trailing
        Int ``9`` proves the field after the String is at the right offset."""
        val = _run("""\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<String, Int> = Tuple(show(42), 9); match @Tuple<String, Int>.0 { Tuple(@String, @Int) -> @Int.0 } }
""", fn="main")
        assert val == 9

    def test_genuine_hash_in_tuple_field_still_runs(self) -> None:
        """LOAD-BEARING: a GENUINE ability ``hash(42)`` (no user fn; Int derives
        Hash, identity) in a constructor field must STILL be sized as the
        ability-op ``i64`` (Int).  ``Tuple(hash(42), 9)`` indexed at the
        module-call field (``@Int.1`` = first) must be ``hash(42) == 42``."""
        val = _run("""\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = Tuple(hash(42), 9); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 } }
""", fn="main")
        assert val == 42

    def test_genuine_show_in_array_literal_element_still_runs(self) -> None:
        """LOAD-BEARING: a GENUINE ability ``hash(42)`` as an array-literal
        element must still size the array as ``Int`` (i64) so indexing returns
        the correct value.  ``[hash(42), 9]`` indexed at 0 must be ``42``."""
        val = _run("""\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [hash(42), 9]; @Array<Int>.0[0] }
""", fn="main")
        assert val == 42


class TestImportedNestedWhereEmission989(TestCrossModuleCodegen):
    """#989 (PR review, Edge A): an IMPORTED function's grandchild where-helper
    must be REGISTERED for Pass-2.5 emission, not just its direct children.

    ``_register_modules`` collected imported where-fns with a one-level loop
    (``for wfn in tld.decl.where_fns or ()``), so an imported ``libfn -> child
    -> grandchild`` chain registered ``libfn`` and ``child`` but never
    ``grandchild``.  The checker and verifier recurse into nested ``where``
    blocks, so ``grandchild`` is checked (E-clean) and verified (Tier-1 green)
    — but Pass 2.5 never emitted its body, and ``child``'s call to it dangled
    (``unknown func: $grandchild``) at WAT assembly on a check+verify-green
    program.  Mirrors the #978 local-path emission fix, one level up in the
    registration walk.
    """

    def test_imported_grandchild_where_fn_emitted(self) -> None:
        """The panel repro: lib ``libfn -> child -> grandchild``, imported and
        called as ``libfn(10)`` == 16 (``grandchild(11) == 11 + 5``).

        Pins the full pipeline: check-green, verify-green, compile-green, and
        run == 16.  Before the registration recursion, check + verify passed
        but compile failed with ``unknown func: $grandchild``.
        """
        import tempfile

        from vera.checker import typecheck
        from vera.verifier import verify

        lib_src = """\
public fn libfn(@Int -> @Int)
  requires(true) ensures(@Int.result == @Int.0 + 6) effects(pure)
{ child(@Int.0) }
where {
  fn child(@Int -> @Int)
    requires(true) ensures(@Int.result == @Int.0 + 6) effects(pure)
  { grandchild(@Int.0 + 1) }
  where {
    fn grandchild(@Int -> @Int)
      requires(true) ensures(@Int.result == @Int.0 + 5) effects(pure)
    { @Int.0 + 5 }
  }
}
"""
        main_src = """\
import lib(libfn);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ libfn(10) }
"""
        mod = self._resolved(("lib",), lib_src)

        # check-green + verify-green (the "silent" property: neither stage
        # rejects the program — only codegen dropped the grandchild body).
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as f:
            f.write(main_src)
            f.flush()
            path = f.name
        try:
            prog = transform(parse_file(path))
            check_diags = typecheck(prog, main_src, resolved_modules=[mod])
            check_errors = [d for d in check_diags if d.severity == "error"]
            assert check_errors == [], [e.description for e in check_errors]
            vres = verify(prog, main_src, resolved_modules=[mod])
            verrors = [d for d in vres.diagnostics if d.severity == "error"]
            assert verrors == [], [e.description for e in verrors]
        finally:
            Path(path).unlink(missing_ok=True)

        # compile-green + run == 16 (the flip: dangling $grandchild at head).
        assert self._run_mod(main_src, [mod], fn="main") == 16

    def test_imported_three_level_where_chain_runs(self) -> None:
        """A deeper imported chain: ``top -> a -> b -> c`` (three nested levels).

        ``top(5)`` → ``a(5)`` → ``b(6)`` → ``c(16)`` → ``16 + 100`` = 116.  The
        registration walk must reach ``c`` (a great-grandchild), not just ``a``
        and ``b``, or ``b``'s ``call $c`` dangles.
        """
        lib_src = """\
public fn top(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ a(@Int.0) }
where {
  fn a(@Int -> @Int) requires(true) ensures(true) effects(pure)
  { b(@Int.0 + 1) }
  where {
    fn b(@Int -> @Int) requires(true) ensures(true) effects(pure)
    { c(@Int.0 + 10) }
    where {
      fn c(@Int -> @Int) requires(true) ensures(true) effects(pure)
      { @Int.0 + 100 }
    }
  }
}
"""
        main_src = """\
import lib(top);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ top(5) }
"""
        mod = self._resolved(("lib",), lib_src)
        assert self._run_mod(main_src, [mod], fn="main") == 116

    def test_shadowed_imported_fn_nested_helpers_run(self) -> None:
        """A locally-shadowed imported fn (Pass 2.6, `<path>::…` emission) whose
        body reaches a nested grandchild helper: the module-qualified call
        must run the module's version through the full helper chain while the
        bare call resolves to the local shadow (#814 §8.5.3).

        The Pass-2.5/2.6 compile sites need no where-fn walk of their own —
        `_register_modules` pre-flattens the helper tree into
        `_imported_fn_decls` — and this pins that the shadow path inherits
        that: `calc(1)` = 100 (local) + `lib::calc(10)` = 16 (module chain
        through `grandchild`) = 116.
        """
        lib_src = """\
public fn calc(@Int -> @Int)
  requires(true) ensures(@Int.result == @Int.0 + 6) effects(pure)
{ child(@Int.0) }
where {
  fn child(@Int -> @Int)
    requires(true) ensures(@Int.result == @Int.0 + 6) effects(pure)
  { grandchild(@Int.0 + 1) }
  where {
    fn grandchild(@Int -> @Int)
      requires(true) ensures(@Int.result == @Int.0 + 5) effects(pure)
    { @Int.0 + 5 }
  }
}
"""
        main_src = """\
import lib;
private fn calc(@Int -> @Int)
  requires(true) ensures(@Int.result == @Int.0 * 100) effects(pure)
{ @Int.0 * 100 }
public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 116) effects(pure)
{ calc(1) + lib::calc(10) }
"""
        mod = self._resolved(("lib",), lib_src)
        assert self._run_mod(main_src, [mod], fn="main") == 116


# =====================================================================
# #999-#1015 import-door cluster — cross-module fixes
# =====================================================================


class TestImportDoorCluster:
    """Cross-module fixes from the mono/import-door cluster: imported-body
    where-helper hoisting (#1015), a module's own ADT layouts (#1008),
    imported-body generic discovery (#999), and module-qualified private
    generic harvesting (#1000, replacing draft PR #1026)."""

    _resolved = staticmethod(TestCrossModuleCodegen._resolved)
    _compile_mod = staticmethod(TestCrossModuleCodegen._compile_mod)
    _run_mod = staticmethod(TestCrossModuleCodegen._run_mod)

    LEAF_MODULE = """\
public fn a(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  leaf(@Int.0)
}
where {
  fn leaf(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { @Int.0 + 1 }
}

public fn b(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  leaf(@Int.0)
}
where {
  fn leaf(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { @Int.0 + 2 }
}
"""

    def test_imported_same_named_where_helpers_run_own_bodies_1015(
        self,
    ) -> None:
        """Two imported fns each carrying a same-named non-generic
        where-helper must run their OWN helper bodies (#1015).

        Pre-fix imported module ASTs were never given the #991
        parent-qualified hoist, so both `leaf`s collided first-seen-wins in
        the flat namespace and main returned 101 (b's leaf resolved to a's
        +1 body).  Correct: a(0)=1, b(0)=2 -> 102."""
        mod = self._resolved(("lib",), self.LEAF_MODULE)
        val = self._run_mod("""\
import lib(a, b);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  a(0) * 100 + b(0)
}
""", [mod], fn="main")
        assert val == 102

    ADT_MODULE = """\
public data Inner { MkInner(Int) }
public fn make(@Int -> @Inner)
  requires(true) ensures(true) effects(pure)
{ MkInner(@Int.0) }
public fn unwrap(@Inner -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Inner.0 { MkInner(@Int) -> @Int.0 } }
"""

    def test_module_constructs_own_adt_without_type_import_1008(self) -> None:
        """An imported fn constructing its module's OWN ADT must compile even
        when the importer never names the type (#1008).

        Pre-fix constructor layouts were registered per the importer's
        filter, so `make`'s body hit `unknown constructor MkInner` ->
        CodegenSkip -> `unknown func $make` at run unless the importer added
        `Inner` to the import list."""
        mod = self._resolved(("lib",), self.ADT_MODULE)
        val = self._run_mod("""\
import lib(make, unwrap);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ unwrap(make(7)) }
""", [mod], fn="main")
        assert val == 7

    def test_unimported_ctor_stays_rejected_at_check_1008(self) -> None:
        """PINNED INVARIANT (green pre- and post-fix): the CHECKER rejects an
        importer pattern-matching a constructor whose type it never imported
        (E320) — registering the module's own layouts unconditionally in
        codegen must not soften this user-facing guard rail."""
        from vera.checker import typecheck

        main_src = """\
import lib(make, unwrap);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match make(7) { MkInner(@Int) -> @Int.0 } }
"""
        mod = self._resolved(("lib",), self.ADT_MODULE)
        import tempfile
        from pathlib import Path

        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8"
        ) as f:
            f.write(main_src)
            f.flush()
            path = f.name
        try:
            prog = transform(parse_file(path))
            diags = typecheck(prog, main_src, resolved_modules=[mod])
            assert any(d.error_code == "E320" for d in diags), (
                "pattern-matching an unimported module ctor must stay E320 "
                f"at check (guard rail, #1008); got "
                f"{[d.error_code for d in diags]}"
            )
        finally:
            Path(path).unlink(missing_ok=True)

    NESTED_GEN_MODULE = """\
public fn compute(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ gid(@Int.0) + 1 }
where {
  forall<T> fn gid(@T -> @T)
    requires(true) ensures(@T.result == @T.0) effects(pure)
  { @T.0 }
}
"""

    def test_imported_fn_nested_generic_helper_discovered_999(self) -> None:
        """An imported fn's call to its OWN nested `forall` where-helper must
        be seeded into instance discovery (#999).

        Pre-fix discovery scanned only the importer's declarations, so the
        imported `compute`'s `gid(@Int.0)` had no clone base and WAT assembly
        failed with `unknown func $gid`."""
        mod = self._resolved(("lib_nested",), self.NESTED_GEN_MODULE)
        val = self._run_mod("""\
import lib_nested(compute);
public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 11) effects(pure)
{ compute(10) }
""", [mod], fn="main")
        assert val == 11

    PRIV_MODULE = """\
private forall<T> fn inner(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ @T.0 }
public forall<T> fn outer(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ inner(@T.0) }
"""

    def test_private_generic_reached_transitively_executes_1000(self) -> None:
        """A private module generic called by the module's public generic must
        be harvested as a (module-qualified) clone base (#1000).

        Pre-fix `_register_modules` skipped private generics entirely, so the
        public clone's body call dangled at `unknown func $inner`."""
        mod = self._resolved(("lib_priv",), self.PRIV_MODULE)
        val = self._run_mod("""\
import lib_priv(outer);
public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 7) effects(pure)
{ outer(7) }
""", [mod], fn="main")
        assert val == 7

    COLLIDE_MODULE = """\
private forall<T> fn dup(@T -> @Int) requires(true) ensures(true) effects(pure) { 0 }
public forall<T> fn caller(@T -> @Int) requires(true) ensures(true) effects(pure) { dup(@T.0) }
"""

    def test_local_fn_survives_transitive_private_generic_collision_1000(
        self,
    ) -> None:
        """A LOCAL fn and a transitively-reached private module generic
        sharing a name must EACH keep their own body (#1000).

        Both hijack directions are covered: pre-fix, main returned 105103 —
        the local dup(5) kept its body (105) but the imported caller's
        transitive `dup` call bound to the LOCAL dup (3+100=103) instead of
        the module's private helper (0), a silent wrong body on today's main.
        (The draft-PR #1026 bare-name harvest inverted the hijack: local
        dup(5) returned the import clone's 0.)  Module-qualified keying gives
        each caller its own callee: 105 * 1000 + 0 = 105000."""
        mod = self._resolved(("lib",), self.COLLIDE_MODULE)
        val = self._run_mod("""\
import lib(caller);
private fn dup(@Int -> @Int) requires(true) ensures(@Int.result == @Int.0 + 100) effects(pure) { @Int.0 + 100 }
public fn main(@Unit -> @Int) requires(true) ensures(true) effects(pure) { dup(5) * 1000 + caller(3) }
""", [mod], fn="main")
        assert val == 105000

    PRIVATE_ADT_MODULE = """\
private data Hidden { MkHidden(Int) }
public fn roundtrip(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match MkHidden(@Int.0) { MkHidden(@Int) -> @Int.0 } }
"""

    def test_module_private_adt_constructed_by_own_fn_1008(self) -> None:
        """A module fn constructing its module's PRIVATE ADT must compile —
        the private-ADT variant of #1008, where no import list could ever
        name the type.  Pre-fix: `unknown constructor` -> CodegenSkip ->
        `unknown func $roundtrip` at run."""
        mod = self._resolved(("lib",), self.PRIVATE_ADT_MODULE)
        val = self._run_mod("""\
import lib(roundtrip);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ roundtrip(9) }
""", [mod], fn="main")
        assert val == 9

    SHADOW_HELPER_MODULE = """\
private forall<T> fn pick(@T -> @Int)
  requires(true) ensures(true) effects(pure)
{ 100 }
public forall<T> fn outer(@T -> @Int)
  requires(true) ensures(true) effects(pure)
{ pick(@T.0) }
where {
  fn pick(@T -> @Int)
    requires(true) ensures(true) effects(pure)
  { 7 }
}
"""

    def test_private_generic_reroute_respects_helper_shadowing_1000(
        self,
    ) -> None:
        """A where-helper sharing a private module generic's name owns the
        bare call lexically (spec section 5) — the #1000 reroute must NOT
        capture it onto the module generic (PR #1029 review: pre-fix this
        returned 100, the private generic's body, instead of the helper's
        7)."""
        mod = self._resolved(("lib",), self.SHADOW_HELPER_MODULE)
        val = self._run_mod("""\
import lib(outer);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ outer(3) }
""", [mod], fn="main")
        assert val == 7

    def test_nongeneric_caller_of_private_generic_runs_1029(self) -> None:
        """#1029 (R1): a NON-generic imported fn (`use_it`) that calls a private
        module generic (`inner`) must reach the module's own `lib::inner`
        clone.  Pre-fix only the public-generic branch rerouted, so `use_it`'s
        bare `inner(@Int.0)` compiled to a `call $inner` that dangled at run
        (`unknown func`).  `inner` is identity, so `use_it(4) = 4 + 1 = 5`."""
        mod = self._resolved(("lib",), """\
private forall<T> fn inner(@T -> @T)
  requires(true) ensures(@T.result == @T.0) effects(pure)
{ @T.0 }
public fn use_it(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ inner(@Int.0) + 1 }
""")
        val = self._run_mod("""\
import lib(use_it);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ use_it(4) }
""", [mod], fn="main")
        assert val == 5

    def test_private_to_private_generic_chain_runs_1029(self) -> None:
        """#1029 (R1): a public generic → private `aa` → private `bb` chain must
        emit every link's clone.  Pre-fix the private generic's own body was
        harvested RAW, so `aa`'s bare `bb(@T.0)` call dangled.  `bb` returns 42,
        `aa` forwards it, `pub` forwards that — `pub(7) = 42`."""
        mod = self._resolved(("m",), """\
private forall<T> fn bb(@T -> @Int)
  requires(true) ensures(@Int.result == 42) effects(pure)
{ 42 }
private forall<T> fn aa(@T -> @Int)
  requires(true) ensures(true) effects(pure)
{ bb(@T.0) }
public forall<T> fn pub(@T -> @Int)
  requires(true) ensures(true) effects(pure)
{ aa(@T.0) }
""")
        val = self._run_mod("""\
import m(pub);
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ pub(7) }
""", [mod], fn="main")
        assert val == 42


# =====================================================================
# #1111 — module-local type-alias namespaces
# =====================================================================


class TestModuleLocalAliasNamespaces:
    """#1111: same-named type aliases in different modules stay module-local.

    Spec §8.4.1: a type alias is module-local — not importable, so two
    modules may legally reuse one alias name for different targets.
    Codegen used to merge every module's aliases into a single flat
    bare-name map (``setdefault``, first module won) and then let the
    main file's own aliases overwrite unconditionally, so one module's
    declarations resolved through another namespace's alias: wrong WASM
    signatures, invalid modules, and an import-order-dependent victim.
    """

    _resolved = staticmethod(TestCrossModuleCodegen._resolved)
    _compile_mod = staticmethod(TestCrossModuleCodegen._compile_mod)
    _run_mod = staticmethod(TestCrossModuleCodegen._run_mod)

    MOD_INT = """\
type F = Int;

public fn gc(@Unit -> @F)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""

    MOD_STR = """\
type F = String;

public fn gd(@Unit -> @F)
  requires(true) ensures(true) effects(pure)
{ "hello" }
"""

    MAIN = """\
import ca(gc);
import da(gd);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = gc(());
  let @String = gd(());
  let @Nat = string_length(@String.0);
  if @Nat.0 == 5 then { @Int.0 } else { 0 - 1 }
}
"""

    def test_conflicting_module_aliases_run(self) -> None:
        """The issue's repro: ``F = Int`` (ca) vs ``F = String`` (da).

        Pre-fix ca's ``F`` won the merge, so ``gd`` was emitted
        ``(result i64)`` against a String-returning body — an invalid
        module at instantiation.  Correct: gc() == 42 and gd() is a
        5-char String, so main returns 42 (else-arm -1 discriminates a
        silently corrupted String value).
        """
        mods = [
            self._resolved(("ca",), self.MOD_INT),
            self._resolved(("da",), self.MOD_STR),
        ]
        assert self._run_mod(self.MAIN, mods, fn="main") == 42

    def test_conflicting_module_aliases_run_flipped_order(self) -> None:
        """Same program, module list reversed — pre-fix the corrupted
        module flipped with processing order (da's ``F = String`` won and
        ``gc`` broke instead)."""
        mods = [
            self._resolved(("da",), self.MOD_STR),
            self._resolved(("ca",), self.MOD_INT),
        ]
        assert self._run_mod(self.MAIN, mods, fn="main") == 42

    def test_module_fn_signatures_stay_module_typed(self) -> None:
        """Emitted WAT signatures follow each module's OWN alias: gc's
        ``F = Int`` is ``(result i64)``, gd's ``F = String`` is the
        two-value String pair ``(result i32 i32)``."""
        mods = [
            self._resolved(("ca",), self.MOD_INT),
            self._resolved(("da",), self.MOD_STR),
        ]
        result = self._compile_mod(self.MAIN, mods)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, f"Unexpected errors: {[e.description for e in errors]}"
        assert "(func $gc (result i64)" in result.wat
        assert "(func $gd (result i32 i32)" in result.wat

    def test_local_alias_never_leaks_into_module_body(self) -> None:
        """A main-file ``type F = Bool`` must not re-type an imported
        module's ``F = Int`` declarations (pre-fix the local registration
        overwrote the flat map, so ``gc`` was emitted ``(result i32)``
        against its harvested i64 signature)."""
        mods = [self._resolved(("ca",), self.MOD_INT)]
        val = self._run_mod("""\
import ca(gc);

type F = Bool;

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @F = true;
  let @Int = gc(());
  if @F.0 then { @Int.0 } else { 0 - 1 }
}
""", mods, fn="main")
        assert val == 42

    def test_generic_clones_use_defining_module_alias(self) -> None:
        """Monomorphized clones of imported generics resolve alias-typed
        params/returns against their DEFINING module's namespace: ga's
        ``G = Int`` vs gb's ``G = String``."""
        mods = [
            self._resolved(("ga",), """\
type G = Int;

public forall<T> fn pick(@T, @G -> @G)
  requires(true) ensures(true) effects(pure)
{ @G.0 }
"""),
            self._resolved(("gb",), """\
type G = String;

public forall<T> fn wrap(@T, @G -> @G)
  requires(true) ensures(true) effects(pure)
{ @G.0 }
"""),
        ]
        val = self._run_mod("""\
import ga(pick);
import gb(wrap);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = pick(true, 42);
  let @String = wrap(1, "hey");
  if string_length(@String.0) == 3 then { @Int.0 } else { 0 - 1 }
}
""", mods, fn="main")
        assert val == 42

    def test_single_module_alias_regression_guard(self) -> None:
        """No-conflict baseline (green before AND after the fix): one
        module using its own alias in param + return position keeps
        working — guards the fix against dropping the working case."""
        mods = [self._resolved(("ma",), """\
type N = Int;

public fn add1(@N -> @N)
  requires(true) ensures(true) effects(pure)
{ @N.0 + 1 }
""")]
        val = self._run_mod("""\
import ma(add1);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ add1(41) }
""", mods, fn="main")
        assert val == 42

    def test_module_body_resolves_prelude_combinators(self) -> None:
        """No-conflict baseline (green before AND after): a module body
        using prelude combinators (whose signatures are spelled via
        prelude-injected fn-type aliases like ``OptionMapFn``) keeps
        working — guards the per-module effective map's prelude overlay."""
        mods = [self._resolved(("mp",), """\
public fn doubled(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(
    option_map(Some(@Int.0), fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }),
    0
  )
}
""")]
        val = self._run_mod("""\
import mp(doubled);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ doubled(20) }
""", mods, fn="main")
        assert val == 40

    def test_alias_inside_harvested_return_type_is_canonical(self) -> None:
        """A module return type with the alias in a NESTED position
        (``-> @Array<F>``, ``F = Float64``) must reach main's element
        inference already canonical (``Array<Float64>``).  Main indexes
        the call DIRECTLY (no typed let-binding), so the element type
        comes from the harvested return-type registry — a raw ``F``
        there would resolve against main's namespace (where ``F`` is a
        colliding ``String``) or fall to the i64 default; ``Float64``
        elements make either wrong path loud (f64 vs i64 mismatch),
        never a silent coincidence with the default."""
        mods = [self._resolved(("na",), """\
type F = Float64;

public fn nums(@Unit -> @Array<F>)
  requires(true) ensures(true) effects(pure)
{ [1.5, 2.5, 3.5] }
""")]
        val = self._run_mod("""\
import na(nums);

type F = String;

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if nums(())[1] == 2.5 then { 42 } else { 0 - 1 }
}
""", mods, fn="main")
        assert val == 42



    def test_mono_clone_registry_entry_canonical(self) -> None:
        """The CLONE key's entry in the shared bare-name registry is
        canonicalized too — the third door after the Pass-0 harvest and
        the shadowed ``<path>::…`` mirror (PR #1175 review).  ``pick$Bool``
        returns the module's ``G = Int``; the stored expression must be
        the canonical ``Int``, not a raw ``G`` a main-file consumer
        would re-resolve against the flat maps."""
        from vera import ast as vast

        mods = [self._resolved(("ga",), """\
type G = Int;

public forall<T> fn pick(@T, @G -> @G)
  requires(true) ensures(true) effects(pure)
{ @G.0 }
""")]
        source = """\
import ga(pick);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ pick(true, 42) }
"""
        from vera.codegen.core import CodeGenerator

        prog, path = _parse_from_temp_file(source)
        gen = CodeGenerator(
            source=source, file=path, resolved_modules=mods,
        )
        result = gen.compile_program(prog)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, [e.description for e in errors]
        clone_keys = [k for k in gen._fn_ret_type_exprs if "$" in k and k.startswith("pick")]
        assert clone_keys, (
            f"expected a pick clone key, got: "
            f"{sorted(gen._fn_ret_type_exprs)}"
        )
        te = gen._fn_ret_type_exprs[clone_keys[0]]
        assert isinstance(te, vast.NamedType) and te.name == "Int", (
            f"clone-key entry not canonical: {te!r} still carries the "
            f"module-local alias name"
        )

    def test_shadowed_qualified_door_registry_entry_canonical(self) -> None:
        """The mangled ``<path>::…`` registry entry for a SHADOWED module fn
        is canonicalized too — the qualified-door mirror of the bare-name
        harvest (PR #1175 review).  The invariant is registry-level:
        nothing enters ``_fn_ret_type_exprs`` carrying a module-local
        alias name, because any consumer resolving it (the fused-await
        classifier consumes exactly this bare-name registry) would do so
        against the flat maps — the main file's namespace.  Asserted on
        the stored expression directly; the end-to-end doors (await
        fusion through a shadowed async fn) are heavyweight to stage and
        the classifier reads precisely this entry."""
        from vera import ast as vast

        mods = [self._resolved(("na",), """\
type F = Float64;

public fn nums(@Unit -> @Array<F>)
  requires(true) ensures(true) effects(pure)
{ [1.5, 2.5, 3.5] }
""")]
        source = """\
import na(nums);

type F = String;

public fn nums(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 7 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ nums(()) * 6 }
"""
        from vera.codegen.core import CodeGenerator

        prog, path = _parse_from_temp_file(source)
        gen = CodeGenerator(
            source=source, file=path, resolved_modules=mods,
        )
        result = gen.compile_program(prog)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, [e.description for e in errors]
        mangled = [k for k in gen._fn_ret_type_exprs if "::" in k]
        assert mangled, (
            f"expected a qualified entry for the shadowed import, got keys: "
            f"{sorted(gen._fn_ret_type_exprs)}"
        )
        te = gen._fn_ret_type_exprs[mangled[0]]
        assert isinstance(te, vast.NamedType) and te.name == "Array"
        assert te.type_args and isinstance(te.type_args[0], vast.NamedType)
        assert te.type_args[0].name == "Float64", (
            f"shadowed-door entry not canonical: Array<"
            f"{te.type_args[0].name}> still carries the module-local "
            f"alias name"
        )

    def test_parameterized_module_alias(self) -> None:
        """A module's PARAMETERIZED alias (``type Boxed<T> = Option<T>``)
        resolves through the per-module ``_type_alias_params`` capture —
        both in the module's own signature and via the canonicalized
        harvested return type consumed by main."""
        mods = [self._resolved(("pa",), """\
type Boxed<T> = Option<T>;

public fn wrap2(@Int -> @Boxed<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(@Int.0) }
""")]
        val = self._run_mod("""\
import pa(wrap2);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ option_unwrap_or(wrap2(41), 0) + 1 }
""", mods, fn="main")
        assert val == 42

    def test_unit_aliased_generic_clone_statement_position(self) -> None:
        """A module generic returning a Unit-ALIASED type (``-> @U``,
        ``U = Unit``), called in block-statement position from main.

        End-to-end regression for the void-classification edge (#584 ×
        #1111): the clone must emit with NO result and the caller must
        NOT emit a ``drop`` after it.  The statement-position void
        decision currently resolves through the bare-name harvest
        (``consume -> None``, computed under the module's own aliases in
        ``temp``), so this pins the harvested-fallback path; the
        registration-scope in Pass 1.5 additionally records the clone's
        own entry truthfully (see the defence-in-depth note at that
        site — its absence is masked by this very fallback, so no test
        can currently distinguish it)."""
        mods = [self._resolved(("gu",), """\
type U = Unit;

public forall<T> fn consume(@T -> @U)
  requires(true) ensures(true) effects(pure)
{ () }
""")]
        val = self._run_mod("""\
import gu(consume);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  consume(5);
  42
}
""", mods, fn="main")
        assert val == 42


# =====================================================================
# #1184 — user aliases colliding with the prelude's fn-type aliases
# =====================================================================


class TestPreludeFnTypeAliasCollision:
    """#1184: a user alias named after a prelude fn-type alias.

    The prelude spells its closure-taking combinators' parameters
    through type aliases (``option_map(@Option<VeraA>,
    @VeraOptionMapFn<VeraA, VeraB>)``) because a slot reference needs a
    type *name*.  Those names used to live in the same namespace user
    code writes into, so a user (or module) alias of the same name
    re-typed the PRELUDE's declaration — the mirror image of the #1111
    defect that spec §8.4.1 forbids in the other direction (a main-file
    alias must never re-type a module's declarations).

    Pre-fix the two namespaces disagreed about it, and neither was
    right:

    * main file — the user's alias won the flat maps, so ``option_map``
      was emitted with an ``Int``-typed (i64) closure parameter and the
      call passed a funcref: ``vera run`` died at WASM validation.
    * module — Pass-1.5 instantiation discovery ran under the flat maps
      (prelude's fn type) and created ``option_map$Int_JInt``, while the
      module body compiled under ``{prelude, **module_own}`` bound
      ``VeraB`` to the phantom-var default and called
      ``option_map$Int_JBool``.  Missing target ⇒ E602 ⇒ the function
      was skipped, ``main`` was dropped, and ``check``/``verify``/
      ``compile`` all reported success over EMPTY exports.

    The fix gives the prelude's own combinators reserved ``Vera``-
    prefixed spellings of those aliases (the #869 remedy, applied to the
    alias names rather than the type-parameter names), so no user alias
    can reach them from any scope.  #1221 then retired the user-facing
    spellings altogether: the prelude injects nothing outside the
    reserved namespace, so the names these tests declare are ordinary
    user aliases that collide with nothing.  They stay parametrized over
    those names because that is the shape a program in the wild has —
    each one must keep meaning exactly what the user wrote while the
    combinators keep working beside it.
    """

    _resolved = staticmethod(TestCrossModuleCodegen._resolved)
    _compile_mod = staticmethod(TestCrossModuleCodegen._compile_mod)
    _run_mod = staticmethod(TestCrossModuleCodegen._run_mod)

    # One combinator body per prelude fn-type alias.  Each triples its
    # argument, so ``tripled(14)`` is 42 — a value that cannot coincide
    # with any fallback on the broken paths (not ``Bool``, not 0, not
    # the argument).
    BODIES: ClassVar[dict[str, str]] = {
        "OptionMapFn": """\
public fn tripled(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_unwrap_or(
    option_map(Some(@Int.0), fn(@Int -> @Int) effects(pure) { @Int.0 * 3 }),
    0
  )
}
""",
        "OptionBindFn": """\
public fn tripled(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_unwrap_or(
    option_and_then(
      Some(@Int.0),
      fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0 * 3) }
    ),
    0
  )
}
""",
        "ResultMapFn": """\
public fn tripled(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  result_unwrap_or(
    result_map(wrap(@Int.0), fn(@Int -> @Int) effects(pure) { @Int.0 * 3 }),
    0
  )
}

private fn wrap(@Int -> @Result<Int, String>)
  requires(true)
  ensures(true)
  effects(pure)
{ Ok(@Int.0) }
""",
    }

    IMPORTER = """\
import mc(tripled);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ tripled(14) }
"""

    MAIN_TAIL = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ tripled(14) }
"""

    ALIASES = tuple(sorted(BODIES))

    def _run_as_module(self, alias: str, decl: str) -> int:
        """Run *alias*'s combinator body from an imported module."""
        mods = [self._resolved(("mc",), decl + self.BODIES[alias])]
        return self._run_mod(self.IMPORTER, mods, fn="main")

    def _run_as_main(self, alias: str, decl: str) -> int:
        """Run the same body declared in the main file."""
        return self._run_mod(
            decl + self.BODIES[alias] + "\n" + self.MAIN_TAIL,
            [], fn="main",
        )

    @pytest.mark.parametrize("alias", ALIASES)
    def test_module_alias_collision_keeps_combinator_working(
        self, alias: str,
    ) -> None:
        """The issue's repro: a module declaring ``type <Alias> = Int;``
        must not disable the combinator that alias names.

        Pre-fix the module body called ``option_map$Int_JBool``, which
        discovery never created: an E602 *warning* (never an error)
        skipped ``tripled`` and dropped ``main``, so ``vera run`` exited
        1 with "No exported functions to call" over a green
        ``check``/``verify``/``compile``.  Through this harness the same
        state surfaces one step earlier — with the only closure caller
        skipped, the orphaned ``option_map$Int_JInt`` clone is emitted
        against a function table nothing declares and wasmtime rejects
        the module ("unknown table 0")."""
        assert self._run_as_module(alias, f"type {alias} = Int;\n\n") == 42

    @pytest.mark.parametrize("alias", ALIASES)
    def test_main_file_alias_collision_keeps_combinator_working(
        self, alias: str,
    ) -> None:
        """The same collision declared in the MAIN file.

        Pre-fix the user's alias won the flat maps outright, so the
        combinator clone was emitted with an ``Int`` (i64) parameter
        where the call site passes a closure funcref — ``vera run``
        trapped at WASM validation ("type mismatch: expected i64, found
        i32") instead of returning a value."""
        assert self._run_as_main(alias, f"type {alias} = Int;\n\n") == 42

    @pytest.mark.parametrize("alias", ALIASES)
    def test_module_and_main_namespaces_agree(self, alias: str) -> None:
        """The invariant, stated as a differential.

        One program, two namespaces: the collision must mean the same
        thing whether the alias and the combinator call sit in an
        imported module or in the main file.  Pre-fix they disagreed in
        *kind* (silent empty exports vs a WASM validation trap), which
        is what let the module side hide behind a green
        ``check``/``verify``/``compile``.  Compared against the
        no-collision baseline so the pair agreeing on a wrong value
        cannot pass."""
        decl = f"type {alias} = Int;\n\n"
        baseline = self._run_as_main(alias, "")
        assert baseline == self._run_as_module(alias, ""), (
            "no-collision baseline already disagrees across namespaces"
        )
        assert self._run_as_main(alias, decl) == baseline
        assert self._run_as_module(alias, decl) == baseline

    @pytest.mark.parametrize("alias", ["OptionMapFn", "OptionBindFn"])
    def test_shadowing_every_option_alias_at_once(self, alias: str) -> None:
        """Both Option-combinator alias names taken in one program.

        Distinct door from the single-alias tests: ``inject_prelude``
        used to gate a user-facing alias block on the user having taken
        *all* of a group's names, so taking one name still injected the
        block while taking both skipped it entirely — and the
        declarations the combinators resolve through went with it.  The
        aliases now arrive with the combinator bodies that need them,
        unconditionally and under reserved names (#1221), which is what
        this pair of declarations pins."""
        decl = "type OptionMapFn = Int;\ntype OptionBindFn = String;\n\n"
        assert self._run_as_main(alias, decl) == 42
        assert self._run_as_module(alias, decl) == 42

    @pytest.mark.parametrize("alias", ALIASES)
    def test_colliding_alias_still_means_what_the_user_wrote(
        self, alias: str,
    ) -> None:
        """Over-correction guard: the user's alias keeps ITS meaning.

        Green before AND after — pinned because the obvious fix (give
        the prelude's names precedence in every scope) would buy the
        combinator back by silently re-typing the user's own alias,
        which the checker would still read as ``Int``.  Both namespaces
        must keep resolving ``@<Alias>.0`` as the user's ``Int``."""
        body = f"""\
type {alias} = Int;

public fn tripled(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @{alias} = 7;
  @{alias}.0 * 6
}}
"""
        assert self._run_mod(
            body + "\n" + """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ tripled(()) }
""", [], fn="main") == 42
        mods = [self._resolved(("mc",), body)]
        assert self._run_mod("""\
import mc(tripled);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ tripled(()) }
""", mods, fn="main") == 42

    def test_module_local_fn_type_alias_still_module_local(self) -> None:
        """Over-correction guard for #1111: a module-local alias naming a
        *closure* type still resolves against its own namespace.

        The shape closest to what #1184 changes — an fn-type alias used
        as a higher-order parameter and reached through ``apply_fn`` —
        and one #1111's own tests do not cover (theirs alias ``Int`` /
        ``String`` / ``Unit`` / ``Option<T>`` / ``Array<Float64>``).  The
        main file reuses the name for an unrelated non-fn type, so a fix
        that flattened alias namespaces would resolve the module's
        parameter through ``Int`` and mis-type the ``call_indirect``."""
        mods = [self._resolved(("hof",), """\
type Mapper = fn(Int -> Int) effects(pure);

public fn apply_twice(@Int, @Mapper -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ apply_fn(@Mapper.0, apply_fn(@Mapper.0, @Int.0)) }

public fn tripled(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ apply_twice(@Int.0, fn(@Int -> @Int) effects(pure) { @Int.0 + 7 }) }
""")]
        val = self._run_mod("""\
import hof(tripled);

type Mapper = String;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Mapper = "unrelated";
  if string_length(@Mapper.0) == 9 then { tripled(28) } else { 0 - 1 }
}
""", mods, fn="main")
        assert val == 42

    def test_module_alias_scope_keeps_alias_and_param_maps_paired(
        self,
    ) -> None:
        """``_module_alias_scope`` must override BOTH alias maps together.

        The scope merged ``_type_aliases`` and ``_type_alias_params``
        independently, so a module alias shadowing a *parameterized*
        prelude alias with a *non*-parameterized one paired the module's
        target with the prelude's stale ``('VeraA', 'VeraB')`` param
        list.  ``resolve_type_alias`` substitutes whenever
        ``len(params) == len(type_args)``, so the stale pair is a live
        wrong-substitution door for any consumer that reaches the name
        with two type args — which is exactly how the prelude's own
        ``@VeraOptionMapFn<VeraA, VeraB>`` parameter used to resolve to
        the module's ``Int``.  Asserted on the maps rather than end to
        end, and driven straight at ``CodeGenerator``: every prelude
        alias now lives in the reserved namespace (#1221), so the module
        below is a shape ``vera check`` refuses (E154) and only this
        layer can still be handed.  The pairing is what keeps that
        refusal from being the only thing standing between a module
        alias and the prelude's parameter list."""
        from vera.codegen.core import CodeGenerator

        mods = [self._resolved(("mc",), """\
type VeraOptionMapFn = Int;

public fn ident(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
""")]
        source = """\
import mc(ident);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ ident(42) }
"""
        prog, path = _parse_from_temp_file(source)
        gen = CodeGenerator(source=source, file=path, resolved_modules=mods)
        result = gen.compile_program(prog)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, [e.description for e in errors]

        # The prelude's own entry is parameterized, so a stale param
        # list is distinguishable from a correctly paired override.
        assert gen._prelude_type_alias_params.get("VeraOptionMapFn") == (
            "VeraA", "VeraB",
        ), "prelude alias params missing — test no longer probes the hole"

        with gen._module_alias_scope(("mc",)):
            assert isinstance(
                gen._type_aliases["VeraOptionMapFn"], ast.NamedType,
            ) and gen._type_aliases["VeraOptionMapFn"].name == "Int", (
                "module alias lost its own target inside its scope"
            )
            assert "VeraOptionMapFn" not in gen._type_alias_params, (
                "module's non-parameterized alias is paired with the "
                "prelude's stale param list"
            )

    def test_parameterized_module_alias_takes_its_own_params(self) -> None:
        """A parameterized module alias pairs with ITS params (PR #1191 review).

        The pairing invariant's other branch: `type OptionMapFn<A> =
        Option<A>;` in a module must resolve at arity 1 inside that
        module.  Dropping the `_type_alias_params.update(mod_params)`
        overlay leaves the module's target with no parameter list at
        all, and the arity-1 use below stops substituting — the missing
        pairing is loud, end to end.
        """
        from vera.codegen.core import CodeGenerator

        mods = [self._resolved(("palias",), """\
type OptionMapFn<A> = Option<A>;

public fn wrap(@Int -> @OptionMapFn<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ Some(@Int.0) }
""")]
        source = """\
import palias(wrap);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ option_unwrap_or(palias::wrap(41), 0) + 1 }
"""
        prog, path = _parse_from_temp_file(source)
        gen = CodeGenerator(source=source, file=path, resolved_modules=mods)
        result = gen.compile_program(prog)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, [e.description for e in errors]
        assert "main" in result.exports
        from vera.codegen import execute
        assert execute(result).value == 42
