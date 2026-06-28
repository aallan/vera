"""Tests for vera.codegen — Cross-module codegen.

Covers the cross-module guard rail and cross-module function compilation
via flattening.
"""

from __future__ import annotations

import pytest
import wasmtime

from vera.codegen import (
    CompileResult,
    compile,
    execute,
)
from vera.parser import parse_file
from vera.resolver import ResolvedModule
from vera.transform import transform


# =====================================================================
# Helpers
# =====================================================================


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    # Write to a temp source and parse
    import tempfile

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
    ) -> ResolvedModule:
        """Build a ResolvedModule from source text."""
        import tempfile
        from pathlib import Path

        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            f.flush()
            fpath = f.name

        tree = parse_file(fpath)
        prog = transform(tree)
        return ResolvedModule(
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
        """#814 C2: inside a qualified-reached ``mod$`` body, an intra-module
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
        under its ``mod$…`` name, never a second bare ``$helper``).  Before the
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

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> ResolvedModule:
        import tempfile
        from pathlib import Path
        # Explicit utf-8 encoding (Windows-portability) + try/finally
        # cleanup so the temp file is removed after parse + transform.
        # Safe because `compile()` works off the in-memory `source`
        # string + the AST `prog`, not by re-reading the file path
        # (CR-2 on PR #664).
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False,
            encoding="utf-8",
        ) as f:
            f.write(source)
            f.flush()
            fpath = f.name
        try:
            tree = parse_file(fpath)
            prog = transform(tree)
            return ResolvedModule(
                path=path, file_path=Path(fpath), program=prog,
                source=source,
            )
        finally:
            Path(fpath).unlink(missing_ok=True)

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

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> ResolvedModule:
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
