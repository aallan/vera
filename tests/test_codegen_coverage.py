"""Tests for vera.codegen — Coverage gap tests.

Defensive error paths in codegen.py. These construct AST nodes directly
(bypassing the type checker) to reach error branches that cannot be
triggered via well-typed source.
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

import vera.ast as ast


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
    ast_mod = transform(tree)
    return compile(ast_mod, source=source, file=path)


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
# Coverage gap tests -- defensive error paths
# =====================================================================


class TestCodegenCoverageGaps:
    """Tests for defensive error paths in codegen.py.

    These construct AST nodes directly (bypassing the type checker) to
    reach error branches that can't be triggered via well-typed source.
    """

    def _make_program(
        self, decl: "ast.FnDecl", visibility: str = "public"
    ) -> "ast.Program":
        """Wrap a FnDecl in a minimal Program."""
        from vera.ast import Program, TopLevelDecl

        return Program(
            module=None,
            imports=(),
            declarations=(TopLevelDecl(visibility=visibility, decl=decl),),
        )

    def _make_fn(
        self,
        name: str = "f",
        params: tuple = (),
        return_type: "ast.TypeExpr | None" = None,
        effect: "ast.EffectRow | None" = None,
        body: "ast.Expr | None" = None,
    ) -> "ast.FnDecl":
        """Build a minimal FnDecl with sensible defaults."""
        from vera.ast import (
            Block,
            BoolLit,
            Ensures,
            FnDecl,
            IntLit,
            NamedType,
            PureEffect,
            Requires,
        )

        return FnDecl(
            name=name,
            forall_vars=None,
            forall_constraints=None,
            params=params,
            return_type=return_type or NamedType(name="Int", type_args=None),
            contracts=(Requires(expr=BoolLit(value=True)),
                       Ensures(expr=BoolLit(value=True))),
            effect=effect or PureEffect(),
            body=body or Block(statements=(), expr=IntLit(value=0)),
            where_fns=None,
        )

    # -- E605: _is_compilable rejects unsupported return type ----------

    def test_e605_unsupported_return_type(self) -> None:
        """A function returning an unknown type triggers E605."""
        from vera.ast import NamedType

        fn = self._make_fn(
            name="bad_ret",
            return_type=NamedType(name="UnknownType", type_args=None),
        )
        prog = self._make_program(fn)
        result = compile(prog)
        codes = [d.error_code for d in result.diagnostics]
        assert "E605" in codes, f"Expected E605, got {codes}"

    # -- E606: State effect without type argument ----------------------

    def test_e606_state_without_type_arg(self) -> None:
        """State without <T> triggers E606."""
        from vera.ast import EffectRef, EffectSet, NamedType

        fn = self._make_fn(
            name="bad_state",
            return_type=NamedType(name="Int", type_args=None),
            effect=EffectSet(effects=(EffectRef(name="State", type_args=None),)),
        )
        prog = self._make_program(fn)
        result = compile(prog)
        codes = [d.error_code for d in result.diagnostics]
        assert "E606" in codes, f"Expected E606, got {codes}"

    # -- E600: defensive param type guard in _compile_fn ---------------

    def test_e600_defensive_unsupported_param(self) -> None:
        """Bypass _is_compilable to hit the E600 guard in _compile_fn."""
        from unittest.mock import patch

        from vera.ast import NamedType

        fn = self._make_fn(
            name="bad_param",
            params=(NamedType(name="UnknownType", type_args=None),),
            return_type=NamedType(name="Int", type_args=None),
        )
        prog = self._make_program(fn)
        # Monkeypatch _is_compilable to always return True so the function
        # reaches _compile_fn where the E600 guard lives.
        with patch(
            "vera.codegen.CodeGenerator._is_compilable", return_value=True
        ):
            result = compile(prog)
        codes = [d.error_code for d in result.diagnostics]
        assert "E600" in codes, f"Expected E600, got {codes}"

    # -- E601: defensive return type guard in _compile_fn --------------

    def test_e601_defensive_unsupported_return(self) -> None:
        """Bypass _is_compilable to hit the E601 guard in _compile_fn."""
        from unittest.mock import patch

        from vera.ast import NamedType

        fn = self._make_fn(
            name="bad_ret2",
            return_type=NamedType(name="UnknownType", type_args=None),
        )
        prog = self._make_program(fn)
        with patch(
            "vera.codegen.CodeGenerator._is_compilable", return_value=True
        ):
            result = compile(prog)
        codes = [d.error_code for d in result.diagnostics]
        assert "E601" in codes, f"Expected E601, got {codes}"

    # -- ModuleCall to unknown module function -------------------------

    def test_cross_module_unknown_module_call(self) -> None:
        """ModuleCall to a non-existent module function is detected."""
        from vera.ast import Block, IntLit, ModuleCall, NamedType

        body = Block(
            statements=(),
            expr=ModuleCall(
                path=("fake", "module"),
                name="nonexistent",
                args=(IntLit(value=1),),
            ),
        )
        fn = self._make_fn(name="caller", body=body)
        prog = self._make_program(fn)
        result = compile(prog)
        descs = [d.description for d in result.diagnostics]
        assert any("nonexistent" in d and "not defined" in d for d in descs), (
            f"Expected cross-module error about 'nonexistent', got {descs}"
        )
