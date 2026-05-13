"""Synthetic-AST tests for the defensive `isinstance` branches
added by #597 to compiler walker functions.

These branches are unreachable via end-to-end programs today —
every flow is masked by an upstream guard (type checker
rejection, `[E602]` codegen-skip, etc.).  Without these tests,
a future refactor that breaks a defensive branch would land
silently (no production path exercises them).

Strategy: construct synthetic AST nodes directly and invoke the
walker, asserting the defensive branch produces the correct
result.  Pins each branch's behaviour against future regression.

The 11 defensive branches:

- ``_scan_io_ops`` (compilability.py): IndexExpr, ArrayLit,
  InterpolatedString, AnonFn → recurses into sub-exprs to find
  IO/host-import builtins.
- ``_scan_expr_for_handlers`` (compilability.py): QualifiedCall,
  IndexExpr, ArrayLit, InterpolatedString, AnonFn → recurses
  into sub-exprs to find HandleExpr nodes.
- ``_infer_expr_wasm_type`` (inference.py): AnonFn → "i32",
  ModuleCall → None.
- ``_infer_vera_type`` (inference.py): Block / MatchExpr /
  HandleExpr / AssertExpr / AssumeExpr / AnonFn / QualifiedCall /
  ModuleCall.
"""

from __future__ import annotations

from vera import ast
from vera.codegen.core import CodeGenerator
from vera.wasm.context import WasmContext
from vera.wasm.helpers import StringPool


# =====================================================================
# Helpers
# =====================================================================


def _make_cg() -> CodeGenerator:
    """Build a fresh CodeGenerator for compilability scans."""
    return CodeGenerator()


def _make_ctx() -> WasmContext:
    """Build a fresh WasmContext for inference helpers."""
    return WasmContext(string_pool=StringPool())


def _io_print(arg: ast.Expr = ast.UnitLit()) -> ast.QualifiedCall:
    return ast.QualifiedCall(qualifier="IO", name="print", args=(arg,))


def _slot(type_name: str = "Int", index: int = 0) -> ast.SlotRef:
    return ast.SlotRef(
        type_name=type_name, type_args=None, index=index)


# =====================================================================
# `_scan_io_ops` defensive branches (#597)
# =====================================================================


class TestScanIoOpsDefensiveBranches:
    """Each branch recurses into a sub-expression position so IO/
    host-import builtins buried inside are still registered."""

    def test_indexexpr_collection_recursion(self) -> None:
        cg = _make_cg()
        # `coll[0]` where coll is an IO call (purely synthetic —
        # type checker would reject this construction at the source
        # level, but the scanner must still find it for the defensive
        # branch to be testable).
        node = ast.IndexExpr(
            collection=_io_print(), index=ast.IntLit(value=0))
        cg._scan_io_ops(node)
        assert "print" in cg._io_ops_used

    def test_indexexpr_index_recursion(self) -> None:
        cg = _make_cg()
        node = ast.IndexExpr(
            collection=_slot("Array"), index=_io_print())
        cg._scan_io_ops(node)
        assert "print" in cg._io_ops_used

    def test_arraylit_elements_recursion(self) -> None:
        cg = _make_cg()
        node = ast.ArrayLit(elements=(_io_print(),))
        cg._scan_io_ops(node)
        assert "print" in cg._io_ops_used

    def test_interpolated_string_parts_recursion(self) -> None:
        cg = _make_cg()
        # InterpolatedString.parts is `tuple[Expr | str, ...]` —
        # string fragments are bare ``str`` and Expr parts are AST
        # nodes.  The defensive branch must skip the str parts and
        # recurse into the Expr parts.
        node = ast.InterpolatedString(
            parts=("prefix: ", _io_print(), " suffix"))
        cg._scan_io_ops(node)
        assert "print" in cg._io_ops_used

    def test_anonfn_body_recursion(self) -> None:
        cg = _make_cg()
        # The AnonFn defensive branch is the PRIMARY defence —
        # `_compile_lifted_closure` does NOT call `_scan_io_ops`
        # on lifted bodies.  Without this branch, IO ops inside
        # a closure body would silently miss their host-import
        # registration.
        body = ast.Block(statements=(), expr=_io_print())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        cg._scan_io_ops(node)
        assert "print" in cg._io_ops_used


# =====================================================================
# `_scan_expr_for_handlers` defensive branches (#597)
# =====================================================================


def _handle_expr() -> ast.HandleExpr:
    """Build a minimal HandleExpr for State<Int>."""
    return ast.HandleExpr(
        effect=ast.EffectRef(
            name="State",
            type_args=(ast.NamedType(name="Int", type_args=None),)),
        state=None,
        clauses=(),
        body=ast.Block(statements=(), expr=ast.UnitLit()),
    )


class TestScanExprForHandlersDefensiveBranches:
    """Each branch recurses into a sub-expression position so
    HandleExprs buried inside are still discovered for type
    registration."""

    def test_qualifiedcall_args_recursion(self) -> None:
        cg = _make_cg()
        node = ast.QualifiedCall(
            qualifier="IO", name="print", args=(_handle_expr(),))
        cg._scan_expr_for_handlers(node)
        # State<Int> registered
        assert ("Int", "i64") in cg._state_types

    def test_indexexpr_recursion(self) -> None:
        cg = _make_cg()
        node = ast.IndexExpr(
            collection=_handle_expr(), index=ast.IntLit(value=0))
        cg._scan_expr_for_handlers(node)
        assert ("Int", "i64") in cg._state_types

    def test_arraylit_recursion(self) -> None:
        cg = _make_cg()
        node = ast.ArrayLit(elements=(_handle_expr(),))
        cg._scan_expr_for_handlers(node)
        assert ("Int", "i64") in cg._state_types

    def test_interpolated_string_recursion(self) -> None:
        cg = _make_cg()
        node = ast.InterpolatedString(parts=("x: ", _handle_expr()))
        cg._scan_expr_for_handlers(node)
        assert ("Int", "i64") in cg._state_types

    def test_anonfn_body_recursion(self) -> None:
        cg = _make_cg()
        body = ast.Block(statements=(), expr=_handle_expr())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        cg._scan_expr_for_handlers(node)
        assert ("Int", "i64") in cg._state_types


# =====================================================================
# `_infer_expr_wasm_type` defensive branches (#597)
# =====================================================================


class TestInferExprWasmTypeDefensiveBranches:
    """AnonFn → "i32" (closure handle), ModuleCall → None (path
    field can't be threaded through bare-name FnCall dispatch)."""

    def test_anonfn_returns_i32(self) -> None:
        ctx = _make_ctx()
        body = ast.Block(statements=(), expr=ast.UnitLit())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        assert ctx._infer_expr_wasm_type(node) == "i32"

    def test_modulecall_returns_none(self) -> None:
        """ModuleCall carries `expr.path` that the bare-name FnCall
        dispatcher can't consume.  Returning None surfaces the
        unknown-type cleanly rather than masking with a wrong same-
        name lookup."""
        ctx = _make_ctx()
        node = ast.ModuleCall(
            path=("some_module",), name="some_fn", args=())
        assert ctx._infer_expr_wasm_type(node) is None


# =====================================================================
# `_infer_vera_type` defensive branches (#597)
# =====================================================================


class TestInferVeraTypeDefensiveBranches:
    """Block / MatchExpr / HandleExpr → trailing-expr type;
    AssertExpr / AssumeExpr → "Unit"; AnonFn / QualifiedCall /
    ModuleCall → None (path/qualifier fields can't be threaded
    through the bare-name FnCall dispatcher)."""

    def test_block_returns_trailing_expr_type(self) -> None:
        ctx = _make_ctx()
        node = ast.Block(statements=(), expr=ast.IntLit(value=42))
        assert ctx._infer_vera_type(node) == "Int"

    def test_matchexpr_returns_first_arm_body_type(self) -> None:
        ctx = _make_ctx()
        arm = ast.MatchArm(
            pattern=ast.WildcardPattern(),
            body=ast.BoolLit(value=True),
        )
        node = ast.MatchExpr(
            scrutinee=ast.IntLit(value=0), arms=(arm,))
        assert ctx._infer_vera_type(node) == "Bool"

    def test_matchexpr_no_arms_returns_none(self) -> None:
        ctx = _make_ctx()
        node = ast.MatchExpr(
            scrutinee=ast.IntLit(value=0), arms=())
        assert ctx._infer_vera_type(node) is None

    def test_handleexpr_returns_body_expr_type(self) -> None:
        ctx = _make_ctx()
        node = ast.HandleExpr(
            effect=ast.EffectRef(name="State", type_args=()),
            state=None,
            clauses=(),
            body=ast.Block(statements=(), expr=ast.FloatLit(value=1.5)),
        )
        assert ctx._infer_vera_type(node) == "Float64"

    def test_assertexpr_returns_unit(self) -> None:
        ctx = _make_ctx()
        node = ast.AssertExpr(expr=ast.BoolLit(value=True))
        assert ctx._infer_vera_type(node) == "Unit"

    def test_assumeexpr_returns_unit(self) -> None:
        ctx = _make_ctx()
        node = ast.AssumeExpr(expr=ast.BoolLit(value=True))
        assert ctx._infer_vera_type(node) == "Unit"

    def test_anonfn_returns_none(self) -> None:
        """Closure handle has no simple Vera-type name suitable
        for call rewriting; None lets callers handle the unknown
        case explicitly (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        body = ast.Block(statements=(), expr=ast.UnitLit())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        assert ctx._infer_vera_type(node) is None

    def test_qualifiedcall_returns_none(self) -> None:
        """`qualifier` can't be threaded through bare-name FnCall
        dispatch (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        node = ast.QualifiedCall(
            qualifier="IO", name="read_line", args=(ast.UnitLit(),))
        assert ctx._infer_vera_type(node) is None

    def test_modulecall_returns_none(self) -> None:
        """`path` can't be threaded through bare-name FnCall
        dispatch (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        node = ast.ModuleCall(
            path=("some_module",), name="some_fn", args=())
        assert ctx._infer_vera_type(node) is None
