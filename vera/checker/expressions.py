"""Expression type synthesis and related checking for the Vera type checker.

This mixin provides the core expression type synthesis dispatch
(_synth_expr), slot references, binary/unary operators, indexing,
blocks/statements, anonymous functions, array literals, assert/assume,
quantifiers, and old/new contract expressions.
"""

from __future__ import annotations

from vera import ast
from vera.types import (
    BOOL,
    BYTE,
    FLOAT64,
    INT,
    NAT,
    NUMERIC_TYPES,
    ORDERABLE_TYPES,
    STRING,
    UNIT,
    AdtType,
    PrimitiveType,
    EffectInstance,
    FunctionType,
    Type,
    UnknownType,
    base_type,
    is_subtype,
    pretty_type,
    types_equal,
)


class ExpressionsMixin:
    """Mixin providing expression type synthesis and related methods."""

    # -----------------------------------------------------------------
    # Expression type synthesis
    # -----------------------------------------------------------------

    def _synth_expr(self, expr: ast.Expr, *,
                    expected: Type | None = None) -> Type | None:
        """Synthesise the type of an expression.  Returns None on error.

        When *expected* is provided, it is threaded to constructors,
        if/match, and blocks so that nullary constructors of parameterised
        ADTs can resolve their TypeVars from context (bidirectional checking).
        """
        if isinstance(expr, ast.IntLit):
            # Byte coercion: integer literals 0–255 accepted as Byte when
            # the expected type is Byte (bidirectional checking).
            if (expected is not None
                    and isinstance(expected, PrimitiveType)
                    and expected.name == "Byte"
                    and 0 <= expr.value <= 255):
                return BYTE
            # Non-negative integer literals are Nat (which is a subtype of
            # Int).  This lets literals like 0, 1, 42 satisfy Nat parameters
            # without refinement verification.
            return NAT if expr.value >= 0 else INT
        if isinstance(expr, ast.FloatLit):
            return FLOAT64
        if isinstance(expr, ast.StringLit):
            return STRING
        if isinstance(expr, ast.BoolLit):
            return BOOL
        if isinstance(expr, ast.UnitLit):
            return UNIT
        if isinstance(expr, ast.SlotRef):
            return self._check_slot_ref(expr)
        if isinstance(expr, ast.ResultRef):
            return self._check_result_ref(expr)
        if isinstance(expr, ast.BinaryExpr):
            return self._check_binary(expr)
        if isinstance(expr, ast.UnaryExpr):
            return self._check_unary(expr)
        if isinstance(expr, ast.IndexExpr):
            return self._check_index(expr)
        if isinstance(expr, ast.FnCall):
            return self._check_fn_call(expr)
        if isinstance(expr, ast.ConstructorCall):
            return self._check_constructor_call(expr, expected=expected)
        if isinstance(expr, ast.NullaryConstructor):
            return self._check_nullary_constructor(expr, expected=expected)
        if isinstance(expr, ast.QualifiedCall):
            return self._check_qualified_call(expr)
        if isinstance(expr, ast.ModuleCall):
            return self._check_module_call(expr)
        if isinstance(expr, ast.IfExpr):
            return self._check_if(expr, expected=expected)
        if isinstance(expr, ast.MatchExpr):
            return self._check_match(expr, expected=expected)
        if isinstance(expr, ast.Block):
            return self._check_block(expr, expected=expected)
        if isinstance(expr, ast.AnonFn):
            return self._check_anon_fn(expr)
        if isinstance(expr, ast.HandleExpr):
            return self._check_handle(expr)
        if isinstance(expr, ast.ArrayLit):
            return self._check_array_lit(expr)
        if isinstance(expr, ast.AssertExpr):
            return self._check_assert(expr)
        if isinstance(expr, ast.AssumeExpr):
            return self._check_assume(expr)
        if isinstance(expr, ast.ForallExpr):
            return self._check_forall_expr(expr)
        if isinstance(expr, ast.ExistsExpr):
            return self._check_exists_expr(expr)
        if isinstance(expr, ast.OldExpr):
            return self._check_old_expr(expr)
        if isinstance(expr, ast.NewExpr):
            return self._check_new_expr(expr)
        self._error(expr, f"Unknown expression type: {type(expr).__name__}", error_code="E176")
        return None

    # -----------------------------------------------------------------
    # Slot references
    # -----------------------------------------------------------------

    def _check_slot_ref(self, ref: ast.SlotRef) -> Type | None:
        """Type-check @T.n slot reference."""
        tname = self._slot_type_name(ref.type_name, ref.type_args)
        resolved = self.env.resolve_slot(tname, ref.index)
        if resolved is None:
            count = self.env.count_bindings(tname)
            self._error(
                ref,
                f"Cannot resolve @{tname}.{ref.index}: "
                f"only {count} {tname} binding(s) in scope "
                f"(valid indices: 0..{count - 1})."
                if count > 0
                else f"Cannot resolve @{tname}.{ref.index}: "
                     f"no {tname} bindings in scope.",
                rationale=f"Slot reference @{tname}.{ref.index} requires at "
                          f"least {ref.index + 1} binding(s) of type {tname}.",
                fix=f"Ensure enough {tname} bindings are in scope, or use a "
                    f"lower index.",
                spec_ref='Chapter 3, Section 3.4 "Reference Resolution"',
                error_code="E130",
            )
            return UnknownType()
        return resolved

    def _check_result_ref(self, ref: ast.ResultRef) -> Type | None:
        """Type-check @T.result reference."""
        if not self.env.in_ensures:
            self._error(
                ref,
                f"@{ref.type_name}.result is only valid inside ensures() "
                f"clauses.",
                rationale="The @T.result reference refers to a function's "
                          "return value, which is only meaningful in "
                          "postcondition context.",
                fix="Move the @T.result reference inside an ensures() clause.",
                spec_ref='Chapter 3, Section 3.6 "The @result Reference"',
                error_code="E131",
            )
            return UnknownType()

        ret = self.env.current_return_type
        if ret is None:
            return UnknownType()
        return ret

    # -----------------------------------------------------------------
    # Binary operators
    # -----------------------------------------------------------------

    def _check_binary(self, expr: ast.BinaryExpr) -> Type | None:
        """Type-check a binary operator expression."""
        # Pipe is special
        if expr.op == ast.BinOp.PIPE:
            return self._check_pipe(expr)

        left_ty = self._synth_expr(expr.left)
        right_ty = self._synth_expr(expr.right)
        if left_ty is None or right_ty is None:
            return None
        if isinstance(left_ty, UnknownType) or isinstance(right_ty, UnknownType):
            return UnknownType()

        op = expr.op

        # Arithmetic: +, -, *, /, %
        if op in (ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
                  ast.BinOp.DIV, ast.BinOp.MOD):
            left_base = base_type(left_ty)
            right_base = base_type(right_ty)
            if left_base not in NUMERIC_TYPES or right_base not in NUMERIC_TYPES:
                self._error(
                    expr,
                    f"Operator '{op.value}' requires numeric operands, found "
                    f"{pretty_type(left_ty)} and {pretty_type(right_ty)}.",
                    rationale="Arithmetic operators work on Int, Nat, or "
                              "Float64.",
                    spec_ref='Chapter 4, Section 4.3 "Operators"',
                    error_code="E140",
                )
                return UnknownType()
            # Allow Nat+Int => Int, etc. Result is the more general type.
            if is_subtype(left_base, right_base):
                return right_base
            if is_subtype(right_base, left_base):
                return left_base
            self._error(
                expr,
                f"Operator '{op.value}' requires matching numeric types, "
                f"found {pretty_type(left_ty)} and {pretty_type(right_ty)}.",
                rationale="Both operands must be the same numeric type "
                          "(or Nat where Int is expected).",
                spec_ref='Chapter 4, Section 4.3 "Operators"',
                error_code="E141",
            )
            return UnknownType()

        # Comparison: ==, !=, <, >, <=, >=
        if op in (ast.BinOp.EQ, ast.BinOp.NEQ):
            left_base = base_type(left_ty)
            right_base = base_type(right_ty)
            if not (is_subtype(left_base, right_base)
                    or is_subtype(right_base, left_base)):
                self._error(
                    expr,
                    f"Cannot compare {pretty_type(left_ty)} with "
                    f"{pretty_type(right_ty)}.",
                    rationale="Equality comparison requires compatible types.",
                    spec_ref='Chapter 4, Section 4.3 "Operators"',
                    error_code="E142",
                )
            return BOOL

        if op in (ast.BinOp.LT, ast.BinOp.GT, ast.BinOp.LE, ast.BinOp.GE):
            left_base = base_type(left_ty)
            right_base = base_type(right_ty)
            if (left_base not in ORDERABLE_TYPES
                    or right_base not in ORDERABLE_TYPES):
                self._error(
                    expr,
                    f"Operator '{op.value}' requires orderable operands, "
                    f"found {pretty_type(left_ty)} and "
                    f"{pretty_type(right_ty)}.",
                    spec_ref='Chapter 4, Section 4.3 "Operators"',
                    error_code="E143",
                )
            return BOOL

        # Logical: &&, ||, ==>
        if op in (ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES):
            left_base = base_type(left_ty)
            right_base = base_type(right_ty)
            if not is_subtype(left_base, BOOL):
                self._error(
                    expr,
                    f"Left operand of '{op.value}' must be Bool, found "
                    f"{pretty_type(left_ty)}.",
                    spec_ref='Chapter 4, Section 4.3 "Operators"',
                    error_code="E144",
                )
            if not is_subtype(right_base, BOOL):
                self._error(
                    expr,
                    f"Right operand of '{op.value}' must be Bool, found "
                    f"{pretty_type(right_ty)}.",
                    spec_ref='Chapter 4, Section 4.3 "Operators"',
                    error_code="E145",
                )
            return BOOL

        return UnknownType()

    def _check_pipe(self, expr: ast.BinaryExpr) -> Type | None:
        """Type-check pipe: left |> right (right must be a FnCall)."""
        left_ty = self._synth_expr(expr.left)
        if left_ty is None:
            return None

        # The right side should be a FnCall — prepend left as first arg
        if isinstance(expr.right, ast.FnCall):
            # Create a virtual call with left prepended
            all_args = (expr.left,) + expr.right.args
            return self._check_call_with_args(
                expr.right.name, all_args, expr.right)
        # Fallback: just synth the right side
        return self._synth_expr(expr.right)

    # -----------------------------------------------------------------
    # Unary operators
    # -----------------------------------------------------------------

    def _check_unary(self, expr: ast.UnaryExpr) -> Type | None:
        """Type-check a unary operator expression."""
        operand_ty = self._synth_expr(expr.operand)
        if operand_ty is None:
            return None
        if isinstance(operand_ty, UnknownType):
            return UnknownType()

        operand_base = base_type(operand_ty)

        if expr.op == ast.UnaryOp.NOT:
            if not is_subtype(operand_base, BOOL):
                self._error(
                    expr,
                    f"Operator '!' requires Bool operand, found "
                    f"{pretty_type(operand_ty)}.",
                    spec_ref='Chapter 4, Section 4.3 "Operators"',
                    error_code="E146",
                )
            return BOOL

        if expr.op == ast.UnaryOp.NEG:
            if operand_base not in NUMERIC_TYPES:
                self._error(
                    expr,
                    f"Operator '-' requires numeric operand, found "
                    f"{pretty_type(operand_ty)}.",
                    spec_ref='Chapter 4, Section 4.3 "Operators"',
                    error_code="E147",
                )
                return UnknownType()
            # Negating Nat produces Int (may go negative)
            if types_equal(operand_base, NAT):
                return INT
            return operand_base

        return UnknownType()

    # -----------------------------------------------------------------
    # Index
    # -----------------------------------------------------------------

    def _check_index(self, expr: ast.IndexExpr) -> Type | None:
        """Type-check array index: collection[index]."""
        coll_ty = self._synth_expr(expr.collection)
        idx_ty = self._synth_expr(expr.index)
        if coll_ty is None or idx_ty is None:
            return None
        if isinstance(coll_ty, UnknownType):
            return UnknownType()

        coll_base = base_type(coll_ty)

        # Must be Array<T>
        if isinstance(coll_base, AdtType) and coll_base.name == "Array":
            if coll_base.type_args:
                elem_type = coll_base.type_args[0]
            else:
                elem_type = UnknownType()

            # Index must be Int or Nat
            if idx_ty and not isinstance(idx_ty, UnknownType):
                idx_base = base_type(idx_ty)
                if not is_subtype(idx_base, INT):
                    self._error(
                        expr.index,
                        f"Array index must be Int or Nat, found "
                        f"{pretty_type(idx_ty)}.",
                        spec_ref='Chapter 4, Section 4.4 "Array Access"',
                        error_code="E160",
                    )
            return elem_type

        self._error(
            expr.collection,
            f"Cannot index {pretty_type(coll_ty)}: indexing requires "
            f"Array<T>.",
            spec_ref='Chapter 4, Section 4.4 "Array Access"',
            error_code="E161",
        )
        return UnknownType()

    # -----------------------------------------------------------------
    # Blocks and statements
    # -----------------------------------------------------------------

    def _check_block(self, block: ast.Block, *,
                     expected: Type | None = None) -> Type | None:
        """Type-check a block expression."""
        self.env.push_scope()
        for stmt in block.statements:
            self._check_stmt(stmt)
        result = self._synth_expr(block.expr, expected=expected)
        self.env.pop_scope()
        return result

    def _check_stmt(self, stmt: ast.Stmt) -> None:
        """Type-check a statement."""
        if isinstance(stmt, ast.LetStmt):
            self._check_let(stmt)
        elif isinstance(stmt, ast.LetDestruct):
            self._check_let_destruct(stmt)
        elif isinstance(stmt, ast.ExprStmt):
            self._synth_expr(stmt.expr)

    def _check_let(self, stmt: ast.LetStmt) -> None:
        """Type-check a let binding."""
        declared_type = self._resolve_type(stmt.type_expr)
        val_type = self._synth_expr(stmt.value, expected=declared_type)

        if val_type and not isinstance(val_type, UnknownType):
            if not isinstance(declared_type, UnknownType):
                if not is_subtype(val_type, declared_type):
                    self._error(
                        stmt.value,
                        f"Let binding expects {pretty_type(declared_type)}, "
                        f"value has type {pretty_type(val_type)}.",
                        spec_ref='Chapter 4, Section 4.5 "Let Bindings"',
                        error_code="E170",
                    )

        tname = self._type_expr_to_slot_name(stmt.type_expr)
        self.env.bind(tname, declared_type, "let")

    def _check_let_destruct(self, stmt: ast.LetDestruct) -> None:
        """Type-check a destructuring let."""
        val_type = self._synth_expr(stmt.value)

        for te in stmt.type_bindings:
            resolved = self._resolve_type(te)
            tname = self._type_expr_to_slot_name(te)
            self.env.bind(tname, resolved, "destruct")

    # -----------------------------------------------------------------
    # Anonymous functions
    # -----------------------------------------------------------------

    def _check_anon_fn(self, expr: ast.AnonFn) -> Type | None:
        """Type-check an anonymous function."""
        param_types = tuple(self._resolve_type(p) for p in expr.params)
        ret_type = self._resolve_type(expr.return_type)
        eff = self._resolve_effect_row(expr.effect)

        self.env.push_scope()
        for param_te, param_ty in zip(expr.params, param_types):
            tname = self._type_expr_to_slot_name(param_te)
            self.env.bind(tname, param_ty, "param")

        body_type = self._synth_expr(expr.body, expected=ret_type)
        self.env.pop_scope()

        if body_type and not isinstance(body_type, UnknownType):
            if not is_subtype(body_type, ret_type):
                self._error(
                    expr.body,
                    f"Anonymous function body has type "
                    f"{pretty_type(body_type)}, expected "
                    f"{pretty_type(ret_type)}.",
                    spec_ref='Chapter 5, Section 5.7 "Anonymous Functions"',
                    error_code="E171",
                )

        return FunctionType(param_types, ret_type, eff)

    # -----------------------------------------------------------------
    # Arrays
    # -----------------------------------------------------------------

    def _check_array_lit(self, expr: ast.ArrayLit) -> Type | None:
        """Type-check an array literal."""
        if not expr.elements:
            return AdtType("Array", (UnknownType(),))

        elem_types: list[Type | None] = []
        for elem in expr.elements:
            elem_types.append(self._synth_expr(elem))

        first = None
        for et in elem_types:
            if et and not isinstance(et, UnknownType):
                first = et
                break

        if first is None:
            return AdtType("Array", (UnknownType(),))

        return AdtType("Array", (first,))

    # -----------------------------------------------------------------
    # Assert / Assume
    # -----------------------------------------------------------------

    def _check_assert(self, expr: ast.AssertExpr) -> Type | None:
        """Type-check assert(expr)."""
        ty = self._synth_expr(expr.expr)
        if ty and not isinstance(ty, UnknownType):
            if not is_subtype(base_type(ty), BOOL):
                self._error(
                    expr.expr,
                    f"assert() requires Bool, found {pretty_type(ty)}.",
                    spec_ref='Chapter 6, Section 6.2.5 "Assertions"',
                    error_code="E172",
                )
        return UNIT

    def _check_assume(self, expr: ast.AssumeExpr) -> Type | None:
        """Type-check assume(expr)."""
        ty = self._synth_expr(expr.expr)
        if ty and not isinstance(ty, UnknownType):
            if not is_subtype(base_type(ty), BOOL):
                self._error(
                    expr.expr,
                    f"assume() requires Bool, found {pretty_type(ty)}.",
                    spec_ref='Chapter 6, Section 6.2.6 "Assumptions"',
                    error_code="E173",
                )
        return UNIT

    # -----------------------------------------------------------------
    # Quantifiers
    # -----------------------------------------------------------------

    def _check_forall_expr(self, expr: ast.ForallExpr) -> Type | None:
        """Type-check forall(type, domain, predicate)."""
        self._resolve_type(expr.binding_type)
        self._synth_expr(expr.domain)
        self._synth_expr(expr.predicate)
        return BOOL

    def _check_exists_expr(self, expr: ast.ExistsExpr) -> Type | None:
        """Type-check exists(type, domain, predicate)."""
        self._resolve_type(expr.binding_type)
        self._synth_expr(expr.domain)
        self._synth_expr(expr.predicate)
        return BOOL

    # -----------------------------------------------------------------
    # Old / New (contract expressions)
    # -----------------------------------------------------------------

    def _check_old_expr(self, expr: ast.OldExpr) -> Type | None:
        """Type-check old(EffectRef) — state before effect execution."""
        if not self.env.in_ensures:
            self._error(
                expr,
                "old() is only valid inside ensures() clauses.",
                spec_ref='Chapter 7, Section 7.9 "Effect-Contract Interaction"',
                error_code="E174",
            )
        ei = self._resolve_effect_ref(expr.effect_ref)
        if ei:
            return self._effect_state_type(ei)
        return UnknownType()

    def _check_new_expr(self, expr: ast.NewExpr) -> Type | None:
        """Type-check new(EffectRef) — state after effect execution."""
        if not self.env.in_ensures:
            self._error(
                expr,
                "new() is only valid inside ensures() clauses.",
                spec_ref='Chapter 7, Section 7.9 "Effect-Contract Interaction"',
                error_code="E175",
            )
        ei = self._resolve_effect_ref(expr.effect_ref)
        if ei:
            return self._effect_state_type(ei)
        return UnknownType()

    def _effect_state_type(self, ei: EffectInstance) -> Type:
        """Get the state type of a State-like effect."""
        if ei.name == "State" and ei.type_args:
            return ei.type_args[0]
        # For other effects, return Unknown
        return UnknownType()
