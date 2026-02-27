"""Vera type checker — Tier 1 decidable type checking.

Validates expression types, slot reference resolution, effect annotations,
and contract well-formedness.  Consumes Program AST nodes from parse_to_ast()
and produces a list of Diagnostic errors (empty = success).

Refinement predicate verification and contract satisfiability are handled
by the contract verifier (vera/verifier.py) via Z3.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from vera.resolver import ResolvedModule

from vera import ast
from vera.errors import Diagnostic, SourceLocation
from vera.environment import (
    AdtInfo,
    Binding,
    ConstructorInfo,
    EffectInfo,
    FunctionInfo,
    OpInfo,
    TypeAliasInfo,
    TypeEnv,
)
from vera.types import (
    BOOL,
    FLOAT64,
    INT,
    NAT,
    NEVER,
    NUMERIC_TYPES,
    ORDERABLE_TYPES,
    PRIMITIVES,
    STRING,
    UNIT,
    AdtType,
    ConcreteEffectRow,
    EffectInstance,
    EffectRowType,
    FunctionType,
    PrimitiveType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    base_type,
    canonical_type_name,
    is_subtype,
    pretty_effect,
    pretty_type,
    substitute,
    substitute_effect,
    types_equal,
)


# =====================================================================
# Public API
# =====================================================================

def typecheck(
    program: ast.Program,
    source: str = "",
    file: str | None = None,
    resolved_modules: list[ResolvedModule] | None = None,
) -> list[Diagnostic]:
    """Type-check a Vera Program AST.

    Returns a list of Diagnostics (empty = no errors).

    *resolved_modules* — modules resolved from ``import`` declarations
    (see :class:`~vera.resolver.ModuleResolver`).  Used in C7a to
    improve diagnostics for cross-module calls; actual type merging
    is deferred to C7b.
    """
    checker = TypeChecker(
        source=source, file=file, resolved_modules=resolved_modules,
    )
    checker.check_program(program)
    return checker.errors


# =====================================================================
# Type checker
# =====================================================================

class TypeChecker:
    """Top-down type checker with error accumulation."""

    def __init__(
        self,
        source: str = "",
        file: str | None = None,
        resolved_modules: list[ResolvedModule] | None = None,
    ) -> None:
        self.env = TypeEnv()
        self.errors: list[Diagnostic] = []
        self.source = source
        self.file = file
        self._effect_ops_used: set[str] = set()
        # Resolved module paths for improved diagnostics (C7a).
        # Actual type merging is deferred to C7b.
        self._resolved_module_paths: set[tuple[str, ...]] = {
            m.path for m in (resolved_modules or [])
        }

    # -----------------------------------------------------------------
    # Diagnostics
    # -----------------------------------------------------------------

    def _error(self, node: ast.Node, description: str, *,
               rationale: str = "", fix: str = "",
               spec_ref: str = "", severity: str = "error") -> None:
        """Record a type error diagnostic."""
        loc = SourceLocation(file=self.file)
        if node.span:
            loc.line = node.span.line
            loc.column = node.span.column
        self.errors.append(Diagnostic(
            description=description,
            location=loc,
            source_line=self._source_line(node),
            rationale=rationale,
            fix=fix,
            spec_ref=spec_ref,
            severity=severity,
        ))

    def _source_line(self, node: ast.Node) -> str:
        """Extract source line for a node."""
        if not node.span or not self.source:
            return ""
        lines = self.source.splitlines()
        idx = node.span.line - 1
        if 0 <= idx < len(lines):
            return lines[idx]
        return ""

    # -----------------------------------------------------------------
    # Type resolution: AST TypeExpr -> semantic Type
    # -----------------------------------------------------------------

    def _resolve_type(self, te: ast.TypeExpr) -> Type:
        """Convert an AST TypeExpr into a resolved semantic Type."""
        if isinstance(te, ast.NamedType):
            return self._resolve_named_type(te)
        if isinstance(te, ast.FnType):
            params = tuple(self._resolve_type(p) for p in te.params)
            ret = self._resolve_type(te.return_type)
            eff = self._resolve_effect_row(te.effect)
            return FunctionType(params, ret, eff)
        if isinstance(te, ast.RefinementType):
            base = self._resolve_type(te.base_type)
            return RefinedType(base, te.predicate)
        return UnknownType()

    def _resolve_named_type(self, te: ast.NamedType) -> Type:
        """Resolve a named type (possibly parameterised)."""
        name = te.name

        # Type variable?
        if name in self.env.type_params:
            return self.env.type_params[name]

        # Primitive?
        if name in PRIMITIVES and not te.type_args:
            return PRIMITIVES[name]

        # Type alias?
        alias = self.env.type_aliases.get(name)
        if alias:
            if te.type_args and alias.type_params:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                mapping = dict(zip(alias.type_params, args))
                return substitute(alias.resolved_type, mapping)
            return alias.resolved_type

        # ADT or parameterised built-in?
        adt = self.env.data_types.get(name)
        if adt is not None:
            if te.type_args:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                return AdtType(name, args)
            return AdtType(name, ())

        # Array, Tuple (always parameterised)
        if name in ("Array", "Tuple"):
            if te.type_args:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                return AdtType(name, args)
            return AdtType(name, ())

        # Unknown — might be a type from an unresolved import
        return AdtType(name, tuple(
            self._resolve_type(a) for a in te.type_args
        ) if te.type_args else ())

    def _resolve_effect_row(self, er: ast.EffectRow) -> EffectRowType:
        """Convert an AST EffectRow into a semantic EffectRowType."""
        if isinstance(er, ast.PureEffect):
            return PureEffectRow()
        if isinstance(er, ast.EffectSet):
            instances = []
            row_var = None
            for ref in er.effects:
                if isinstance(ref, ast.EffectRef):
                    # Check if it's a type variable (effect polymorphism)
                    if ref.name in self.env.type_params:
                        row_var = ref.name
                        continue
                    args = tuple(
                        self._resolve_type(a) for a in ref.type_args
                    ) if ref.type_args else ()
                    instances.append(EffectInstance(ref.name, args))
                elif isinstance(ref, ast.QualifiedEffectRef):
                    args = tuple(
                        self._resolve_type(a) for a in ref.type_args
                    ) if ref.type_args else ()
                    instances.append(
                        EffectInstance(f"{ref.module}.{ref.name}", args))
            return ConcreteEffectRow(frozenset(instances), row_var)
        return PureEffectRow()

    def _resolve_effect_ref(self, ref: ast.EffectRefNode) -> EffectInstance | None:
        """Resolve a single effect reference."""
        if isinstance(ref, ast.EffectRef):
            args = tuple(
                self._resolve_type(a) for a in ref.type_args
            ) if ref.type_args else ()
            return EffectInstance(ref.name, args)
        if isinstance(ref, ast.QualifiedEffectRef):
            args = tuple(
                self._resolve_type(a) for a in ref.type_args
            ) if ref.type_args else ()
            return EffectInstance(f"{ref.module}.{ref.name}", args)
        return None

    # -----------------------------------------------------------------
    # Canonical type name for slot references
    # -----------------------------------------------------------------

    def _slot_type_name(self, type_name: str,
                        type_args: tuple[ast.TypeExpr, ...] | None) -> str:
        """Form the canonical type name for slot reference matching."""
        if not type_args:
            return type_name
        resolved = tuple(self._resolve_type(a) for a in type_args)
        return canonical_type_name(type_name, resolved)

    # -----------------------------------------------------------------
    # Pass 1: Registration
    # -----------------------------------------------------------------

    def _register_all(self, program: ast.Program) -> None:
        """Register all top-level declarations (forward reference support)."""
        for tld in program.declarations:
            self._register_decl(tld.decl)

    def _register_decl(self, decl: ast.Decl) -> None:
        """Register a single declaration's signature."""
        if isinstance(decl, ast.DataDecl):
            self._register_data(decl)
        elif isinstance(decl, ast.TypeAliasDecl):
            self._register_alias(decl)
        elif isinstance(decl, ast.EffectDecl):
            self._register_effect(decl)
        elif isinstance(decl, ast.FnDecl):
            self._register_fn(decl)

    def _register_data(self, decl: ast.DataDecl) -> None:
        """Register an ADT and its constructors."""
        # Set up type params for resolving constructor field types
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ctors: dict[str, ConstructorInfo] = {}
        for ctor in decl.constructors:
            field_types = None
            if ctor.fields is not None:
                field_types = tuple(
                    self._resolve_type(f) for f in ctor.fields)
            ci = ConstructorInfo(
                name=ctor.name,
                parent_type=decl.name,
                parent_type_params=decl.type_params,
                field_types=field_types,
            )
            ctors[ctor.name] = ci
            self.env.constructors[ctor.name] = ci

        self.env.data_types[decl.name] = AdtInfo(
            name=decl.name,
            type_params=decl.type_params,
            constructors=ctors,
        )

        self.env.type_params = saved_params

    def _register_alias(self, decl: ast.TypeAliasDecl) -> None:
        """Register a type alias."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        resolved = self._resolve_type(decl.type_expr)
        self.env.type_aliases[decl.name] = TypeAliasInfo(
            name=decl.name,
            type_params=decl.type_params,
            resolved_type=resolved,
        )

        self.env.type_params = saved_params

    def _register_effect(self, decl: ast.EffectDecl) -> None:
        """Register an effect and its operations."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ops: dict[str, OpInfo] = {}
        for op in decl.operations:
            param_types = tuple(self._resolve_type(p) for p in op.param_types)
            ret_type = self._resolve_type(op.return_type)
            ops[op.name] = OpInfo(
                name=op.name,
                param_types=param_types,
                return_type=ret_type,
                parent_effect=decl.name,
            )

        self.env.effects[decl.name] = EffectInfo(
            name=decl.name,
            type_params=decl.type_params,
            operations=ops,
        )

        self.env.type_params = saved_params

    def _register_fn(self, decl: ast.FnDecl) -> None:
        """Register a function signature."""
        from vera.registration import register_fn
        register_fn(
            self.env, decl,
            self._resolve_type, self._resolve_effect_row,
        )

    # -----------------------------------------------------------------
    # Pass 2: Checking
    # -----------------------------------------------------------------

    def check_program(self, program: ast.Program) -> None:
        """Entry point: register all declarations, then check each."""
        self._register_all(program)
        for tld in program.declarations:
            self._check_decl(tld.decl)

    def _check_decl(self, decl: ast.Decl) -> None:
        """Check a single declaration."""
        if isinstance(decl, ast.FnDecl):
            self._check_fn(decl)
        elif isinstance(decl, ast.DataDecl):
            self._check_data(decl)
        # TypeAliasDecl and EffectDecl are validated during registration

    def _check_data(self, decl: ast.DataDecl) -> None:
        """Check an ADT declaration (invariant well-formedness)."""
        if decl.invariant is not None:
            # Push scope with constructor bindings for invariant checking
            self.env.push_scope()
            saved_params = dict(self.env.type_params)
            if decl.type_params:
                for tv in decl.type_params:
                    self.env.type_params[tv] = TypeVar(tv)

            inv_type = self._synth_expr(decl.invariant)
            if inv_type and not is_subtype(inv_type, BOOL):
                self._error(
                    decl.invariant,
                    f"Invariant must be Bool, found {pretty_type(inv_type)}.",
                    rationale="Data type invariants are predicates that must "
                              "evaluate to Bool.",
                    spec_ref='Chapter 2, Section 2.5 "Algebraic Data Types"',
                )

            self.env.type_params = saved_params
            self.env.pop_scope()

    def _check_fn(self, decl: ast.FnDecl) -> None:
        """Check a function declaration."""
        saved_params = dict(self.env.type_params)
        saved_return = self.env.current_return_type
        saved_effect = self.env.current_effect_row

        # 1. Bind forall type parameters
        if decl.forall_vars:
            for tv in decl.forall_vars:
                self.env.type_params[tv] = TypeVar(tv)

        # 2. Resolve parameter and return types
        param_types = tuple(self._resolve_type(p) for p in decl.params)
        return_type = self._resolve_type(decl.return_type)
        effect_row = self._resolve_effect_row(decl.effect)

        # 3. Set context
        self.env.current_return_type = return_type
        self.env.current_effect_row = effect_row
        self._effect_ops_used = set()

        # 4. Push scope and bind parameters
        self.env.push_scope()
        for i, (param_te, param_ty) in enumerate(
                zip(decl.params, param_types)):
            tname = self._type_expr_to_slot_name(param_te)
            self.env.bind(tname, param_ty, "param")

        # 5. Check contracts
        for contract in decl.contracts:
            self._check_contract(contract, decl)

        # 6. Check body
        body_type = self._synth_expr(decl.body)
        if body_type and not isinstance(body_type, UnknownType):
            if not is_subtype(body_type, return_type):
                self._error(
                    decl.body,
                    f"Function '{decl.name}' body has type "
                    f"{pretty_type(body_type)}, expected "
                    f"{pretty_type(return_type)}.",
                    rationale="The function body's type must match the "
                              "declared return type.",
                    fix=f"Change the return type or adjust the body "
                        f"expression.",
                    spec_ref='Chapter 5, Section 5.1 "Function Declarations"',
                )

        # 7. Check effect compliance (basic)
        if isinstance(effect_row, PureEffectRow) and self._effect_ops_used:
            ops_str = ", ".join(sorted(self._effect_ops_used))
            self._error(
                decl,
                f"Pure function '{decl.name}' performs effect operations: "
                f"{ops_str}.",
                rationale="Functions declared with effects(pure) cannot "
                          "call effect operations.",
                fix=f"Declare the appropriate effects, e.g. "
                    f"effects(<{next(iter(self._effect_ops_used), '...')}>).",
                spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
            )

        # 8. Check where-block functions
        if decl.where_fns:
            for wfn in decl.where_fns:
                self._check_fn(wfn)

        # 9. Restore context
        self.env.pop_scope()
        self.env.type_params = saved_params
        self.env.current_return_type = saved_return
        self.env.current_effect_row = saved_effect

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str:
        """Extract the canonical slot name from a type expression used as a
        parameter binding.  This is the syntactic name — aliases are opaque."""
        if isinstance(te, ast.NamedType):
            if te.type_args:
                resolved_args = tuple(
                    self._resolve_type(a) for a in te.type_args)
                return canonical_type_name(te.name, resolved_args)
            return te.name
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_slot_name(te.base_type)
        if isinstance(te, ast.FnType):
            # Function-typed parameters: use a synthetic name
            return "Fn"
        return "?"

    # -----------------------------------------------------------------
    # Contracts
    # -----------------------------------------------------------------

    def _check_contract(self, contract: ast.Contract,
                        fn: ast.FnDecl) -> None:
        """Check a contract clause for well-formedness."""
        if isinstance(contract, ast.Requires):
            self.env.in_contract = True
            ty = self._synth_expr(contract.expr)
            self.env.in_contract = False
            if ty and not is_subtype(ty, BOOL):
                self._error(
                    contract.expr,
                    f"requires() predicate must be Bool, found "
                    f"{pretty_type(ty)}.",
                    rationale="Contract predicates must evaluate to Bool.",
                    spec_ref='Chapter 6, Section 6.2 "Preconditions"',
                )

        elif isinstance(contract, ast.Ensures):
            self.env.in_ensures = True
            self.env.in_contract = True
            ty = self._synth_expr(contract.expr)
            self.env.in_ensures = False
            self.env.in_contract = False
            if ty and not is_subtype(ty, BOOL):
                self._error(
                    contract.expr,
                    f"ensures() predicate must be Bool, found "
                    f"{pretty_type(ty)}.",
                    rationale="Contract predicates must evaluate to Bool.",
                    spec_ref='Chapter 6, Section 6.3 "Postconditions"',
                )

        elif isinstance(contract, ast.Decreases):
            self.env.in_contract = True
            for expr in contract.exprs:
                ty = self._synth_expr(expr)
                # Type is checked; termination verification is Tier 3
            self.env.in_contract = False

    # -----------------------------------------------------------------
    # Expression type synthesis
    # -----------------------------------------------------------------

    def _synth_expr(self, expr: ast.Expr) -> Type | None:
        """Synthesise the type of an expression.  Returns None on error."""
        if isinstance(expr, ast.IntLit):
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
            return self._check_constructor_call(expr)
        if isinstance(expr, ast.NullaryConstructor):
            return self._check_nullary_constructor(expr)
        if isinstance(expr, ast.QualifiedCall):
            return self._check_qualified_call(expr)
        if isinstance(expr, ast.ModuleCall):
            return self._check_module_call(expr)
        if isinstance(expr, ast.IfExpr):
            return self._check_if(expr)
        if isinstance(expr, ast.MatchExpr):
            return self._check_match(expr)
        if isinstance(expr, ast.Block):
            return self._check_block(expr)
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
        self._error(expr, f"Unknown expression type: {type(expr).__name__}")
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
                )
            if not is_subtype(right_base, BOOL):
                self._error(
                    expr,
                    f"Right operand of '{op.value}' must be Bool, found "
                    f"{pretty_type(right_ty)}.",
                    spec_ref='Chapter 4, Section 4.3 "Operators"',
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
                )
            return BOOL

        if expr.op == ast.UnaryOp.NEG:
            if operand_base not in NUMERIC_TYPES:
                self._error(
                    expr,
                    f"Operator '-' requires numeric operand, found "
                    f"{pretty_type(operand_ty)}.",
                    spec_ref='Chapter 4, Section 4.3 "Operators"',
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
                    )
            return elem_type

        self._error(
            expr.collection,
            f"Cannot index {pretty_type(coll_ty)}: indexing requires "
            f"Array<T>.",
            spec_ref='Chapter 4, Section 4.4 "Array Access"',
        )
        return UnknownType()

    # -----------------------------------------------------------------
    # Function calls
    # -----------------------------------------------------------------

    def _check_fn_call(self, expr: ast.FnCall) -> Type | None:
        """Type-check a function call."""
        return self._check_call_with_args(expr.name, expr.args, expr)

    def _check_call_with_args(self, name: str, args: tuple[ast.Expr, ...],
                              node: ast.Node) -> Type | None:
        """Check a call to function `name` with given arguments."""
        # Look up function
        fn_info = self.env.lookup_function(name)
        if fn_info:
            return self._check_fn_call_with_info(fn_info, args, node)

        # Maybe it's an effect operation
        op_info = self.env.lookup_effect_op(name)
        if op_info:
            self._effect_ops_used.add(op_info.parent_effect)
            return self._check_op_call(op_info, args, node)

        # Unresolved — emit warning and continue
        self._error(
            node,
            f"Unresolved function '{name}'.",
            rationale="The function is not defined in this file and may come "
                      "from an unresolved import.",
            severity="warning",
        )
        # Still synth arg types to find errors within them
        for arg in args:
            self._synth_expr(arg)
        return UnknownType()

    def _check_fn_call_with_info(self, fn_info: FunctionInfo,
                                 args: tuple[ast.Expr, ...],
                                 node: ast.Node) -> Type | None:
        """Check a call against a known function signature."""
        # Synth arg types
        arg_types: list[Type | None] = []
        for arg in args:
            arg_types.append(self._synth_expr(arg))

        # Arity check
        if len(args) != len(fn_info.param_types):
            self._error(
                node,
                f"Function '{fn_info.name}' expects {len(fn_info.param_types)}"
                f" argument(s), got {len(args)}.",
                spec_ref='Chapter 5, Section 5.1 "Function Declarations"',
            )
            return fn_info.return_type

        # Generic inference
        param_types = fn_info.param_types
        return_type = fn_info.return_type
        if fn_info.forall_vars:
            mapping = self._infer_type_args(
                fn_info.forall_vars, fn_info.param_types, arg_types)
            if mapping:
                param_types = tuple(
                    substitute(p, mapping) for p in param_types)
                return_type = substitute(return_type, mapping)

        # Check each argument
        for i, (arg_ty, param_ty) in enumerate(zip(arg_types, param_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            if not is_subtype(arg_ty, param_ty):
                self._error(
                    args[i],
                    f"Argument {i} of '{fn_info.name}' has type "
                    f"{pretty_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    spec_ref='Chapter 5, Section 5.1 "Function Declarations"',
                )

        # Track effects
        if not isinstance(fn_info.effect, PureEffectRow):
            if isinstance(fn_info.effect, ConcreteEffectRow):
                for ei in fn_info.effect.effects:
                    self._effect_ops_used.add(ei.name)

        return return_type

    def _check_op_call(self, op_info: OpInfo,
                       args: tuple[ast.Expr, ...],
                       node: ast.Node) -> Type | None:
        """Check a call to an effect operation."""
        arg_types: list[Type | None] = []
        for arg in args:
            arg_types.append(self._synth_expr(arg))

        # Resolve type params from current effect context
        mapping = self._effect_type_mapping(op_info.parent_effect)
        param_types = tuple(substitute(p, mapping) for p in op_info.param_types)
        return_type = substitute(op_info.return_type, mapping)

        if len(args) != len(param_types):
            self._error(
                node,
                f"Effect operation '{op_info.name}' expects "
                f"{len(param_types)} argument(s), got {len(args)}.",
            )
            return return_type

        for i, (arg_ty, param_ty) in enumerate(zip(arg_types, param_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            if not is_subtype(arg_ty, param_ty):
                self._error(
                    args[i],
                    f"Argument {i} of '{op_info.name}' has type "
                    f"{pretty_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                )

        return return_type

    def _effect_type_mapping(self, effect_name: str) -> dict[str, Type]:
        """Get the type argument mapping for an effect from the current
        effect row context."""
        if not isinstance(self.env.current_effect_row, ConcreteEffectRow):
            return {}
        for ei in self.env.current_effect_row.effects:
            if ei.name == effect_name:
                eff_info = self.env.lookup_effect(effect_name)
                if eff_info and eff_info.type_params and ei.type_args:
                    return dict(zip(eff_info.type_params, ei.type_args))
        return {}

    # -----------------------------------------------------------------
    # Constructors
    # -----------------------------------------------------------------

    def _check_constructor_call(self, expr: ast.ConstructorCall) -> Type | None:
        """Type-check a constructor call: Ctor(args)."""
        ci = self.env.lookup_constructor(expr.name)
        if ci is None:
            self._error(
                expr,
                f"Unknown constructor '{expr.name}'.",
                severity="warning",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # Synth arg types
        arg_types: list[Type | None] = []
        for arg in expr.args:
            arg_types.append(self._synth_expr(arg))

        if ci.field_types is None:
            if expr.args:
                self._error(
                    expr,
                    f"Constructor '{expr.name}' is nullary but was given "
                    f"{len(expr.args)} argument(s).",
                )
            return self._ctor_result_type(ci, arg_types)

        if len(expr.args) != len(ci.field_types):
            self._error(
                expr,
                f"Constructor '{expr.name}' expects "
                f"{len(ci.field_types)} field(s), got {len(expr.args)}.",
            )
            return self._ctor_result_type(ci, arg_types)

        # Infer type args for parameterised ADTs
        mapping = self._infer_ctor_type_args(ci, arg_types)
        field_types = ci.field_types
        if mapping:
            field_types = tuple(substitute(ft, mapping) for ft in field_types)

        for i, (arg_ty, field_ty) in enumerate(zip(arg_types, field_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(field_ty, (TypeVar, UnknownType)):
                continue
            if not is_subtype(arg_ty, field_ty):
                self._error(
                    expr.args[i],
                    f"Constructor '{expr.name}' field {i} has type "
                    f"{pretty_type(arg_ty)}, expected "
                    f"{pretty_type(field_ty)}.",
                )

        return self._ctor_result_type(ci, arg_types)

    def _check_nullary_constructor(self, expr: ast.NullaryConstructor) -> Type | None:
        """Type-check a nullary constructor: None, Nil, etc."""
        ci = self.env.lookup_constructor(expr.name)
        if ci is None:
            self._error(expr, f"Unknown constructor '{expr.name}'.",
                        severity="warning")
            return UnknownType()

        if ci.field_types is not None:
            self._error(
                expr,
                f"Constructor '{expr.name}' requires "
                f"{len(ci.field_types)} field(s) but was used as nullary.",
            )

        return self._ctor_result_type(ci, [])

    def _ctor_result_type(self, ci: ConstructorInfo,
                          arg_types: list[Type | None]) -> Type:
        """Compute the result type of a constructor call."""
        if ci.parent_type_params:
            # Try to infer type args from argument types
            mapping = self._infer_ctor_type_args(ci, arg_types)
            if mapping:
                args = tuple(
                    mapping.get(tv, TypeVar(tv))
                    for tv in ci.parent_type_params
                )
                return AdtType(ci.parent_type, args)
            # Leave as type vars
            return AdtType(ci.parent_type, tuple(
                TypeVar(tv) for tv in ci.parent_type_params))
        return AdtType(ci.parent_type, ())

    def _infer_ctor_type_args(self, ci: ConstructorInfo,
                              arg_types: list[Type | None]) -> dict[str, Type]:
        """Infer type arguments for a parameterised constructor."""
        if not ci.parent_type_params or not ci.field_types:
            return {}
        mapping: dict[str, Type] = {}
        for field_ty, arg_ty in zip(ci.field_types, arg_types):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            self._unify_for_inference(field_ty, arg_ty, mapping)
        return mapping

    # -----------------------------------------------------------------
    # Qualified / module calls
    # -----------------------------------------------------------------

    def _check_qualified_call(self, expr: ast.QualifiedCall) -> Type | None:
        """Type-check a qualified call: Effect.op(args)."""
        # Try as effect operation
        op_info = self.env.lookup_effect_op(expr.name, expr.qualifier)
        if op_info:
            self._effect_ops_used.add(op_info.parent_effect)
            return self._check_op_call(op_info, expr.args, expr)

        # Try as module-qualified function
        self._error(
            expr,
            f"Unresolved qualified call '{expr.qualifier}.{expr.name}'.",
            severity="warning",
        )
        for arg in expr.args:
            self._synth_expr(arg)
        return UnknownType()

    def _check_module_call(self, expr: ast.ModuleCall) -> Type | None:
        """Type-check a module call: path.to.fn(args)."""
        mod_path = tuple(expr.path)
        if mod_path in self._resolved_module_paths:
            # Module was resolved by the resolver (C7a) but cross-module
            # type merging is not yet implemented (C7b).
            self._error(
                expr,
                f"Module '{'.'.join(expr.path)}' resolved, but "
                f"cross-module type checking is not yet implemented "
                f"(C7b). Call to '{expr.name}' is unchecked.",
                severity="warning",
                rationale=(
                    "The module was found and parsed successfully. "
                    "Type merging across module boundaries will be "
                    "available in a future release (C7b)."
                ),
            )
        else:
            self._error(
                expr,
                f"Module '{'.'.join(expr.path)}' not found. "
                f"Cannot resolve call to '{expr.name}'.",
                severity="warning",
                rationale=(
                    "No module matching this import path was resolved. "
                    "Check that the file exists and is imported."
                ),
            )
        for arg in expr.args:
            self._synth_expr(arg)
        return UnknownType()

    # -----------------------------------------------------------------
    # Control flow
    # -----------------------------------------------------------------

    def _check_if(self, expr: ast.IfExpr) -> Type | None:
        """Type-check if-then-else."""
        cond_ty = self._synth_expr(expr.condition)
        if cond_ty and not isinstance(cond_ty, UnknownType):
            if not is_subtype(base_type(cond_ty), BOOL):
                self._error(
                    expr.condition,
                    f"If condition must be Bool, found "
                    f"{pretty_type(cond_ty)}.",
                    spec_ref='Chapter 4, Section 4.8 "Conditional Expressions"',
                )

        then_ty = self._synth_expr(expr.then_branch)
        else_ty = self._synth_expr(expr.else_branch)

        if then_ty is None or else_ty is None:
            return then_ty or else_ty
        if isinstance(then_ty, UnknownType):
            return else_ty
        if isinstance(else_ty, UnknownType):
            return then_ty

        # Never propagation
        if types_equal(then_ty, NEVER):
            return else_ty
        if types_equal(else_ty, NEVER):
            return then_ty

        # Branches must have compatible types
        if is_subtype(then_ty, else_ty):
            return else_ty
        if is_subtype(else_ty, then_ty):
            return then_ty

        self._error(
            expr,
            f"If branches have incompatible types: then-branch is "
            f"{pretty_type(then_ty)}, else-branch is "
            f"{pretty_type(else_ty)}.",
            rationale="Both branches of an if-expression must have "
                      "the same type.",
            spec_ref='Chapter 4, Section 4.8 "Conditional Expressions"',
        )
        return then_ty  # use then-branch type as best guess

    def _check_match(self, expr: ast.MatchExpr) -> Type | None:
        """Type-check a match expression."""
        scrutinee_ty = self._synth_expr(expr.scrutinee)
        if scrutinee_ty is None:
            return None

        result_type: Type | None = None
        for arm in expr.arms:
            # Check pattern and collect bindings
            bindings = self._check_pattern(arm.pattern, scrutinee_ty)

            # Push scope with pattern bindings
            self.env.push_scope()
            for b in bindings:
                self.env.bind(b.type_name, b.resolved_type, "match")

            # Synth arm body type
            arm_ty = self._synth_expr(arm.body)
            self.env.pop_scope()

            if arm_ty is None or isinstance(arm_ty, UnknownType):
                continue

            if result_type is None or isinstance(result_type, UnknownType):
                result_type = arm_ty
            elif types_equal(result_type, NEVER):
                result_type = arm_ty
            elif not types_equal(arm_ty, NEVER):
                if not (is_subtype(arm_ty, result_type)
                        or is_subtype(result_type, arm_ty)):
                    self._error(
                        arm.body if hasattr(arm, 'body') else expr,
                        f"Match arm type {pretty_type(arm_ty)} is "
                        f"incompatible with previous arm type "
                        f"{pretty_type(result_type)}.",
                        rationale="All match arms must have the same type.",
                        spec_ref='Chapter 4, Section 4.9 "Pattern Matching"',
                    )

        self._check_exhaustiveness(expr, scrutinee_ty)
        return result_type or UnknownType()

    def _check_exhaustiveness(
        self, expr: ast.MatchExpr, scrutinee_ty: Type
    ) -> None:
        """Check that match arms cover all possible values of the scrutinee.

        Spec Section 4.9.2: compiler MUST verify match is exhaustive.
        Spec Section 4.9.3: compiler SHOULD warn about unreachable arms.
        """
        raw_ty = base_type(scrutinee_ty)

        # --- Unreachable arm detection ---
        catch_all_idx: int | None = None
        for i, arm in enumerate(expr.arms):
            pat = arm.pattern
            if isinstance(pat, (ast.WildcardPattern, ast.BindingPattern)):
                catch_all_idx = i
                break

        if catch_all_idx is not None:
            # Warn about arms after the catch-all
            for j in range(catch_all_idx + 1, len(expr.arms)):
                self._error(
                    expr.arms[j].pattern,
                    "Unreachable match arm: pattern after catch-all "
                    "will never match.",
                    severity="warning",
                    rationale="A wildcard or binding pattern already "
                    "matches all remaining values.",
                    fix="Remove this arm or move it before the catch-all.",
                    spec_ref='Chapter 4, Section 4.9.3 "Unreachable Arms"',
                )
            return  # catch-all guarantees exhaustiveness

        # --- ADT exhaustiveness ---
        if isinstance(raw_ty, AdtType):
            adt_info = self.env.data_types.get(raw_ty.name)
            if adt_info is None:
                return  # unknown ADT, can't check
            all_ctors = set(adt_info.constructors.keys())
            covered: set[str] = set()
            for arm in expr.arms:
                pat = arm.pattern
                if isinstance(pat, ast.ConstructorPattern):
                    covered.add(pat.name)
                elif isinstance(pat, ast.NullaryPattern):
                    covered.add(pat.name)
            missing = sorted(all_ctors - covered)
            if missing:
                self._error(
                    expr,
                    f"Non-exhaustive match: missing patterns for "
                    f"{', '.join(missing)}.",
                    rationale="All constructors of the matched type "
                    "must be covered.",
                    fix="Add a wildcard '_' arm or cover all cases.",
                    spec_ref='Chapter 4, Section 4.9.2 '
                    '"Exhaustiveness Checking"',
                )
            return

        # --- Bool exhaustiveness ---
        if isinstance(raw_ty, PrimitiveType) and raw_ty.name == "Bool":
            covered_bools: set[bool] = set()
            for arm in expr.arms:
                pat = arm.pattern
                if isinstance(pat, ast.BoolPattern):
                    covered_bools.add(pat.value)
            missing_bools = []
            if True not in covered_bools:
                missing_bools.append("true")
            if False not in covered_bools:
                missing_bools.append("false")
            if missing_bools:
                self._error(
                    expr,
                    f"Non-exhaustive match: missing patterns for "
                    f"{', '.join(missing_bools)}.",
                    rationale="Bool matches must cover both true and false.",
                    fix="Add a wildcard '_' arm or cover all cases.",
                    spec_ref='Chapter 4, Section 4.9.2 '
                    '"Exhaustiveness Checking"',
                )
            return

        # --- Infinite types (Int, String, Float64, Nat, etc.) ---
        # No catch-all found and type has infinite domain → non-exhaustive
        self._error(
            expr,
            "Non-exhaustive match: type has infinite domain, "
            "a wildcard '_' or binding pattern is required.",
            rationale="Matches on types with infinite values cannot "
            "enumerate all cases.",
            fix="Add a wildcard '_' arm or a binding pattern.",
            spec_ref='Chapter 4, Section 4.9.2 '
            '"Exhaustiveness Checking"',
        )

    # -----------------------------------------------------------------
    # Patterns
    # -----------------------------------------------------------------

    def _check_pattern(self, pat: ast.Pattern,
                       expected: Type | None) -> list[Binding]:
        """Check a pattern against an expected type, return bindings."""
        if isinstance(pat, ast.ConstructorPattern):
            return self._check_ctor_pattern(pat, expected)
        if isinstance(pat, ast.NullaryPattern):
            return self._check_nullary_pattern(pat, expected)
        if isinstance(pat, ast.BindingPattern):
            return self._check_binding_pattern(pat, expected)
        if isinstance(pat, ast.WildcardPattern):
            return []
        if isinstance(pat, ast.IntPattern):
            return []
        if isinstance(pat, ast.StringPattern):
            return []
        if isinstance(pat, ast.BoolPattern):
            return []
        return []

    def _check_ctor_pattern(self, pat: ast.ConstructorPattern,
                            expected: Type | None) -> list[Binding]:
        """Check a constructor pattern."""
        ci = self.env.lookup_constructor(pat.name)
        if ci is None:
            self._error(pat, f"Unknown constructor '{pat.name}' in pattern.",
                        severity="warning")
            return []

        # Infer type args from expected type
        mapping: dict[str, Type] = {}
        if (isinstance(expected, AdtType) and ci.parent_type_params
                and expected.type_args):
            for tv, arg in zip(ci.parent_type_params, expected.type_args):
                mapping[tv] = arg

        field_types = ci.field_types or ()
        if mapping:
            field_types = tuple(substitute(ft, mapping) for ft in field_types)

        if len(pat.sub_patterns) != len(field_types):
            self._error(
                pat,
                f"Constructor '{pat.name}' has {len(field_types)} field(s), "
                f"pattern has {len(pat.sub_patterns)} sub-pattern(s).",
            )
            return []

        bindings: list[Binding] = []
        for sub_pat, field_ty in zip(pat.sub_patterns, field_types):
            bindings.extend(self._check_pattern(sub_pat, field_ty))
        return bindings

    def _check_nullary_pattern(self, pat: ast.NullaryPattern,
                               expected: Type | None) -> list[Binding]:
        """Check a nullary constructor pattern."""
        ci = self.env.lookup_constructor(pat.name)
        if ci is None:
            self._error(pat, f"Unknown constructor '{pat.name}' in pattern.",
                        severity="warning")
        return []

    def _check_binding_pattern(self, pat: ast.BindingPattern,
                               expected: Type | None) -> list[Binding]:
        """Check a binding pattern (@Type)."""
        resolved = self._resolve_type(pat.type_expr)
        tname = self._type_expr_to_slot_name(pat.type_expr)
        return [Binding(tname, resolved, "match")]

    # -----------------------------------------------------------------
    # Blocks and statements
    # -----------------------------------------------------------------

    def _check_block(self, block: ast.Block) -> Type | None:
        """Type-check a block expression."""
        self.env.push_scope()
        for stmt in block.statements:
            self._check_stmt(stmt)
        result = self._synth_expr(block.expr)
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
        val_type = self._synth_expr(stmt.value)

        if val_type and not isinstance(val_type, UnknownType):
            if not isinstance(declared_type, UnknownType):
                if not is_subtype(val_type, declared_type):
                    self._error(
                        stmt.value,
                        f"Let binding expects {pretty_type(declared_type)}, "
                        f"value has type {pretty_type(val_type)}.",
                        spec_ref='Chapter 4, Section 4.5 "Let Bindings"',
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

        body_type = self._synth_expr(expr.body)
        self.env.pop_scope()

        if body_type and not isinstance(body_type, UnknownType):
            if not is_subtype(body_type, ret_type):
                self._error(
                    expr.body,
                    f"Anonymous function body has type "
                    f"{pretty_type(body_type)}, expected "
                    f"{pretty_type(ret_type)}.",
                    spec_ref='Chapter 5, Section 5.7 "Anonymous Functions"',
                )

        return FunctionType(param_types, ret_type, eff)

    # -----------------------------------------------------------------
    # Handlers
    # -----------------------------------------------------------------

    def _check_handle(self, expr: ast.HandleExpr) -> Type | None:
        """Type-check a handler expression."""
        # Resolve the handled effect
        effect_inst = self._resolve_effect_ref(expr.effect)
        if effect_inst is None:
            return UnknownType()

        eff_info = self.env.lookup_effect(effect_inst.name)
        if eff_info is None:
            self._error(
                expr.effect,
                f"Unknown effect '{effect_inst.name}' in handler.",
            )
            return UnknownType()

        # Build type mapping for effect type params
        mapping: dict[str, Type] = {}
        if eff_info.type_params and effect_inst.type_args:
            mapping = dict(zip(eff_info.type_params, effect_inst.type_args))

        # Check handler state
        state_type: Type | None = None
        if expr.state:
            state_type = self._resolve_type(expr.state.type_expr)
            init_type = self._synth_expr(expr.state.init_expr)
            if init_type and not isinstance(init_type, UnknownType):
                if not is_subtype(init_type, state_type):
                    self._error(
                        expr.state.init_expr,
                        f"Handler state initial value has type "
                        f"{pretty_type(init_type)}, expected "
                        f"{pretty_type(state_type)}.",
                    )

        # Compute handler state canonical type name (for with-clause checks)
        state_tname_outer: str | None = None
        if state_type and expr.state:
            state_tname_outer = self._type_expr_to_slot_name(
                expr.state.type_expr)

        # Check handler clauses
        for clause in expr.clauses:
            op_info = eff_info.operations.get(clause.op_name)
            if op_info is None:
                self._error(
                    clause if hasattr(clause, 'span') else expr,
                    f"Effect '{eff_info.name}' has no operation "
                    f"'{clause.op_name}'.",
                )
                continue

            self.env.push_scope()
            # Bind operation parameters
            op_param_types = tuple(
                substitute(p, mapping) for p in op_info.param_types)
            for param_te, param_ty in zip(clause.params, op_param_types):
                tname = self._type_expr_to_slot_name(param_te)
                self.env.bind(tname, param_ty, "handler")

            # Bind handler state if present
            if state_type:
                state_tname = self._type_expr_to_slot_name(
                    expr.state.type_expr) if expr.state else "?"
                self.env.bind(state_tname, state_type, "handler")

            # Bind resume — takes the operation's return type, returns Unit.
            # resume is only available inside handler clause bodies.
            op_return_type = substitute(op_info.return_type, mapping)
            saved_resume = self.env.functions.get("resume")
            self.env.functions["resume"] = FunctionInfo(
                name="resume",
                forall_vars=None,
                param_types=(op_return_type,),
                return_type=UNIT,
                effect=PureEffectRow(),
            )

            self._synth_expr(clause.body)

            # Type-check with clause (state update) if present
            if clause.state_update is not None:
                upd_te, upd_expr = clause.state_update
                if state_type is None:
                    self._error(
                        clause,
                        "Handler clause has 'with' state update but "
                        "handler has no state declaration.",
                    )
                else:
                    upd_slot = self._type_expr_to_slot_name(upd_te)
                    if upd_slot != state_tname_outer:
                        self._error(
                            clause,
                            f"State update type '{upd_slot}' does not "
                            f"match handler state type "
                            f"'{state_tname_outer}'.",
                        )
                    upd_type = self._synth_expr(upd_expr)
                    if (upd_type and state_type
                            and not isinstance(upd_type, UnknownType)
                            and not is_subtype(upd_type, state_type)):
                        self._error(
                            upd_expr,
                            f"State update expression has type "
                            f"{pretty_type(upd_type)}, expected "
                            f"{pretty_type(state_type)}.",
                        )

            # Restore previous resume binding (if any)
            if saved_resume is not None:
                self.env.functions["resume"] = saved_resume
            else:
                del self.env.functions["resume"]

            self.env.pop_scope()

        # Check handler body — temporarily add handled effect to context
        # so effect operations resolve correctly inside the body
        saved_effect = self.env.current_effect_row
        saved_ops = self._effect_ops_used

        # Add the handled effect to the current effect row
        handler_effects = frozenset({effect_inst})
        if isinstance(self.env.current_effect_row, ConcreteEffectRow):
            handler_effects = handler_effects | self.env.current_effect_row.effects
            self.env.current_effect_row = ConcreteEffectRow(
                handler_effects, self.env.current_effect_row.row_var)
        else:
            self.env.current_effect_row = ConcreteEffectRow(handler_effects)

        # Track ops used inside handler body separately (they're discharged)
        self._effect_ops_used = set()

        # Bind handler state in handler body scope too
        if state_type and expr.state:
            self.env.push_scope()
            state_tname = self._type_expr_to_slot_name(expr.state.type_expr)
            self.env.bind(state_tname, state_type, "handler")

        body_type = self._synth_expr(expr.body)

        if state_type and expr.state:
            self.env.pop_scope()

        # Restore — the handler discharges its effect
        self.env.current_effect_row = saved_effect
        self._effect_ops_used = saved_ops

        return body_type

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
                    spec_ref='Chapter 6, Section 6.6 "Assertions"',
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
                    spec_ref='Chapter 6, Section 6.7 "Assumptions"',
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

    # -----------------------------------------------------------------
    # Type inference helpers
    # -----------------------------------------------------------------

    def _infer_type_args(self, forall_vars: tuple[str, ...],
                         param_types: tuple[Type, ...],
                         arg_types: list[Type | None]) -> dict[str, Type]:
        """Infer type variable bindings by matching args against params."""
        mapping: dict[str, Type] = {}
        for param_ty, arg_ty in zip(param_types, arg_types):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            self._unify_for_inference(param_ty, arg_ty, mapping)
        return mapping

    def _unify_for_inference(self, pattern: Type, concrete: Type,
                             mapping: dict[str, Type]) -> None:
        """Simple unification for type argument inference."""
        if isinstance(pattern, TypeVar):
            if pattern.name not in mapping:
                mapping[pattern.name] = concrete
            return

        if isinstance(pattern, AdtType) and isinstance(concrete, AdtType):
            if pattern.name == concrete.name:
                for p_arg, c_arg in zip(pattern.type_args, concrete.type_args):
                    self._unify_for_inference(p_arg, c_arg, mapping)

        if isinstance(pattern, FunctionType) and isinstance(concrete, FunctionType):
            for p_param, c_param in zip(pattern.params, concrete.params):
                self._unify_for_inference(p_param, c_param, mapping)
            self._unify_for_inference(
                pattern.return_type, concrete.return_type, mapping)
