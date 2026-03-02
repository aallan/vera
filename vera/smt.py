"""Vera SMT translation layer — AST to Z3 bridge.

Translates Vera AST expressions into Z3 formulas for contract
verification.  Manages solver context, variable declarations,
De Bruijn slot resolution, and counterexample extraction.

See spec/06-contracts.md, Section 6.4 "Verification Conditions".
"""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any, Callable

import z3

from vera import ast
from vera.types import (
    AdtType,
    PrimitiveType,
    Type,
    TypeVar,
    BOOL,
    INT,
    NAT,
)

if TYPE_CHECKING:
    from vera.environment import AdtInfo


# =====================================================================
# Slot environment — De Bruijn → Z3 variable mapping
# =====================================================================

@dataclass
class SlotEnv:
    """Maps Vera typed De Bruijn indices to Z3 variables.

    Maintains a stack per type name.  Index 0 = most recent binding
    (last element in the list), matching De Bruijn convention.
    """

    _stacks: dict[str, list[z3.ExprRef]] = field(default_factory=dict)

    def resolve(self, type_name: str, index: int) -> z3.ExprRef | None:
        """Look up @Type.index in the current scope."""
        stack = self._stacks.get(type_name, [])
        pos = len(stack) - 1 - index
        if 0 <= pos < len(stack):
            return stack[pos]
        return None

    def push(self, type_name: str, expr: z3.ExprRef) -> SlotEnv:
        """Return a new environment with *expr* pushed for *type_name*."""
        new_stacks = {k: list(v) for k, v in self._stacks.items()}
        new_stacks.setdefault(type_name, []).append(expr)
        return SlotEnv(new_stacks)


# =====================================================================
# SMT result
# =====================================================================

@dataclass
class SmtResult:
    """Outcome of a Z3 validity check."""

    status: str  # "verified" | "violated" | "unknown" | "unsupported"
    counterexample: dict[str, str] | None = None  # slot_name → value


@dataclass
class CallViolation:
    """Records a call site where a callee's precondition may not hold."""

    callee_name: str
    call_node: ast.FnCall | ast.ModuleCall
    precondition: ast.Requires
    counterexample: dict[str, str] | None = None


# =====================================================================
# SMT context — solver and translation
# =====================================================================

# Z3 operator mapping for binary expressions
_ARITH_OPS: dict[ast.BinOp, str] = {
    ast.BinOp.ADD: "+",
    ast.BinOp.SUB: "-",
    ast.BinOp.MUL: "*",
    ast.BinOp.DIV: "/",
    ast.BinOp.MOD: "%",
}

_CMP_OPS: dict[ast.BinOp, str] = {
    ast.BinOp.EQ: "==",
    ast.BinOp.NEQ: "!=",
    ast.BinOp.LT: "<",
    ast.BinOp.GT: ">",
    ast.BinOp.LE: "<=",
    ast.BinOp.GE: ">=",
}

_BOOL_OPS: set[ast.BinOp] = {ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES}


# =====================================================================
# ADT type helpers
# =====================================================================

def _adt_sort_key(adt_name: str, type_args: tuple[Type, ...]) -> str:
    """Build a canonical key for an ADT sort, e.g. ``List<Int>``."""
    if not type_args:
        return adt_name
    arg_strs = []
    for a in type_args:
        if isinstance(a, PrimitiveType):
            arg_strs.append(a.name)
        elif isinstance(a, AdtType):
            arg_strs.append(_adt_sort_key(a.name, a.type_args))
        else:
            arg_strs.append("?")
    return f"{adt_name}<{', '.join(arg_strs)}>"


def _substitute_type(ty: Type, subst: dict[str, Type]) -> Type:
    """Substitute ``TypeVar`` names in *ty* using *subst*."""
    if isinstance(ty, TypeVar):
        return subst.get(ty.name, ty)
    if isinstance(ty, AdtType):
        new_args = tuple(_substitute_type(a, subst) for a in ty.type_args)
        return AdtType(ty.name, new_args)
    return ty


class SmtContext:
    """Z3 solver context with AST-to-Z3 expression translation."""

    def __init__(
        self,
        timeout_ms: int = 10_000,
        fn_lookup: Callable[[str], Any] | None = None,
        module_fn_lookup: (
            Callable[[tuple[str, ...], str], Any] | None
        ) = None,
    ) -> None:
        self.solver = z3.Solver()
        self.solver.set("timeout", timeout_ms)
        self._vars: dict[str, z3.ExprRef] = {}
        self._result_var: z3.ExprRef | None = None
        # Uninterpreted functions for length (constrained >= 0)
        # Keyed by domain sort — supports both Int and ADT domains
        self._length_fns: dict[str, z3.FuncDeclRef] = {
            "Int": z3.Function("length", z3.IntSort(), z3.IntSort()),
        }
        # Callee contract verification
        self._fn_lookup = fn_lookup
        self._module_fn_lookup = module_fn_lookup
        self._call_violations: list[CallViolation] = []
        self._fresh_counter: int = 0
        # ADT support
        self._adt_registry: dict[str, AdtInfo] = {}
        self._ctor_to_adt: dict[str, str] = {}  # ctor name → ADT name
        self._z3_sorts: dict[str, z3.SortRef] = {}  # "List<Int>" → Z3 sort

    # -----------------------------------------------------------------
    # Variable management
    # -----------------------------------------------------------------

    def declare_int(self, name: str) -> z3.ArithRef:
        """Declare a Z3 integer variable."""
        v = z3.Int(name)
        self._vars[name] = v
        return v

    def declare_bool(self, name: str) -> z3.BoolRef:
        """Declare a Z3 boolean variable."""
        v = z3.Bool(name)
        self._vars[name] = v
        return v

    def declare_nat(self, name: str) -> z3.ArithRef:
        """Declare a Z3 integer variable constrained >= 0 (for Nat)."""
        v = z3.Int(name)
        self._vars[name] = v
        self.solver.add(v >= 0)
        return v

    def set_result_var(self, var: z3.ExprRef) -> None:
        """Set the variable used for @T.result references."""
        self._result_var = var

    def get_var(self, name: str) -> z3.ExprRef | None:
        """Look up a declared variable by name."""
        return self._vars.get(name)

    def _fresh_name(self, prefix: str) -> str:
        """Generate a unique Z3 variable name."""
        self._fresh_counter += 1
        return f"_call_{prefix}_{self._fresh_counter}"

    def drain_call_violations(self) -> list[CallViolation]:
        """Return accumulated call-site violations and clear the list."""
        violations = list(self._call_violations)
        self._call_violations.clear()
        return violations

    # -----------------------------------------------------------------
    # ADT support
    # -----------------------------------------------------------------

    def register_adt(self, adt_info: AdtInfo) -> None:
        """Register an ADT definition for Z3 sort creation."""
        self._adt_registry[adt_info.name] = adt_info
        for ctor_name in adt_info.constructors:
            self._ctor_to_adt[ctor_name] = adt_info.name

    def declare_adt(
        self, name: str, ty: Type,
    ) -> z3.ExprRef | None:
        """Declare a Z3 constant of an ADT sort."""
        z3_sort = self._vera_type_to_z3_sort(ty)
        if z3_sort is None:
            return None
        v = z3.Const(name, z3_sort)
        self._vars[name] = v
        return v

    def _vera_type_to_z3_sort(
        self,
        ty: Type,
        *,
        self_ref_key: str | None = None,
        self_ref_dt: Any | None = None,
    ) -> z3.SortRef | None:
        """Map a Vera Type to a Z3 sort.

        Returns None for unsupported types (String, Float64, Unit,
        TypeVar, function types).
        """
        if isinstance(ty, PrimitiveType):
            if ty.name in ("Int", "Nat"):
                return z3.IntSort()
            if ty.name == "Bool":
                return z3.BoolSort()
            return None
        if isinstance(ty, AdtType):
            key = _adt_sort_key(ty.name, ty.type_args)
            # Self-reference during datatype creation
            if key == self_ref_key and self_ref_dt is not None:
                return self_ref_dt
            return self._get_or_create_adt_sort(ty.name, ty.type_args)
        return None

    def _get_or_create_adt_sort(
        self,
        adt_name: str,
        type_args: tuple[Type, ...],
    ) -> z3.SortRef | None:
        """Lazily create a Z3 ADT sort for a concrete type instantiation."""
        key = _adt_sort_key(adt_name, type_args)
        if key in self._z3_sorts:
            return self._z3_sorts[key]

        adt_info = self._adt_registry.get(adt_name)
        if adt_info is None:
            return None

        # Build type parameter substitution
        subst: dict[str, Type] = {}
        if adt_info.type_params:
            if len(type_args) != len(adt_info.type_params):
                return None
            subst = dict(zip(adt_info.type_params, type_args))

        # Create Z3 Datatype
        z3_name = key.replace("<", "_").replace(">", "").replace(", ", "_")
        dt = z3.Datatype(z3_name)

        for ctor_name, ctor_info in adt_info.constructors.items():
            if ctor_info.field_types is None:
                dt.declare(ctor_name)
            else:
                fields: list[tuple[str, Any]] = []
                for i, ft in enumerate(ctor_info.field_types):
                    concrete = _substitute_type(ft, subst)
                    field_name = f"{ctor_name}_{i}"
                    z3_sort = self._vera_type_to_z3_sort(
                        concrete,
                        self_ref_key=key,
                        self_ref_dt=dt,
                    )
                    if z3_sort is None:
                        return None
                    fields.append((field_name, z3_sort))
                dt.declare(ctor_name, *fields)

        sort = dt.create()
        self._z3_sorts[key] = sort
        return sort

    def _get_length_fn(self, sort: z3.SortRef) -> z3.FuncDeclRef:
        """Get or create a length function for the given domain sort."""
        key = str(sort)
        if key not in self._length_fns:
            fn_name = f"length_{key}"
            self._length_fns[key] = z3.Function(
                fn_name, sort, z3.IntSort(),
            )
        return self._length_fns[key]

    def get_rank_fn(self, sort: z3.SortRef) -> z3.FuncDeclRef | None:
        """Get or create a rank function for structural ordering on an ADT.

        Adds axioms: ``rank(x) >= 0`` and for each constructor with
        recursive fields, ``is_Ctor(x) ==> rank(field_i(x)) < rank(x)``.

        Returns None if the sort is not a Z3 DatatypeSortRef.
        """
        if not isinstance(sort, z3.DatatypeSortRef):
            return None
        key = f"_rank_{sort}"
        if key in self._length_fns:
            return self._length_fns[key]
        rank = z3.Function(key, sort, z3.IntSort())
        self._length_fns[key] = rank
        # Add axioms via a universally-quantified variable
        x = z3.Const("_rank_x", sort)
        self.solver.add(z3.ForAll([x], rank(x) >= 0))
        # For each constructor, add structural decrease axioms
        for i in range(sort.num_constructors()):
            ctor = sort.constructor(i)
            recognizer = sort.recognizer(i)
            for j in range(ctor.arity()):
                accessor = sort.accessor(i, j)
                if accessor.range() == sort:
                    # Recursive field: rank(field) < rank(parent)
                    self.solver.add(z3.ForAll(
                        [x],
                        z3.Implies(
                            recognizer(x),
                            rank(accessor(x)) < rank(x),
                        ),
                    ))
        return rank

    # -----------------------------------------------------------------
    # Expression translation
    # -----------------------------------------------------------------

    def translate_expr(
        self, expr: ast.Expr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a Vera AST expression to a Z3 formula.

        Returns None if the expression contains unsupported constructs
        (triggers Tier 3 fallback).
        """
        if isinstance(expr, ast.IntLit):
            return z3.IntVal(expr.value)

        if isinstance(expr, ast.BoolLit):
            return z3.BoolVal(expr.value)

        if isinstance(expr, ast.SlotRef):
            return self._translate_slot_ref(expr, env)

        if isinstance(expr, ast.ResultRef):
            return self._result_var

        if isinstance(expr, ast.BinaryExpr):
            return self._translate_binary(expr, env)

        if isinstance(expr, ast.UnaryExpr):
            return self._translate_unary(expr, env)

        if isinstance(expr, ast.IfExpr):
            return self._translate_if(expr, env)

        if isinstance(expr, ast.FnCall):
            return self._translate_call(expr, env)

        if isinstance(expr, ast.ModuleCall):
            return self._translate_module_call(expr, env)

        if isinstance(expr, ast.Block):
            return self._translate_block(expr, env)

        if isinstance(expr, ast.MatchExpr):
            return self._translate_match(expr, env)

        if isinstance(expr, ast.NullaryConstructor):
            return self._translate_nullary_ctor(expr)

        if isinstance(expr, ast.ConstructorCall):
            return self._translate_ctor_call(expr, env)

        # Unsupported: handle, lambdas, quantifiers,
        # old/new, assert/assume, etc.
        return None

    def _translate_slot_ref(
        self, ref: ast.SlotRef, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate @Type.n to the corresponding Z3 variable."""
        type_name = ref.type_name
        if ref.type_args:
            # Parameterised type — build canonical name
            # e.g. Array<Int> → "Array<Int>"
            arg_names = []
            for ta in ref.type_args:
                if isinstance(ta, ast.NamedType):
                    arg_names.append(ta.name)
                else:
                    return None  # complex type arg — unsupported
            type_name = f"{ref.type_name}<{', '.join(arg_names)}>"
        return env.resolve(type_name, ref.index)

    def _translate_binary(
        self, expr: ast.BinaryExpr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate binary operators."""
        # Pipe: a |> f(x, y) → f(a, x, y)
        if expr.op == ast.BinOp.PIPE:
            if isinstance(expr.right, ast.FnCall):
                desugared = ast.FnCall(
                    name=expr.right.name,
                    args=(expr.left,) + expr.right.args,
                    span=expr.span,
                )
                return self._translate_call(desugared, env)
            if isinstance(expr.right, ast.ModuleCall):
                desugared_mc = ast.ModuleCall(
                    path=expr.right.path,
                    name=expr.right.name,
                    args=(expr.left,) + expr.right.args,
                    span=expr.span,
                )
                return self._translate_module_call(desugared_mc, env)
            return None  # unsupported RHS

        left = self.translate_expr(expr.left, env)
        right = self.translate_expr(expr.right, env)
        if left is None or right is None:
            return None

        op = expr.op

        # Arithmetic
        if op == ast.BinOp.ADD:
            return left + right
        if op == ast.BinOp.SUB:
            return left - right
        if op == ast.BinOp.MUL:
            return left * right
        if op == ast.BinOp.DIV:
            return left / right
        if op == ast.BinOp.MOD:
            return left % right

        # Comparison
        if op == ast.BinOp.EQ:
            return left == right
        if op == ast.BinOp.NEQ:
            return left != right
        if op == ast.BinOp.LT:
            return left < right
        if op == ast.BinOp.GT:
            return left > right
        if op == ast.BinOp.LE:
            return left <= right
        if op == ast.BinOp.GE:
            return left >= right
        # Boolean
        if op == ast.BinOp.AND:
            return z3.And(left, right)
        if op == ast.BinOp.OR:
            return z3.Or(left, right)
        if op == ast.BinOp.IMPLIES:
            return z3.Implies(left, right)

        return None

    def _translate_unary(
        self, expr: ast.UnaryExpr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate unary operators."""
        operand = self.translate_expr(expr.operand, env)
        if operand is None:
            return None

        if expr.op == ast.UnaryOp.NOT:
            return z3.Not(operand)
        if expr.op == ast.UnaryOp.NEG:
            return -operand
        return None

    def _translate_if(
        self, expr: ast.IfExpr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate if-then-else to Z3 If."""
        cond = self.translate_expr(expr.condition, env)
        then = self.translate_expr(expr.then_branch, env)
        else_ = self.translate_expr(expr.else_branch, env)
        if cond is None or then is None or else_ is None:
            return None
        return z3.If(cond, then, else_)

    def _translate_call(
        self, call: ast.FnCall, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a function call via modular contract verification.

        For ``length()``, uses the built-in uninterpreted function.
        For user-defined functions, looks up the callee and delegates
        to ``_translate_call_with_info``.
        """
        # Built-in: length()
        if call.name == "length" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                length_fn = self._get_length_fn(arg.sort())
                result = length_fn(arg)
                self.solver.add(result >= 0)
                return result
            return None

        # No function lookup → can't do modular verification
        if self._fn_lookup is None:
            return None

        callee_info = self._fn_lookup(call.name)
        if callee_info is None:
            return None

        return self._translate_call_with_info(
            callee_info, call.name, call.args, call, env,
        )

    def _translate_module_call(
        self, call: ast.ModuleCall, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a module-qualified call (C7d).

        Looks up the callee via the module function lookup callback,
        then delegates to the shared contract verification logic.
        """
        if self._module_fn_lookup is None:
            return None

        callee_info = self._module_fn_lookup(
            tuple(call.path), call.name,
        )
        if callee_info is None:
            return None

        return self._translate_call_with_info(
            callee_info, call.name, call.args, call, env,
        )

    def _translate_call_with_info(
        self,
        callee_info: Any,
        callee_name: str,
        args: tuple[ast.Expr, ...],
        call_node: ast.FnCall | ast.ModuleCall,
        env: SlotEnv,
    ) -> z3.ExprRef | None:
        """Core modular verification: check preconditions, assume postconditions.

          1. Check callee is non-generic with matching arity
          2. Translate actual arguments in the caller's env
          3. Check each callee precondition holds (solver has caller assumptions)
          4. Create a fresh return variable
          5. Assume callee postconditions about the return variable
          6. Return the fresh variable
        """
        # Generic functions can't be translated to Z3
        if callee_info.forall_vars:
            return None

        # Must have matching arity
        if len(args) != len(callee_info.param_type_exprs):
            return None

        # Translate actual arguments in the caller's env
        z3_args: list[z3.ExprRef] = []
        for arg_expr in args:
            z3_arg = self.translate_expr(arg_expr, env)
            if z3_arg is None:
                return None
            z3_args.append(z3_arg)

        # Build callee's SlotEnv: push params in declaration order
        callee_env = SlotEnv()
        for param_te, z3_arg in zip(callee_info.param_type_exprs, z3_args):
            slot_name = self._type_expr_to_slot_name(param_te)
            if slot_name is None:
                return None
            callee_env = callee_env.push(slot_name, z3_arg)

        # Check each callee precondition
        for contract in callee_info.contracts:
            if not isinstance(contract, ast.Requires):
                continue
            # Skip trivial requires(true)
            if isinstance(contract.expr, ast.BoolLit) and contract.expr.value:
                continue
            z3_pre = self.translate_expr(contract.expr, callee_env)
            if z3_pre is None:
                # Can't translate precondition → bail to Tier 3
                return None
            # Check validity: solver state already has caller's assumptions
            result = self.check_valid(z3_pre, [])
            if result.status != "verified":
                self._call_violations.append(CallViolation(
                    callee_name=callee_name,
                    call_node=call_node,
                    precondition=contract,
                    counterexample=result.counterexample,
                ))
                return None

        # Create fresh return variable
        from vera.types import RefinedType
        ret_type = callee_info.return_type
        base_ret = ret_type.base if isinstance(ret_type, RefinedType) else ret_type
        fresh = self._fresh_name(callee_name)
        if base_ret == NAT:
            ret_var = self.declare_nat(fresh)
        elif base_ret == BOOL:
            ret_var = self.declare_bool(fresh)
        elif isinstance(base_ret, AdtType):
            adt_var = self.declare_adt(fresh, base_ret)
            ret_var = adt_var if adt_var is not None else self.declare_int(fresh)
        else:
            ret_var = self.declare_int(fresh)

        # Assume callee postconditions about the return variable
        saved_result = self._result_var
        self._result_var = ret_var
        for contract in callee_info.contracts:
            if not isinstance(contract, ast.Ensures):
                continue
            if isinstance(contract.expr, ast.BoolLit) and contract.expr.value:
                continue
            z3_post = self.translate_expr(contract.expr, callee_env)
            if z3_post is not None:
                self.solver.add(z3_post)
        self._result_var = saved_result

        return ret_var

    def _translate_block(
        self, block: ast.Block, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a block expression: process statements then final expr."""
        current_env = env
        for stmt in block.statements:
            if isinstance(stmt, ast.LetStmt):
                val = self.translate_expr(stmt.value, current_env)
                if val is None:
                    return None
                # Extract slot type name from the let binding
                type_name = self._type_expr_to_slot_name(stmt.type_expr)
                if type_name is None:
                    return None
                current_env = current_env.push(type_name, val)
            elif isinstance(stmt, ast.ExprStmt):
                # Side-effect statement — doesn't affect the result value
                continue
            else:
                # LetDestruct or unknown statement type
                return None
        return self.translate_expr(block.expr, current_env)

    # -----------------------------------------------------------------
    # Match and constructor translation
    # -----------------------------------------------------------------

    def _translate_match(
        self, expr: ast.MatchExpr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a match expression to a Z3 If-chain."""
        scrutinee = self.translate_expr(expr.scrutinee, env)
        if scrutinee is None:
            return None

        # Build reverse If-chain: last arm is the default
        arms = list(expr.arms)
        if not arms:
            return None

        # Translate last arm body (default case)
        last_env = self._bind_pattern(scrutinee, arms[-1].pattern, env)
        if last_env is None:
            return None
        result = self.translate_expr(arms[-1].body, last_env)
        if result is None:
            return None

        # Wrap preceding arms in z3.If(condition, body, previous)
        for arm in reversed(arms[:-1]):
            cond = self._pattern_condition(scrutinee, arm.pattern)
            if cond is None:
                return None
            arm_env = self._bind_pattern(scrutinee, arm.pattern, env)
            if arm_env is None:
                return None
            arm_body = self.translate_expr(arm.body, arm_env)
            if arm_body is None:
                return None
            result = z3.If(cond, arm_body, result)

        return result

    def _find_ctor_index(
        self, sort: z3.SortRef, ctor_name: str,
    ) -> int | None:
        """Find the index of a constructor by name in a Z3 ADT sort."""
        if not isinstance(sort, z3.DatatypeSortRef):
            return None
        for i in range(sort.num_constructors()):
            if sort.constructor(i).name() == ctor_name:
                return i
        return None

    def _pattern_condition(
        self, scrutinee: z3.ExprRef, pattern: ast.Pattern
    ) -> z3.ExprRef | None:
        """Return a Z3 Boolean for when *pattern* matches *scrutinee*."""
        if isinstance(pattern, ast.NullaryPattern):
            sort = scrutinee.sort()
            idx = self._find_ctor_index(sort, pattern.name)
            if idx is None:
                return None
            return sort.recognizer(idx)(scrutinee)

        if isinstance(pattern, ast.ConstructorPattern):
            sort = scrutinee.sort()
            idx = self._find_ctor_index(sort, pattern.name)
            if idx is None:
                return None
            return sort.recognizer(idx)(scrutinee)

        if isinstance(pattern, ast.WildcardPattern):
            return z3.BoolVal(True)

        if isinstance(pattern, ast.BindingPattern):
            return z3.BoolVal(True)

        if isinstance(pattern, ast.IntPattern):
            return scrutinee == z3.IntVal(pattern.value)

        if isinstance(pattern, ast.BoolPattern):
            return scrutinee == z3.BoolVal(pattern.value)

        return None

    def _bind_pattern(
        self,
        scrutinee: z3.ExprRef,
        pattern: ast.Pattern,
        env: SlotEnv,
    ) -> SlotEnv | None:
        """Extend *env* with bindings introduced by *pattern*."""
        if isinstance(pattern, (
            ast.NullaryPattern, ast.WildcardPattern,
            ast.IntPattern, ast.BoolPattern, ast.StringPattern,
        )):
            return env

        if isinstance(pattern, ast.BindingPattern):
            slot_name = self._type_expr_to_slot_name(pattern.type_expr)
            if slot_name is None:
                return None
            return env.push(slot_name, scrutinee)

        if isinstance(pattern, ast.ConstructorPattern):
            sort = scrutinee.sort()
            idx = self._find_ctor_index(sort, pattern.name)
            if idx is None:
                return None
            cur = env
            for i, sub_pat in enumerate(pattern.sub_patterns):
                accessor = sort.accessor(idx, i)
                field_val = accessor(scrutinee)
                bound = self._bind_pattern(field_val, sub_pat, cur)
                if bound is None:
                    return None
                cur = bound
            return cur

        return None

    def _find_sort_for_ctor(self, ctor_name: str) -> z3.SortRef | None:
        """Find a cached Z3 sort that has a constructor named *ctor_name*."""
        adt_name = self._ctor_to_adt.get(ctor_name)
        if adt_name is None:
            return None
        for key, sort in self._z3_sorts.items():
            base = key.split("<")[0] if "<" in key else key
            if base == adt_name:
                if self._find_ctor_index(sort, ctor_name) is not None:
                    return sort
        return None

    def _translate_nullary_ctor(
        self, expr: ast.NullaryConstructor
    ) -> z3.ExprRef | None:
        """Translate a nullary constructor (e.g. ``Nil``) to Z3."""
        sort = self._find_sort_for_ctor(expr.name)
        if sort is None:
            return None
        idx = self._find_ctor_index(sort, expr.name)
        if idx is None:
            return None
        return sort.constructor(idx)()

    def _translate_ctor_call(
        self, expr: ast.ConstructorCall, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a constructor call (e.g. ``Cons(1, Nil)``) to Z3."""
        sort = self._find_sort_for_ctor(expr.name)
        if sort is None:
            return None
        idx = self._find_ctor_index(sort, expr.name)
        if idx is None:
            return None
        # Translate arguments
        z3_args: list[z3.ExprRef] = []
        for arg in expr.args:
            z3_arg = self.translate_expr(arg, env)
            if z3_arg is None:
                return None
            z3_args.append(z3_arg)
        return sort.constructor(idx)(*z3_args)

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str | None:
        """Extract the slot name from a type expression."""
        if isinstance(te, ast.NamedType):
            if te.type_args:
                arg_names = []
                for a in te.type_args:
                    if isinstance(a, ast.NamedType):
                        arg_names.append(a.name)
                    else:
                        return None
                return f"{te.name}<{', '.join(arg_names)}>"
            return te.name
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_slot_name(te.base_type)
        return None

    # -----------------------------------------------------------------
    # Validity checking
    # -----------------------------------------------------------------

    def check_valid(
        self,
        goal: z3.ExprRef,
        assumptions: list[z3.ExprRef],
    ) -> SmtResult:
        """Check if assumptions ⟹ goal is valid.

        Uses refutation: assert assumptions and ¬goal.
        - unsat → goal always holds (verified)
        - sat → counterexample found (violated)
        - unknown → solver timeout or incomplete (unknown)
        """
        self.solver.push()
        for a in assumptions:
            self.solver.add(a)
        self.solver.add(z3.Not(goal))

        result = self.solver.check()
        self.solver.pop()

        if result == z3.unsat:
            return SmtResult(status="verified")
        elif result == z3.sat:
            model = self.solver.model()
            ce = self._extract_counterexample(model)
            return SmtResult(status="violated", counterexample=ce)
        else:
            return SmtResult(status="unknown")

    def _extract_counterexample(
        self, model: z3.ModelRef
    ) -> dict[str, str]:
        """Extract variable values from a Z3 model."""
        ce: dict[str, str] = {}
        for name, var in self._vars.items():
            val = model.evaluate(var, model_completion=True)
            ce[name] = str(val)
        return ce

    def reset(self) -> None:
        """Reset solver state for the next function."""
        self.solver.reset()
        self._vars.clear()
        self._result_var = None
        self._call_violations.clear()
        self._fresh_counter = 0
        # Keep _adt_registry and _ctor_to_adt (they persist across functions)
        # but clear cached Z3 sorts (tied to solver state)
        self._z3_sorts.clear()
