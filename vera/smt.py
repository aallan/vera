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

if TYPE_CHECKING:
    pass


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
    call_node: ast.FnCall
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


class SmtContext:
    """Z3 solver context with AST-to-Z3 expression translation."""

    def __init__(
        self,
        timeout_ms: int = 10_000,
        fn_lookup: Callable[[str], Any] | None = None,
    ) -> None:
        self.solver = z3.Solver()
        self.solver.set("timeout", timeout_ms)
        self._vars: dict[str, z3.ExprRef] = {}
        self._result_var: z3.ExprRef | None = None
        # Uninterpreted function for length (constrained >= 0)
        self._length_fn = z3.Function("length", z3.IntSort(), z3.IntSort())
        # Callee contract verification
        self._fn_lookup = fn_lookup
        self._call_violations: list[CallViolation] = []
        self._fresh_counter: int = 0

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

        if isinstance(expr, ast.Block):
            return self._translate_block(expr, env)

        # Unsupported: match, handle, lambdas, constructors,
        # quantifiers, old/new, assert/assume, etc.
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

        # Pipe — unsupported in verification context
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
        For user-defined functions:
          1. Look up the callee's FunctionInfo
          2. Translate actual arguments in the caller's env
          3. Check each callee precondition holds (solver has caller assumptions)
          4. Create a fresh return variable
          5. Assume callee postconditions about the return variable
          6. Return the fresh variable
        """
        # Built-in: length()
        if call.name == "length" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                result = self._length_fn(arg)
                self.solver.add(result >= 0)
                return result
            return None

        # No function lookup → can't do modular verification
        if self._fn_lookup is None:
            return None

        callee_info = self._fn_lookup(call.name)
        if callee_info is None:
            return None

        # Generic functions can't be translated to Z3
        if callee_info.forall_vars:
            return None

        # Must have matching arity
        if len(call.args) != len(callee_info.param_type_exprs):
            return None

        # Translate actual arguments in the caller's env
        z3_args: list[z3.ExprRef] = []
        for arg_expr in call.args:
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
                    callee_name=call.name,
                    call_node=call,
                    precondition=contract,
                    counterexample=result.counterexample,
                ))
                return None

        # Create fresh return variable
        from vera.types import NAT, BOOL, RefinedType
        ret_type = callee_info.return_type
        base_ret = ret_type.base if isinstance(ret_type, RefinedType) else ret_type
        fresh = self._fresh_name(call.name)
        if base_ret == NAT:
            ret_var = self.declare_nat(fresh)
        elif base_ret == BOOL:
            ret_var = self.declare_bool(fresh)
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
