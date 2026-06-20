"""Vera SMT translation layer — AST to Z3 bridge.

Translates Vera AST expressions into Z3 formulas for contract
verification.  Manages solver context, variable declarations,
De Bruijn slot resolution, and counterexample extraction.

See spec/06-contracts.md, Section 6.4 "Verification Conditions".
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any, Callable

import z3

from vera import ast
from vera.types import (
    AdtType,
    PrimitiveType,
    RefinedType,
    Type,
    TypeVar,
    BOOL,
    FLOAT64,
    INT,
    NAT,
    STRING,
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
        # Retained so reset() can re-apply it on warm-session reuse.
        self._timeout_ms = timeout_ms
        self._vars: dict[str, z3.ExprRef] = {}
        self._result_var: z3.ExprRef | None = None
        # Uninterpreted functions for length (constrained >= 0)
        # Keyed by domain sort — supports both Int and ADT domains
        self._length_fns: dict[str, z3.FuncDeclRef] = {
            "Int": z3.Function("length", z3.IntSort(), z3.IntSort()),
        }
        # Uninterpreted index functions for `arr[i]` translation
        # (#667).  Keyed by array sort name so each (Array<T>)
        # gets its own typed signature `Array_<T> × Int → <T>`.
        self._index_fns: dict[str, z3.FuncDeclRef] = {}
        # Reverse map from array-sort-name → element sort, populated
        # whenever an Array_<T> sort is created.  Avoids fragile
        # string-parsing recovery (#667 follow-up): for ADT element
        # types, the Z3 sort name has `<`/`>` stripped (via the
        # transformation in `_get_or_create_adt_sort`) so a naive
        # `str(elt_sort)` round-trip doesn't recover the canonical
        # `_adt_sort_key` form used by `_z3_sorts`.  Storing the
        # element sort at creation time is the durable fix.
        self._array_element_sorts: dict[str, z3.SortRef] = {}
        # Callee contract verification
        self._fn_lookup = fn_lookup
        self._module_fn_lookup = module_fn_lookup
        self._call_violations: list[CallViolation] = []
        self._fresh_counter: int = 0
        # Path conditions accumulated from if/match branches so that
        # call-site precondition checks can see which branch is active.
        self._path_conditions: list[z3.ExprRef] = []
        # Optional hook (injected by the verifier) returning the source-type
        # facts a constructor pattern's refined / @Nat sub-pattern bindings
        # carry, so a match arm body's call PRECONDITIONS see them (CR
        # PR-review).  Signature: (scrutinee_ast, scrutinee_z3, pattern, smt)
        # -> list[z3 fact].  None when no verifier is driving (pure-SMT tests).
        self._subpattern_fact_hook: Any = None
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

    def declare_string(self, name: str) -> z3.SeqRef:
        """Declare a Z3 string variable (sequence sort)."""
        v = z3.String(name)
        self._vars[name] = v
        return v

    def declare_float64(self, name: str) -> z3.ArithRef:
        """Declare a Z3 real variable (mathematical reals, approximates Float64)."""
        v = z3.Real(name)
        self._vars[name] = v
        return v

    # -----------------------------------------------------------------
    # Array support (#667 — IndexExpr / ArrayLit / Float64 contract
    # predicates).  Pre-#667 `Array<T>` parameters fell through to
    # `declare_int` and the Array-element/Index/Lit constructs in
    # contracts returned None from `translate_expr`, dropping every
    # affected predicate to Tier 3 (runtime check).  The model here
    # is the same uninterpreted-function shape the existing `length`
    # function uses: an `Array<T>` slot is a constant of a fresh
    # `Array_<elt>` uninterpreted sort; `arr[i]` is `index_<elt>(arr,
    # i)`.  Sound but partial — the verifier can prove relational
    # facts ("if `i < length(arr)` and `arr[i] > 0` then ...") but
    # not anything that requires knowing element structure (e.g.
    # "for all valid i, arr[i] > 0").  Quantified contracts are
    # tracked separately as part of #427 (Tier 2 verification).
    # -----------------------------------------------------------------

    def _get_array_sort(self, element_sort: z3.SortRef) -> z3.SortRef:
        """Get-or-create an uninterpreted ``Array_<elt>`` sort
        keyed by the element sort's string name.

        Also populates ``_array_element_sorts`` with the
        element-sort association, so the reverse lookup in
        ``_get_element_sort_for_array`` can recover the element
        sort by direct map lookup rather than by parsing the
        Z3 sort name string."""
        key = f"Array_{element_sort}"
        if key in self._z3_sorts:
            return self._z3_sorts[key]
        sort = z3.DeclareSort(key)
        self._z3_sorts[key] = sort
        # Record the (array-sort-name → element-sort) association
        # for `_get_element_sort_for_array`'s reverse lookup.
        self._array_element_sorts[str(sort)] = element_sort
        return sort

    def _get_index_fn(
        self, array_sort: z3.SortRef, element_sort: z3.SortRef,
    ) -> z3.FuncDeclRef:
        """Get-or-create the uninterpreted ``index_<sort>(arr, idx)
        → elt`` function for the given (array, element) pair."""
        key = f"index_{array_sort}"
        if key not in self._index_fns:
            self._index_fns[key] = z3.Function(
                key, array_sort, z3.IntSort(), element_sort,
            )
        return self._index_fns[key]

    def declare_array_var(
        self, name: str, element_sort: z3.SortRef,
    ) -> z3.ExprRef:
        """Declare an Array-typed Z3 constant.  The constant lives
        in the ``Array_<elt>`` uninterpreted sort created by
        ``_get_array_sort``; this matches the rest of the SMT
        layer's pattern of opaque carrier sorts + uninterpreted
        observer functions (length, index)."""
        array_sort = self._get_array_sort(element_sort)
        v = z3.Const(name, array_sort)
        self._vars[name] = v
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
        """Declare a Z3 constant of an ADT sort.

        Unwraps a refinement OVER an ADT base (`{ @Box | P }`) to its base
        sort, so a refined-ADT param/return is declared with the ADT sort
        rather than falling to ``declare_int`` (which would make a
        pattern-match / projection see an Int term — a false Tier-3 or a Z3
        sort failure; CR d338946).  Mirrors the array path's internal unwrap."""
        if isinstance(ty, RefinedType):
            ty = ty.base
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

        Returns None for unsupported types (Unit, TypeVar, function types).
        String maps to z3.StringSort(); Float64 maps to z3.RealSort().
        """
        if isinstance(ty, RefinedType):
            # A refinement's Z3 SORT is its base's sort — the predicate
            # constrains values, not the carrier set, and is enforced
            # separately (as an assumption / obligation).  Unwrap HERE, not only
            # at the `declare_adt` call site, so a refined type nested as a
            # tuple component or constructor field (`Tuple<PosInt, Int>`,
            # `Box(PosInt)`) resolves to its base sort instead of None — which
            # would otherwise fail the enclosing tuple / datatype sort creation
            # and silently degrade the whole structure to a weaker model (CR
            # PR-review).
            ty = ty.base
        if isinstance(ty, PrimitiveType):
            if ty.name in ("Int", "Nat"):
                return z3.IntSort()
            if ty.name == "Bool":
                return z3.BoolSort()
            if ty.name == "String":
                return z3.StringSort()
            if ty.name == "Float64":
                return z3.RealSort()
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
            # #747: Tuple is variadic and never registered as an ADT, so it
            # would otherwise fall back to a scalar Int.  Synthesise a
            # single-constructor datatype on demand so its components are
            # projectable (non-literal tuple-destructure obligations).
            if adt_name == "Tuple" and type_args:
                return self._get_or_create_tuple_sort(key, type_args)
            return None

        # Build type parameter substitution
        subst: dict[str, Type] = {}
        if adt_info.type_params:
            if len(type_args) != len(adt_info.type_params):  # pragma: no cover
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

    def _get_or_create_tuple_sort(
        self, key: str, type_args: tuple[Type, ...],
    ) -> z3.SortRef | None:
        """#747: synthesise a Z3 datatype for a concrete ``Tuple`` instance.

        The variadic ``Tuple`` type is never in the ADT registry, so without
        this it falls back to a scalar ``Int``.  One ``Tuple`` constructor
        with a field per component makes the components projectable via
        accessors — needed for non-literal tuple-destructure narrowing
        obligations.  Cached like any other ADT sort.
        """
        z3_name = key.replace("<", "_").replace(">", "").replace(", ", "_")
        dt = z3.Datatype(z3_name)
        fields: list[tuple[str, Any]] = []
        for i, ft in enumerate(type_args):
            z3_sort = self._vera_type_to_z3_sort(
                ft, self_ref_key=key, self_ref_dt=dt)
            if z3_sort is None:
                return None
            fields.append((f"Tuple_{i}", z3_sort))
        dt.declare("Tuple", *fields)
        sort = dt.create()
        self._z3_sorts[key] = sort
        return sort

    def _get_length_fn(self, sort: z3.SortRef) -> z3.FuncDeclRef:
        """Get or create a length function for the given domain sort."""
        key = str(sort)
        if key not in self._length_fns:  # pragma: no cover
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
        if not isinstance(sort, z3.DatatypeSortRef):  # pragma: no cover
            return None
        key = f"_rank_{sort}"
        if key in self._length_fns:  # pragma: no cover
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

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.
        # SMT translation is intentionally narrow — contracts permit
        # a subset of expression shapes — so most Expr subclasses are
        # either "Cannot occur in contract context" or "deliberately
        # unsupported pending issue-tracked expansion".)
        #
        # Handled (explicit isinstance branch):
        #   IntLit            → z3.IntVal
        #   BoolLit           → z3.BoolVal
        #   StringLit         → z3.StringVal
        #   FloatLit          → z3.RealVal (Float64 → Real sort, #667)
        #   SlotRef           → bound Z3 variable
        #   ResultRef         → @Result substitution variable
        #   BinaryExpr        → translated by op family
        #   UnaryExpr         → translated by op family
        #   IfExpr            → If(cond, then, else)
        #   FnCall            → user-fn uninterpreted function or
        #                       built-in axiomatised translation
        #   ModuleCall        → cross-module fn lookup
        #   Block             → trailing-expr translation
        #   MatchExpr         → arm dispatch
        #   ConstructorCall   → ADT constructor application
        #   NullaryConstructor → ADT nullary tag
        #   IndexExpr         → uninterpreted `index_<sort>(arr, i)`
        #                       function call (#667)
        #   ArrayLit          → fresh Array constant with asserted
        #                       length and per-element values (#667)
        #
        # Intentionally ignored (returns None → Tier 3 fallback;
        # listed in the inline comment after the dispatch chain):
        #   AnonFn            → lambdas not in contract grammar
        #   HandleExpr        → handle-effect not in contract grammar
        #   ForallExpr        → quantifier translation deferred (#427)
        #   ExistsExpr        → quantifier translation deferred (#427)
        #   OldExpr           → contract operator; Tier 3 fallback
        #   NewExpr           → contract operator; Tier 3 fallback
        #   AssertExpr        → statement-like; not a predicate
        #   AssumeExpr        → statement-like; not a predicate
        #   UnitLit           → predicates are Bool, not Unit
        #
        # Cannot occur (rejected at check time or not in contracts):
        #   InterpolatedString → not in contract predicates
        #   QualifiedCall     → effects in contracts violate purity
        #   HoleExpr          → check time rejects
        """
        if isinstance(expr, ast.IntLit):
            return z3.IntVal(expr.value)

        if isinstance(expr, ast.BoolLit):
            return z3.BoolVal(expr.value)

        if isinstance(expr, ast.StringLit):
            return z3.StringVal(expr.value)

        if isinstance(expr, ast.FloatLit):
            # #667: Float64 maps to Z3 Real sort; literal value
            # translates directly.  Sound for proving relational
            # properties; not a full IEEE-754 model (intentional
            # — real arithmetic is decidable in Z3, FP isn't).
            return z3.RealVal(expr.value)

        if isinstance(expr, ast.IndexExpr):
            # #667: `arr[i]` translates to `index_<sort>(arr, i)`
            # where `index_<sort>` is an uninterpreted function
            # specific to the array's sort.  Sound — the verifier
            # can reason that two references to `arr[i]` with the
            # same `i` produce the same value (function congruence)
            # — but doesn't know element structure beyond what
            # explicit predicates assert.
            return self._translate_index_expr(expr, env)

        if isinstance(expr, ast.ArrayLit):
            # #667: `[a, b, c]` translates to a fresh constant of
            # the appropriate Array sort, with `length(lit) == N`
            # and `index(lit, i) == translate(elem_i)` asserted to
            # the solver for each known position.  Element types
            # that can't be sorted (e.g. function-typed elements)
            # fail the translation cleanly via None.
            return self._translate_array_lit(expr, env)

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
                else:  # pragma: no cover
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
            return None  # unsupported RHS  # pragma: no cover

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

        return None  # pragma: no cover

    def _translate_index_expr(
        self, expr: ast.IndexExpr, env: SlotEnv,
    ) -> z3.ExprRef | None:
        """Translate `coll[idx]` to `index_<sort>(coll, idx)`
        where `index_<sort>` is an uninterpreted function
        specific to the collection's Z3 sort (#667).

        Returns None when either side fails to translate, when
        the collection's sort isn't a recognised Array sort, or
        when the element-sort can't be inferred from the
        collection's sort name.
        """
        coll = self.translate_expr(expr.collection, env)
        idx = self.translate_expr(expr.index, env)
        if coll is None or idx is None:
            return None
        coll_sort = coll.sort()
        # Only Array_<elt> uninterpreted sorts created by
        # `_get_array_sort` are recognised here.  Other sorts
        # (e.g. an Int-fallback Array from a path that hasn't
        # been migrated to `_is_array_type`) fail cleanly.
        sort_name = str(coll_sort)
        if not sort_name.startswith("Array_"):
            return None
        element_sort = self._get_element_sort_for_array(coll_sort)
        if element_sort is None:
            return None
        index_fn = self._get_index_fn(coll_sort, element_sort)
        return index_fn(coll, idx)

    def _get_element_sort_for_array(
        self, array_sort: z3.SortRef,
    ) -> z3.SortRef | None:
        """Reverse-lookup the element sort for an `Array_<elt>`
        uninterpreted sort.

        Three-tier lookup, in order of robustness:

        1. **`_array_element_sorts` direct map**: populated whenever
           `_get_array_sort` creates a new Array_<T> sort.  Works
           for every element type — primitive, ADT (incl. nested
           generic), and any future shape — because the
           association is recorded at creation time rather than
           reverse-engineered from the sort name string.

        2. **Primitive pattern match**: covers `Array_Int`,
           `Array_Real`, `Array_Bool`, `Array_String` for callers
           that obtain an array sort via a path that hasn't
           populated `_array_element_sorts` (defensive — every
           code path today populates it, but the fallback shields
           against future regressions).

        3. **`_z3_sorts` direct key lookup**: tries the raw
           stripped key (e.g. `MyAdt`) and the angle-bracketed
           generic form (e.g. `List_Int` → `List<Int>`) as
           defensive last-ditch ADT-sort recovery.  Mostly
           redundant given (1) — every `Array_<T>` sort is
           created via `_get_array_sort` which populates
           `_array_element_sorts` at creation time — but kept as
           defence-in-depth against a future code path that
           bypasses `_get_array_sort`.
        """
        sort_name = str(array_sort)
        # 1. Direct map (populated at sort-creation time).
        mapped = self._array_element_sorts.get(sort_name)
        if mapped is not None:
            return mapped
        # 2. Primitive pattern match.
        if sort_name == "Array_Int":
            return z3.IntSort()
        if sort_name == "Array_Real":
            return z3.RealSort()
        if sort_name == "Array_Bool":
            return z3.BoolSort()
        if sort_name == "Array_String":
            return z3.StringSort()
        # 3. ADT-element fallback — try the stripped name, then a
        # few canonical key shapes.  `_z3_sorts` uses
        # `_adt_sort_key(name, type_args)` which produces
        # `"List<Int>"`-style keys with angle brackets; the Z3
        # sort name has those stripped via the transformation in
        # `_get_or_create_adt_sort`, so direct round-trip isn't
        # always possible — these candidates catch the common
        # generic-ADT shapes.
        elt_key = sort_name[len("Array_"):]
        for candidate in (elt_key, elt_key.replace("_", "<", 1) + ">"):
            sort = self._z3_sorts.get(candidate)
            if sort is not None:
                return sort
        return None

    def _translate_array_lit(
        self, expr: ast.ArrayLit, env: SlotEnv,
    ) -> z3.ExprRef | None:
        """Translate `[a, b, c]` to a fresh Array constant with
        `length(lit) == N` and `index(lit, i) == translate(elem_i)`
        asserted to the solver for each position (#667).

        The literal's element type is inferred from the first
        successfully-translated element's sort; if the elements
        translate to inconsistent sorts (shouldn't happen post-
        typecheck, but defensive against future relaxations), the
        first sort wins and subsequent elements that don't match
        fail the translation.

        Returns None on empty arrays (no element sort available)
        or on element translation failure.
        """
        if not expr.elements:
            return None
        raw_elements = [self.translate_expr(e, env) for e in expr.elements]
        if any(e is None for e in raw_elements):
            return None
        # Narrowed: every element translated successfully.
        element_z3s: list[z3.ExprRef] = [e for e in raw_elements if e is not None]
        element_sort = element_z3s[0].sort()
        # Defensive sort-consistency check: the type checker should
        # have rejected heterogeneous-element array literals upstream,
        # but if we receive one (e.g. due to a future relaxation in
        # the checker), bail to None rather than letting Z3 raise an
        # uncaught `Z3Exception: sort mismatch` on the per-element
        # axiom below.  See pr-review-toolkit silent-failure-hunter
        # review on PR #670.
        if any(e.sort() != element_sort for e in element_z3s[1:]):
            return None
        array_sort = self._get_array_sort(element_sort)
        lit_name = self._fresh_name("array_lit")
        lit_const = z3.Const(lit_name, array_sort)
        self._vars[lit_name] = lit_const
        # Length axiom: `length(lit) == N`.
        length_fn = self._get_length_fn(array_sort)
        self.solver.add(length_fn(lit_const) == len(expr.elements))
        # Per-element axioms: `index(lit, i) == element_i`.
        index_fn = self._get_index_fn(array_sort, element_sort)
        for i, elt in enumerate(element_z3s):
            self.solver.add(index_fn(lit_const, z3.IntVal(i)) == elt)
        return lit_const

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
        return None  # pragma: no cover

    def _translate_if(
        self, expr: ast.IfExpr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate if-then-else to Z3 If.

        Tracks the branch condition in ``_path_conditions`` while
        translating each branch so that call-site precondition checks
        (via ``check_valid``) can see which branch is active.
        """
        cond = self.translate_expr(expr.condition, env)
        if cond is None:
            # Can't translate condition — no path condition available
            then = self.translate_expr(expr.then_branch, env)
            else_ = self.translate_expr(expr.else_branch, env)
            if then is None or else_ is None:  # pragma: no cover
                return None
            return None

        # Translate then-branch with cond as path condition
        self._path_conditions.append(cond)
        then = self.translate_expr(expr.then_branch, env)
        self._path_conditions.pop()

        # Translate else-branch with Not(cond) as path condition
        self._path_conditions.append(z3.Not(cond))
        else_ = self.translate_expr(expr.else_branch, env)
        self._path_conditions.pop()

        if then is None or else_ is None:
            return None
        return z3.If(cond, then, else_)

    def _translate_call(
        self, call: ast.FnCall, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a function call via modular contract verification.

        For ``array_length()``, uses the built-in uninterpreted function.
        For user-defined functions, looks up the callee and delegates
        to ``_translate_call_with_info``.
        """
        # Built-in: array_length()
        if call.name == "array_length" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                length_fn = self._get_length_fn(arg.sort())
                result = length_fn(arg)
                self.solver.add(result >= 0)
                return result
            return None  # pragma: no cover

        # Built-in: map_size() — uninterpreted, result >= 0
        if call.name == "map_size" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                size_fn = z3.Function(
                    "map_size", arg.sort(), z3.IntSort(),
                )
                result = size_fn(arg)
                self.solver.add(result >= 0)
                return result
            return None  # pragma: no cover

        # Built-in: map_contains() — returns Bool (uninterpreted)
        if call.name == "map_contains" and len(call.args) == 2:
            return None  # opaque to verifier

        # Built-in: set_size() — uninterpreted, result >= 0
        if call.name == "set_size" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                size_fn = z3.Function(
                    "set_size", arg.sort(), z3.IntSort(),
                )
                result = size_fn(arg)
                self.solver.add(result >= 0)
                return result
            return None  # pragma: no cover

        # Built-in: set_contains() — returns Bool (uninterpreted)
        if call.name == "set_contains" and len(call.args) == 2:
            return None  # opaque to verifier

        # Built-in: abs()
        if call.name == "abs" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                import z3 as z3mod
                return z3mod.If(arg >= 0, arg, -arg)
            return None  # pragma: no cover

        # Built-in: min()
        if call.name == "min" and len(call.args) == 2:
            a = self.translate_expr(call.args[0], env)
            b = self.translate_expr(call.args[1], env)
            if a is not None and b is not None:
                import z3 as z3mod
                return z3mod.If(a <= b, a, b)
            return None  # pragma: no cover

        # Built-in: max()
        if call.name == "max" and len(call.args) == 2:
            a = self.translate_expr(call.args[0], env)
            b = self.translate_expr(call.args[1], env)
            if a is not None and b is not None:
                import z3 as z3mod
                return z3mod.If(a >= b, a, b)
            return None  # pragma: no cover

        # Built-in: nat_to_int() — identity (both IntSort in Z3)
        if call.name == "nat_to_int" and len(call.args) == 1:
            return self.translate_expr(call.args[0], env)

        # Built-in: string_length() — use z3.Length() for String sorts so that
        # Z3's string theory gives exact lengths (e.g. for literal arguments at
        # call sites).  Fall back to an uninterpreted function for other sorts.
        if call.name == "string_length" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                if isinstance(arg.sort(), z3.SeqSortRef):
                    result = z3.Length(arg)
                else:
                    length_fn = z3.Function(
                        "string_length", arg.sort(), z3.IntSort(),
                    )
                    result = length_fn(arg)
                self.solver.add(result >= 0)
                return result
            return None  # pragma: no cover

        # Built-ins: string_contains / string_starts_with / string_ends_with
        # Z3's native string theory encodes these exactly.
        # string_contains(haystack, needle) → Contains(haystack, needle)
        # string_starts_with(s, prefix)     → PrefixOf(prefix, s)
        # string_ends_with(s, suffix)       → SuffixOf(suffix, s)
        if call.name == "string_contains" and len(call.args) == 2:
            haystack = self.translate_expr(call.args[0], env)
            needle = self.translate_expr(call.args[1], env)
            if haystack is not None and needle is not None:
                return z3.Contains(haystack, needle)
            return None  # pragma: no cover

        if call.name == "string_starts_with" and len(call.args) == 2:
            s = self.translate_expr(call.args[0], env)
            prefix = self.translate_expr(call.args[1], env)
            if s is not None and prefix is not None:
                return z3.PrefixOf(prefix, s)
            return None  # pragma: no cover

        if call.name == "string_ends_with" and len(call.args) == 2:
            s = self.translate_expr(call.args[0], env)
            suffix = self.translate_expr(call.args[1], env)
            if s is not None and suffix is not None:
                return z3.SuffixOf(suffix, s)
            return None  # pragma: no cover

        # Built-ins: float_is_nan / float_is_infinite
        # Float64 maps to z3.Real (mathematical reals), which have no NaN or
        # infinity.  Returning BoolVal(False) here would be UNSOUND: the
        # compiler would skip the runtime check for requires(!float_is_nan(x)),
        # silently dropping a safety guard.  Tier 3 (runtime check) is correct.
        if call.name in ("float_is_nan", "float_is_infinite"):
            return None

        # Built-in: byte_to_int() — identity (both IntSort in Z3)
        if call.name == "byte_to_int" and len(call.args) == 1:
            return self.translate_expr(call.args[0], env)

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
            if slot_name is None:  # pragma: no cover
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
            if z3_pre is None:  # pragma: no cover
                # Can't translate precondition → bail to Tier 3
                return None
            # Check validity: solver state already has caller's assumptions
            result = self.check_valid(z3_pre, [])
            if result.status != "verified":
                # The same call site is translated more than once per
                # function (the @Nat-subtraction walker re-translates
                # let RHSes, branch conditions, and subtraction
                # operands to rebuild its state) — and for some sites,
                # e.g. inside an ExprStmt, the walker is the ONLY
                # translator.  Dedup keeps exactly one violation per
                # (call site, precondition) regardless of how many
                # passes visit it (#727).  The site is keyed by SPAN,
                # not node identity: pipe translation desugars to a
                # fresh synthetic FnCall on every pass, so the node
                # object differs while the span (copied from the pipe
                # expression) is stable.  Spanless nodes fall back to
                # object identity rather than colliding on None.
                already = any(
                    v.precondition is contract
                    and (
                        v.call_node.span == call_node.span
                        if (
                            v.call_node.span is not None
                            and call_node.span is not None
                        )
                        else v.call_node is call_node
                    )
                    for v in self._call_violations
                )
                if not already:
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
        # Mirror the parameter-declaration dispatch in
        # `vera/verifier.py::_verify_decl`: each Vera type gets a
        # typed Z3 variable.  Pre-#667 follow-up this branch only
        # handled NAT / BOOL / AdtType, falling back to
        # `declare_int` for String / Float64 / Array — so callers
        # couldn't reason about helper return values of those
        # types in postconditions.
        if base_ret == NAT:
            ret_var = self.declare_nat(fresh)
        elif base_ret == BOOL:
            ret_var = self.declare_bool(fresh)
        elif base_ret == STRING:
            ret_var = self.declare_string(fresh)
        elif base_ret == FLOAT64:
            ret_var = self.declare_float64(fresh)
        elif isinstance(base_ret, AdtType) and base_ret.name == "Array":
            # Array<T> return type — declare with a proper Array
            # sort so `result[i]` predicates on the call site can
            # reason about the result via `index_<T>`.
            element_sort: z3.SortRef | None = None
            if base_ret.type_args:
                element_sort = self._vera_type_to_z3_sort(base_ret.type_args[0])
            if element_sort is None:
                # Element type not representable in Z3 (e.g.
                # `Array<FnType<...>>`).  Signal Tier 3 cleanly
                # rather than silently type-erasing to Int — that
                # would let the caller's postcondition translate
                # against a wrong-typed result variable.  Pr-
                # review-toolkit follow-up on #670 flagged this
                # as the same silent-failure pattern #667 was
                # written to close.
                return None
            ret_var = self.declare_array_var(fresh, element_sort)
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

        # #746: a refined return type is an implicit postcondition — assume
        # its predicate on the fresh call result so a caller can rely on a
        # verified refined return (the producing function discharges the
        # predicate at its return position).  Only the 5 statically-modelled
        # primitive bases (Int/Nat/Bool/Float64/String) have a substitutable
        # binder *and* a runtime-guarded producer; an unmodelled base such as
        # `@Byte` or `@Unit` must NOT let the caller assume the predicate (for
        # `@Unit` it isn't even runtime-guarded, so assuming e.g.
        # `always_false(@Unit.0)` would add `false` → UNSAT → vacuously
        # discharge the caller's own obligations).  The base-`@Nat` `>= 0` is
        # already carried by the `declare_nat` above, so the predicate alone
        # suffices here.
        if isinstance(ret_type, RefinedType) and ret_type.base in (
            INT,
            NAT,
            BOOL,
            FLOAT64,
            STRING,
        ):
            # Push the value under the predicate's ACTUAL binder name (alias-
            # aware: `@Age.0` for `type Age = Nat; { @Age | @Age.0 >= 18 }`),
            # not the resolved base name — otherwise the predicate's `@Age.0`
            # won't resolve against `Nat` and `z3_pred` is None, silently
            # dropping the refined-return fact so a caller can't rely on it (CR
            # PR-review — the SMT analogue of the verifier/codegen binder fix).
            binder = (ast.predicate_binder_name(ret_type.predicate)
                      or ret_type.base.name)
            inner_env = SlotEnv().push(binder, ret_var)
            z3_pred = self.translate_expr(ret_type.predicate, inner_env)
            if z3_pred is not None:
                self.solver.add(z3_pred)

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
                if type_name is None:  # pragma: no cover
                    return None
                current_env = current_env.push(type_name, val)
            elif isinstance(stmt, ast.ExprStmt):
                # Side-effect statement — doesn't affect the result value
                continue
            else:
                # LetDestruct or unknown statement type
                return None  # pragma: no cover
        return self.translate_expr(block.expr, current_env)

    # -----------------------------------------------------------------
    # Match and constructor translation
    # -----------------------------------------------------------------

    def _arm_source_facts(
        self, scrutinee_ast: ast.Expr, scrutinee_z3: z3.ExprRef,
        pattern: ast.Pattern,
    ) -> list[z3.ExprRef]:
        """Source-type facts to assume while translating *pattern*'s arm body —
        via the verifier-injected ``_subpattern_fact_hook`` — so a call
        precondition inside the arm sees a refined sub-pattern binding's
        invariant (CR PR-review).  Empty when no hook is set (pure-SMT tests)
        or the pattern is not a constructor pattern."""
        if (self._subpattern_fact_hook is None
                or not isinstance(pattern, ast.ConstructorPattern)):
            return []
        facts = self._subpattern_fact_hook(
            scrutinee_ast, scrutinee_z3, pattern, self)
        return list(facts) if facts else []

    def _translate_match(
        self, expr: ast.MatchExpr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a match expression to a Z3 If-chain.

        Tracks pattern conditions in ``_path_conditions`` while
        translating each arm's body so that call-site precondition
        checks can see which arm is active.
        """
        scrutinee = self.translate_expr(expr.scrutinee, env)
        if scrutinee is None:
            return None

        # Build reverse If-chain: last arm is the default
        arms = list(expr.arms)
        if not arms:  # pragma: no cover
            return None

        # Collect preceding arm conditions for the default case
        preceding_conds: list[z3.ExprRef] = []
        for arm in arms[:-1]:
            pc = self._pattern_condition(scrutinee, arm.pattern)
            if pc is not None:
                preceding_conds.append(pc)

        # Translate last arm body (default case)
        last_env = self._bind_pattern(scrutinee, arms[-1].pattern, env)
        if last_env is None:
            return None

        # Default arm: none of the preceding patterns matched
        for pc in preceding_conds:
            self._path_conditions.append(z3.Not(pc))
        last_facts = self._arm_source_facts(
            expr.scrutinee, scrutinee, arms[-1].pattern)
        for f in last_facts:
            self._path_conditions.append(f)
            # Global implication: the fact holds whenever THIS (default) arm is
            # taken — i.e. no preceding pattern matched — so the refined-RETURN
            # goal (checked after this match translates, once path conditions
            # have popped) can use `arm-taken => fact`, not only the in-arm
            # precondition checks that read `_path_conditions` live (CR
            # PR-review).  Empty preceding ⇒ irrefutable arm ⇒ unconditional.
            if preceding_conds:
                self.solver.add(z3.Implies(
                    z3.And(*[z3.Not(pc) for pc in preceding_conds]), f))
            else:
                self.solver.add(f)
        result = self.translate_expr(arms[-1].body, last_env)
        for _ in last_facts:
            self._path_conditions.pop()
        for _ in preceding_conds:
            self._path_conditions.pop()

        if result is None:
            return None

        # Wrap preceding arms in z3.If(condition, body, previous)
        for arm in reversed(arms[:-1]):
            cond = self._pattern_condition(scrutinee, arm.pattern)
            if cond is None:  # pragma: no cover
                return None
            arm_env = self._bind_pattern(scrutinee, arm.pattern, env)
            if arm_env is None:  # pragma: no cover
                return None

            self._path_conditions.append(cond)
            arm_facts = self._arm_source_facts(
                expr.scrutinee, scrutinee, arm.pattern)
            for f in arm_facts:
                # Global implication `arm-matched => fact` (see the default-arm
                # note) so the refined-return goal sees it after the path
                # conditions pop, while the live `_path_conditions` push covers
                # in-arm precondition checks.
                self.solver.add(z3.Implies(cond, f))
                self._path_conditions.append(f)
            arm_body = self.translate_expr(arm.body, arm_env)
            for _ in arm_facts:
                self._path_conditions.pop()
            self._path_conditions.pop()

            if arm_body is None:  # pragma: no cover
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
        return None  # pragma: no cover

    def _pattern_condition(
        self, scrutinee: z3.ExprRef, pattern: ast.Pattern
    ) -> z3.ExprRef | None:
        """Return a Z3 Boolean for when *pattern* matches *scrutinee*."""
        if isinstance(pattern, ast.NullaryPattern):
            sort = scrutinee.sort()
            idx = self._find_ctor_index(sort, pattern.name)
            if idx is None:  # pragma: no cover
                return None
            return sort.recognizer(idx)(scrutinee)

        if isinstance(pattern, ast.ConstructorPattern):
            sort = scrutinee.sort()
            idx = self._find_ctor_index(sort, pattern.name)
            if idx is None:  # pragma: no cover
                return None
            return sort.recognizer(idx)(scrutinee)

        if isinstance(pattern, ast.WildcardPattern):  # pragma: no cover
            return z3.BoolVal(True)

        if isinstance(pattern, ast.BindingPattern):
            return z3.BoolVal(True)

        if isinstance(pattern, ast.IntPattern):
            return scrutinee == z3.IntVal(pattern.value)

        if isinstance(pattern, ast.BoolPattern):
            return scrutinee == z3.BoolVal(pattern.value)

        return None  # pragma: no cover

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
            if slot_name is None:  # pragma: no cover
                return None
            return env.push(slot_name, scrutinee)

        if isinstance(pattern, ast.ConstructorPattern):
            sort = scrutinee.sort()
            idx = self._find_ctor_index(sort, pattern.name)
            if idx is None:  # pragma: no cover
                return None
            cur = env
            for i, sub_pat in enumerate(pattern.sub_patterns):
                accessor = sort.accessor(idx, i)
                field_val = accessor(scrutinee)
                bound = self._bind_pattern(field_val, sub_pat, cur)
                if bound is None:  # pragma: no cover
                    return None
                cur = bound
            return cur

        return None  # pragma: no cover

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
        if idx is None:  # pragma: no cover
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
        if idx is None:  # pragma: no cover
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
                    else:  # pragma: no cover
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
        Also includes any accumulated ``_path_conditions`` from
        if/match branches so branch-guarded preconditions verify.
        - unsat → goal always holds (verified)
        - sat → counterexample found (violated)
        - unknown → solver timeout or incomplete (unknown)
        """
        self.solver.push()
        for a in assumptions:
            self.solver.add(a)
        for pc in self._path_conditions:
            self.solver.add(pc)
        self.solver.add(z3.Not(goal))

        result = self.solver.check()
        # Extract the model BEFORE popping: a Z3 model is only valid
        # while the assertions that produced it remain on the solver
        # stack.  Popping first leaves model() describing the base
        # context, so model_completion fills the now-unconstrained
        # slots with arbitrary defaults — yielding counterexamples that
        # don't witness the violation (e.g. `@Int.0 = 0` for the goal
        # `@Int.0 >= 0`).  Affects E502 / E503 / call-site precondition
        # diagnostics alike.
        ce: dict[str, str] | None = None
        if result == z3.sat:
            ce = self._extract_counterexample(self.solver.model())
        self.solver.pop()

        if result == z3.unsat:
            return SmtResult(status="verified")
        elif result == z3.sat:
            return SmtResult(status="violated", counterexample=ce)
        else:  # pragma: no cover
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
        """Reset per-function state for warm-session reuse (#222 Phase A).

        Called by the warm verification path between functions so one
        ``z3.Solver`` serves a whole program.  Everything tied to the
        previous function's solver assertions must go; only the ADT
        registry (pure Python metadata, identical across functions of
        one program) persists.

        ``_length_fns`` / ``_index_fns`` MUST be cleared even though
        their ``FuncDeclRef`` objects stay valid across
        ``solver.reset()``: their side-effect axioms do not.
        ``get_rank_fn`` asserts its ``ForAll rank(x) >= 0`` axiom only
        at dict-miss, so a surviving cache entry would silently skip
        re-asserting the axiom into the reset solver and ADT-measure
        ``decreases`` checks would diverge from a fresh context (caught
        by the cold-vs-warm differential tests in test_obligations.py).
        """
        self.solver.reset()
        # solver.reset() drops assertions but keeps parameters; re-apply
        # the timeout anyway so reuse never depends on that detail.
        self.solver.set("timeout", self._timeout_ms)
        self._vars.clear()
        self._result_var = None
        self._call_violations.clear()
        self._fresh_counter = 0
        self._path_conditions.clear()
        self._length_fns = {
            "Int": z3.Function("length", z3.IntSort(), z3.IntSort()),
        }
        self._index_fns.clear()
        self._array_element_sorts.clear()
        # Keep _adt_registry and _ctor_to_adt (they persist across functions)
        # but clear cached Z3 sorts (tied to solver state)
        self._z3_sorts.clear()
