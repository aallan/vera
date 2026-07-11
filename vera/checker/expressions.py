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
    contains_typevar,
    base_type,
    erases_to_unit,
    is_subtype,
    numeric_join,
    pretty_type,
    types_equal,
)

# Machine bounds for the integer types (#812): `@Int` is i64, `@Nat` is u64.  An
# integer literal must fit its target type's range — otherwise codegen's
# fixed-width `i64.const` either hard-fails (> u64.MAX) or silently reinterprets
# the bit pattern (an `@Int` literal in (i64.MAX, u64.MAX] runs as a negative)
# while the verifier reasons over the unbounded mathematical value.
_I64_MAX = 2**63 - 1
_I64_MIN = -(2**63)
_U64_MAX = 2**64 - 1


class ExpressionsMixin:
    """Mixin providing expression type synthesis and related methods."""

    # -----------------------------------------------------------------
    # Expression type synthesis
    # -----------------------------------------------------------------

    def _synth_expr(self, expr: ast.Expr, *,
                    expected: Type | None = None) -> Type | None:
        """Synthesise an expression's type, recording it when artifact
        collection is on (#222 Phase D).

        Thin wrapper around :meth:`_synth_expr_impl` (the dispatcher):
        every synthesis — including recursive sub-expression calls —
        flows through here, so the ``expr_types`` side-table covers the
        whole tree.  With collection off (``self.expr_types is None``,
        the default), this adds a single attribute test per expression.
        """
        result = self._synth_expr_impl(expr, expected=expected)
        if self.expr_types is not None and expr.span is not None:
            key = ast.span_key(expr)
            if result is not None:
                self.expr_types[key] = pretty_type(result)
                # #747: parallel table of *semantic* result types, so the
                # verifier can resolve the type of a scrutinee / RHS /
                # constructor-call at a deferred narrowing site.
                if self.expr_semantic_types is not None:
                    self.expr_semantic_types[key] = result
            # #747: the ``expected`` (instantiated target) type the
            # expression was checked against — e.g. a generic formal or
            # field fixed to @Nat at this call/construction site.
            if self.expr_target_types is not None and expected is not None:
                self.expr_target_types[key] = expected
        return result

    def _synth_expr_impl(self, expr: ast.Expr, *,
                         expected: Type | None = None) -> Type | None:
        """Synthesise the type of an expression.  Returns None on error.

        When *expected* is provided, it is threaded to constructors,
        if/match, and blocks so that nullary constructors of parameterised
        ADTs can resolve their TypeVars from context (bidirectional checking).

        # WALKER_COVERAGE: (#597 — canonical "must handle every Expr"
        # dispatcher.  Every subclass below has an explicit
        # isinstance branch; check_walker_coverage.py enforces it.)
        #
        # Handled (every Expr subclass):
        #   IntLit            → Int (or Byte via bidirectional check)
        #   FloatLit          → Float64
        #   BoolLit           → Bool
        #   UnitLit           → Unit
        #   StringLit         → String
        #   InterpolatedString → String (sub-exprs type-checked)
        #   HoleExpr          → emits E170, returns None
        #   SlotRef           → resolved from current slot env
        #   ResultRef         → emits E131 outside ensures
        #   BinaryExpr        → arith/cmp/logic dispatch
        #   UnaryExpr         → neg/not dispatch
        #   IndexExpr         → element type of indexed collection
        #   FnCall            → function-table lookup + arg check
        #   QualifiedCall     → effect-op dispatch
        #   ModuleCall        → imported-module lookup
        #   ConstructorCall   → ADT constructor type
        #   NullaryConstructor → ADT nullary constructor type
        #   AnonFn            → fn-type from param + body
        #   IfExpr            → unified branch type
        #   MatchExpr         → unified arm type
        #   Block             → trailing expr type (or Unit)
        #   HandleExpr        → body type minus handled effect
        #   AssertExpr        → Unit
        #   AssumeExpr        → Unit
        #   ForallExpr        → Bool (predicate type-checked under binders)
        #   ExistsExpr        → Bool
        #   OldExpr           → snapshot of inner expr (ensures-only)
        #   NewExpr           → snapshot of inner expr (ensures-only)
        #   ArrayLit          → Array<element-type>
        #
        # No "Cannot occur" entries: every Expr subclass is reachable
        # by the type checker since it's the first compiler pass that
        # sees user code.  This walker is the canonical complete set
        # against which the other walkers are audited.
        """
        if isinstance(expr, ast.IntLit):
            # Byte coercion: integer literals 0–255 accepted as Byte when
            # the expected type resolves to Byte (bidirectional checking).
            # #865: see through a refinement wrapper (`{ @Byte | P }`, incl.
            # via a `type SmallByte = { @Byte | P }` alias) with `base_type`,
            # not a bare `isinstance(expected, PrimitiveType)` — otherwise
            # `let @{ @Byte | @Byte.0 < 10 } = 5` fell through to @Nat and
            # rejected the literal with E170, the same coercion gap as the
            # #865 call-argument site (the predicate is deferred to the
            # verifier, which is exactly how a `@Byte` argument to a refined
            # parameter is already handled).
            if (expected is not None
                    and base_type(expected) == BYTE
                    and 0 <= expr.value <= 255):
                return BYTE
            # #812: range-check the literal against its target machine type
            # before typing it.  The target's base type (refinements stripped)
            # decides the bound: an `@Int` context is i64 (max 2^63-1), anything
            # else — `@Nat`, or no expected type, where a non-negative literal
            # defaults to `@Nat` below — is u64 (max 2^64-1).  A literal past its
            # bound is a clean error here instead of (loud) an opaque
            # `i64.const … out of range` codegen failure or (silent, unsound) a
            # Tier-1 proof over a value the i64 runtime reinterprets.
            base = base_type(expected) if expected is not None else None
            targets_int = (isinstance(base, PrimitiveType)
                           and base.name == "Int")
            bound = _I64_MAX if targets_int else _U64_MAX
            if expr.value > bound:
                type_name = "@Int (i64)" if targets_int else "@Nat (u64)"
                self._error(
                    expr,
                    f"Integer literal {expr.value} is out of range for "
                    f"{type_name}; the maximum is {bound}.",
                    rationale=(
                        "Integer literals are fixed-width at runtime — `@Int` "
                        "is a signed 64-bit integer, `@Nat` an unsigned one.  A "
                        "literal beyond the type's range cannot be represented: "
                        "codegen would either reject it or silently reinterpret "
                        "its bit pattern, diverging from what the verifier "
                        "proved (#812)."
                    ),
                    fix=(
                        "Use a literal within the type's range, or choose a "
                        "wider target type (`@Nat` reaches "
                        f"{_U64_MAX} where `@Int` stops at {_I64_MAX})."
                    ),
                    spec_ref='Chapter 4, Section 4.2 "Literals"',
                    error_code="E149",
                )
            # Non-negative integer literals are Nat (which is a subtype of
            # Int).  This lets literals like 0, 1, 42 satisfy Nat parameters
            # without refinement verification.
            return NAT if expr.value >= 0 else INT
        if isinstance(expr, ast.FloatLit):
            return FLOAT64
        if isinstance(expr, ast.StringLit):
            return STRING
        if isinstance(expr, ast.InterpolatedString):
            return self._check_interpolated_string(expr)
        if isinstance(expr, ast.BoolLit):
            return BOOL
        if isinstance(expr, ast.UnitLit):
            return UNIT
        if isinstance(expr, ast.HoleExpr):
            return self._check_hole(expr, expected=expected)
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
            result = self._check_fn_call(expr)
            # Bidirectional coercion: when a generic call returns a type
            # with unresolved TypeVars (e.g. map_new() → Map<K, V>) and
            # we have an expected concrete type (e.g. Map<String, Int>),
            # use the expected type if structurally compatible.
            if (result is not None
                    and expected is not None
                    and contains_typevar(result)
                    and not contains_typevar(expected)
                    and isinstance(result, AdtType)
                    and isinstance(expected, AdtType)
                    and result.name == expected.name
                    and len(result.type_args) == len(expected.type_args)):
                return expected
            return result
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
            return self._check_array_lit(expr, expected=expected)
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
        self._error(
            expr,
            f"Unknown expression type: {type(expr).__name__}",
            rationale=(
                "The type checker reached an expression form it does not "
                "recognise; only the expression forms defined by the language "
                "may appear here."
            ),
            fix=(
                "Rewrite the expression using a supported form (literal, slot "
                "reference, operator, call, if/match, block, or quantifier). If "
                "this is valid Vera, it signals a compiler bug — please report "
                "it."
            ),
            spec_ref='Chapter 4, Section 4.1 "Overview"',
            error_code="E176",
        )
        return None

    # -----------------------------------------------------------------
    # String interpolation
    # -----------------------------------------------------------------

    # Types that have a corresponding *_to_string builtin.
    _TO_STRING_TYPES: dict[str, str] = {
        "Int": "to_string",
        "Nat": "nat_to_string",
        "Bool": "bool_to_string",
        "Byte": "byte_to_string",
        "Float64": "float_to_string",
    }

    def _check_interpolated_string(
        self, expr: ast.InterpolatedString,
    ) -> Type:
        """Type-check an interpolated string expression."""
        for part in expr.parts:
            if isinstance(part, str):
                continue
            part_ty = self._synth_expr(part)
            if part_ty is None:
                continue  # error already emitted
            # String expressions are fine as-is
            if is_subtype(part_ty, STRING):
                continue
            # Check for auto-convertible primitive types
            type_name = (
                part_ty.name
                if isinstance(part_ty, PrimitiveType)
                else None
            )
            if type_name not in self._TO_STRING_TYPES:
                self._error(
                    part,
                    f"Type '{pretty_type(part_ty)}' cannot be "
                    f"automatically converted to String in string "
                    f"interpolation. Only String, Int, Nat, Bool, "
                    f"Byte, and Float64 are supported.",
                    rationale=(
                        "An interpolated expression must be String or a "
                        "primitive with a built-in string conversion; other "
                        "types have no automatic rendering."
                    ),
                    fix=(
                        "Convert the value to String before interpolating, e.g. "
                        "call a *_to_string builtin or wrap it in an explicit "
                        "conversion that yields String."
                    ),
                    spec_ref='Chapter 4, Section 4.13.1 "String Interpolation"',
                    error_code="E148",
                )
        return STRING

    # -----------------------------------------------------------------
    # Slot references
    # -----------------------------------------------------------------

    def _check_slot_ref(self, ref: ast.SlotRef) -> Type | None:
        """Type-check @T.n slot reference."""
        tname = self._slot_type_name(ref.type_name, ref.type_args)
        resolved = self.env.resolve_slot(tname, ref.index)
        if resolved is None:
            count = self.env.count_bindings(tname)
            # #973: a failed slot resolution whose type is the state of the
            # INNERMOST enclosing handler's HANDLED BODY — and for which no
            # real binding exists — is almost certainly an attempt to read
            # handler state directly, which is not a slot there.  Steer the
            # user to the typed operation.  The gate is deliberately narrow
            # (PR #975 review): with a real same-typed binding in scope the
            # likely fix is a lower index, and under nested different-typed
            # handlers get(()) reaches the innermost state, so only its type
            # may carry the hint.
            if (count == 0
                    and self._handler_body_state_tnames
                    and tname == self._handler_body_state_tnames[-1]):
                fix = (
                    f"Handler state is not a slot in the handled body — read "
                    f"it through the typed operation: get(()) returns the "
                    f"current {tname} state, and put(<{tname}>) updates it."
                )
            elif (count == 0
                    and self._where_helper_outer_tnames
                    and tname in self._where_helper_outer_tnames[-1]):
                # #969: inside a where-helper body, an unresolved slot whose
                # type the PARENT function binds is almost certainly an attempt
                # to read the outer parameter.  where-helpers are closed,
                # param-rooted scopes — steer the user to pass the value in.
                # The gate is narrow (PR review discipline mirroring #973):
                # empty outside helper bodies, and only the parent's own param
                # types carry the hint, so an unrelated unresolved slot keeps
                # the generic lower-index message.
                fix = (
                    f"where-helpers are closed, param-rooted scopes (spec §5): "
                    f"the outer function's @{tname} slot is not in scope here. "
                    f"Pass it as an explicit argument — add @{tname} to the "
                    f"helper's parameters and pass the value at the call site."
                )
            else:
                fix = (f"Ensure enough {tname} bindings are in scope, or use a "
                       f"lower index.")
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
                fix=fix,
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
                spec_ref='Chapter 3, Section 3.6 "The `@result` Reference"',
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
        # #861: inside a refinement predicate over a `@Byte` BASE (§2.6),
        # an integer literal compared against a Byte-typed operand is typed
        # against Byte, not Nat.  `@Byte.0 < 10` has a defined i32
        # runtime-guard lowering (#766's `_translate_byte_binop`), so —
        # unlike a general expression, where Byte-vs-Nat is E142 (no
        # implicit numeric coercion, DESIGN §0.2.2) — the literal takes the
        # binder's Byte type here.  A literal is not a runtime value, so
        # this is literal-typing-from-context (the same rule that lets
        # `small(7)` pass a Byte parameter), not a coercion.  Keyed on the
        # INNERMOST active refinement base resolving to Byte (PR #876
        # review): a Byte-typed operand inside an `@Int`-based refinement
        # (`{ @Int | b(@Int.0) < 10 }` with `b : Int -> Byte`) stays E142.
        if (self.env.refinement_bases
                and base_type(self.env.refinement_bases[-1]) == BYTE):
            if (isinstance(expr.right, ast.IntLit)
                    and base_type(left_ty) == BYTE):
                right_ty = self._synth_expr(expr.right, expected=BYTE)
            elif (isinstance(expr.left, ast.IntLit)
                    and base_type(right_ty) == BYTE):
                left_ty = self._synth_expr(expr.left, expected=BYTE)
            if left_ty is None or right_ty is None:
                return None
        if isinstance(left_ty, UnknownType) or isinstance(right_ty, UnknownType):
            return UnknownType()

        op = expr.op

        # #981: a bare nullary constructor operand of `==`/`!=` (e.g. `None`)
        # is synthesized with no expected type, so `@Option<T>.result == None`
        # compares Option<T> with an unrelated Option<T$1> and is rejected
        # E142 — for both operand orders, and even at a concrete Option<Int>.
        # Give the constructor operand its sibling's known ADT type as expected
        # so the #971 fill in `_ctor_result_type` adopts the declared var.
        left_ty, right_ty = self._resynth_eq_ctor_operand(
            op, expr, left_ty, right_ty)

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
                    fix=(
                        f"Apply '{op.value}' to numeric operands (Int, Nat, or "
                        "Float64); convert any non-numeric operand to a numeric "
                        "type first."
                    ),
                    spec_ref='Chapter 4, Section 4.4 "Arithmetic Expressions"',
                    error_code="E140",
                )
                return UnknownType()
            # Mixed numeric arithmetic joins to the *formal* least-upper-bound:
            # Nat <op> Int (either order) => Int, since only Nat <: Int is a
            # formal subtyping rule (Nat = { @Int | @Int.0 >= 0 }; spec §2.2.1).
            # Do NOT use the bidirectional is_subtype here — its Int <: Nat clause
            # is a verifier-mediated narrowing relaxation, and treating it as a
            # widening typed `Int <op> Nat` as Nat (#755), dishonestly asserting
            # non-negativity with no verifier obligation (§0.2.2).
            joined = numeric_join(left_base, right_base)
            if joined is not None:
                return joined
            self._error(
                expr,
                f"Operator '{op.value}' requires matching numeric types, "
                f"found {pretty_type(left_ty)} and {pretty_type(right_ty)}.",
                rationale="Both operands must be the same numeric type "
                          "(or Nat where Int is expected).",
                fix=(
                    "Make both operands the same numeric type. Vera has no "
                    "implicit numeric coercion — e.g. convert the Int operand "
                    "to Float64 (or vice versa) so both sides match."
                ),
                spec_ref='Chapter 4, Section 4.4 "Arithmetic Expressions"',
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
                    fix=(
                        "Compare values of the same type. One must be a subtype "
                        "of the other — convert one operand so both sides share "
                        "a type before applying '==' or '!='."
                    ),
                    spec_ref='Chapter 4, Section 4.5 "Comparison Expressions"',
                    error_code="E142",
                )
            else:
                # #928: `==` / `!=` is the surface spelling of the `Eq` ability
                # (§9.8.1), so the operand type must be Eq-DERIVABLE — not merely
                # compatible.  Without this gate a non-Eq `==` (two function
                # values, or a State<Rec>/composite whose field is a Map) passes
                # check AND compiles: unlike the direct-ADT path (which routes
                # through `_translate_adt_eq` and raises a clean E613), it falls
                # to a raw i32/pointer compare that never reaches the structural-
                # Eq derivability dispatch — a SILENT pointer-identity comparison
                # (the equality sibling of #921's ordering hole).  Reject here,
                # the earliest and loudest gate, mirroring #921's E242 for Ord.
                self._check_eq_ability(expr, left_ty, right_ty)
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
                    rationale=(
                        "Ordering operators (<, >, <=, >=) are defined only on "
                        "orderable types — the numeric types and other types "
                        "with a total order."
                    ),
                    fix=(
                        f"Apply '{op.value}' to orderable operands (e.g. Int, "
                        "Nat, Float64); a non-orderable type must be reduced to "
                        "an orderable value before comparing."
                    ),
                    spec_ref='Chapter 4, Section 4.5 "Comparison Expressions"',
                    error_code="E143",
                )
            elif not (is_subtype(left_base, right_base)
                      or is_subtype(right_base, left_base)):
                # #797: both operands orderable but mutually incompatible (e.g.
                # `@Float64 < @Int`).  Vera has no implicit numeric coercion — the
                # arithmetic (E141) and equality (E142) arms already reject mixed
                # Float64/Int, so ordering must too.  Without this the pair
                # reached the SMT layer and raised an uncaught Z3 sort mismatch
                # once @Float64 became an FP sort (no Int<->FP coercion).
                self._error(
                    expr,
                    f"Cannot compare {pretty_type(left_ty)} with "
                    f"{pretty_type(right_ty)}.",
                    rationale="Ordering comparison requires compatible types.",
                    fix=(
                        "Order values of the same type. Vera has no implicit "
                        "numeric coercion — convert one operand (e.g. Int to "
                        "Float64) so both sides share a type before comparing."
                    ),
                    spec_ref='Chapter 4, Section 4.5 "Comparison Expressions"',
                    error_code="E142",
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
                    rationale=(
                        "Logical operators (&&, ||, ==>) combine Bool values; "
                        "their left operand must already be Bool."
                    ),
                    fix=(
                        "Make the left operand a Bool — e.g. compare it to a "
                        f"value to yield a Bool before applying '{op.value}'."
                    ),
                    spec_ref='Chapter 4, Section 4.6 "Logical Expressions"',
                    error_code="E144",
                )
            if not is_subtype(right_base, BOOL):
                self._error(
                    expr,
                    f"Right operand of '{op.value}' must be Bool, found "
                    f"{pretty_type(right_ty)}.",
                    rationale=(
                        "Logical operators (&&, ||, ==>) combine Bool values; "
                        "their right operand must already be Bool."
                    ),
                    fix=(
                        "Make the right operand a Bool — e.g. compare it to a "
                        f"value to yield a Bool before applying '{op.value}'."
                    ),
                    spec_ref='Chapter 4, Section 4.6 "Logical Expressions"',
                    error_code="E145",
                )
            return BOOL

        return UnknownType()

    def _resynth_eq_ctor_operand(
        self, op: ast.BinOp, expr: ast.BinaryExpr,
        left_ty: Type, right_ty: Type,
    ) -> tuple[Type, Type]:
        """Re-synth a bare constructor operand of `==`/`!=` bidirectionally.

        #981: the operands of a comparison are each synthesized with no
        expected type, so a nullary constructor (`None`) mints a fresh ctor var
        that never unifies with its sibling's declared type — `Option<T>` vs
        `Option<T$1>` (a `forall<T>` postcondition) or even `Option<Int>` vs
        `Option<T$1>` (a concrete comparison), both rejected E142.  When an
        operand is a constructor expression whose type still carries an
        unresolved var and the other operand has a resolved ADT type, re-synth
        the constructor operand against that type so the #971 bidirectional fill
        can adopt the sibling's type arguments.  The sibling may itself be a
        constructor (`Some(5) == None`, #993) — what matters is that the
        adopted-FROM side is resolved: two unresolved ctor operands
        (`None == None`) still fall through to E142.  Restricting to `==`/`!=`
        (ADTs are neither numeric nor orderable) and to a still-unresolved ctor
        type keeps this from re-typing (and possibly re-diagnosing) any operand
        that was already well-typed, and the fill's
        `expected.name == ci.parent_type` guard rejects a genuinely cross-ADT
        comparison (`Result<..> == None`) exactly as before.
        """
        if op not in (ast.BinOp.EQ, ast.BinOp.NEQ):
            return left_ty, right_ty
        left_base = base_type(left_ty)
        right_base = base_type(right_ty)
        if is_subtype(left_base, right_base) or is_subtype(
            right_base, left_base
        ):
            return left_ty, right_ty  # already compatible — nothing to fix
        left_ctor = isinstance(
            expr.left, (ast.ConstructorCall, ast.NullaryConstructor))
        right_ctor = isinstance(
            expr.right, (ast.ConstructorCall, ast.NullaryConstructor))
        if (right_ctor
                and contains_typevar(right_ty)
                and isinstance(left_ty, AdtType)
                and not (left_ctor and contains_typevar(left_ty))):
            new_right = self._synth_expr(expr.right, expected=left_ty)
            if new_right is not None and not isinstance(
                    new_right, UnknownType):
                right_ty = new_right
        elif (left_ctor
                and contains_typevar(left_ty)
                and isinstance(right_ty, AdtType)
                and not (right_ctor and contains_typevar(right_ty))):
            new_left = self._synth_expr(expr.left, expected=right_ty)
            if new_left is not None and not isinstance(
                    new_left, UnknownType):
                left_ty = new_left
        return left_ty, right_ty

    def _check_eq_ability(
        self, node: ast.Node, left_ty: Type, right_ty: Type,
    ) -> None:
        """Reject `==` / `!=` / `eq` on a non-Eq-derivable operand type (#928).

        `Eq` is the ability behind equality (§9.8.1); it derives STRUCTURALLY
        (§9.8.2) for the Eq primitives, simple enums, and ADTs whose fields are
        (recursively) all Eq — but NOT for function types, `Array` / `Map` /
        `Set` / `Tuple`, or an ADT/State-composite carrying such a field.  A
        non-derivable operand that slips past here reaches codegen and silently
        pointer-compares (identity, not value), so this is the load-bearing
        soundness gate — its verdict is kept in lockstep with codegen's
        structural-Eq dispatch by the #928 differential.

        A TypeVar operand (a `forall<T where Eq<T>>` body) is DEFERRED: the
        `Eq<T>` constraint promises derivability and the monomorphizer's E613
        gate re-checks every concrete instantiation, so rejecting here would
        break the legitimate constrained-generic form.  `UnknownType` is
        likewise deferred (error recovery — no cascading E243).
        """
        from vera.checker.eq_ability import is_eq_derivable

        # Defer any operand still carrying a type variable — a constrained
        # generic (`Eq<T>`) is decided per-instantiation downstream, exactly as
        # #921 defers a bare-TypeVar Ord operand.  `contains_typevar` catches
        # nested forms (`Box<T>`, `Option<T>`) too, so a generic body's `==`
        # over a partially-generic type is never spuriously rejected here.
        if (contains_typevar(left_ty) or contains_typevar(right_ty)
                or isinstance(left_ty, UnknownType)
                or isinstance(right_ty, UnknownType)):
            return
        # The compatibility check (E142) already ran; judge the more specific
        # (subtype) operand — they share a type up to Nat<:Int, and Eq-ness is
        # invariant across that pair (both Nat and Int are Eq primitives).
        if is_eq_derivable(left_ty, self.env):
            return
        self._error(
            node,
            f"Type {pretty_type(left_ty)} does not satisfy the 'Eq' ability; "
            f"'==' / '!=' requires both operands to be Eq-derivable.",
            rationale=(
                "Equality ('==' / '!=', the surface spelling of the Eq "
                "ability) is defined only on Eq-derivable types — the Eq "
                "primitives (Int, Nat, Bool, Float64, String, Byte, Unit) and "
                "ADTs whose fields are (recursively) all Eq. A function type, "
                "an Array / Map / Set / Tuple, or a composite carrying such a "
                "field has no structural equality, so comparing it would fall "
                "to a raw pointer comparison — identity, not value equality."
            ),
            fix=(
                "Compare Eq-derivable values instead. Reduce the operand to an "
                "Eq-derivable value first (e.g. an Eq primitive or an ADT whose "
                "every field is itself Eq); functions and Array / Map / Set / "
                "Tuple values are not Eq-comparable."
            ),
            spec_ref='Chapter 9, Section 9.8.1 "Built-in Abilities"',
            error_code="E243",
        )

    def _check_pipe(self, expr: ast.BinaryExpr) -> Type | None:
        """Type-check pipe: left |> right (right must be a FnCall/ModuleCall)."""
        left_ty = self._synth_expr(expr.left)
        if left_ty is None:
            return None

        # The right side should be a FnCall — prepend left as first arg
        if isinstance(expr.right, ast.FnCall):
            # Create a virtual call with left prepended
            all_args = (expr.left,) + expr.right.args
            return self._check_call_with_args(
                expr.right.name, all_args, expr.right)
        # Module-qualified pipe: left |> mod::fn(args) → mod::fn(left, args)
        if isinstance(expr.right, ast.ModuleCall):
            desugared = ast.ModuleCall(
                path=expr.right.path,
                name=expr.right.name,
                args=(expr.left,) + expr.right.args,
                span=expr.right.span,
            )
            return self._check_module_call(desugared)
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
                    rationale=(
                        "Logical negation '!' is defined only on Bool; it has "
                        "no meaning for non-Bool operands."
                    ),
                    fix=(
                        "Apply '!' to a Bool — e.g. negate a comparison or a "
                        "predicate that already yields Bool."
                    ),
                    spec_ref='Chapter 4, Section 4.6 "Logical Expressions"',
                    error_code="E146",
                )
            return BOOL

        if expr.op == ast.UnaryOp.NEG:
            if operand_base not in NUMERIC_TYPES:
                self._error(
                    expr,
                    f"Operator '-' requires numeric operand, found "
                    f"{pretty_type(operand_ty)}.",
                    rationale=(
                        "Unary negation '-' is defined only on the numeric "
                        "types (Int, Nat, Float64)."
                    ),
                    fix=(
                        "Apply '-' to a numeric operand; convert a non-numeric "
                        "value to Int, Nat, or Float64 before negating it."
                    ),
                    spec_ref='Chapter 4, Section 4.4 "Arithmetic Expressions"',
                    error_code="E147",
                )
                return UnknownType()
            # #812: a negated integer literal `-m` is an `@Int` (i64), whose
            # magnitude may reach 2^63 (forming i64.MIN = -2^63) but no further.
            # The operand literal `m` is checked above against the u64 bound (it
            # has no `@Int` context under the negation), so the band
            # (2^63, u64.MAX] slips past — and would reinterpret to a wrong value
            # at runtime (e.g. `-9223372036854775809` runs to 9223372036854775807).
            # Reject it here.  (`m > u64.MAX` is already E149 at the operand, so
            # cap at u64.MAX to avoid a double diagnostic.)
            if (isinstance(expr.operand, ast.IntLit)
                    and 2**63 < expr.operand.value <= _U64_MAX):
                self._error(
                    expr,
                    f"Integer literal -{expr.operand.value} is out of range "
                    f"for @Int (i64); the minimum is {_I64_MIN}.",
                    rationale=(
                        "A negated integer literal is a signed 64-bit `@Int`; "
                        "its magnitude must fit the i64 range, which is "
                        "asymmetric (the minimum -2^63 has magnitude 2^63, but "
                        "no negative value goes below it).  A larger magnitude "
                        "would reinterpret its bit pattern at runtime (#812)."
                    ),
                    fix=(
                        "Use a value within the signed 64-bit range "
                        f"({_I64_MIN} .. {_I64_MAX})."
                    ),
                    spec_ref='Chapter 4, Section 4.2 "Literals"',
                    error_code="E149",
                )
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
                        rationale=(
                            "Array elements are addressed by integer position, "
                            "so the index expression must be an Int or Nat."
                        ),
                        fix=(
                            "Use an Int or Nat index — convert the index "
                            "expression to an integer type before indexing."
                        ),
                        spec_ref='Chapter 4, Section 4.12.2 "Array Indexing"',
                        error_code="E160",
                    )
            return elem_type

        self._error(
            expr.collection,
            f"Cannot index {pretty_type(coll_ty)}: indexing requires "
            f"Array<T>.",
            rationale=(
                "The index operator [] is defined only on Array<T>; other "
                "types have no positional element access."
            ),
            fix=(
                "Index an Array<T> value. If the collection is not an array, "
                "obtain its elements another way (e.g. pattern-match an ADT or "
                "use a built-in accessor)."
            ),
            spec_ref='Chapter 4, Section 4.12.2 "Array Indexing"',
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
        # #861: the annotation may carry a refinement whose predicate must be
        # checked — pre-fix, a non-Bool predicate here was check-green and
        # then crashed `vera verify` (uncaught Z3Exception in the refined-
        # binding obligation).
        self._check_refinement_predicates(stmt.type_expr)
        declared_type = self._resolve_type(stmt.type_expr)
        val_type = self._synth_expr(stmt.value, expected=declared_type)

        if val_type and not isinstance(val_type, UnknownType):
            if not isinstance(declared_type, UnknownType):
                if not is_subtype(val_type, declared_type):
                    self._error(
                        stmt.value,
                        f"Let binding expects {pretty_type(declared_type)}, "
                        f"value has type {pretty_type(val_type)}.",
                        rationale=(
                            "A let binding's value must be a subtype of the "
                            "binding's declared type."
                        ),
                        fix=(
                            f"Give the value type {pretty_type(declared_type)}, "
                            "or change the binding's declared type to match the "
                            f"value's type {pretty_type(val_type)}."
                        ),
                        spec_ref='Chapter 4, Section 4.7 "Let Bindings"',
                        error_code="E170",
                    )

        tname = self._type_expr_to_slot_name(stmt.type_expr)
        self.env.bind(tname, declared_type, "let")

    def _check_let_destruct(self, stmt: ast.LetDestruct) -> None:
        """Type-check a destructuring let."""
        self._synth_expr(stmt.value)

        for te in stmt.type_bindings:
            self._check_refinement_predicates(te)  # #861
            resolved = self._resolve_type(te)
            tname = self._type_expr_to_slot_name(te)
            self.env.bind(tname, resolved, "destruct")

    # -----------------------------------------------------------------
    # Anonymous functions
    # -----------------------------------------------------------------

    def _check_anon_fn(self, expr: ast.AnonFn) -> Type | None:
        """Type-check an anonymous function."""
        # #861: closure signatures carry the same refinement positions as
        # top-level fn signatures.
        for param_te in expr.params:
            self._check_refinement_predicates(param_te)
        self._check_refinement_predicates(expr.return_type)
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
                    rationale=(
                        "An anonymous function's body must produce a value that "
                        "is a subtype of its declared return type."
                    ),
                    fix=(
                        f"Make the body yield {pretty_type(ret_type)}, or change "
                        "the closure's declared return type to "
                        f"{pretty_type(body_type)}."
                    ),
                    spec_ref='Chapter 5, Section 5.7 "Anonymous Functions (Closures)"',
                    error_code="E171",
                )

        return FunctionType(param_types, ret_type, eff)

    # -----------------------------------------------------------------
    # Arrays
    # -----------------------------------------------------------------

    def _check_array_lit(self, expr: ast.ArrayLit, *,
                         expected: Type | None = None) -> Type | None:
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

        # #945: a bare array literal `[()]` whose element erases to a zero-size
        # type has no valid WASM layout (the store acts on an empty stack →
        # invalid WASM on a check-green program).  Reject at check, mirroring
        # the `Array<T>` type-resolution gate (E135) — this catches the
        # un-annotated literal (`array_length([()])`) that never flows through
        # `_resolve_type`.
        #
        # PR #938 review: when this literal is the RHS of an annotated
        # `Array<zero-size>` binding/return, `_resolve_type` has ALREADY emitted
        # E135 for that annotation (it returns the `Array<Unit>` type intact —
        # resolution.py:178), so a second, literal-level E135 would double the
        # diagnostic for one root cause.  Suppress it when `expected` is already
        # a zero-size array; the un-annotated literal (`expected` is None, or a
        # non-degenerate expected type) still reports here — its only gate.
        # `expected` may be a `RefinedType` (`{ @Array<Unit> | pred }`), so
        # strip to the base first (as `erases_to_unit` itself does) — otherwise
        # the refined shape misses this guard and the literal-level E135
        # double-fires alongside the annotation's (PR #938 review).
        expected_base = base_type(expected) if expected is not None else None
        expected_is_zero_size_array = (
            isinstance(expected_base, AdtType)
            and expected_base.name == "Array"
            and len(expected_base.type_args) == 1
            and erases_to_unit(expected_base.type_args[0])
        )
        if erases_to_unit(first) and not expected_is_zero_size_array:
            self._error(
                expr,
                f"An array literal of a zero-size element type "
                f"'{pretty_type(first)}' is not supported.",
                rationale="A zero-size type (`Unit`, or a `Future` wrapping "
                "one) occupies 0 bytes and has no runtime value, so an array "
                "element of that type has no WASM representation to store — the "
                "literal would compile to invalid WASM.",
                fix="Use `Nat` for a count of zero-size items, or give the "
                "element type a runtime value (e.g. `[1, 2, 3]`).",
                spec_ref='Chapter 2, Section 2.2 "Primitive Types"',
                error_code="E135",
            )

        return AdtType("Array", (first,))

    # -----------------------------------------------------------------
    # Typed holes
    # -----------------------------------------------------------------

    def _collect_scope_bindings(self) -> list[tuple[str, str]]:
        """All bindings in scope, innermost first, as
        ``(slot_ref_string, pretty_type_string)`` pairs.

        Shared by the W001 hole diagnostic's fix hint and the LSP
        typed-hole completion (#222 Phase D) — same data, two
        renderings.
        """
        bindings: list[tuple[str, str]] = []
        index_by_type: dict[str, int] = {}
        for scope in reversed(self.env._scopes):
            for binding in reversed(scope):
                tname = binding.type_name
                idx = index_by_type.get(tname, 0)
                index_by_type[tname] = idx + 1
                bindings.append((f"@{tname}.{idx}",
                                  pretty_type(binding.resolved_type)))
        return bindings

    def _check_hole(self, expr: ast.HoleExpr, *,
                    expected: Type | None) -> Type:
        """Emit a hole warning with expected type and available bindings."""
        expected_str = pretty_type(expected) if expected else "unknown"

        bindings = self._collect_scope_bindings()

        if self.hole_sites is not None and expr.span is not None:
            from vera.checker.core import HoleSite
            self.hole_sites.append(HoleSite(
                line=expr.span.line,
                column=expr.span.column,
                end_line=expr.span.end_line,
                end_column=expr.span.end_column,
                expected=expected_str,
                bindings=list(bindings),
            ))

        if bindings:
            context = "; ".join(
                f"{ref}: {ty}" for ref, ty in bindings
            )
            fix_hint = (
                f"Replace ? with an expression of type {expected_str}. "
                f"Available bindings: {context}."
            )
        else:
            fix_hint = f"Replace ? with an expression of type {expected_str}."

        self._error(
            expr,
            f"Typed hole: expected {expected_str}.",
            rationale=(
                "? is a placeholder for an incomplete expression. "
                "The compiler reports the expected type and available "
                "bindings so the hole can be filled in."
            ),
            fix=fix_hint,
            spec_ref='Chapter 4, Section 4.17 "Typed Holes"',
            severity="warning",
            error_code="W001",
        )
        return expected if expected is not None else UnknownType()

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
                    rationale=(
                        "assert() states a condition to be verified, so its "
                        "argument must be a Bool predicate."
                    ),
                    fix=(
                        "Pass a Bool condition to assert() — e.g. compare the "
                        "value or call a predicate that returns Bool."
                    ),
                    spec_ref='Chapter 6, Section 6.2.5 "Assertions (`assert`)"',
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
                    rationale=(
                        "assume() introduces a condition the verifier may take "
                        "as given, so its argument must be a Bool predicate."
                    ),
                    fix=(
                        "Pass a Bool condition to assume() — e.g. compare the "
                        "value or call a predicate that returns Bool."
                    ),
                    spec_ref='Chapter 6, Section 6.2.6 "Assumptions (`assume`)"',
                    error_code="E173",
                )
        return UNIT

    # -----------------------------------------------------------------
    # Quantifiers
    # -----------------------------------------------------------------

    def _check_forall_expr(self, expr: ast.ForallExpr) -> Type | None:
        """Type-check forall(type, domain, predicate)."""
        self._check_refinement_predicates(expr.binding_type)  # #861
        self._resolve_type(expr.binding_type)
        self._synth_expr(expr.domain)
        self._synth_expr(expr.predicate)
        return BOOL

    def _check_exists_expr(self, expr: ast.ExistsExpr) -> Type | None:
        """Type-check exists(type, domain, predicate)."""
        self._check_refinement_predicates(expr.binding_type)  # #861
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
                rationale=(
                    "old() snapshots effect state from before the call, which "
                    "is only meaningful in a postcondition that relates "
                    "before- and after-states."
                ),
                fix="Move the old() expression inside an ensures() clause.",
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
                rationale=(
                    "new() snapshots effect state from after the call, which "
                    "is only meaningful in a postcondition that relates "
                    "before- and after-states."
                ),
                fix="Move the new() expression inside an ensures() clause.",
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
