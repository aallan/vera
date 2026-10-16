"""Expression type synthesis and related checking for the Vera type checker.

This mixin provides the core expression type synthesis dispatch
(_synth_expr), slot references, binary/unary operators, indexing,
blocks/statements, anonymous functions, array literals, assert/assume,
quantifiers, and old/new contract expressions.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from typing import Any, ClassVar

from vera import ast, fold, naming
from vera.checker.sql import resolve_array_len, resolve_literal_string
from vera.lowering import (
    PREDICATE_ARITY,
    PREDICATE_PARAMETER,
    PREDICATE_RESULT,
    quantifier_bound_lowerable,
    quantifier_predicate_refusals,
)
from vera.types import (
    AdtType,
    base_type,
    BOOL,
    BYTE,
    canonical_type_name,
    ConcreteEffectRow,
    contains_fresh_typevar,
    contains_typevar,
    EffectInstance,
    erases_to_unit,
    FLOAT64,
    FunctionType,
    INT,
    is_effect_subtype,
    is_subtype,
    NAT,
    literal_meets_nat,
    numeric_join,
    NUMERIC_TYPES,
    ORDERABLE_TYPES,
    pretty_effect,
    pretty_inferred_type,
    pretty_type,
    PrimitiveType,
    PureEffectRow,
    RefinedType,
    STRING,
    TO_STRING_BUILTINS,
    Type,
    types_equal,
    TypeVar,
    UNIT,
    UnknownType,
)

# Machine bounds for the integer types (#812): `@Int` is i64 and `@Nat` its
# non-negative half (spec §2.2).  An integer literal must fit — otherwise
# codegen's fixed-width `i64.const` either hard-fails or silently reinterprets
# the bit pattern (a literal above i64.MAX runs as a negative) while the
# verifier reasons over the unbounded mathematical value.  A literal's
# magnitude reaches 2^63 only under a negation, as `Int`'s minimum.
_I64_MAX = 2**63 - 1
_I64_MIN = -(2**63)


# Shared E174/E175 fix text — one copy so the two diagnostics cannot
# drift apart (PR #1180 review).
_STATE_FORM_PLACEMENT_FIX = (
    "Move the predicate into an ensures() clause. A precondition cannot "
    "constrain effect state at all: contract predicates must be pure "
    "(Section 7.9.1), and old()/new() are the only contract forms that "
    "name state."
)


# Widest `Available bindings:` table any diagnostic renders (#558).  The
# scope it reports is unbounded — one row per binding — and the LSP
# concatenates the fix into the hover message, so a wide function turns
# one diagnostic into a wall of rows.  12 sits above the measured corpus:
# across the 2,080 slot-reference positions in `tests/**/*.vera` and
# `examples/` the table is 7 rows at p95 and 11 at p99, so every site
# through the 99th percentile still renders complete and only the tail
# (12 of 2,080) elides.  The cap is a RENDERING rule — see
# `_render_scope_table` — not a change to `_collect_scope_bindings()`,
# whose other consumer is the LSP typed-hole completion, where a dropped
# row is a missing completion item.
_SCOPE_TABLE_MAX_ROWS = 12


def _render_scope_table(bindings: Sequence[tuple[str, str]]) -> str:
    """Render in-scope bindings as ``@T.n: Type; …``, capped.

    One rule for every table: the first `_SCOPE_TABLE_MAX_ROWS` rows in
    scope order, then ``; … and K more`` naming how many rows are not
    shown.  Rows are dropped off the END, so a rendered ``@T.n`` means
    the same thing capped or not — the reader can use any row printed.

    Shared by the E130 unresolved-slot fix and the W001 hole hint so the
    two cannot disagree about the scope they both describe.
    """
    shown = bindings[:_SCOPE_TABLE_MAX_ROWS]
    table = "; ".join(f"{ref}: {ty}" for ref, ty in shown)
    hidden = len(bindings) - len(shown)
    if hidden:
        table += f"; … and {hidden} more"
    return table


def _element_list(indices: Sequence[int]) -> str:
    """`element 1`, `elements 1 and 3`, `elements 1, 2 and 4`."""
    if len(indices) == 1:
        return f"element {indices[0]}"
    head = ", ".join(str(i) for i in indices[:-1])
    return f"elements {head} and {indices[-1]}"


def _holds_unknown(ty: Type) -> bool:
    """Whether a part of *ty* is the `Unknown` an unresolvable type leaves."""
    if isinstance(ty, UnknownType):
        return True
    if isinstance(ty, AdtType):
        return any(_holds_unknown(a) for a in ty.type_args)
    if isinstance(ty, FunctionType):
        return (any(_holds_unknown(p) for p in ty.params)
                or _holds_unknown(ty.return_type))
    if isinstance(ty, RefinedType):
        return _holds_unknown(ty.base)
    return False


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
        if (expected is None and self._pattern_arg_targets
                and isinstance(expr, (ast.ConstructorCall, ast.ArrayLit))):
            # #1503: a pattern that binds this construction at a composite
            # type is its context (`_register_pattern_reads`).
            pattern_key = ast.span_key(expr)
            if pattern_key is not None:
                expected = self._pattern_arg_targets.get(pattern_key)
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

        Each class's synthesis is its arm in ``_SYNTH_ARMS``, a
        ``vera.fold.dispatch`` table, so every `Expr` class has one: the type
        checker is the first pass that sees user code, so every class can
        reach it.
        """
        arm = _SYNTH_ARMS.get(type(expr))
        if arm is not None:
            return arm(self, expr, expected)
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

    # Types that have a corresponding *_to_string builtin — the shared
    # table (#1347), not a copy of it; codegen's dispatch reads the same
    # object, so the two sides cannot drift about what is interpolable.
    _TO_STRING_TYPES: ClassVar[dict[str, str]] = TO_STRING_BUILTINS

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
            # Check for auto-convertible primitive types, on the type's
            # RESOLVED form (#1347).  `base_type` unwraps refinement
            # layers; an alias is already resolved by the time a type
            # reaches here.  A refinement renders exactly as the
            # primitive it refines — the predicate constrains which
            # values exist, not how one prints — so testing
            # `isinstance(part_ty, PrimitiveType)` rejected
            # `{ @Float64 | ... }` while accepting `type C = Float64`,
            # two spellings of the same runtime value.
            resolved = base_type(part_ty)
            type_name = (
                resolved.name
                if isinstance(resolved, PrimitiveType)
                else None
            )
            if type_name not in self._TO_STRING_TYPES:
                self._error(
                    part,
                    f"Type '{pretty_inferred_type(part_ty)}' cannot be "
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
            # #558: append the slot table AT THE ERROR POSITION — deep in a
            # match arm the stack has grown past the signature, which is all
            # `--explain-slots` shows.  Rendered through the same
            # `_render_scope_table` as the W001 hole hint, so the read-time
            # and write-time diagnostics agree on both the set and the cap.
            # The table is the WHOLE scope, zero-size bindings included:
            # the index range in the description counts them, so hiding
            # them makes one diagnostic report two different scopes (a
            # `@Unit.1` against `(@Unit, @Int)` would say "valid indices:
            # 0..0" above a table with no Unit row).  A zero-size read is
            # E182's job, and it says what to write instead.
            scope = self._collect_scope_bindings()
            if scope:
                fix += f" Available bindings: {_render_scope_table(scope)}."
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
        # #1005: a zero-size slot READ resolves (the binding exists) but the
        # type compiles to no WASM local, so the read would lower to a
        # `local.get` on a local that does not exist — the dangling-slot
        # invariant behind E699.  DECLARING the binding stays legal (it
        # erases cleanly from the ABI — the same declare-vs-read line the
        # E206 generic-at-Unit guard draws via `forall_vars_read`); only
        # the read is rejected, uniformly for fn params, handler-clause op
        # params, and any other binding form.
        if erases_to_unit(resolved):
            self._error(
                ref,
                f"Cannot read @{tname}.{ref.index}: type "
                f"'{pretty_type(resolved)}' is zero-size and carries no "
                f"runtime value.",
                rationale="A zero-size type (`Unit`, or a `Future` wrapping "
                          "one) compiles to no WASM local, so a slot "
                          "reference to it resolves to no runtime location.",
                fix="Write the unit literal `()` where a Unit value is "
                    "needed; a zero-size binding exists only as a "
                    "declaration and cannot be read.",
                spec_ref='Chapter 2, Section 2.2 "Primitive Types"',
                error_code="E182",
            )
            # Error recovery: unlike the unresolved-slot arm above, this slot
            # HAS a type — return it so downstream diagnostics stay
            # meaningful (an `UnknownType` here masked the E206 call-site
            # check for `idf(@Future<Unit>.0)` and cascaded E170/E121).
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

        # #1489: a result reference's type ARGUMENTS name types, and resolve
        # like a slot reference's (`_check_slot_name_args`, which
        # `_slot_type_name` runs), so a name in one that nothing declares is
        # refused (E136) instead of being ignored.  The head is a slot-name
        # head, not a type to resolve: a function-typed result is
        # `@Fn.result`, and `Fn` names no declaration.
        key = self._slot_type_name(ref.type_name, ref.type_args)

        ret = self.env.current_return_type
        if ret is None:
            return UnknownType()
        # #1517: the reference names the result only if its name is the
        # return type's (§3.6), judged as a slot reference names its binding
        # (§3.4, §3.8): the reference's key against the key a binding of the
        # declared return type is bound under, one renderer for both.  So the
        # head stays opaque (`@Cnt.result` for a `@Cnt` return, never
        # `@Int.result`), type arguments resolve, a refinement is written as
        # its base and an inline function type as `Fn`.  The return type's
        # own diagnostics were reported when its signature was resolved, so
        # this renders it without the reporting pass, and a return type the
        # check refused where it is written is not judged again
        # (`_return_type_refused`).  `in_ensures` is set only while
        # `_check_fn` checks its own contracts, so the frame on top of the
        # scope stack is the function whose contract this is.
        fn = self._fn_scope_stack[-1]
        ret_key = naming.slot_name(fn.return_type, self._naming_env())
        if key == ret_key or self._return_type_refused(fn.return_type, ret):
            return ret
        # The message spells each type as the program does (`_as_written`): a
        # key elides a refinement's predicate, so it is a name to match and
        # not one to write.  The name the fix gives is the return type's own
        # spelling, which keys as the declaration does, so it is accepted.
        written = self._written_slot_name(fn.return_type, ret_key)
        self._error(
            ref,
            f"{self._as_written(ref, f'@{key}.result')} does not refer to "
            f"the result of '{fn.name}', which returns "
            f"{self._as_written(fn.return_type, pretty_type(ret))}: its "
            f"result is @{written}.result.",
            rationale=(
                "@T.result refers to the function's return value, where T is "
                "the return type, written as a slot reference to a binding of "
                "that type is written: an alias at the head stays the alias, "
                "a refinement written out at the head is written as its base "
                "type and a function type written out there as Fn, and type "
                "arguments resolve through aliases, a refinement among them "
                "staying a refinement.  A result reference of any other type "
                "refers to no value, so a contract written with one would be "
                "checked and verified against a value of a type the function "
                "does not return."
            ),
            fix=f"Write @{written}.result.",
            spec_ref='Chapter 3, Section 3.6 "The `@result` Reference"',
            error_code="E163",
        )
        return UnknownType()

    def _return_type_refused(self, te: ast.TypeExpr, ret: Type) -> bool:
        """Whether the check refused the declared return type *te*, which
        resolved to *ret*, where it is written: a part of it resolved to no
        type, or an error is placed inside it (#1517).

        Registration resolves a signature first and reports it then, and the
        diagnostic table keeps one copy of a report (`_seen_diag_keys`), so
        what tells is where the reports stand, not whether resolving the type
        again reports one.  A removed alias is reported at its first use
        only, so a return type that repeats one is reported nowhere; the part
        it leaves unresolved tells instead.  Only an error counts: a warning
        inside the type (a typed hole in its refinement, W001) refuses
        nothing, so the reference is still judged.  Either way the skip only
        ever drops an E163 from a program already refused, since every part
        that resolves to no type was reported as an error where its name was
        first written.
        """
        if _holds_unknown(ret):
            return True
        span = te.span
        if span is None:
            return False
        start = (span.line, span.column)
        end = (span.end_line, span.end_column)
        return any(
            d.severity == "error"
            and d.location.file == self.file
            and start <= (d.location.line, d.location.column) < end
            for d in self.errors)

    def _as_written(self, node: ast.Node, fallback: str) -> str:
        """*node* as the source spells it, on one line, or *fallback* where
        the checker holds no source text for it."""
        span = node.span
        lines = self.source.split("\n") if self.source else []
        if span is None or not 0 < span.line <= span.end_line <= len(lines):
            return fallback
        if span.line == span.end_line:
            text = lines[span.line - 1][span.column - 1:span.end_column - 1]
        else:
            text = "\n".join([
                lines[span.line - 1][span.column - 1:],
                *lines[span.line:span.end_line - 1],
                lines[span.end_line - 1][:span.end_column - 1],
            ])
        return " ".join(text.split()) or fallback

    def _written_slot_name(self, te: ast.TypeExpr, key: str) -> str:
        """The name a slot reference to a binding declared *te* is written
        with, as the source spells it, or the key *key* where no source text
        is held: a refinement written out is named by its base and a function
        type written out by `Fn` (§3.7), and every argument keeps its
        spelling, so the name keys as the declaration does."""
        while isinstance(te, ast.RefinementType):
            te = te.base_type
        if isinstance(te, ast.FnType):
            return "Fn"
        return self._as_written(te, key)

    # -----------------------------------------------------------------
    # Binary operators
    # -----------------------------------------------------------------

    def _check_binary(self, expr: ast.BinaryExpr) -> Type | None:
        """Type-check a binary operator expression.  (A pipe is not one: the
        transform writes `a |> f(b)` as the call `f(a, b)`.)"""
        left_ty = self._synth_expr(expr.left)
        right_ty = self._synth_expr(expr.right)
        if left_ty is None or right_ty is None:
            return None
        # #861: inside a refinement predicate over a `@Byte` BASE (§2.6),
        # an integer literal compared against a Byte-typed operand is typed
        # against Byte, not Int.  `@Byte.0 < 10` has a defined i32
        # runtime-guard lowering (#766's `_translate_byte_binop`), so —
        # unlike a general expression, where Byte-vs-Int is E142 (no
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
                    f"{pretty_inferred_type(left_ty)} and "
                    f"{pretty_inferred_type(right_ty)}.",
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
                    f"Cannot compare {pretty_inferred_type(left_ty)} with "
                    f"{pretty_inferred_type(right_ty)}.",
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
                    f"found {pretty_inferred_type(left_ty)} and "
                    f"{pretty_inferred_type(right_ty)}.",
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
                    f"{pretty_inferred_type(left_ty)}.",
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
                    f"{pretty_inferred_type(right_ty)}.",
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
        adopted-FROM side carries no FRESH (`$`-marked) var.  A rigid forall
        var is fine: `Some(@T.0) == None` under `forall<T where Eq<T>>`
        adopts `Option<T>`, a fully-resolved type inside its own body (PR
        #1009 review).  Two unresolved ctor operands (`None == None`) still
        fall through to E142.  Restricting to `==`/`!=`
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
                and not (left_ctor and contains_fresh_typevar(left_ty))):
            new_right = self._synth_expr(expr.right, expected=left_ty)
            if new_right is not None and not isinstance(
                    new_right, UnknownType):
                right_ty = new_right
        elif (left_ctor
                and contains_typevar(left_ty)
                and isinstance(right_ty, AdtType)
                and not (right_ctor and contains_fresh_typevar(right_ty))):
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

    # -----------------------------------------------------------------
    # Unary operators
    # -----------------------------------------------------------------

    def _check_unary(self, expr: ast.UnaryExpr) -> Type | None:
        """Type-check a unary operator expression."""
        negated = self._negated_literal
        if (expr.op == ast.UnaryOp.NEG
                and isinstance(expr.operand, ast.IntLit)):
            self._negated_literal = expr.operand
        try:
            operand_ty = self._synth_expr(expr.operand)
        finally:
            self._negated_literal = negated
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
                    f"{pretty_inferred_type(operand_ty)}.",
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
                    f"{pretty_inferred_type(operand_ty)}.",
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
            # The operand literal `m` is synthesized as a negation's operand
            # (`_negated_literal`), so the IntLit branch leaves its bound to
            # this check, which names the value the program wrote: a larger
            # magnitude would reinterpret to a wrong value at runtime (e.g.
            # `-9223372036854775809` runs to 9223372036854775807).
            if (isinstance(expr.operand, ast.IntLit)
                    and expr.operand.value > 2**63):
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

    def _check_index(self, expr: ast.IndexExpr, *,
                     expected: Type | None = None) -> Type | None:
        """Type-check array index: collection[index].

        An element expected at a type is read from an array of that type:
        where the collection's literals decided an element that *expected*
        makes a `Nat`, the collection is checked against it
        (:meth:`_check_in_literal_context`; PR #1583 review), so
        `let @Nat = array_reverse([0 - 3, 5])[0]` is refused (E503) as
        `let @Nat = id(0 - 3)` is."""
        coll_ty = self._synth_expr(expr.collection)
        if expected is not None:
            coll_ty = self._check_in_literal_context(
                expr.collection, coll_ty, AdtType("Array", (expected,)))
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
                        f"{pretty_inferred_type(idx_ty)}.",
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
            f"Cannot index {pretty_inferred_type(coll_ty)}: indexing requires "
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
                        f"value has type {pretty_inferred_type(val_type)}.",
                        rationale=(
                            "A let binding's value must be a subtype of the "
                            "binding's declared type."
                        ),
                        fix=(
                            f"Give the value type {pretty_type(declared_type)}, "
                            "or change the binding's declared type to match the "
                            f"value's type {pretty_inferred_type(val_type)}."
                        ),
                        spec_ref='Chapter 4, Section 4.7 "Let Bindings"',
                        error_code="E170",
                    )

        # #1006: a let of a zero-size type has no WASM representation — the
        # binding could never be read (E182), so its only conceivable use is
        # sequencing, which the expression statement already provides.
        # Pre-fix `let @Unit = put(5);` was check-green and codegen skipped
        # the whole enclosing function (E602).  Uniform over any RHS
        # (effect op or plain call); the value expression above is still
        # checked, so its own diagnostics and effect tracking are kept.
        if erases_to_unit(declared_type):
            self._error(
                stmt.value,
                f"Cannot bind a let of type "
                f"'{pretty_type(declared_type)}': it is zero-size and "
                f"carries no runtime value.",
                rationale="A zero-size type (`Unit`, or a `Future` wrapping "
                          "one) compiles to no WASM local, so the binding "
                          "would have no runtime location and could never "
                          "be read.",
                fix="Evaluate the expression as a statement instead — "
                    "`put(5);` rather than `let @Unit = put(5);` — and "
                    "delete the binding.",
                spec_ref='Chapter 4, Section 4.7 "Let Bindings"',
                error_code="E183",
            )

        tname = self._type_expr_to_slot_name(stmt.type_expr)
        # #309: resolve the value's literal provenance in THIS scope, before
        # ``bind`` shifts slot indices, and record it on the binding.  A later
        # slot reference then reads a value resolved where it was written — the
        # De Bruijn-safe way to follow a ``let`` chain of literals into the SQL
        # provenance gate.  Returns None for any non-literal value.
        # #1160 resolves the array length the same way and for the same reason,
        # so the E208 arity check follows a let chain as the E207 gate does.
        lit = resolve_literal_string(stmt.value, self.env,
                                     self._slot_ref_key)
        alen = resolve_array_len(stmt.value, self.env, self._slot_ref_key)
        self.env.bind(tname, declared_type, "let", literal_str=lit,
                      array_len=alen)

    def _check_let_destruct(self, stmt: ast.LetDestruct) -> None:
        """Type-check a destructuring let."""
        tuple_shape = stmt.constructor == "Tuple"
        self._register_pattern_reads(
            stmt.value, list(stmt.type_bindings),
            lambda name: (name == "Tuple") == tuple_shape,
        )
        value_ty = self._synth_expr(stmt.value)
        # Read before the bindings are resolved, as a `match` reads it
        # before its arms: an error in a binding's type says nothing about
        # the value (#1671).
        after_error = any(d.severity == "error" for d in self.errors)

        resolved_types: list[Type] = []
        for te in stmt.type_bindings:
            self._check_refinement_predicates(te)  # #861
            resolved_types.append(self._resolve_type(te))

        # #1545: the destructure is the one-arm constructor pattern it
        # names, held to the arm's rules and its bindings to a `let`'s,
        # against the type the value synthesized above, never the type the
        # bindings would give it (`_check_destructure`).
        self._check_destructure(
            stmt, value_ty, resolved_types, after_error=after_error)

        # #1541, PR #1583 review: a tuple destructure's bindings are the
        # type its source is expected at, as a `let`'s declared type is,
        # whatever the source's form: a generic call (a pipe is one), or one
        # reached through `if`, `match` and block tails or an index.  So
        # `let Tuple<@Nat, @Nat> = id(Tuple(1, 0 - 3))` is refused (E503)
        # as `let @Nat = id(0 - 3)` is, and so is the same call in an `if`
        # branch.
        if tuple_shape:
            self._check_in_literal_context(
                stmt.value, value_ty, AdtType("Tuple", tuple(resolved_types)))

        for te, resolved in zip(stmt.type_bindings, resolved_types):
            tname = self._type_expr_to_slot_name(te)
            self.env.bind(tname, resolved, "destruct")

    def _check_in_literal_context(self, expr: ast.Expr, ty: Type | None,
                                  context: Type) -> Type | None:
        """*expr*, synthesized as *ty* without an expected type, checked
        again against *context* where a generic call it reaches let its
        literals fix a position that *context* makes a `Nat`
        (:meth:`_call_literal_meets_nat`; #1541, PR #1583 review).

        `if`, `match`, a block, a tuple, an array literal and an index each
        thread the expected type to the call, which then places each literal
        at the type *context* gives it, where it is a narrowing the verifier
        obligates — refuted where the literal is negative (E503).  A literal
        the source builds directly is not re-checked: the destructure's or
        the binding's own narrowing reads it where it is.  Returns the type
        the check settled on."""
        if (ty is None or isinstance(ty, UnknownType)
                or contains_typevar(context)
                or not self._call_literal_meets_nat(expr, context)):
            return ty
        rechecked = self._synth_expr(expr, expected=context)
        if rechecked is None or isinstance(rechecked, UnknownType):
            return ty
        return rechecked

    def _call_literal_meets_nat(self, expr: ast.Expr, context: Type) -> bool:
        """Whether a generic call that *expr* evaluates to, or builds into
        the value, fixed a type argument from its literals where *context*
        holds a `Nat`
        (:func:`literal_meets_nat` over the recorded soft result).  Read
        through a block's result, the branches of an `if` and the arms of a
        `match`, a tuple's fields, an array literal's elements, and the
        array an index reads."""
        while isinstance(context, RefinedType):
            context = context.base
        if isinstance(expr, ast.Block):
            return self._call_literal_meets_nat(expr.expr, context)
        if isinstance(expr, ast.IfExpr):
            return any(
                self._call_literal_meets_nat(branch, context)
                for branch in (expr.then_branch, expr.else_branch))
        if isinstance(expr, ast.MatchExpr):
            return any(self._call_literal_meets_nat(arm.body, context)
                       for arm in expr.arms)
        if isinstance(expr, ast.IndexExpr):
            return self._call_literal_meets_nat(
                expr.collection, AdtType("Array", (context,)))
        if (isinstance(expr, ast.ConstructorCall) and expr.name == "Tuple"
                and isinstance(context, AdtType) and context.name == "Tuple"
                and len(context.type_args) == len(expr.args)):
            return any(self._call_literal_meets_nat(a, c)
                       for a, c in zip(expr.args, context.type_args))
        if (isinstance(expr, ast.ArrayLit) and isinstance(context, AdtType)
                and context.name == "Array" and len(context.type_args) == 1):
            return any(self._call_literal_meets_nat(e, context.type_args[0])
                       for e in expr.elements)
        if isinstance(expr, (ast.FnCall, ast.ModuleCall)):
            soft = self._literal_soft_results.get(ast.span_key(expr))
            return soft is not None and literal_meets_nat(soft, context)
        return False

    # -----------------------------------------------------------------
    # Anonymous functions
    # -----------------------------------------------------------------

    def _check_anon_fn(self, expr: ast.AnonFn) -> Type | None:
        """Type-check an anonymous function.

        Its body is checked under its own row (#1702), as a function's is
        under the row it declares: that row is the row in force, its order
        resolves a bare operation name, and the operations the body
        performs are held to that row.  A `pure` closure that performs an
        effect is refused at the closure (E122).  The effects any other
        closure performs, directly or through a closure written in it,
        count for the purity of the declaration it is written in, so a
        `pure` function cannot write a closure that performs one (E122 at
        the function); under a row that is not `pure`, the closure's row is
        held where the closure is applied (`apply_fn`, E125).  The type the
        closure is given, its parameters, result and row, is the one it
        declares."""
        # #861: closure signatures carry the same refinement positions as
        # top-level fn signatures.
        for param_te in expr.params:
            self._check_refinement_predicates(param_te)
        self._check_refinement_predicates(expr.return_type)
        param_types = tuple(self._resolve_type(p) for p in expr.params)
        ret_type = self._resolve_type(expr.return_type)
        eff, eff_order = self._resolve_effect_row_ordered(expr.effect)

        saved_effect = self.env.current_effect_row
        saved_effect_order = self.env.current_effect_order
        saved_ops = self._effect_ops_used
        saved_row_owner = self._row_owner
        self.env.current_effect_row = eff
        self.env.current_effect_order = eff_order
        self._effect_ops_used: set[str] = set()
        self._row_owner = (
            "the anonymous function's effects clause and to the row of the "
            "function type it is given", eff)

        self.env.push_scope()
        for param_te, param_ty in zip(expr.params, param_types):
            tname = self._type_expr_to_slot_name(param_te)
            self.env.bind(tname, param_ty, "param")

        # `vera.lowering` rule 7: the handlers written inside this body are
        # the ones its State and Exn operations lower under.  A quantifier's
        # predicate is inlined into the function around it, not lifted, so
        # it is no closure the rule reads.
        lifted = id(expr) not in self._inlined_closures
        if lifted:
            self._closure_handler_marks.append(len(self._handled_effects))
        body_type = self._synth_expr(expr.body, expected=ret_type)
        if lifted:
            self._closure_handler_marks.pop()
        self.env.pop_scope()

        performed = self._effect_ops_used
        self.env.current_effect_row = saved_effect
        self.env.current_effect_order = saved_effect_order
        self._effect_ops_used = saved_ops
        self._row_owner = saved_row_owner
        # The effects the closure performs, those of the closures written in
        # it included, count for the declaration it is written in, so they
        # reach the function at any depth.  A row variable can drop a
        # value's row on the way to an application (a sub with one is
        # permissive, #294), so this is what holds a `pure` function to its
        # closures.  An operation a judgement refused was never counted
        # (`_check_op_call`): its code at the call is its one.
        if isinstance(eff, ConcreteEffectRow):
            self._effect_ops_used |= performed

        if body_type and not isinstance(body_type, UnknownType):
            if not is_subtype(body_type, ret_type):
                self._error(
                    expr.body,
                    f"Anonymous function body has type "
                    f"{pretty_inferred_type(body_type)}, expected "
                    f"{pretty_type(ret_type)}.",
                    rationale=(
                        "An anonymous function's body must produce a value that "
                        "is a subtype of its declared return type."
                    ),
                    fix=(
                        f"Make the body yield {pretty_type(ret_type)}, or change "
                        "the closure's declared return type to "
                        f"{pretty_inferred_type(body_type)}."
                    ),
                    spec_ref='Chapter 5, Section 5.7 "Anonymous Functions (Closures)"',
                    error_code="E171",
                )

        if isinstance(eff, PureEffectRow) and performed:
            self._refuse_pure_closure_effects(expr, performed)

        return FunctionType(param_types, ret_type, eff)

    def _refuse_pure_closure_effects(
        self, expr: ast.AnonFn, performed: set[str],
    ) -> None:
        """E122 at a `pure` closure whose body performs effects (#1702),
        the purity check a `pure` function's body is held to, worded for
        the closure; each effect the fix names is written with its type
        parameters where it takes them (`State<T>`)."""
        entries = []
        for name in sorted(performed):
            info = self.env.lookup_effect(name)
            params = tuple(info.type_params or ()) if info else ()
            entries.append(EffectInstance(
                name, tuple(TypeVar(p) for p in params)))
        wanted = pretty_effect(ConcreteEffectRow(frozenset(entries)))
        self._error(
            expr,
            f"Pure anonymous function performs effect operations: "
            f"{', '.join(sorted(performed))}.",
            rationale=(
                "An anonymous function declared with effects(pure) cannot "
                "perform effects: its row is part of its type, and an effect "
                "it performs would be hidden from every function that "
                "applies it."
            ),
            fix=(
                f"Declare the effects in the anonymous function's effects "
                f"clause and in the row of the function type it is given: "
                f"{wanted}."
            ),
            spec_ref='Chapter 5, Section 5.7 "Anonymous Functions (Closures)"',
            error_code="E122",
        )

    # -----------------------------------------------------------------
    # Arrays
    # -----------------------------------------------------------------

    def _check_array_lit(self, expr: ast.ArrayLit, *,
                         expected: Type | None = None) -> Type | None:
        """Type-check an array literal."""
        if not expr.elements:
            return AdtType("Array", (UnknownType(),))

        # An element is synthesized with no expected type; where *expected*
        # makes it a `Nat` and a generic call in it let a negative literal
        # fix an `Int` there, it is checked against the element type
        # (`_check_in_literal_context`; PR #1583 review).
        expected_base = base_type(expected) if expected is not None else None
        element_ctx = (
            expected_base.type_args[0]
            if (isinstance(expected_base, AdtType)
                and expected_base.name == "Array"
                and len(expected_base.type_args) == 1)
            else None)
        elem_types: list[Type | None] = []
        for elem in expr.elements:
            et = self._synth_expr(elem)
            if element_ctx is not None:
                et = self._check_in_literal_context(elem, et, element_ctx)
            elem_types.append(et)

        first = None
        first_at = 0
        for i, et in enumerate(elem_types):
            if et and not isinstance(et, UnknownType):
                first, first_at = et, i
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

        # #1584, #1668: every element has the element type, the type the
        # elements have together.  A zero-size one is refused for the whole
        # literal (E135, here or at the annotation the literal meets), so its
        # elements are not held to it as well.
        element_type = first
        if not erases_to_unit(first):
            element_type, completed_by, conflicting = self._join_elements(
                elem_types, first, first_at)
            self._check_array_elements(
                expr, elem_types, element_type, first_at, completed_by,
                conflicting)

        return AdtType("Array", (element_type,))

    def _join_elements(self, elem_types: Sequence[Type | None],
                       first: Type, first_at: int,
                       ) -> tuple[Type, tuple[int, ...], frozenset[int]]:
        """The element type of a literal whose element types are
        *elem_types*, the elements after its first typed one (*first*, at
        *first_at*) that completed it, and the elements whose type gives
        one open type variable two types that do not agree (#1668).

        The element type is the join of the elements (`_join`): *first*,
        with each position it leaves open — a `None`'s `T`, an empty
        literal's element type — given by the first later element that
        fills it.  An element that does not fit the join of the elements
        before it fills nothing; `_check_array_elements` reports it.  A
        position no element fills, or one the join does not fill (a type
        variable code generation compiles behaviour for, or a built-in's),
        stays as the elements leave it, and the context the literal meets
        decides it."""
        joined = first
        completed_by: list[int] = []
        conflicting: set[int] = set()
        for i, ty in enumerate(elem_types):
            if i <= first_at or ty is None or isinstance(ty, UnknownType):
                continue
            step, conflict, _ = self._join_parts(ty, joined)
            if conflict:
                conflicting.add(i)
            elif step is not None and step is not joined:
                joined = step
                completed_by.append(i)
        return joined, tuple(completed_by), frozenset(conflicting)

    def _check_array_elements(self, expr: ast.ArrayLit,
                              elem_types: Sequence[Type | None],
                              element_type: Type, first_at: int,
                              completed_by: Sequence[int] = (),
                              conflicting: frozenset[int] = frozenset(),
                              ) -> None:
        """Hold each element of *expr* after its first typed one, at
        *first_at*, to the literal's *element_type* (#1584).

        Spec §4.12.1: all elements of an array literal have the same type.
        The element type is the join of the elements (`_join_elements`):
        the first typed element's type, completed by the elements in
        *completed_by* where it leaves a position open (#1668).  It is the
        type the literal is given, `Array<element_type>`, and the type code
        generation stores and reads back every element at.  Each other
        element is held to it by the judgement a call argument is held to
        its parameter by (`_fits`), and one it refuses is E162, at the
        element; so is one in *conflicting*, whose type gives one type
        variable two types, which that judgement, one position at a time,
        does not see.  An element whose type is already an error was
        reported by its own check and is not judged again."""
        source = f"the type of element {first_at}"
        if completed_by:
            source += f", completed by {_element_list(completed_by)}"
        for i, (elem, ty) in enumerate(zip(expr.elements, elem_types)):
            if i <= first_at or ty is None or isinstance(ty, UnknownType):
                continue
            if i not in conflicting and self._fits(ty, element_type):
                continue
            shown = pretty_inferred_type(element_type)
            self._error(
                elem,
                f"Array literal element {i} has type "
                f"{pretty_inferred_type(ty)}, but the literal's element "
                f"type is {shown}, {source}.",
                rationale=(
                    "An array literal has one element type (Section "
                    "4.12.1): it is an Array<T> whose T is the type of its "
                    "first element, with each part that type leaves open "
                    "(a None's T, the element type of []) given by the "
                    "first element that fills it, and every element is "
                    "stored and read back as a T, so an element of another "
                    "type would be stored at the wrong width or read back "
                    "as a value it does not hold."
                ),
                fix=(
                    f"Give element {i} the type {shown}, or give every "
                    f"element the type {pretty_inferred_type(ty)} if that "
                    "is what the array holds.  To keep values of different "
                    "types in one array, wrap each in a constructor of one "
                    "data type and make the array of that type."
                ),
                spec_ref='Chapter 4, Section 4.12.1 "Array Literals"',
                error_code="E162",
            )

    # -----------------------------------------------------------------
    # Typed holes
    # -----------------------------------------------------------------

    def _collect_scope_bindings(self) -> list[tuple[str, str]]:
        """All bindings in scope, innermost first, as
        ``(slot_ref_string, pretty_type_string)`` pairs.

        Shared by the W001 hole diagnostic's fix hint, the E130
        unresolved-slot fix (#558) and the LSP typed-hole completion
        (#222 Phase D) — same data, three renderings.

        Returns the WHOLE scope.  The two message renderings cap what
        they print (`_render_scope_table`); completion consumes the list
        itself, where a dropped row is a missing completion item.
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
            context = _render_scope_table(bindings)
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
                    f"assert() requires Bool, found "
                    f"{pretty_inferred_type(ty)}.",
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
                    f"assume() requires Bool, found "
                    f"{pretty_inferred_type(ty)}.",
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
        self._check_quantifier_index(expr.binding_type, "forall")
        self._check_quantifier_bound(expr.domain, "forall")
        self._check_quantifier_predicate(expr.predicate, "forall")
        self._apply_quantifier_predicate(expr, "forall")
        return BOOL

    def _check_exists_expr(self, expr: ast.ExistsExpr) -> Type | None:
        """Type-check exists(type, domain, predicate)."""
        self._check_refinement_predicates(expr.binding_type)  # #861
        self._check_quantifier_index(expr.binding_type, "exists")
        self._check_quantifier_bound(expr.domain, "exists")
        self._check_quantifier_predicate(expr.predicate, "exists")
        self._apply_quantifier_predicate(expr, "exists")
        return BOOL

    def _apply_quantifier_predicate(
        self, expr: ast.ForallExpr | ast.ExistsExpr, form: str,
    ) -> None:
        """Check a quantifier's predicate, and hold the quantifier to its
        row (#1702).

        The predicate is a closure literal, checked as one: its body under
        its own row.  Code generation inlines it into the loop it lowers the
        quantifier to (spec §11.13.2), so the quantifier performs the
        predicate's effects where it is written, and is held to the
        predicate's row as an `apply_fn` of it would be: the row in force
        must permit it (E125), and its effects count for the purity check
        (E122).  Inlined, the predicate is compiled with the function around
        it, so `vera.lowering` rule 7 does not read it: its `State` and
        `Exn` operations reach that function's cell and tag."""
        self._inlined_closures.add(id(expr.predicate))
        pred_ty = self._synth_expr(expr.predicate)
        self._inlined_closures.discard(id(expr.predicate))
        if not isinstance(pred_ty, FunctionType):
            return
        effect = pred_ty.effect
        if isinstance(effect, ConcreteEffectRow):
            for ei in effect.effects:
                self._effect_ops_used.add(ei.name)
        row = self.env.current_effect_row
        if row is None or is_effect_subtype(effect, row):
            return
        allowed = row.effects if isinstance(row, ConcreteEffectRow) else frozenset()
        missing = (effect.effects - allowed
                   if isinstance(effect, ConcreteEffectRow) else frozenset())
        target, declared = self._row_owner or (
            "the enclosing function's effects clause", row)
        entries = (declared.effects if isinstance(declared, ConcreteEffectRow)
                   else frozenset())
        row_var = (declared.row_var
                   if isinstance(declared, ConcreteEffectRow) else None)
        wanted = pretty_effect(ConcreteEffectRow(entries | missing, row_var))
        shown = ", ".join(sorted(
            canonical_type_name(e.name, e.type_args or None) for e in missing))
        self._error(
            expr,
            f"{form}: its predicate requires {pretty_effect(effect)} but call "
            f"site only allows {pretty_effect(row)}.",
            rationale=(
                "A quantifier applies its predicate in place, to each value of "
                "its index, so it performs the predicate's effects where it is "
                "written: the call site must permit all of them "
                "(subeffecting), as for apply_fn."
            ),
            fix=(f"Add {shown} to {target}: {wanted}.  Or write a predicate "
                 f"whose effects the call site permits."),
            spec_ref='Chapter 7, Section 7.8 "Effect Subtyping"',
            error_code="E125",
        )

    def _check_quantifier_index(self, te: ast.TypeExpr, form: str) -> None:
        """The index type is ``Int`` or ``Nat``, or a refinement of one
        (spec §6.3.3, E186).

        A refinement of the index is honoured: the quantifier ranges over the
        values below the bound that satisfy it (``forall`` holds when the
        predicate holds for each of them, ``exists`` when it holds for one),
        in the runtime check code generation emits.  Any other index type has
        no meaning there — the index is a count — and was accepted and never
        read, so ``forall(@String, 3, ...)`` checked and ran.  A type
        parameter defers to the instantiation, as the bound's does (PR #1202):
        the generic's integer instantiations are the ones that run, and
        checking the others where the types are known is #1506's remaining
        work.
        """
        before = len(self.errors)
        ty = self._resolve_type(te)
        if len(self.errors) > before:
            return
        base = ty
        while isinstance(base, RefinedType):
            base = base.base
        if (base is None or isinstance(base, (UnknownType, TypeVar))
                or base in (INT, NAT)):
            return
        what = pretty_type(base)
        self._error(
            te,
            f"The {form}() index type must be Int or Nat, or a refinement "
            f"of one: it is {what}.",
            rationale=(
                "A quantifier's first argument is the type of its index, "
                "which runs over 0 up to the bound: a count.  A refinement of "
                "Int or Nat narrows the values it ranges over; any other type "
                "names no count."
            ),
            fix=(
                "Give the index type @Nat or @Int — or a refinement such as "
                "@{ @Nat | @Nat.0 > 0 } to range over the values that "
                "satisfy it — and read anything else inside the predicate."
            ),
            spec_ref='Chapter 6, Section 6.3.3 "Quantified Expressions"',
            error_code="E186",
        )

    def _check_quantifier_predicate(
        self, pred: ast.AnonFn, form: str,
    ) -> None:
        """The predicate is a function of the INDEX to Bool (#1506, E179).

        Spec §6.3.3: the index runs over ``0 .. bound-1`` and the predicate is
        applied to each value, so it takes exactly one parameter, the index —
        of type ``Int`` or ``Nat``, or an alias of either — and returns
        ``Bool``.  Nothing checked it, and code generation, which lowers the
        quantifier as a loop binding an i64 counter under the parameter's type
        and reading an i32 result, stopped with E699 on a refined parameter or
        a wrong arity, and emitted a module that fails to load for a ``Bool``
        parameter or an ``Int`` result.

        A refinement of the PARAMETER is refused.  The predicate is applied
        to every value of the index, so a refinement narrower than the index
        type cannot hold for all of them, and binding a value the declared
        type excludes would mislead every guard downstream.  A refinement
        that means "range over these values" belongs on the index type,
        where it is honoured (`_check_quantifier_index`), or in the body, as
        ``P ==> ...`` for ``forall`` and ``P && ...`` for ``exists``.

        A type parameter is refused at either position (#1506): the predicate
        lowers only at the instantiations that make it ``Int``/``Nat`` ->
        ``Bool``, and the template answers for all of them.  The rule is
        `vera.lowering.quantifier_predicate_refusals` (rule 3), which code
        generation's ``_translate_quantifier`` backstops.
        """
        connective = "==>" if form == "forall" else "&&"

        def refuse(node: ast.Node, what: str) -> None:
            self._error(
                node,
                f"The {form}() predicate must be a function of the index to "
                f"Bool, fn(@Nat -> @Bool) or fn(@Int -> @Bool): {what}.",
                rationale=(
                    "A quantifier applies its predicate to every value of "
                    "the index, 0 up to the bound, so the predicate takes "
                    "exactly one parameter — the index, an Int or a Nat — "
                    "and returns Bool.  A refinement narrower than the index "
                    "type cannot hold for every value in the range, and any "
                    "other shape has no lowering: code generation binds the "
                    "index as a 64-bit integer and reads a Bool."
                ),
                fix=(
                    f"Write the predicate as fn(@Nat -> @Bool) (or @Int, or "
                    f"an alias of either).  For a refinement {{ @Nat | P }}, "
                    f"refine the index type instead — "
                    f"{form}(@{{ @Nat | P }}, ...) — or test P in the body: "
                    f"fn(@Nat -> @Bool) effects(pure) {{ P {connective} ... }}."
                ),
                spec_ref='Chapter 6, Section 6.3.3 "Quantified Expressions"',
                error_code="E179",
            )

        def resolve(te: ast.TypeExpr) -> Type | None:
            """*te* resolved — or ``None`` when resolving it was itself
            refused (an unknown name, E136; an alias arity, E133), which is
            the one diagnostic that mistake gets."""
            before = len(self.errors)
            ty = self._resolve_type(te)
            return None if len(self.errors) > before else ty

        param = (resolve(pred.params[0]) if len(pred.params) == 1 else None)
        result = resolve(pred.return_type)
        at: dict[str, ast.Node] = {
            PREDICATE_ARITY: pred,
            PREDICATE_PARAMETER: (pred.params[0] if pred.params else pred),
            PREDICATE_RESULT: pred.return_type,
        }
        for position, why in quantifier_predicate_refusals(
                len(pred.params), param, result):
            refuse(at[position], why)

    def _check_quantifier_bound(self, domain: ast.Expr, form: str) -> None:
        """The quantifier's domain is a numeric BOUND (spec §6.3.3:
        ``forall(@IndexType, @BoundExpr, @PredicateFn)`` quantifies the
        index over ``0 .. bound-1``) — require an @Int/@Nat bound (#1204).

        An array-typed domain previously type-checked and then died at
        codegen with a raw WASM translation error (`_translate_quantifier`
        lowers only the count form); rejecting it here keeps the
        check-green ⇒ compilable contract.

        The rule is `vera.lowering.quantifier_bound_lowerable` (rule 3).  A
        bound typed by a type parameter is refused at the template (#1506):
        the counter loop compares an ``i64``, so it lowers only at the
        integer instantiations, and at any other the module failed to load.
        """
        domain_ty = self._synth_expr(domain)
        if quantifier_bound_lowerable(domain_ty):
            return
        base = base_type(domain_ty) if domain_ty is not None else None
        if isinstance(base, TypeVar):
            self._error(
                domain,
                f"{form}() bound must be an integer count, got the type "
                f"parameter {base.name}.",
                rationale=(
                    "A quantifier's second argument is the exclusive upper "
                    "BOUND of the index range, which code generation "
                    "compares as a 64-bit integer.  A bound typed by a type "
                    "parameter is a count only at the instantiations that "
                    "make it Int or Nat, and the template answers for all of "
                    "them."
                ),
                fix=(
                    f"Type the bound as a count: give the parameter it comes "
                    f"from the type @Int or @Nat in place of @{base.name}, "
                    f"or pass a length — array_length(...) — as the bound."
                ),
                spec_ref='Chapter 6, Section 6.3.3 "Quantified Expressions"',
                error_code="E128",
            )
            return
        shown = getattr(base, "name", None) or {
            "FunctionType": "a function type",
        }.get(type(base).__name__, type(base).__name__)
        self._error(
            domain,
            f"{form}() bound must be an integer count, got {shown}.",
            rationale=(
                "A quantifier's second argument is the exclusive upper "
                "BOUND of the index range — the quantified variable runs "
                "over 0 .. bound-1 — not a collection to iterate. To "
                "quantify over an array's indices, pass its length as the "
                "bound and index the array inside the predicate."
            ),
            fix=(
                "Pass an integer bound: forall(@Int, "
                "array_length(@Array<T>.0), fn(@Int -> @Bool) ... { "
                "@Array<T>.0[@Int.0] ... })."
            ),
            spec_ref='Chapter 6, Section 6.3.3 "Quantified Expressions"',
            error_code="E128",
        )

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
                    "before- and after-states. A requires() or decreases() "
                    "clause is itself evaluated before the body runs, so "
                    "every expression in it already observes the pre-state "
                    "and old() has nothing left to refer to."
                ),
                fix=_STATE_FORM_PLACEMENT_FIX,
                spec_ref='Chapter 7, Section 7.9 "Effect-Contract Interaction"',
                error_code="E174",
            )
        ei = self._resolve_effect_ref(expr.effect_ref)
        if ei:
            self._check_effect_ref_declared(expr, ei, "old")
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
                    "before- and after-states. A requires() or decreases() "
                    "clause is evaluated before the body runs, so the "
                    "after-state new() names does not exist yet at that "
                    "point."
                ),
                fix=_STATE_FORM_PLACEMENT_FIX,
                spec_ref='Chapter 7, Section 7.9 "Effect-Contract Interaction"',
                error_code="E175",
            )
        ei = self._resolve_effect_ref(expr.effect_ref)
        if ei:
            self._check_effect_ref_declared(expr, ei, "new")
            return self._effect_state_type(ei)
        return UnknownType()

    def _check_effect_ref_declared(
        self, expr: ast.Expr, ei: EffectInstance, form: str,
    ) -> None:
        """Refuse an ``old()`` / ``new()`` naming an effect the row omits (#1298).

        Both forms read the same cell, so one rule serves both.  The cell is
        keyed by effect FAMILY (`State<Bool>` and `State<Int>` are different
        cells since #1285), and a family the enclosing row never declares has
        no cell at all: `old()` finds no snapshot local and `new()` no
        registered getter, so codegen raised E699 — the
        internal-compiler-error diagnostic whose own text says the type
        checker should have rejected the input, on a check-green program,
        carrying a bug-report request the user should not act on.

        Checked here because this is where the rest of the clause is checked
        and where the declared row is in scope: `env.current_effect_row` is
        the enclosing function's, restored around each declaration, and a
        `handle` block extends it for its own body, so a form written under a
        handler still sees what is actually available.
        """
        row = self.env.current_effect_row
        if row is None:
            return
        declared: frozenset[EffectInstance] = (
            row.effects if isinstance(row, ConcreteEffectRow) else frozenset()
        )
        if ei in declared:
            return
        if isinstance(row, ConcreteEffectRow) and row.row_var is not None:
            # An OPEN row's tail may carry the family at a call site, so the
            # declaration here does not settle it.  Refusing would reject a
            # program that is legal under some instantiation.
            return
        def _render(e: EffectInstance) -> str:
            if not e.type_args:
                return e.name
            return f"{e.name}<{', '.join(pretty_type(a) for a in e.type_args)}>"

        named = _render(ei)
        have = ", ".join(sorted(_render(e) for e in declared)) or "pure"
        self._error(
            expr,
            f"{form}({named}) names an effect this function does not "
            f"declare. Declared: {have}.",
            rationale=(
                f"{form}() reads the state cell of the effect it names, and "
                f"cells are keyed by effect family — {named} and a different "
                f"instantiation of the same effect are different cells. A "
                f"family absent from the effect row has no cell in this "
                f"function, so there is no state for the contract to refer to."
            ),
            fix=(
                f"Add {named} to the effects row — effects(<{named}>) — or "
                f"name a family the row already declares."
            ),
            spec_ref='Chapter 7, Section 7.9 "Effect-Contract Interaction"',
            error_code="E177",
        )

    def _effect_state_type(self, ei: EffectInstance) -> Type:
        """Get the state type of a State-like effect."""
        if ei.name == "State" and ei.type_args:
            return ei.type_args[0]
        # For other effects, return Unknown
        return UnknownType()


# =====================================================================
# `_synth_expr_impl`: one arm per expression class
# =====================================================================

def _synth_int_lit(ctx: ExpressionsMixin, expr: ast.IntLit,
                   expected: Type | None) -> Type | None:
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
    if expected is not None and base_type(expected) == BYTE:
        if 0 <= expr.value <= 255:
            return BYTE
        # #1252: `@Byte` is a target machine type like `@Int` and
        # `@Nat`, so an out-of-range literal in a `@Byte` context is
        # the same E149 — reported HERE, where the mistake is, rather
        # than left to fall through to `@Nat` and be described by
        # whatever downstream mismatch that caused.  In a join it was
        # E301 ("then-branch is Nat, else-branch is Byte"), true but
        # about a consequence; at a call argument, E202; under a `let`,
        # E170.  The literal keeps the type its context asked for, so
        # the one real error is the only one reported.
        ctx._literal_range_error(
            expr,
            f"Integer literal {expr.value} is out of range for "
            f"@Byte; the range is 0..255.",
            rationale=(
                "`@Byte` is an unsigned 8-bit integer, stored and "
                "compared at that width.  A literal outside 0..255 "
                "cannot be represented in it, so the value the "
                "verifier reasons about and the value the runtime "
                "holds would differ (#812/#1252)."
            ),
            fix=(
                "Use a literal in 0..255, or give the surrounding "
                "binding, argument or return a wider type such as "
                "`@Nat` or `@Int`."
            ),
            # This pass KNOWS the target is `@Byte`, so it supersedes
            # an unconstrained verdict on the same literal.
            contextual=True,
        )
        return BYTE
    # #812: range-check the literal against its target machine type
    # before typing it.  Every target but `@Byte` is i64 — `@Int`, and
    # `@Nat`, its non-negative half — so the bound is i64.MAX wherever
    # the literal is written, whatever its context.  A literal past it
    # is a clean error here instead of (loud) an opaque `i64.const …
    # out of range` codegen failure or (silent, unsound) a Tier-1
    # proof over a value the i64 runtime reinterprets.  The operand of
    # a negation reaches 2^63, `Int`'s minimum, and `_check_unary`
    # bounds it there.
    if (expr.value > _I64_MAX
            and ctx._negated_literal is not expr):
        base = base_type(expected) if expected is not None else None
        type_name = ("@Nat" if isinstance(base, PrimitiveType)
                     and base.name == "Nat" else "@Int")
        ctx._literal_range_error(
            expr,
            f"Integer literal {expr.value} is out of range for "
            f"{type_name} (i64); the maximum is {_I64_MAX}.",
            rationale=(
                "Integer literals are fixed-width at runtime: `@Int` "
                "is a signed 64-bit integer and `@Nat` holds its "
                "non-negative half, so neither holds a value above "
                f"{_I64_MAX}.  A literal beyond that range cannot be "
                "represented: codegen would either reject it or "
                "silently reinterpret its bit pattern, diverging from "
                "what the verifier proved (#812)."
            ),
            fix=(
                "Use a literal no greater than "
                f"{_I64_MAX}, or hold a larger value as a `@Float64` "
                "or a `@Decimal`."
            ),
            # `expected is None` names no target, so a later
            # contextual verdict (a `@Byte` one) wins.
            contextual=expected is not None,
        )
    # Every integer literal is an `Int` (spec §4.2).  In a `@Nat` or
    # refined context it is a narrowing, which the checker admits
    # (`Int` where `Nat` is expected) and the verifier obligates.
    return INT


def _synth_fn_call(ctx: ExpressionsMixin, expr: ast.FnCall,
                   expected: Type | None) -> Type | None:
    result = ctx._check_fn_call(expr, expected=expected)
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


_SynthArm = Callable[[ExpressionsMixin, Any, "Type | None"], "Type | None"]

#: The type an expression synthesises, by class.
_SYNTH_ARMS: Mapping[type[ast.Expr], _SynthArm] = fold.dispatch(
    "_synth_expr_impl", {
        ast.IntLit: _synth_int_lit,
        ast.FloatLit: lambda ctx, e, expected: FLOAT64,
        ast.StringLit: lambda ctx, e, expected: STRING,
        ast.InterpolatedString:
            lambda ctx, e, expected: ctx._check_interpolated_string(e),
        ast.BoolLit: lambda ctx, e, expected: BOOL,
        ast.UnitLit: lambda ctx, e, expected: UNIT,
        ast.HoleExpr:
            lambda ctx, e, expected: ctx._check_hole(e, expected=expected),
        ast.SlotRef: lambda ctx, e, expected: ctx._check_slot_ref(e),
        ast.ResultRef: lambda ctx, e, expected: ctx._check_result_ref(e),
        ast.BinaryExpr: lambda ctx, e, expected: ctx._check_binary(e),
        ast.UnaryExpr: lambda ctx, e, expected: ctx._check_unary(e),
        ast.IndexExpr:
            lambda ctx, e, expected: ctx._check_index(e, expected=expected),
        ast.FnCall: _synth_fn_call,
        ast.ConstructorCall: lambda ctx, e, expected:
            ctx._check_constructor_call(e, expected=expected),
        ast.NullaryConstructor: lambda ctx, e, expected:
            ctx._check_nullary_constructor(e, expected=expected),
        ast.QualifiedCall:
            lambda ctx, e, expected: ctx._check_qualified_call(e),
        ast.ModuleCall: lambda ctx, e, expected:
            ctx._check_module_call(e, expected=expected),
        ast.IfExpr:
            lambda ctx, e, expected: ctx._check_if(e, expected=expected),
        ast.MatchExpr:
            lambda ctx, e, expected: ctx._check_match(e, expected=expected),
        ast.Block:
            lambda ctx, e, expected: ctx._check_block(e, expected=expected),
        ast.AnonFn: lambda ctx, e, expected: ctx._check_anon_fn(e),
        ast.HandleExpr: lambda ctx, e, expected: ctx._check_handle(e),
        ast.ArrayLit: lambda ctx, e, expected:
            ctx._check_array_lit(e, expected=expected),
        ast.AssertExpr: lambda ctx, e, expected: ctx._check_assert(e),
        ast.AssumeExpr: lambda ctx, e, expected: ctx._check_assume(e),
        ast.ForallExpr: lambda ctx, e, expected: ctx._check_forall_expr(e),
        ast.ExistsExpr: lambda ctx, e, expected: ctx._check_exists_expr(e),
        ast.OldExpr: lambda ctx, e, expected: ctx._check_old_expr(e),
        ast.NewExpr: lambda ctx, e, expected: ctx._check_new_expr(e),
    })
