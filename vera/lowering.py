"""What code generation lowers, one rule each (check implies compile).

A program ``vera check`` accepts is a program ``vera compile`` builds
(#1489, #1493).  Code generation lowers a fixed set of constructs, and the
rules for that set lived in code generation alone, so the checker accepted
what the backend then refused: a handler for an effect other than ``State``
and ``Exn`` (#1597), a ``State`` cell whose value is a ``(ptr, len)`` pair
(#1512), a quantifier the counter loop cannot bind (#1506), a call to a user
ability's operation (#1499), a generic cell that an instantiation makes the
same family as an enclosing one (#1522), an effect row naming a user-declared
effect or, in a function's own row, a row variable, a call of a
user-declared effect's operation (#1681), and a ``State`` or ``Exn``
operation in a closure's body outside a handler written in it (#1702).
Each rule is a function here.

The checker applies a rule where its construct is written and refuses the
construct there, with **E340** ("code generation cannot lower this
construct") or with the rule's own code where the rule already had one:
E179 and E128 for the quantifier (rule 3), E339 for a handler-clause
operation (rule 5).  Code generation asks the same function at the site that
lowers the construct, where it has one; a refusal there means a program
passed a check that should have refused it, so it is an internal error naming
the rule (E699), never a silent skip.

A rule whose answer depends on what a type parameter is instantiated at is
applied at the template where the template's answer covers every
instantiation, and conservatively where the construct lowers at few of them
(a quantifier position written as a type parameter; a type-parameter cell
nested in a cell it can coincide with).  A ``State<T>`` cell typed by a type
parameter lowers at most instantiations, so it is accepted at the template,
and code generation's E607 stays the report for a clone at ``String``: the
checker infers each call's type arguments but holds no instantiation set
(#1679).

Imports ``vera.ast``, ``vera.fold``, ``vera.types`` and ``vera.narrowing``'s
effect roster only, so the checker imports this module without importing code
generation.
"""

from __future__ import annotations

from collections.abc import Iterator, Sequence
from dataclasses import dataclass, field, fields, is_dataclass

from vera import ast, fold
from vera.narrowing import COMPILABLE_EFFECTS
from vera.types import (
    BOOL,
    INT,
    NAT,
    AdtType,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    base_type,
    contains_typevar,
    has_no_wasm_representation,
    is_pair_represented,
    pretty_type,
    types_equal,
)

# =====================================================================
# The contract positions code generation lowers
# =====================================================================


def contract_exprs(
    contracts: Sequence[ast.Contract],
) -> Iterator[ast.Expr]:
    """Every predicate expression carried by a function's contracts.

    One enumeration shared by both import pre-scans (#1210 round 2), because
    a contract is LOWERED code: `requires` / `ensures` become runtime checks
    and `decreases` becomes the termination guard's measure, so anything in
    one that needs a host import or a State/Exn family needs it registered.

    `Decreases` is why this exists at all: it carries `exprs` (a tuple — a
    lexicographic measure is several expressions) where the other kinds carry
    `expr`, so the `getattr(c, "expr")` shortcut this replaced silently
    skipped it and a `handle[State<Nat>]` in a `decreases` measure emitted
    `state_push_Nat` against an import that was never declared.

    The expressions are each clause's children in `vera.fold`, which reads
    the clause's fields, so a contract kind added to `vera/ast.py` has its
    expressions enumerated by construction, under whatever field names it
    declares.
    """
    for contract in contracts:
        for child in fold.children(contract):
            if isinstance(child, ast.Expr):
                yield child


# =====================================================================
# Rule 1: the effect a handler handles (#1597)
# =====================================================================

#: The effects a ``handle`` expression is lowered for: ``State<T>`` through
#: the host's cell imports, ``Exn<E>`` through WebAssembly exception handling.
HANDLED_EFFECTS: frozenset[str] = frozenset({"State", "Exn"})


def handler_lowerable(effect_name: str) -> bool:
    """Whether code generation lowers a ``handle[effect_name]`` (#1597).

    Replaces the refusal in ``_translate_handle_expr``
    (``vera/wasm/calls_handlers.py``), "only State<T> and Exn<E> handlers
    supported".  A handler for any other effect resumes the handled body
    from its clauses, which needs the continuation of each operation; code
    generation builds none.  A built-in host effect's operations are
    implemented by the host, and a user-declared effect's by nothing.
    """
    return effect_name in HANDLED_EFFECTS


# =====================================================================
# Rule 2: the State cell and the Exn payload (#1512)
# =====================================================================

#: A `State<T>` cell's value crosses four host imports — `state_get_X
#: (result W)`, `state_put_X (param W)` and the two scope markers — whose
#: signatures carry ONE word.  So a `(ptr, len)` pair cannot be a cell however
#: well the write guard could bind it: the value has no way through the
#: import, which is a property of the cell's ABI rather than of the guard.


def state_cell_lowerable(*, representable: bool, pair: bool) -> bool:
    """Whether code generation registers a ``State<T>`` cell whose value is
    *representable* at all and is or is not a *pair* (#1439, #1512).

    THE rule, once, for three components that answer its inputs with
    different oracles: ``_register_state_cell``
    (``vera/codegen/compilability.py``, the E607 site) from the cell's TYPE
    EXPRESSION through ``_type_expr_to_wasm_type``, and the checker and the
    verifier from the semantic type through
    :func:`state_cell_type_lowerable`.  What legitimately differs is the
    oracle; what must not is the answer.
    """
    return representable and not pair


def state_cell_type_lowerable(ty: Type) -> bool:
    """:func:`state_cell_lowerable` over the checker's semantic type of the
    cell (#1512).

    ``String`` and ``Array<T>`` are pairs, through refinements and
    ``Future``; ``Unit`` and ``Never`` have no representation.  A type
    parameter answers True: the template's cell is not yet a pair, and an
    instantiation that makes it one is code generation's E607 (#1679).
    """
    return state_cell_lowerable(
        representable=not has_no_wasm_representation(ty),
        pair=is_pair_represented(ty),
    )


def exn_payload_lowerable(*, representable: bool) -> bool:
    """Whether code generation declares an ``Exn<E>`` tag for a payload that
    is or is not *representable* (#1512's twin).

    Replaces the refusal in ``_register_exn_tag``
    (``vera/codegen/compilability.py``, the E612 site).  Unlike a cell, a
    pair payload IS lowerable: the tag takes two ``i32`` params.  A payload
    with no representation (``Unit``, ``Never``) has nothing to throw.
    """
    return representable


def exn_payload_type_lowerable(ty: Type) -> bool:
    """:func:`exn_payload_lowerable` over the checker's semantic type."""
    return exn_payload_lowerable(
        representable=not has_no_wasm_representation(ty))


def cell_type_spelling_lowerable(te: ast.TypeExpr) -> bool:
    """Whether a handler's ``State<T>`` or ``Exn<E>`` argument is written as
    a type NAME, the one form the handler lowering keys a cell by.

    Replaces the refusals in ``_translate_handle_state`` and
    ``_translate_handle_exn`` (``vera/wasm/calls_handlers.py``), "type
    argument must be a named type".  An inline refinement literal is refused;
    the same refinement named by an alias is lowerable (spec §7.5.1).
    """
    return isinstance(te, ast.NamedType)


# =====================================================================
# Rule 2b: a State handler clause's resume (single shot, in the tail)
# =====================================================================


def tail_resume_arg(body: ast.Expr) -> ast.Expr | None:
    """The tail ``resume(v)``'s argument, descending the join-free chain (a
    Block's trailing expression, a single-arm match) — ``None`` when the
    tail is not a one-argument resume.

    Read by :func:`state_clause_refusal`, by code generation's #1203
    get-result guard and by the verifier's obligation for that guard
    (``ContractVerifier._tail_resume_value``), so the lowering predicate,
    the guard and its obligation cannot drift apart.
    """
    tail: ast.Expr = body
    while True:
        if isinstance(tail, ast.Block):
            tail = tail.expr
            continue
        if isinstance(tail, ast.MatchExpr) and len(tail.arms) == 1:
            tail = tail.arms[0].body
            continue
        break
    if (isinstance(tail, ast.FnCall) and tail.name == "resume"
            and len(tail.args) == 1):
        return tail.args[0]
    return None


def contains_resume(node: object) -> bool:
    """Whether *node* contains a ``resume(...)`` call — a nested handler's
    clauses excluded, since their resumes are the inner handler's; its body
    and state init are lexically part of the enclosing clause."""
    return _resume_count(node) > 0


def _resume_count(node: object) -> int:
    if isinstance(node, ast.HandleExpr):
        n = _resume_count(node.body)
        if node.state is not None:
            n += _resume_count(node.state.init_expr)
        return n
    if isinstance(node, ast.FnCall) and node.name == "resume":
        # resume's own arguments cannot contain another resume in a checkable
        # program (resume returns Unit); count them anyway so a pathological
        # nesting is refused, not miscounted.
        return 1 + sum(_resume_count(a) for a in node.args)
    if isinstance(node, (list, tuple)):
        return sum(_resume_count(item) for item in node)
    if is_dataclass(node) and not isinstance(node, type):
        return sum(_resume_count(getattr(node, f.name)) for f in fields(node))
    return 0


#: :func:`state_clause_refusal`'s two answers.
CLAUSE_NOT_SINGLE_SHOT = "not-single-shot"
CLAUSE_RESUME_IN_WITH = "resume-in-with"


def state_clause_refusal(clause: ast.HandlerClause) -> str | None:
    """Why code generation cannot inline this ``State`` handler clause, or
    ``None`` when it can.

    Replaces the two refusals in ``_translate_state_clause_op``
    (``vera/wasm/calls_handlers.py``).  A clause is inlined at each
    operation that reaches it, and the inlining makes the clause's
    ``resume(v)`` the operation's result at that site, so:

    * :data:`CLAUSE_NOT_SINGLE_SHOT` — the body holds exactly one resume and
      it is the body's tail.  An ``if`` or a multi-arm ``match`` is a join,
      and a resume in an arm pushes a value onto a branch the checker types
      as ``Unit``; a missing or repeated resume leaves the site's stack
      wrong.  The canonical form branches inside the argument:
      ``resume(if c then { a } else { b })``.
    * :data:`CLAUSE_RESUME_IN_WITH` — a resume inside the ``with`` update
      has no effect: the body's tail resume is the continuation.
    """
    if not (tail_resume_arg(clause.body) is not None
            and _resume_count(clause.body) == 1):
        return CLAUSE_NOT_SINGLE_SHOT
    if (clause.state_update is not None
            and contains_resume(clause.state_update[1])):
        return CLAUSE_RESUME_IN_WITH
    return None


# =====================================================================
# Rule 3: a quantifier's predicate and bound (#1506) — E179, E128
# =====================================================================


#: The positions :func:`quantifier_predicate_refusals` can refuse.
PREDICATE_ARITY = "arity"
PREDICATE_PARAMETER = "parameter"
PREDICATE_RESULT = "result"


def quantifier_predicate_refusals(
    arity: int, param: Type | None, result: Type | None,
) -> list[tuple[str, str]]:
    """Each position at which a ``forall`` / ``exists`` predicate of *arity*
    parameters, the first of type *param*, returning *result*, has no
    lowering, with the reason: ``[(position, reason), ...]``, empty when it
    lowers.  This is E179's rule (spec §6.3.3).

    Code generation lowers the quantifier as a loop over an ``i64`` counter,
    binds the counter under the predicate parameter's type and reads an
    ``i32`` Bool (``_translate_quantifier``, ``vera/wasm/operators.py``).
    So the predicate takes exactly one parameter, of type ``Int`` or
    ``Nat`` — an alias of either resolves to it — and returns ``Bool``.

    * A refinement of the parameter is refused: the predicate is applied to
      every index below the bound, so a refinement narrower than the index
      cannot hold of all of them (a refinement of the INDEX type is
      honoured).
    * A type parameter is refused at either position (#1506): the counter
      is an ``i64`` and the result an ``i32``, so the predicate lowers only
      at the instantiations that make it ``Int``/``Nat`` -> ``Bool``.
      Conservative: the template answers for every instantiation.

    *param* is read only for a predicate of one parameter.  *param* or
    *result* ``None`` (or ``UnknownType``) means resolving it was itself
    refused, and that position gets no verdict here.
    """
    refusals: list[tuple[str, str]] = []
    if arity != 1:
        refusals.append((PREDICATE_ARITY, f"this one takes {arity} parameters"))
    elif isinstance(param, RefinedType):
        refusals.append(
            (PREDICATE_PARAMETER, "its parameter is a refinement type"))
    elif isinstance(param, TypeVar):
        refusals.append((
            PREDICATE_PARAMETER,
            f"its parameter is the type parameter {param.name}, which the "
            f"index is bound to only where it is Int or Nat",
        ))
    elif not (param is None or isinstance(param, UnknownType)
              or param in (INT, NAT)):
        refusals.append(
            (PREDICATE_PARAMETER, f"its parameter is {pretty_type(param)}"))
    shown = result
    while isinstance(shown, RefinedType):
        shown = shown.base
    if isinstance(shown, TypeVar):
        refusals.append((
            PREDICATE_RESULT,
            f"it returns the type parameter {shown.name}, which is read as "
            f"a Bool only where it is Bool",
        ))
    elif not (shown is None or isinstance(shown, UnknownType)
              or shown == BOOL):
        refusals.append((PREDICATE_RESULT, f"it returns {pretty_type(shown)}"))
    return refusals


def quantifier_predicate_shape_lowerable(pred: ast.AnonFn) -> bool:
    """Code generation's half of rule 3: the shape ``_translate_quantifier``
    binds the counter under — one parameter, written as a type name (an
    alias of ``Int`` or ``Nat`` included; the checker has resolved what the
    name means).  Replaces its two invariant errors."""
    return len(pred.params) == 1 and isinstance(pred.params[0], ast.NamedType)


def quantifier_bound_lowerable(ty: Type | None) -> bool:
    """Whether a quantifier's bound of type *ty* lowers: an ``Int`` or
    ``Nat`` count, through refinements (spec §6.3.3).  This is E128's rule.

    The counter loop compares an ``i64``, so a bound typed by a type
    parameter lowers only at its integer instantiations and is refused at
    the template (#1506).  ``None`` or ``UnknownType`` gets no verdict.
    """
    if ty is None or isinstance(ty, UnknownType):
        return True
    base = base_type(ty)
    return base in (INT, NAT)


# =====================================================================
# Rule 4: abilities (#1499)
# =====================================================================

#: The abilities code generation implements: ``eq`` and ``compare`` are
#: rewritten to comparisons, ``hash`` and ``show`` dispatched on the
#: argument's type (spec §9.8.3).  No declaration implements an ability for
#: a type, so a user-declared ability's operation has no body anywhere.
LOWERED_ABILITIES: frozenset[str] = frozenset({"Eq", "Ord", "Hash", "Show"})


def ability_lowerable(ability_name: str) -> bool:
    """Whether code generation lowers *ability_name*'s operations and its
    use as a constraint (#1499).

    Replaces the refusal in ``_check_constraints``
    (``vera/codegen/monomorphize.py``), "Ability ... is not yet supported for
    code generation" (E613 at line 0), and the guard rail that met a bare
    call to a user ability's operation as an undefined function.  The
    checker refuses a call to an operation of an ability this answers
    False for, a ``where`` constraint naming one, and a qualified
    ``Ability.op(...)`` call, which names an ability where only an effect
    can be named: an ability's operation is called bare.
    """
    return ability_name in LOWERED_ABILITIES


# =====================================================================
# Rule 5: a clause-body State operation under nested cells (#1233, #1522)
# — E339
# =====================================================================

# #1211/#1233: nesting cap for the OUTWARD re-entry of inlined `State` clause
# bodies.  A bare `get`/`put` written in a clause body is an operation of the
# ENCLOSING context, so lowering it inlines the enclosing handler's clause,
# whose own bare ops inline the one outside that, and so on.  Each clause body
# is re-expanded once per bare op that reaches it, so a nest of N handlers
# whose clauses each perform k bare ops emits O(k**N) instructions from O(N)
# lines of source.  Reaching the depth needs N DISTINCT cell families — a
# repeated family shadows the outer cell and is refused outright (#1233) — so
# the series is measured over one ADT per level with two bare `put`s per
# clause: WAT grows 851 → 1,583 → 4,331 → 15,143 lines at depths 2/4/6/8
# (`_deep_nest` in `tests/test_nested_handler_clause_ops.py` generates it).
#
# The checker refuses a re-entry past the cap where the operation is written
# (E339), and code generation's gate is the backstop.  The cap fires on
# PROGRAM STRUCTURE, not on the interpreter's recursion limit, so the refusal
# is deterministic.  Set generously: the legitimate nested-handler matrix
# (`tests/conformance/ch07_clause_body_op_enclosing.vera`,
# `tests/test_nested_handler_clause_ops.py`) reaches depth 2 and hand-written
# handler nests are shallower still, while a program at the cap needs eight
# distinct cell families and two bare ops in every clause — so anything past
# it is a generated program, not a written one.
STATE_CLAUSE_INLINE_DEPTH_CAP = 8


@dataclass(frozen=True)
class Cell:
    """A pushed ``State`` cell, as the shadowing rule compares it.

    ``family`` is the cell's identity (:func:`vera.naming.family_name`, the
    name code generation keys its host intrinsics by).  ``type`` is the
    checker's semantic type of the cell, ``None`` where the family is all
    there is (code generation's clones, whose families are concrete); it
    takes no part in equality or hashing.
    """

    family: str
    type: Type | None = field(default=None, compare=False, hash=False)


def cells_may_coincide(a: Cell, b: Cell) -> bool:
    """Whether cells *a* and *b* are, or at some instantiation become, one
    family (#1233, #1522).  This is E339's shadowing judgement.

    Equal families coincide.  A cell whose type mentions a type parameter
    coincides with any cell its type can unify with, a type parameter
    unifying with anything: ``State<T>`` with ``State<Int>`` (at ``T =
    Int``), with ``State<U>``, and ``State<Option<T>>`` with
    ``State<Option<Int>>``, but not ``State<Option<T>>`` with
    ``State<Int>``.  Conservative by design: ``State<T>`` nested in
    ``State<Int>`` is refused even where every instantiation is
    ``Bool``, because the checker does not hold the instantiation set.
    Without a type on either side the families are all that is compared,
    which is code generation's question about a clone.
    """
    if a.family == b.family:
        return True
    if a.type is None or b.type is None:
        return False
    if not (contains_typevar(a.type) or contains_typevar(b.type)):
        return False
    return _may_unify(a.type, b.type)


def _may_unify(a: Type, b: Type) -> bool:
    if isinstance(a, TypeVar) or isinstance(b, TypeVar):
        return True
    if isinstance(a, AdtType) and isinstance(b, AdtType):
        return (a.name == b.name and len(a.type_args) == len(b.type_args)
                and all(_may_unify(x, y)
                        for x, y in zip(a.type_args, b.type_args)))
    if isinstance(a, AdtType) or isinstance(b, AdtType):
        # An ADT against anything but an ADT or a type parameter: no
        # instantiation makes them one type (`Option<T>` is never `Int`).
        return False
    if contains_typevar(a) or contains_typevar(b):
        # A type parameter inside a shape the walk does not take apart
        # (a function type, a refinement of one): it may coincide.
        return True
    # Both concrete: `types_equal` compares refinements by base, so it may
    # answer True for two families that differ — the conservative direction.
    return types_equal(a, b)


def shadowing_cell(target: Cell, pushed: Sequence[Cell]) -> Cell | None:
    """The first cell of *pushed* — the cells pushed since the scope the
    operation resolves in — that may be *target*'s family, or ``None``.

    Code generation's host intrinsics address only the innermost cell of a
    family, so an operation whose cell is shadowed would read or write the
    wrong one.  Asked by the checker's E339 walk with semantic types and by
    ``_reject_unaddressable_clause_op`` (``vera/wasm/calls_handlers.py``)
    with families alone.
    """
    for cell in pushed:
        if cells_may_coincide(target, cell):
            return cell
    return None


# =====================================================================
# Rule 6: an effect row's entries, and an operation's effect (#1681)
# =====================================================================

#: The reasons :func:`effect_row_entry_refusal` gives: the entry names an
#: effect code generation lowers nothing for, ``State`` / ``Exn`` without
#: the one type argument that types its cell or its payload, or a row
#: variable in a declaration's own row.
ROW_EFFECT_NOT_LOWERED = "effect"
ROW_TYPE_ARGUMENT = "type argument"
ROW_VARIABLE = "row variable"


def effect_row_entry_refusal(
    name: str, type_args: int, *,
    row_variable: bool = False, declaration: bool = False,
) -> str | None:
    """Why code generation cannot lower an effect row entry naming *name*
    with *type_args* type arguments, or ``None`` when it lowers (#1681).

    An entry lowers when it names an effect code generation compiles,
    :data:`~vera.narrowing.COMPILABLE_EFFECTS` (every built-in effect), and,
    for ``State`` and ``Exn``, carries exactly one type argument: the cell's
    type, the payload's.  Replaces the refusals in ``_is_compilable``
    (``vera/codegen/compilability.py``), which dropped a function whose row
    named a user-declared effect, or ``State`` or ``Exn`` without a type
    argument.

    A *row_variable*, a ``forall`` variable written as an entry, lowers in a
    function type's row, a parameter's or a closure literal's, where the
    row is erased with the function value, and not in a *declaration*'s own
    row.  Code generation compiles a generic function once per
    instantiation of its type parameters, and an instantiation substitutes
    the types and leaves the row as written, so a clone's row still names
    the variable and there is no effect to compile for it: the template and
    every clone were dropped.  The checker admits a function value
    under a row variable only when its row fits the row's other entries, so
    a value's variable stands for no effect.

    A user-declared effect has no lowering anywhere: no handler for one is
    lowered (rule 1), so its operations have no implementation.  The checker
    refuses it in every row, a closure's and a function type's as well as a
    declaration's.  Code generation compiles a closure whose row names one,
    and nothing applies it: applying it needs the effect in the caller's
    row, and that row is refused.  An operation of one, called under a row
    that does not name it, is refused at the call
    (:func:`effect_operation_lowerable`).  So the declaration is all of a
    user-declared effect that checks.
    """
    if row_variable:
        return ROW_VARIABLE if declaration else None
    if name not in COMPILABLE_EFFECTS:
        return ROW_EFFECT_NOT_LOWERED
    if name in ("State", "Exn") and type_args != 1:
        return ROW_TYPE_ARGUMENT
    return None


def effect_operation_lowerable(effect_name: str) -> bool:
    """Whether code generation lowers an operation of *effect_name* (#1681).

    A built-in effect's operations are lowered, through the host and, for
    ``State`` and ``Exn``, through their handlers; a user-declared effect's
    are lowered nowhere.  A row naming the effect is refused at the entry
    and a handler for it at the handler, so the checker refuses a call of
    one wherever the row in force does not name it: under another row, a
    pure one too, and where no function's row is in force yet, in a
    refinement predicate.  Code generation
    lowers an operation by its effect's name and has no site that tells
    such a call apart: it emits a call to a host import no host provides,
    and the module does not load.

    A built-in effect's operation is lowered under any row: the effect
    checker holds it to the row in force (E125, #1702), and in a closure's
    body rule 7 holds a ``State`` or ``Exn`` one to a handler written there.
    """
    return effect_name in COMPILABLE_EFFECTS


# =====================================================================
# Rule 7: a State or Exn operation in a closure's body (#1702)
# =====================================================================


def closure_operation_lowerable(
    effect_name: str, *, handled_in_closure: bool,
) -> bool:
    """Whether code generation lowers an operation of *effect_name* written
    in a closure literal's body, *handled_in_closure* saying that a handler
    for the effect is written inside that closure, around the operation
    (#1702).

    A ``State`` operation reads or writes a cell, and an ``Exn`` one throws
    to a tag, that the function being compiled registers from its row or
    from a handler in its body.  A closure is lifted into a function of its
    own, whose row registers neither: a bare ``put`` or ``throw`` there has
    no route, and code generation drops the function (E602), and a
    qualified one calls a host import the module does not declare, so the
    module does not assemble.  A handler written inside the closure
    registers its cell or its tag in the lifted function, and an operation
    under it lowers.  A handler around the closure does not: the closure is
    compiled apart from it, and can be applied outside it.  The other
    built-in effects' operations are the host's, and lower in a closure as
    anywhere.  A quantifier's predicate is no closure here: code generation
    inlines it into the function around the quantifier (spec §11.13.2),
    whose cell and tag its operations reach.
    """
    return effect_name not in HANDLED_EFFECTS or handled_in_closure
