"""Mixin for function calls, constructor calls, and qualified/module calls.

Extracted from ``core.py`` so that call-checking logic lives in its
own file while the main :class:`TypeChecker` stays focused on
orchestration.
"""

from __future__ import annotations

import functools
from collections import Counter
from collections.abc import Callable
import typing
from typing import Any, cast

from vera import ast, narrowing
from vera.binding import bare_name
from vera.lowering import (
    ability_lowerable,
    closure_operation_lowerable,
    effect_operation_lowerable,
    handler_lowerable,
)
from vera.checker.resolution import _span_text
from vera.checker.sql import (
    count_placeholders,
    resolve_array_len,
    resolve_literal_string,
)
from vera.environment import (
    DB_SQL_OP_NAMES,
    STRING,
    AdtInfo,
    ConstructorInfo,
    FunctionInfo,
    OpInfo,
)
from vera.types import (
    BUILTIN_TYPEVAR_MARKER,
    FREE_BUILTIN_TYPEVAR_MARKER,
    ORDERABLE_TYPES,
    AdtType,
    ConcreteEffectRow,
    EffectInstance,
    FunctionType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    base_type,
    canonical_type_name,
    contains_fresh_typevar,
    contains_literal_hole,
    contains_typevar,
    erases_to_unit,
    is_effect_subtype,
    is_subtype,
    pretty_effect,
    pretty_type,
    pretty_inferred_type,
    strip_builtin_typevar_marker,
    substitute,
    substitute_effect,
    types_equal,
)


def _op_signature_text(op: OpInfo) -> str:
    """An operation's REGISTERED signature as a function type's inside, for
    E340's fix: ``T -> Int``, the resolved types' message form.  Only for an
    effect or ability the program does not declare
    (:meth:`CallsMixin._operation_signature_text` reads a declared one)."""
    params = ", ".join(pretty_type(p) for p in op.param_types)
    return f"{params} -> {pretty_type(op.return_type)}"


def _compatible_modulo_typevars(
        a: Type, b: Type, rigid: frozenset[str]) -> bool:
    """Structural compatibility treating UNRESOLVED TypeVars as wildcards
    (#993), one position at a time.

    Used only by `CallsMixin._fits`, and there only where the join failed
    at a built-in's type variable a failed substitution lost and nothing
    else (`JoinOutcome.builtin`, #1688): the join neither fills nor refuses
    such a variable, so the fit keeps the verdict this rule gave before.
    Everywhere else the join decides (#1684), which binds each open
    variable once, where this matches each occurrence on its own.
    An unresolved var on either side matches anything: there EXISTS an
    instantiation making the two sides agree, so rejecting would be a
    false E202 (or E162).  Unresolved means a fresh `T$n`, a `#b`-marked
    builtin var, or a callee forall var leaked raw from an uninferrable call —
    everything EXCEPT the enclosing function's own declared forall params
    (*rigid*, passed by name from `env.type_params`).  A rigid var is NOT
    a wildcard — inside its own body it is an opaque, already-quantified
    type, so `Option<T>` passed where `Option<Int>` is required must stay
    E202 (the body must be valid for EVERY `T`, PR #1009 review); two
    rigid vars agree only by name.  (A callee var leaked under a
    same-named enclosing forall is conservatively treated as rigid —
    the safe direction.)  Concrete structure must still line up —
    `Option<...>` never matches `Result<...>`, a function's effect row
    must still be permitted by the parameter's (`<IO>` never satisfies
    `pure`), and a genuinely concrete leaf mismatch (`Int` vs `String`)
    is rejected via the subtype fallback.
    """
    a = base_type(a)
    b = base_type(b)
    if isinstance(a, UnknownType) or isinstance(b, UnknownType):
        return True
    if isinstance(a, TypeVar) or isinstance(b, TypeVar):
        a_rigid = (isinstance(a, TypeVar)
                   and "$" not in a.name and a.name in rigid)
        b_rigid = (isinstance(b, TypeVar)
                   and "$" not in b.name and b.name in rigid)
        if isinstance(a, TypeVar) and not a_rigid:
            return True
        if isinstance(b, TypeVar) and not b_rigid:
            return True
        # Every TypeVar side is rigid here: only the same var matches.
        return (isinstance(a, TypeVar) and isinstance(b, TypeVar)
                and a.name == b.name)
    if isinstance(a, AdtType) and isinstance(b, AdtType):
        return (a.name == b.name
                and len(a.type_args) == len(b.type_args)
                and all(_compatible_modulo_typevars(x, y, rigid)
                        for x, y in zip(a.type_args, b.type_args)))
    if isinstance(a, FunctionType) and isinstance(b, FunctionType):
        return (len(a.params) == len(b.params)
                and all(_compatible_modulo_typevars(x, y, rigid)
                        for x, y in zip(a.params, b.params))
                and _compatible_modulo_typevars(
                    a.return_type, b.return_type, rigid)
                and is_effect_subtype(a.effect, b.effect))
    # Leaves (primitives): the instantiation direction is unknown, so
    # accept a subtype relationship either way (Nat vs Int).
    return is_subtype(a, b) or is_subtype(b, a)


def _behaviour_params(
        name: str, data_types: typing.Mapping[str, AdtInfo],
        visiting: frozenset[str] = frozenset()) -> frozenset[int]:
    """The positions of data type *name*'s parameters that a value of it
    can hold behaviour over: those a constructor field holds inside a
    function type, its effect row included, directly or through another
    data type's such position (#1668).  A built-in container (`Array`, `Map`, `Tuple`, ...) has no
    fields, so it holds behaviour only where its argument is a function."""
    info = data_types.get(name)
    if info is None or not info.type_params or name in visiting:
        return frozenset()
    params = info.type_params
    inside = visiting | {name}
    held: set[int] = set()

    def walk(ty: Type, behaviour: bool) -> None:
        ty = base_type(ty)
        if isinstance(ty, TypeVar):
            if behaviour and ty.name in params:
                held.add(params.index(ty.name))
        elif isinstance(ty, AdtType):
            holds = _behaviour_params(ty.name, data_types, inside)
            for i, arg in enumerate(ty.type_args):
                walk(arg, behaviour or i in holds)
        elif isinstance(ty, FunctionType):
            for param in ty.params:
                walk(param, True)
            walk(ty.return_type, True)
            if isinstance(ty.effect, ConcreteEffectRow):
                for inst in ty.effect.effects:
                    for arg in inst.type_args:
                        walk(arg, True)

    for ctor in info.constructors.values():
        for field in ctor.field_types or ():
            walk(field, False)
    return frozenset(held)


#: A position inside a type, from its root: each step a function type's
#: parameter (`("param", i, n)`, the i-th of n), its result (`("result",)`)
#: or a data type's type argument (`("arg", name, i, n)`).
TypePath = tuple[tuple[typing.Any, ...], ...]


class JoinFailure(typing.NamedTuple):
    """Where a join failed, for a diagnostic to name (#1684).

    *variable* is the type variable at fault, on *side* (0 the first type
    joined, 1 the second).  For a *conflict* it was bound at *first* (the
    position, and the type the other side has there) and meets the other
    side's type at *second*.  Otherwise no argument fixed it and it is kept
    for behaviour (it stands in a function type, whose code was compiled at
    a type of its own), it meets another type at *second*, and *first* is
    None."""

    variable: str
    side: int
    first: tuple[TypePath, Type] | None
    second: tuple[TypePath, Type]
    conflict: bool


def describe_position(path: TypePath) -> str:
    """*path* in words, innermost first: `the parameter`, `component 2`,
    `the type argument of Option in component 1`, `the argument` for the
    root."""
    words: list[str] = []
    for step in reversed(path):
        if step[0] == "param":
            _, index, count = step
            words.append(f"parameter {index + 1}" if count > 1
                         else "the parameter")
        elif step[0] == "result":
            words.append("the result")
        else:
            _, name, index, count = step
            if name == "Tuple":
                words.append(f"component {index + 1}")
            elif count > 1:
                words.append(f"type argument {index + 1} of {name}")
            else:
                words.append(f"the type argument of {name}")
    return " in ".join(words) if words else "the argument"


def _variable_name(name: str) -> str:
    """A type variable as a message names it: a variable a call left open
    (`T$3`) by the variable it stands for (`T`), a built-in's without its
    marker."""
    return strip_builtin_typevar_marker(name).split("$", 1)[0]


def _map_holes(ty: Type, to: typing.Callable[[str], Type]) -> Type:
    """*ty* with each type variable a call left open (`T$3`) replaced by
    *to* of its name, at any depth, its function types' effect rows
    included."""
    if isinstance(ty, TypeVar):
        return to(ty.name) if "$" in ty.name else ty
    if isinstance(ty, AdtType):
        return AdtType(ty.name,
                       tuple(_map_holes(arg, to) for arg in ty.type_args))
    if isinstance(ty, FunctionType):
        effect = ty.effect
        if isinstance(effect, ConcreteEffectRow):
            effect = ConcreteEffectRow(
                frozenset(EffectInstance(
                    inst.name,
                    tuple(_map_holes(arg, to) for arg in inst.type_args))
                    for inst in effect.effects),
                effect.row_var)
        return FunctionType(tuple(_map_holes(param, to)
                                  for param in ty.params),
                            _map_holes(ty.return_type, to), effect)
    if isinstance(ty, RefinedType):
        return RefinedType(_map_holes(ty.base, to), ty.predicate)
    return ty


def _named_open(ty: Type) -> Type:
    """*ty* with each type variable a call left open (`T$3`) renamed to the
    variable it stands for, so a message shows `fn(T -> T)` where the
    inferred-type rendering shows `fn(? -> ?)`."""
    return _map_holes(ty, lambda name: TypeVar(_variable_name(name)))


def _holes_unknown(ty: Type) -> Type:
    """*ty* with each type variable a call left open (`T$3`) as the
    unknown, which renders `?`: the type a parameter asks where no argument
    fixed its variable."""
    return _map_holes(ty, lambda name: UnknownType())


def closure_signature(fn_ty: FunctionType,
                      rigid: frozenset[str]) -> str | None:
    """The signature a closure of *fn_ty* is written with, its body left
    out (`fn(@Int -> @Int) effects(pure)`), or None where the rendering is
    not one a program can write: a refinement, which `pretty_type` elides;
    a function type, which a slot names through an alias; a type variable
    other than the enclosing function's own; an open effect row."""

    def writable(t: Type) -> bool:
        if isinstance(t, (RefinedType, FunctionType, UnknownType)):
            return False
        if isinstance(t, TypeVar):
            return "$" not in t.name and t.name in rigid
        if isinstance(t, AdtType):
            return all(writable(arg) for arg in t.type_args)
        return True

    effect = fn_ty.effect
    if not (all(writable(p) for p in fn_ty.params)
            and writable(fn_ty.return_type)
            and (isinstance(effect, PureEffectRow)
                 or (isinstance(effect, ConcreteEffectRow)
                     and effect.row_var is None
                     and all(writable(arg) for inst in effect.effects
                             for arg in inst.type_args)))):
        return None
    params = ", ".join(f"@{pretty_type(p)}" for p in fn_ty.params)
    return (f"fn({params} -> @{pretty_type(fn_ty.return_type)}) "
            f"{pretty_effect(effect)}")


class JoinOutcome(typing.NamedTuple):
    """What `CallsMixin._join_parts` found (#1668).

    *joined* is the join, or None.  *conflict* is whether it failed
    because an open type variable took two types that do not agree.
    *builtin* is whether it failed only where a built-in's type variable
    met another type, with no variable kept for behaviour on either side:
    the join neither fills nor refuses such a variable (one a parameter of
    its call mentions that the arguments left unbound, standing for a type
    a failed substitution lost, #1688), and a site keeps the verdict it
    gave it before.  *failure* is where it failed, when a type variable is
    at fault (#1684)."""

    joined: Type | None
    conflict: bool
    builtin: bool
    failure: JoinFailure | None = None


def _lost_builtin_var(name: str) -> bool:
    """Whether *name* is a built-in's type variable that a parameter of its
    call mentions and the arguments left unbound: one standing for a type
    a failed substitution lost (#1688), which the join does not fill.  A
    built-in's variable the call marked free is open (#1668)."""
    return (BUILTIN_TYPEVAR_MARKER in name
            and FREE_BUILTIN_TYPEVAR_MARKER not in name)


def _rewrapped(original: Type, joined: Type) -> Type:
    """*joined*, under the refinements *original* has over its base."""
    if isinstance(original, RefinedType):
        return RefinedType(_rewrapped(original.base, joined),
                           original.predicate)
    return joined


class _Join:
    """One join of two types, *b* the one the result keeps where both are
    fixed (`CallsMixin._join`, #1668).

    A type variable is open where nothing has fixed it: not the enclosing
    function's own (*rigid*), not a built-in's (a `#b` variable left after
    the call is one a parameter mentions that the arguments did not bind,
    standing for a type a failed substitution lost; one no parameter
    mentions is minted fresh, `_mint_free_builtin_vars`), and nowhere in its own type
    inside a function type or a data type's position a constructor field
    holds a function over (`_behaviour_params`), since code generation
    compiles the behaviour there at a type of its own choosing.  Each open
    variable is bound by name, once per side, to the other side's type at
    its first position; a later occurrence is joined with that binding,
    and one that disagrees is a conflict.  A variable that is not open
    matches only itself.  The checker's unknown (`?`, an empty literal's
    element type) has no name: it is filled where it stands, except
    inside a function type, where it is kept."""

    def __init__(self, rigid: frozenset[str],
                 data_types: typing.Mapping[str, AdtInfo]) -> None:
        self.rigid = rigid
        self.data_types = data_types
        self.kept: tuple[frozenset[str], frozenset[str]] = (
            frozenset(), frozenset())
        self.behaviour: tuple[frozenset[str], frozenset[str]] = (
            frozenset(), frozenset())
        self.bound: tuple[dict[str, Type], dict[str, Type]] = ({}, {})
        #: Where each variable of *bound* was bound (#1684).
        self.bound_at: tuple[dict[str, TypePath], dict[str, TypePath]] = (
            {}, {})
        self.conflict = False
        self.builtin = False
        #: The first type variable at fault, where it is (#1684).
        self.failure: JoinFailure | None = None

    def join(self, a: Type, b: Type) -> Type | None:
        (kept_a, held_a), (kept_b, held_b) = self._kept(a), self._kept(b)
        self.kept = (kept_a, kept_b)
        self.behaviour = (held_a, held_b)
        joined = self._walk(a, b, False, ())
        if joined is None:
            return None
        # A variable bound at one position takes its binding at every
        # other: one of *b*'s where *a* left that position unknown, and one
        # of *a*'s kept where *b* was unknown there.  *b* itself comes back
        # where nothing changes, which `_join_elements` reads as a part that
        # filled nothing.
        for _ in range(len(self.bound[0]) + len(self.bound[1]) + 1):
            again = joined
            for bound in self.bound:
                if bound:
                    again = substitute(again, bound)
            if again == joined:
                break
            joined = again
        return joined

    def _kept(self, ty: Type) -> tuple[frozenset[str], frozenset[str]]:
        """The type variables of *ty* that are not open, and those of them
        that are not open because code generation compiles behaviour for
        them."""
        out: set[str] = set()
        held: set[str] = set()

        def walk(t: Type, behaviour: bool) -> None:
            t = base_type(t)
            if isinstance(t, TypeVar):
                if (behaviour or _lost_builtin_var(t.name)
                        or ("$" not in t.name and t.name in self.rigid)):
                    out.add(t.name)
                if behaviour:
                    held.add(t.name)
            elif isinstance(t, AdtType):
                holds = _behaviour_params(t.name, self.data_types)
                for i, arg in enumerate(t.type_args):
                    walk(arg, behaviour or i in holds)
            elif isinstance(t, FunctionType):
                for param in t.params:
                    walk(param, True)
                walk(t.return_type, True)
                if isinstance(t.effect, ConcreteEffectRow):
                    for inst in t.effect.effects:
                        for arg in inst.type_args:
                            walk(arg, True)

        walk(ty, False)
        return frozenset(out), frozenset(held)

    def _fixed(self, name: str) -> bool:
        """Whether the type variable *name* stands for a type of its own
        whatever its position: the enclosing function's, or a built-in's a
        failed substitution lost."""
        return _lost_builtin_var(name) or (
            "$" not in name and name in self.rigid)

    def _open(self, ty: Type, side: int) -> str | None:
        if isinstance(ty, TypeVar) and ty.name not in self.kept[side]:
            return ty.name
        return None

    def _bind(self, side: int, name: str, other: Type,
              path: TypePath) -> Type | None:
        """Bind *side*'s variable *name* where the other side has *other*,
        at *path*; the type the position takes."""
        prior = self.bound[side].get(name)
        if prior is None:
            self.bound[side][name] = other
            self.bound_at[side][name] = path
            return other
        again = _Join(self.rigid, self.data_types).join(prior, other)
        if again is None:
            self.conflict = True
            if self.failure is None:
                self.failure = JoinFailure(
                    name, side, (self.bound_at[side][name], prior),
                    (path, other), True)
            return None
        self.bound[side][name] = again
        return again

    def _walk(self, a: Type, b: Type, behaviour: bool,
              path: TypePath) -> Type | None:
        a_base = base_type(a)
        b_base = base_type(b)
        if isinstance(a_base, UnknownType):
            return b
        if isinstance(b_base, UnknownType):
            return b if behaviour else a
        a_var = self._open(a_base, 0)
        if a_var is not None:
            return self._bind(0, a_var, b, path)
        b_var = self._open(b_base, 1)
        if b_var is not None:
            return self._bind(1, b_var, a, path)
        if isinstance(a_base, TypeVar) or isinstance(b_base, TypeVar):
            # Neither is open: only the same variable matches.
            if (isinstance(a_base, TypeVar) and isinstance(b_base, TypeVar)
                    and a_base.name == b_base.name):
                return b
            self.builtin = any(
                isinstance(t, TypeVar) and _lost_builtin_var(t.name)
                for t in (a_base, b_base))
            for side, (var, other) in enumerate(((a_base, b), (b_base, a))):
                if (self.failure is None and isinstance(var, TypeVar)
                        and var.name in self.behaviour[side]
                        and not self._fixed(var.name)):
                    self.failure = JoinFailure(
                        var.name, side, None, (path, other), False)
            return None
        if isinstance(a_base, AdtType) and isinstance(b_base, AdtType):
            if (a_base.name != b_base.name
                    or len(a_base.type_args) != len(b_base.type_args)):
                return None
            holds = _behaviour_params(b_base.name, self.data_types)
            args: list[Type] = []
            count = len(b_base.type_args)
            for i, (x, y) in enumerate(zip(a_base.type_args,
                                           b_base.type_args)):
                arg = self._walk(x, y, behaviour or i in holds,
                                 (*path, ("arg", b_base.name, i, count)))
                if arg is None:
                    return None
                args.append(arg)
            if all(arg is y for arg, y in zip(args, b_base.type_args)):
                return b
            return _rewrapped(b, AdtType(b_base.name, tuple(args)))
        if isinstance(a_base, FunctionType) and isinstance(b_base, FunctionType):
            if (len(a_base.params) != len(b_base.params)
                    or not is_effect_subtype(a_base.effect, b_base.effect)):
                return None
            params: list[Type] = []
            count = len(b_base.params)
            for i, (x, y) in enumerate(zip(a_base.params, b_base.params)):
                param = self._walk(x, y, True, (*path, ("param", i, count)))
                if param is None:
                    return None
                params.append(param)
            ret = self._walk(a_base.return_type, b_base.return_type, True,
                             (*path, ("result",)))
            if ret is None:
                return None
            if (ret is b_base.return_type
                    and all(p is y for p, y in zip(params, b_base.params))):
                return b
            return _rewrapped(
                b, FunctionType(tuple(params), ret, b_base.effect))
        # Leaves (primitives): a subtype either way, as the argument
        # judgement accepts them (Nat and Int).
        if is_subtype(a_base, b_base) or is_subtype(b_base, a_base):
            return b
        return None


def _type_var_occurrences(ty: Type, out: Counter[str]) -> None:
    """Count into *out* every occurrence of a type variable in *ty*, at any
    depth: through type arguments, a function type's parameters, result and
    effect row, and a refinement's base."""
    if isinstance(ty, TypeVar):
        out[ty.name] += 1
    elif isinstance(ty, AdtType):
        for arg in ty.type_args:
            _type_var_occurrences(arg, out)
    elif isinstance(ty, FunctionType):
        for param in ty.params:
            _type_var_occurrences(param, out)
        _type_var_occurrences(ty.return_type, out)
        _effect_type_var_occurrences(ty.effect, out)
    elif isinstance(ty, RefinedType):
        _type_var_occurrences(ty.base, out)


def _effect_type_var_occurrences(row: object, out: Counter[str]) -> None:
    """:func:`_type_var_occurrences` over an effect row's type arguments."""
    if isinstance(row, ConcreteEffectRow):
        for inst in row.effects:
            for arg in inst.type_args:
                _type_var_occurrences(arg, out)


def _names(name: str) -> Callable[[str], bool]:
    """The constructor-name test a pattern of constructor *name* makes."""
    def matches(ctor_name: str) -> bool:
        return ctor_name == name
    return matches

_Check = typing.TypeVar("_Check", bound=Callable[..., Any])


def _reported_at_the_stage(check: _Check) -> _Check:
    """Check a call inside `_about_the_call`: what its check reports at the
    call node is about the call itself, so a piped call's is placed at its
    stage, where the call is written (`core._placement`), as `main` placed
    it.  A diagnostic the call's context reports about its value comes
    after the check returns, and stays at the pipe."""
    @functools.wraps(check)
    def checked(self: Any, expr: ast.Expr, *args: Any, **kwargs: Any) -> Any:
        with self._about_the_call(expr):
            return check(self, expr, *args, **kwargs)
    return cast(_Check, checked)


class CallsMixin:
    """Methods for checking function calls, constructors, and qualified calls."""

    def _fits(self, ty: Type, target: Type) -> bool:
        """Whether a value of type *ty* may stand where *target* is
        required: the judgement a call argument is held to its parameter
        with, and an array literal's element to the literal's element type
        (#1584).

        A subtype fits.  So does a type that a type variable left unresolved
        on either side makes compatible (#993), when the instantiation is not
        pinned down — `option_unwrap_or(nothing(()), None)`, whose every
        argument is itself polymorphic, or `[None, Some(1)]`, whose first
        element leaves `Option`'s `T` open — by the one judgement the joins
        of an array literal's elements and an `if`'s and a `match`'s arms
        are given (`_join_parts`, #1668): each open variable is bound by
        name, so one that occurs twice takes one type (#1684), and a
        variable in a position code generation compiles behaviour for, a
        function type or a data field held over one, is not open, since that
        behaviour was compiled at a type of its own.  So `fn(T -> T)`, from a
        call no argument of which fixes `T`, fits neither
        `fn(Option<Nat> -> Option<String>)` nor `fn(Int -> Int)`.  The
        enclosing function's own type parameters are rigid, and fully
        concrete mismatches are unaffected.  A generic call's result takes
        the data type its context expects by the same join
        (`_synth_fn_call`), so an argument reaches this judgement with the
        type its call gave it, never one no instantiation gives.  Where the
        join fails only at a
        built-in's variable a failed substitution lost (#1688), the join
        neither fills nor refuses it, and the fit keeps the verdict it gave
        before, each variable a wildcard one position at a time
        (`_compatible_modulo_typevars`)."""
        if is_subtype(ty, target):
            return True
        if not (contains_typevar(ty) or contains_typevar(target)):
            return False
        outcome = self._join_parts(ty, target)
        if outcome.joined is not None:
            return True
        return outcome.builtin and _compatible_modulo_typevars(
            ty, target, frozenset(self.env.type_params))

    def _join(self, ty: Type, onto: Type) -> Type | None:
        """The type a value of *ty* and a value of *onto* have together:
        *onto*, with each position it leaves open given *ty*'s type there;
        None where the two do not agree (#1668).

        The join an array literal's elements, an `if`'s branches and a
        `match`'s arms are given (`_Join`): each open type variable is
        bound by name, so one that occurs twice takes one type, and a
        variable code generation compiles behaviour for, a built-in's,
        or the enclosing function's own is not filled.  Where both leave a
        position open it stays open, for the context to fill.  *onto*
        itself comes back where *ty* fills nothing."""
        return self._join_parts(ty, onto).joined

    def _join_parts(self, ty: Type, onto: Type) -> JoinOutcome:
        """`_join`, with why it failed where it did (`JoinOutcome`)."""
        walk = _Join(frozenset(self.env.type_params), self.env.data_types)
        joined = walk.join(ty, onto)
        if joined is None and not walk.conflict and is_subtype(ty, onto):
            # A subtype the walk refuses (`Never` beside a variable that
            # is not open): it fills nothing.
            return JoinOutcome(onto, False, False)
        builtin = (joined is None and walk.builtin and not walk.conflict
                   and not (walk.behaviour[0] or walk.behaviour[1]))
        return JoinOutcome(joined, walk.conflict, builtin,
                           walk.failure if joined is None else None)

    # -----------------------------------------------------------------
    # Function calls
    # -----------------------------------------------------------------

    @_reported_at_the_stage
    def _check_fn_call(self, expr: ast.FnCall, *,
                       expected: Type | None = None) -> Type | None:
        """Type-check a function call.

        *expected* is the type the call's result is checked against, where
        the context supplies one: a generic callee's type arguments that
        only literals would fix take it (#1541).
        """
        return self._check_call_with_args(expr.name, expr.args, expr,
                                          expected=expected)

    def _check_call_with_args(self, name: str, args: tuple[ast.Expr, ...],
                              node: ast.Node, *,
                              expected: Type | None = None) -> Type | None:
        """Check a call to function `name` with given arguments."""
        # apply_fn is a checker special form (#854): it is variadic and
        # effect-polymorphic — its arity, argument types, result type,
        # and effect row all come from the applied value's fn type — so
        # it cannot be a fixed-signature registry built-in.  Intercept
        # before any lookup: codegen translates the name unconditionally
        # to call_indirect (vera/wasm/calls.py), and E151 rejects user
        # redefinitions, so this is the name's single canonical meaning.
        if name == "apply_fn":
            return self._check_apply_fn(args, node)

        # The function the resolver pass bound the call to (#1694): the
        # nearest same-named where-helper in the enclosing functions first
        # (#991), so a diamond of same-named helpers with DIFFERENT
        # signatures checks each parent against its OWN helper.
        #
        # #1284: a declaration owns every bare call to its name in its scope
        # before any operation does (spec §7.4: a bare op resolves only for a
        # name no declaration occupies), and codegen has to lower every such
        # call site the way this resolution read it.  Code generation asks
        # `bare_call_denotes_user_fn` over its own scoped table, which the
        # link step names by the same binding: a `fn get` called under a
        # `handle[State<T>]` once lowered to the host cell intrinsic — a
        # silently wrong value, a module WASM validation rejected, or a
        # spurious [E602] naming a State operation the user never wrote.
        fn_info = self._bound_function(node)
        if fn_info is not None:
            return self._check_fn_call_with_info(fn_info, args, node,
                                                 expected=expected)

        # Maybe it's an effect operation (`_check_op_call` counts its effect
        # for the purity check)
        op_info = self.env.lookup_effect_op(name)
        if op_info:
            # #1148: a BARE (unqualified) op call is codegen-routable only for
            # the built-in State/Exn ops get/put/throw (which route to host
            # cells / a host tag even unhandled) or when the effect is handled by
            # an enclosing `handle` block (rewritten to the clause).  Every other
            # bare op — IO / DB / Http / Inference / Random and user effects —
            # fails `vera compile` with a confusing "Function '<op>' is not
            # defined".  Reject it at check time (E217, the safe direction of a
            # check<->codegen disagreement).
            #
            # The carve-out keys on BOTH the effect name AND the op name, not the
            # effect name alone: codegen bare-routes only get/put (State) and
            # throw (Exn) — not an arbitrary op of an effect that merely happens
            # to be named State/Exn.  Keying on the effect name alone let a user
            # `effect State<T> { op sneak(...) }` / `effect Exn<E> { op boom }`
            # shadow's bare op pass check and then hard-fail compile (#1147
            # adversarial workflow), the exact desync E217 exists to close.
            # Such a shadow is itself rejected since #1149 (E152); the op-name
            # keying stays as defence in depth behind that gate.
            bare_routable_builtin = (op_info.parent_effect, op_info.name) in (
                ("State", "get"), ("State", "put"), ("Exn", "throw"),
            )
            if (
                not bare_routable_builtin
                and op_info.parent_effect not in self._handled_effects
            ):
                self._error(
                    node,
                    f"Effect operation '{name}' cannot be called bare here; it "
                    f"must be called qualified as "
                    f"'{op_info.parent_effect}.{name}(...)' or performed inside "
                    f"an enclosing 'handle[{op_info.parent_effect}]' block.",
                    rationale=(
                        "A bare (unqualified) op call is lowered to a handler "
                        "clause of an enclosing 'handle' block; with no such "
                        "block in scope, only the built-in State/Exn ops "
                        "(get/put/throw) have a bare host route, so any other "
                        "bare op call has no code to emit and fails compilation."
                    ),
                    fix=(
                        f"Write '{op_info.parent_effect}.{name}(...)' — a host "
                        "effect routes by qualifier — or perform the op inside a "
                        f"'handle[{op_info.parent_effect}] {{ ... }} in {{ ... }}'"
                        " block."
                    ),
                    spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
                    error_code="E217",
                )
            return self._check_op_call(op_info, args, node)

        # Maybe it's an ability operation
        ab_op = self.env.lookup_ability_op(name)
        if ab_op:
            return self._check_ability_op_call(ab_op, args, node)

        # #1307: the name resolves to nothing HERE, but the program does
        # declare it — as a `where` helper of another declaration, which
        # spec §5.8 makes local to its parent.  Reported as its own error
        # rather than E200's warning: E200's instruction ("define it in
        # this file") is false for a name the file already declares, and
        # codegen has no target for the call either way, so accepting the
        # program would be a check-green module that cannot be built.
        owners = self._where_helper_parents.get(name)
        if owners:
            # Each owner arrives ready to read: "'holder'" for a helper of
            # this file, "'phost' in module 'hlib'" for an imported one.
            owner_list = ", ".join(sorted(owners))
            plural = "s" if len(owners) > 1 else ""
            # The two fixes differ in kind, not just in wording: a caller
            # in this file can move into the parent's body, and a caller in
            # another file cannot — its repair is to call the parent it
            # already imports, or to have the module export the helper.
            imported = any("in module" in o for o in owners)
            parents_only = ", ".join(
                sorted(o.split(" in module ")[0] for o in owners)
            )
            if imported:
                repair = (
                    f"Call {parents_only} instead — a module reaches its "
                    f"helpers, an importer reaches the module's public "
                    f"declarations — or, if '{name}' is meant to be shared, "
                    f"lift it out of the `where` block{plural} to a "
                    f"top-level 'public fn {name}(...)' in that module and "
                    f"import it."
                )
            else:
                repair = (
                    f"Call {parents_only} instead, move this call into the "
                    f"body of {parents_only}, or — if '{name}' is meant to "
                    f"be shared — lift it out of the `where` block{plural} "
                    f"to a top-level 'private fn {name}(...)'."
                )
            self._error(
                node,
                f"'{name}' is a where-helper of {owner_list} and is not in "
                f"scope here.",
                rationale="A function declared in a `where` block is local "
                          "to the function that declares it: it is visible "
                          "to that function's body and to its sibling "
                          "helpers, and to nothing else — not to another "
                          "declaration in the same file, and not to a file "
                          "that imports its parent's module.",
                fix=repair,
                spec_ref='Chapter 5, Section 5.8 "Function Visibility"',
                error_code="E178",
            )
            for arg in args:
                self._synth_expr(arg)
            return UnknownType()

        if name in self._ambiguous_import_fn_names:
            # #1304: two imports supply this name, so it denotes none of
            # their declarations, and the E155 at the import is the one
            # error the program owes.  A second error here would only
            # restate it, and could name no remedy of its own: qualifying
            # the call does not lift an E155 (§8.5.2.2).
            for arg in args:
                self._synth_expr(arg)
            return UnknownType()

        # Unresolved — an error (#1513): a call to nothing has no body to
        # compile, so a warning here let `vera check` pass a program code
        # generation then refused.  Name the module when one this file can
        # see declares the function, which is the fix a reader needs.
        # Sorted: a module checker's `_resolved_modules` is built by walking
        # a set of import paths, so its order follows the hash seed.
        declaring = sorted(
            mod.path for mod in self._resolved_modules
            if name in self._module_functions.get(mod.path, {})
        )
        if declaring:
            fix = ("Import it from the module that declares it: "
                   + " or ".join(self._import_line(m, name)
                                 for m in declaring)
                   + ".  A module reached only through another module's "
                     "imports is not visible to this file until it is "
                     "imported here.")
        else:
            fix = (f"Define 'fn {name}(...)' in this file, or import it from "
                   f"the module that declares it with "
                   f"'import <module>({name});' (replace <module> with that "
                   f"module's path, e.g. 'vera.math'); check the spelling "
                   f"too.")
        self._error(
            node,
            f"Unresolved function '{name}'.",
            rationale="A bare call must resolve to a function, effect "
                      "operation, or ability operation in scope; no "
                      "declaration named this could be found, so there is "
                      "no body to call and the program cannot compile.",
            fix=fix,
            spec_ref='Chapter 8, Section 8.5.1 "Bare Calls"',
            error_code="E200",
        )
        # Still synth arg types to find errors within them
        for arg in args:
            self._synth_expr(arg)
        return UnknownType()

    def _record_instantiation(self, node: ast.Node, fn_info: FunctionInfo,
                              mapping: typing.Mapping[str, Type]) -> None:
        """Record the instantiation the check inferred at the generic call
        *node* (#1679), keyed by the call's identity.

        Only a call the binding binds to a declaration is recorded: a
        built-in generic has no declaration to instantiate, and code
        generation lowers each of its calls itself.  A call checked twice
        (an argument re-synthesised against its formal) records the later
        inference, which is the one its node's type records too."""
        from vera.binding import BUILTIN
        from vera.typed import Instantiation

        if self.instantiations is None or node.node_id is None:
            return
        ident = self._binding.of(node) if self._binding is not None else None
        if ident is None or ident.owner == BUILTIN:
            return
        self.instantiations[node.node_id] = Instantiation(
            callee=ident.link_name,
            forall_vars=tuple(fn_info.forall_vars or ()),
            mapping={tv: mapping[tv] for tv in fn_info.forall_vars or ()
                     if tv in mapping},
        )

    def _check_fn_call_with_info(self, fn_info: FunctionInfo,
                                 args: tuple[ast.Expr, ...],
                                 node: ast.Node, *,
                                 expected: Type | None = None,
                                 ) -> Type | None:
        """Check a call against a known function signature."""
        # Synth arg types.  For non-generic functions pass the declared
        # param type as *expected* so that nested constructors can resolve
        # TypeVars from context (fixes #243).
        arg_types: list[Type | None] = []
        for i, arg in enumerate(args):
            exp: Type | None = None
            if (not fn_info.forall_vars
                    and i < len(fn_info.param_types)):
                pt = fn_info.param_types[i]
                if not contains_typevar(pt):
                    exp = pt
            arg_types.append(self._synth_expr(arg, expected=exp))

        # Arity check
        if len(args) != len(fn_info.param_types):
            self._error(
                node,
                f"Function '{fn_info.name}' expects {len(fn_info.param_types)}"
                f" argument(s), got {len(args)}.",
                rationale="A call must supply exactly one argument per "
                          "declared parameter; the arity does not match the "
                          "function signature.",
                fix=f"Call '{fn_info.name}' with exactly "
                    f"{len(fn_info.param_types)} argument(s) matching its "
                    f"declared parameter types.",
                spec_ref='Chapter 5, Section 5.2 "Function Declaration Syntax"',
                error_code="E201",
            )
            return fn_info.return_type

        # Generic inference
        param_types = fn_info.param_types
        return_type = fn_info.return_type
        type_arg_conflict = False
        # #1769: the callee's row as this call instantiates it.  A generic's
        # row can name its type parameters (`effects(<State<T>>)`), and the
        # call is held to the row at the type arguments it fixes, as its
        # parameters and its return are.
        call_effect = fn_info.effect
        if fn_info.forall_vars:
            conflicts: set[str] = set()
            # #1541/#1565: an argument's literals take their type from the
            # call's other arguments, then from the type the result is
            # expected at, and only then from their own values.
            mapping, soft_mapping = self._infer_type_args_in_context(
                fn_info.forall_vars, fn_info.param_types, arg_types, args,
                result_type=fn_info.return_type, expected=expected,
                conflicts=conflicts)
            self._record_instantiation(node, fn_info, mapping)
            if mapping:
                call_effect = substitute_effect(fn_info.effect, dict(mapping))
            # A variable of the callee's own that no argument fixed leaves
            # the call as a hole, never under the callee's name, which an
            # enclosing generic can share and an enclosing call would then
            # take for the caller's variable (PR #1791 review).  Substituted
            # with the mapping at once, so a type the mapping gives that
            # names the caller's own variable is never mistaken for it.
            open_holes: dict[str, Type] = {
                tv: self._fresh_typevar(tv) for tv in fn_info.forall_vars
                if tv not in mapping and BUILTIN_TYPEVAR_MARKER not in tv}
            self._record_literal_soft_result(
                node, substitute(fn_info.return_type,
                                 {**soft_mapping, **open_holes}))
            if conflicts:
                # #898: two arguments pinned the same type parameter to
                # different, irreconcilable types (`eq2(MkOk("x"), MkOk(5))`
                # fixes `A` to both `String` and `Int`).  Report the conflict
                # directly — a clear E205 — rather than the misleading
                # "expected Res<String, ...>, got Res<Int, ...>" E202 the
                # partial merge would otherwise emit for one arm.
                type_arg_conflict = True
                # #970 (PR #982 review): ``conflicts`` holds raw callee
                # forall-var names; for a built-in generic these carry the
                # internal namespacing marker (``T#b``).  Strip it so the
                # user-facing message names the parameter as ``T``.
                conflict_names = ", ".join(
                    strip_builtin_typevar_marker(c) for c in sorted(conflicts)
                )
                self._error(
                    node,
                    f"Cannot infer a consistent type for the type "
                    f"parameter(s) {conflict_names} of "
                    f"'{fn_info.name}': different arguments require "
                    f"incompatible types.",
                    rationale="A generic call binds each type parameter to one "
                              "type; when several arguments determine the same "
                              "parameter, they must agree (a sparse "
                              "multi-parameter ADT built from different "
                              "constructors must still name one consistent "
                              "instantiation).",
                    fix="Make the arguments agree on the conflicting type "
                        "parameter, or annotate the intended instantiation "
                        "with a typed slot binding.",
                    spec_ref='Chapter 5, Section 5.2 "Function Declaration Syntax"',
                    error_code="E205",
                )
            # #900: reject instantiating a generic type parameter at the
            # zero-size `Unit` type *when the generic's body reads it*.  Unit
            # is 0 bytes with no WASM representation (spec §11.2.2 / §11.3.1:
            # Unit-returning fns have no result type, and `UnitLit` compiles to
            # nothing), so a monomorphized `forall<T>` body's `@T.n` slot READ
            # lowers to a `local.get` with no local — the dangling-slot codegen
            # invariant (E699).  This closes the inferred (arg-pinned) case at
            # check time rather than letting it crash in codegen, per DESIGN.md
            # principle 1 (checkability over correctness).
            #
            # Narrowed to declarations that actually MATERIALIZE `@T` (a `@T.n`
            # SlotRef read — direct return, match scrutinee, or a `requires` /
            # `ensures` clause, all of which lower to a `local.get`; #939).  A
            # `@T` parameter never read — in the body OR a contract — erases
            # cleanly from the ABI, so `firstInt(@T, @Int){ @Int.0 }` and
            # `ignore(@T){ 0 }` run fine at `T = Unit` and must NOT be rejected
            # (`fn_info.forall_vars_read` is the per-declaration set of forall
            # vars read anywhere that lowers to WASM).
            #
            # Keyed to any type with NO WASM representation — bare `Unit` OR a
            # `Future` transparently wrapping one (`Future<Unit>`; #939 review),
            # via `erases_to_unit` (which mirrors codegen's zero-size erasure).
            # A boxed `Option<Unit>` (tag + pointer) and a `Future<Int>` (i32)
            # both erase to a real local, so both are valid, non-zero-size type
            # arguments.  A genuine built-in generic
            # (`async`, `await`, collection/prelude combinators) has hand-written
            # codegen and an EMPTY `forall_vars_read`, so it never contributes a
            # unit var (`async(IO.print(...))`, a valid `Future<Unit>`, is not an
            # over-reject) — while a USER override of a prelude name that DOES read
            # `@T` (`forall<T> option_map`) is correctly caught, which the old
            # name-based exclusion wrongly skipped.  Skipped when a type-argument
            # conflict already reported E205 (the merged mapping is arbitrary
            # there — mirrors the E202 per-argument loop skip).
            unit_vars = (
                sorted(
                    tv for tv in fn_info.forall_vars
                    if tv in fn_info.forall_vars_read
                    and (b := mapping.get(tv)) is not None
                    and erases_to_unit(b)
                )
                if not type_arg_conflict
                else []
            )
            if unit_vars:
                joined = ", ".join(unit_vars)
                self._error(
                    node,
                    f"Cannot instantiate the type parameter(s) {joined} of "
                    f"'{fn_info.name}' at the zero-size type Unit.",
                    rationale="Unit is a zero-size type with no runtime "
                              "representation (a Unit value occupies 0 bytes "
                              "and compiles to no WASM value), so a generic "
                              "function specialised at Unit has a parameter "
                              "slot that refers to no runtime local — the "
                              "monomorphized function cannot be generated.",
                    fix="Do not pass a Unit-typed value where a generic "
                        "parameter is inferred. If you need to thread a unit "
                        "result through, wrap it in a boxed type (e.g. "
                        "Option<Unit>) or restructure so the generic is "
                        "instantiated at a type with a runtime representation.",
                    spec_ref='Chapter 11, Section 11.2.2 "Unit as Void"',
                    error_code="E206",
                )
                # Return the *substituted* result type so the enclosing
                # context (e.g. `let @Unit = idt(...)`) sees the concrete
                # `Unit` rather than a leaked `@T`, avoiding a misleading
                # cascade error on top of the actionable E206.
                return substitute(return_type, mapping)
            if not mapping and open_holes:
                return_type = substitute(return_type, open_holes)
            if mapping:
                param_types = tuple(
                    substitute(p, mapping) for p in param_types)
                return_type = substitute(return_type,
                                         {**mapping, **open_holes})
                # #747: the initial synth used expected=None for generic
                # calls, and an @Int argument flowing into a formal fixed
                # to @Nat by inference (`pick(@Nat.0, @Int.0)` with
                # `pick<T>(@T, @T)`) skips the re-synth at the subtype
                # check (Int <: Nat holds).  Record the instantiated
                # formal as each argument's target now, so the verifier's
                # @Nat narrowing walker can obligate it.
                if self.expr_target_types is not None:
                    for c_arg, c_pt in zip(args, param_types):
                        key = ast.span_key(c_arg)
                        if key is None or contains_typevar(c_pt):
                            continue
                        self.expr_target_types[key] = c_pt
                if self.node_target_types is not None:
                    for c_arg, c_pt in zip(args, param_types):
                        if (c_arg.node_id is not None
                                and not contains_typevar(c_pt)):
                            self.node_target_types[c_arg.node_id] = c_pt

        # Check each argument.  When a type-argument conflict was already
        # reported (#898), skip the per-argument subtype check: the merged
        # parameter type is one arbitrary arm of the conflict, so re-checking
        # would pile a misleading E202 on top of the clear E205.
        for i, (arg_ty, param_ty) in enumerate(zip(arg_types, param_types)):
            if type_arg_conflict:
                break
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            # Re-synth if arg still has unresolved TypeVars (bidirectional)
            if contains_typevar(arg_ty) and not contains_typevar(param_ty):
                arg_ty = self._synth_expr(args[i], expected=param_ty)
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                arg_types[i] = arg_ty
            # Re-synth with expected type when subtype check would fail —
            # enables bidirectional coercion (e.g. IntLit → Byte).
            if (not is_subtype(arg_ty, param_ty)
                    and not contains_typevar(param_ty)):
                re = self._synth_expr(args[i], expected=param_ty)
                if re is not None and not isinstance(re, UnknownType):
                    if is_subtype(re, param_ty):
                        arg_ty = re
                        arg_types[i] = re
            # #1541: an argument whose literals the instantiation typed
            # differently from their own values is checked AGAINST that
            # instantiation, so each literal meets the type it now has —
            # a negative one in a `Nat` position is the narrowing it is
            # (E503), and a nested generic call or constructor takes the
            # instantiation as its own context.
            elif (fn_info.forall_vars
                    and not contains_typevar(param_ty)
                    and not types_equal(arg_ty, param_ty)
                    and contains_literal_hole(
                        self._literal_soft_type(args[i], arg_ty)
                        or arg_ty)):
                re = self._synth_expr(args[i], expected=param_ty)
                if (re is not None and not isinstance(re, UnknownType)
                        and is_subtype(re, param_ty)):
                    arg_ty = re
                    arg_types[i] = re
            # #1010: a constructor argument against a PARTIALLY-generic
            # param (`MkPair(0 - 5, None)` as `@Pair<Nat, T>`) was never
            # re-synthesized — every re-synth above is gated on the WHOLE
            # param being typevar-free — so the concrete `Nat` component's
            # narrowing target went unrecorded and the E503 obligation was
            # silently lost (the fully-concrete analogue obligates).
            # Re-synth ctor expressions against the instantiated param:
            # the #971 fill adopts component-wise, typevar components stay
            # unconstrained, and the ctor check records each field's
            # target exactly as on the concrete path.
            if (contains_typevar(param_ty)
                    and isinstance(param_ty, AdtType)
                    and isinstance(args[i], (
                        ast.ConstructorCall, ast.NullaryConstructor))):
                re = self._synth_expr(args[i], expected=param_ty)
                if re is not None and not isinstance(re, UnknownType):
                    arg_ty = re
                    arg_types[i] = re
            # #993: a type variable left unresolved on either side is a
            # wildcard here (`_fits`), so a call satisfiable at SOME
            # instantiation is not a false E202.
            if not self._fits(arg_ty, param_ty):
                # #1684: a type variable the argument's type leaves open,
                # taking two types or standing in a closure compiled before
                # it had one, is named with its positions.
                why = self._open_variable_refusal(arg_ty, param_ty, args[i])
                if why is not None:
                    self._error(
                        args[i],
                        f"Argument {i} of '{fn_info.name}' has type "
                        f"{pretty_type(_named_open(arg_ty))}, expected "
                        f"{pretty_type(_holes_unknown(param_ty))}: {why[0]}",
                        rationale=why[1],
                        fix=why[2],
                        spec_ref='Chapter 5, Section 5.9 "Generic Functions"',
                        error_code="E202",
                    )
                    continue
                self._error(
                    args[i],
                    f"Argument {i} of '{fn_info.name}' has type "
                    f"{pretty_inferred_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    rationale="Each argument's type must be a subtype of the "
                              "corresponding declared parameter type.",
                    fix=(self._cross_owner_fix(fn_info.name, arg_ty, param_ty)
                         or f"Pass a value of type {pretty_type(param_ty)} "
                            f"for argument {i}, or convert the current value "
                            f"(e.g. int_to_nat(...), int_to_float(...)) to "
                            f"{pretty_type(param_ty)}."),
                    spec_ref='Chapter 5, Section 5.2 "Function Declaration Syntax"',
                    error_code="E202",
                )

        # #1708: in a contract predicate, a callee whose row names an effect
        # no handler written inside the predicate handles is refused, and
        # the call is neither counted nor held to the row in force.
        impure = (self._impure_in_predicate(call_effect.effects)
                  if isinstance(call_effect, ConcreteEffectRow) else None)
        if impure is not None:
            self._refuse_impure_predicate(
                node, f"Call to '{fn_info.name}'",
                f"the call to '{fn_info.name}'", impure)

        # Track effects
        if not isinstance(call_effect, PureEffectRow) and impure is None:
            if isinstance(call_effect, ConcreteEffectRow):
                for ei in call_effect.effects:
                    self._effect_ops_used.add(ei.name)

        # #841: concurrency-eligibility warning for async().  The runtime
        # only makes async(e) concurrent when e's effect row stays within
        # the commutative whitelist; anything else evaluates eagerly, and
        # the checker says so rather than letting the program imply
        # concurrency it does not get.
        if fn_info.name == "async" and len(args) == 1:
            self._warn_non_commutative_async(args[0], node)

        # Call-site effect check: callee's effects must be permitted
        # by the caller's context (Spec §7.8 subeffecting).
        if self.env.current_effect_row is not None and impure is None:
            if not is_effect_subtype(call_effect,
                                     self.env.current_effect_row):
                self._error(
                    node,
                    f"Function '{fn_info.name}' requires "
                    f"{pretty_effect(call_effect)} but call site only "
                    f"allows {pretty_effect(self.env.current_effect_row)}.",
                    rationale="A function can only be called from a context "
                              "that permits all of its declared effects "
                              "(subeffecting).",
                    fix="Either add the missing effects to the calling "
                        "function's effects clause, or handle the effects "
                        "with a handler.",
                    spec_ref='Chapter 7, Section 7.8 "Effect Subtyping"',
                    error_code="E125",
                )

        if fn_info.forall_vars:
            return_type = self._mint_free_builtin_vars(
                fn_info, mapping, return_type)
        return return_type

    def _mint_free_builtin_vars(self, fn_info: FunctionInfo,
                                bound: typing.Mapping[str, Type],
                                result: Type) -> Type:
        """*result*, with each of the built-in *fn_info*'s type variables
        that no parameter type mentions, and so no argument could bind,
        marked free (`FREE_BUILTIN_TYPEVAR_MARKER`, numbered for the call),
        as a constructor mints a type parameter no field holds (#1668).

        `map_new()` has no parameters: its `K` and `V` are open positions
        the call leaves, which a join fills (`[map_new(), map_insert(...)]`
        is one map type).  A variable a parameter mentions that the
        arguments left unbound (*bound* lacks it) stays the built-in's: it
        stands for a type a failed substitution lost (`array_map`'s `B`
        beside a refinement of a function type, which its function-typed
        parameter does not unify through), and the join leaves it alone.
        Read off the signature, so no built-in is named."""
        mentioned: Counter[str] = Counter()
        for param in fn_info.param_types:
            _type_var_occurrences(param, mentioned)
        free: dict[str, Type] = {}
        for tv in fn_info.forall_vars or ():
            if (BUILTIN_TYPEVAR_MARKER in tv and tv not in bound
                    and not mentioned[tv]):
                self._fresh_id += 1
                free[tv] = TypeVar(
                    f"{tv}{FREE_BUILTIN_TYPEVAR_MARKER}{self._fresh_id}")
        return substitute(result, free) if free else result

    def _check_apply_fn(self, args: tuple[ast.Expr, ...],
                        node: ast.Node) -> Type | None:
        """Check the apply_fn special form: apply_fn(f, a0, ..., an) (#854).

        Types the call structurally against ``f``'s ``FunctionType`` —
        mirroring :meth:`_check_fn_call_with_info` for a callee whose
        "signature" is the applied value's fn type: arity (E201),
        argument subtyping with bidirectional re-synthesis (E202), and
        the fn type's effect row joining the caller's used effects and
        being checked against the caller's declared row (E122 via
        ``_effect_ops_used`` / E125 here), exactly as a named call with
        that row would.  The call's result is ``f``'s return type.

        A bare-``TypeVar`` first argument (a ``forall``-var-typed value
        with no structural fn type) is unpicked here — the remaining
        arguments are still synthesised for errors within them and the
        call types as ``UnknownType`` (permissive, like other
        unresolvable-generic sites).
        """
        if not args:
            self._error(
                node,
                "apply_fn expects a function value as its first "
                "argument, got no arguments.",
                rationale="apply_fn applies a stored function value: its "
                          "first argument is the function to apply and the "
                          "remaining arguments are passed to it, so a bare "
                          "apply_fn() has nothing to apply.",
                fix="Pass a function value first, then its arguments, "
                    "e.g. apply_fn(@IntToInt.0, 5).",
                spec_ref='Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"',
                error_code="E201",
            )
            return UnknownType()

        fn_arg, rest = args[0], args[1:]
        fn_ty_raw = self._synth_expr(fn_arg)

        # Error recovery / unresolvable-generic first argument: synth
        # the remaining arguments (to surface errors inside them) and
        # give up on structural checking.
        fn_ty = base_type(fn_ty_raw) if fn_ty_raw is not None else None
        if fn_ty is None or isinstance(fn_ty, (UnknownType, TypeVar)):
            for arg in rest:
                self._synth_expr(arg)
            return UnknownType()

        if not isinstance(fn_ty, FunctionType):
            self._error(
                fn_arg,
                f"Argument 0 of 'apply_fn' has type "
                f"{pretty_inferred_type(fn_ty_raw or fn_ty)}, expected a function "
                f"value (a fn(...) type).",
                rationale="apply_fn invokes a stored function value via "
                          "call_indirect; a non-function first argument "
                          "has no signature to call.",
                fix="Pass a value of a fn type — a parameter or let "
                    "binding declared with a fn(...) effects(...) type, "
                    "e.g. apply_fn(@IntToInt.0, 5).",
                spec_ref='Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"',
                error_code="E202",
            )
            for arg in rest:
                self._synth_expr(arg)
            return UnknownType()

        # Synth applied args against the fn type's formals — bidirectional
        # where the formal is concrete, mirroring plain non-generic calls
        # (this also records the #747 narrowing target for each argument).
        arg_types: list[Type | None] = []
        for i, arg in enumerate(rest):
            exp: Type | None = None
            if i < len(fn_ty.params):
                pt = fn_ty.params[i]
                if not contains_typevar(pt):
                    exp = pt
            arg_types.append(self._synth_expr(arg, expected=exp))

        # Arity: every argument after the function value maps to one
        # parameter of the applied fn type.
        if len(rest) != len(fn_ty.params):
            self._error(
                node,
                f"apply_fn: function value of type {pretty_type(fn_ty)} "
                f"expects {len(fn_ty.params)} argument(s), "
                f"got {len(rest)}.",
                rationale="apply_fn passes every argument after the "
                          "function value to it; the count must match the "
                          "applied function type's parameters.",
                fix=f"Call apply_fn with the function value plus exactly "
                    f"{len(fn_ty.params)} argument(s) matching "
                    f"{pretty_type(fn_ty)}.",
                spec_ref='Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"',
                error_code="E201",
            )
            return fn_ty.return_type

        # Check each applied argument (same discipline as named calls:
        # skip unresolved, re-synth for bidirectional coercion).
        for i, (arg_ty, param_ty) in enumerate(zip(arg_types,
                                                   fn_ty.params)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            # Re-synth if arg still has unresolved TypeVars (bidirectional)
            if contains_typevar(arg_ty) and not contains_typevar(param_ty):
                arg_ty = self._synth_expr(rest[i], expected=param_ty)
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                arg_types[i] = arg_ty
            # Re-synth with expected type when subtype check would fail —
            # enables bidirectional coercion (e.g. IntLit → Byte).
            if (not is_subtype(arg_ty, param_ty)
                    and not contains_typevar(param_ty)):
                re = self._synth_expr(rest[i], expected=param_ty)
                if re is not None and not isinstance(re, UnknownType):
                    if is_subtype(re, param_ty):
                        arg_ty = re
                        arg_types[i] = re
            if not is_subtype(arg_ty, param_ty):
                self._error(
                    rest[i],
                    f"Argument {i + 1} of 'apply_fn' has type "
                    f"{pretty_inferred_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    rationale="Each argument after the function value must "
                              "be a subtype of the corresponding parameter "
                              "of the applied function type.",
                    fix=f"Pass a value of type {pretty_type(param_ty)}, "
                        f"or convert the current value (e.g. "
                        f"int_to_nat(...), int_to_float(...)) to "
                        f"{pretty_type(param_ty)}.",
                    spec_ref='Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"',
                    error_code="E202",
                )

        # #1708: in a contract predicate, a value whose type's row names an
        # effect no handler written inside the predicate handles is refused
        # here, unless it is a closure literal already refused where it is
        # written (`_check_anon_fn`); either way the application is neither
        # counted nor held to the row in force.
        impure = (self._impure_in_predicate(fn_ty.effect.effects)
                  if isinstance(fn_ty.effect, ConcreteEffectRow) else None)
        if impure is not None:
            if id(fn_arg) not in self._impure_literals:
                self._refuse_impure_predicate(
                    node, "apply_fn of a function value", "the apply_fn",
                    impure)
            return fn_ty.return_type

        # The applied row joins the caller's used effects and must be
        # permitted by the caller's declared row — exactly as a named
        # call with this row (E122 via _effect_ops_used; E125 here).
        if isinstance(fn_ty.effect, ConcreteEffectRow):
            for ei in fn_ty.effect.effects:
                self._effect_ops_used.add(ei.name)
        if self.env.current_effect_row is not None:
            if not is_effect_subtype(fn_ty.effect,
                                     self.env.current_effect_row):
                self._error(
                    node,
                    f"apply_fn: applied function value requires "
                    f"{pretty_effect(fn_ty.effect)} but call site only "
                    f"allows "
                    f"{pretty_effect(self.env.current_effect_row)}.",
                    rationale="Applying a function value performs its "
                              "type's declared effects; the call site must "
                              "permit all of them (subeffecting), exactly "
                              "as for a named function call.",
                    fix="Add the missing effects to the calling "
                        "function's effects clause, or apply a function "
                        "value whose type is pure.",
                    spec_ref='Chapter 7, Section 7.8 "Effect Subtyping"',
                    error_code="E125",
                )

        return fn_ty.return_type

    # Effects whose operations are value-confluent — reordering their
    # completions cannot change any observable output — so async() may run
    # them concurrently (#841).  ``Async`` itself is a marker effect with
    # no operations, so it cannot order anything either.
    _ASYNC_COMMUTATIVE: frozenset[str] = frozenset({"Http", "Async"})

    def _warn_non_commutative_async(self, arg: ast.Expr,
                                    node: ast.Node) -> None:
        """Warn (W002) when async()'s argument performs effects outside
        the commutative whitelist — such futures evaluate eagerly."""
        found: set[str] = set()
        self._collect_expr_effects(arg, found)
        outside = sorted(found - self._ASYNC_COMMUTATIVE)
        if outside:
            self._error(
                node,
                f"async argument performs {', '.join(outside)} effects, "
                f"which are outside the commutative set "
                f"({', '.join(sorted(self._ASYNC_COMMUTATIVE - {'Async'}))}); "
                f"it evaluates eagerly (sequentially) at the async() site.",
                rationale="Concurrent evaluation is only observably "
                          "equivalent to eager evaluation when the "
                          "argument's effects commute; for any other "
                          "effect row the implementation preserves program "
                          "order by evaluating eagerly, and warns so the "
                          "program does not imply concurrency it does not "
                          "get.",
                fix="Restrict the async argument to commutative effects "
                    "(e.g. a direct Http.get/Http.post call), or drop the "
                    "async() wrapper if eager evaluation is intended.",
                spec_ref='Chapter 9, Section 9.5.4 "Async"',
                severity="warning",
                error_code="W002",
            )

    def _collect_expr_effects(self, node: ast.Node,
                              acc: set[str]) -> None:
        """Conservatively collect the effect names an expression may
        perform: effect-op calls contribute their parent effect, function
        calls contribute the callee's declared row, and anything that
        cannot be resolved contributes an opaque marker (never silently
        commutative)."""
        import dataclasses as _dc

        if isinstance(node, ast.QualifiedCall):
            if self.env.lookup_effect(node.qualifier) is not None:
                acc.add(node.qualifier)
            else:
                # Cross-module function call — its row is not resolvable
                # from this mixin; conservatively non-commutative.
                acc.add(f"<{node.qualifier}.{node.name}>")
        elif isinstance(node, ast.FnCall):
            # #991: resolve lexically like the call checker above, so a
            # same-named helper in a sibling tree can't contribute the
            # WRONG effect row to the commutativity analysis.
            #
            # #1284: and DECLARATIONS FIRST, which is the rest of what "like
            # the call checker above" means — this walk asked
            # `lookup_effect_op` first, so a user function named after a
            # built-in operation contributed the OPERATION's parent effect
            # instead of its own declared row.  Wrong in both directions and
            # both measured: a PURE `fn get` in a program containing no
            # State at all drew `[W002] async argument performs State
            # effects`, and a `fn get` performing IO under a row naming
            # `Http` first drew NO warning, because `Http` is inside the
            # commutative whitelist and the operation is what the walk
            # thought it had found.  Same predicate as the resolution at the
            # top of this file, so the analysis reasons about the row the
            # checker actually bound.
            fn_info = self._bound_function(node)
            op_info = (
                self.env.lookup_effect_op(node.name)
                if fn_info is None else None
            )
            if op_info is not None:
                acc.add(op_info.parent_effect)
            elif fn_info is None:
                acc.add(f"<{node.name}>")
            elif isinstance(fn_info.effect, ConcreteEffectRow):
                for ei in fn_info.effect.effects:
                    acc.add(ei.name)
            elif not isinstance(fn_info.effect, PureEffectRow):
                acc.add(f"<{node.name}>")
        for field in _dc.fields(node):
            value = getattr(node, field.name)
            if isinstance(value, ast.Node):
                self._collect_expr_effects(value, acc)
            elif isinstance(value, tuple):
                for item in value:
                    if isinstance(item, ast.Node):
                        self._collect_expr_effects(item, acc)

    def _check_op_call(self, op_info: OpInfo,
                       args: tuple[ast.Expr, ...],
                       node: ast.Node, *,
                       counted: bool = True) -> Type | None:
        """Check a call to an effect operation.

        The call is judged once (#1702): refused by `vera.lowering` rule 7
        (E340) when it is a `State` or `Exn` operation in a closure's body
        outside a handler written there, otherwise held to the row in force
        (E125).  Its effect is counted as performed, for the purity check
        (E122) and for every closure around the call, only where neither
        judgement refused it and the caller did not (*counted* false)."""
        # Resolve type params from the current effect context first, so
        # each argument is synthesised against its *instantiated* formal.
        # That records the @Nat target for an ``E<Nat>.op(@Int.0)``
        # narrowing in the #747 side-table (uniform with plain calls and
        # constructor fields) rather than leaving it unchecked.
        mapping = self._effect_type_mapping(op_info.parent_effect)
        param_types = tuple(substitute(p, mapping) for p in op_info.param_types)
        return_type = substitute(op_info.return_type, mapping)
        lowers = self._check_closure_operation_lowerable(
            op_info, node, mapping)

        arg_types: list[Type | None] = []
        for i, arg in enumerate(args):
            exp = param_types[i] if i < len(param_types) else None
            arg_types.append(self._synth_expr(arg, expected=exp))

        if len(args) != len(param_types):
            self._error(
                node,
                f"Effect operation '{op_info.name}' expects "
                f"{len(param_types)} argument(s), got {len(args)}.",
                rationale="An effect operation is called like a function and "
                          "must receive exactly the number of arguments "
                          "declared in its 'op' signature.",
                fix=f"Call '{op_info.name}' with exactly {len(param_types)} "
                    f"argument(s) matching the 'op' declaration in its "
                    f"effect.",
                spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
                error_code="E203",
            )
            # The row judgement is not reached, so it refuses nothing: the
            # call is counted unless rule 7 refused it, as at the base.
            if counted and lowers:
                self._effect_ops_used.add(op_info.parent_effect)
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
                    f"{pretty_inferred_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    rationale="Each argument to an effect operation must be a "
                              "subtype of the parameter type declared in its "
                              "'op' signature.",
                    fix=f"Pass a value of type {pretty_type(param_ty)} for "
                        f"argument {i} of '{op_info.name}', or convert the "
                        f"current value to {pretty_type(param_ty)}.",
                    spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
                    error_code="E204",
                )

        # #309: for a DB SQL op (``DB.query`` / ``DB.execute``), the SQL (first)
        # argument must be literal-provenance (E207), use only anonymous ``?``
        # placeholders (E209), and match a statically-sized params array (E208).
        # ``is_db_sql_op`` matches on ``parent_effect == "DB"`` + the op name —
        # the SAME axis codegen routes to the host database on — NOT built-in
        # OpInfo identity.
        #
        # Historically that distinction decided WHERE a user ``effect DB``
        # shadow was caught: one declaring ``query`` was gated here, while one
        # declaring only some other op failed op resolution and was gated by
        # the spelling fallback in ``_check_qualified_call`` (Cortex #1147
        # Finding 1).  Since #1149 no shadow enters the registry at all (E152),
        # so every ``DB.query`` / ``DB.execute`` resolves against the built-in
        # and arrives here; the fallback is retained only as defence in depth
        # should the registry ever fail to resolve one.  The routing-axis key
        # is likewise kept rather than narrowed to the built-in ``OpInfo``: the
        # gate must cover exactly what codegen emits on its own terms, without
        # depending on E152 to be complete.
        #
        # The gate runs on the codegen routing axis ALONE — it does NOT also
        # require the arg's static type to be ``String``.  Codegen marshals the
        # first arg to the sqlite host by qualifier name whatever its type, so an
        # ``is_subtype(arg, String)`` guard was a soundness hole (#1147
        # adversarial workflow): a runtime SQL string laundered through a generic
        # ``@T`` slot has arg type ``TypeVar`` (SEVERE — attacker SQL executed),
        # and a user ``effect DB`` shadow with a non-``String`` param (``Int`` /
        # ``Array``) type-checks clean yet still reaches the host (a check-clean
        # program emitting invalid WASM).  The provenance walker is
        # conservative-reject, so it correctly rejects a slot / non-literal arg of
        # ANY type.  The one thing we skip is pure E204 cascade: a call whose
        # DECLARED first param is exactly ``String`` already rejected a concrete
        # non-``String`` arg with E204, so a second E207 there is noise.  A
        # ``TypeVar`` param (generic ``DB<T>``) or a user non-``String`` param
        # does NOT fire E204, so those still gate.  (Both shadow shapes in that
        # paragraph are the pre-#1149 world: the block is now E152, so a
        # non-``String`` SQL argument is a plain E204 against the built-in's
        # ``String`` parameter.)
        if (
            self.env.is_db_sql_op(op_info) and args
            and arg_types and arg_types[0] is not None
            and not isinstance(arg_types[0], UnknownType)
        ):
            arg0 = arg_types[0]
            param0 = param_types[0] if param_types else None
            param_is_string = (
                param0 is not None
                and is_subtype(param0, STRING)
                and is_subtype(STRING, param0)
            )
            e204_cascade = param_is_string and not is_subtype(arg0, STRING)
            if not e204_cascade:
                self._check_sql_provenance(op_info.name, args, node)

        refused = (not lowers
                   or self._refuse_operation_in_predicate(op_info, node)
                   or self._refuse_operation_outside_row(
                       op_info, arg_types, node))
        if counted and not refused:
            self._effect_ops_used.add(op_info.parent_effect)
        if refused and not mapping and contains_typevar(op_info.return_type):
            # A refused `State.get`: no row entry and no handler gives the
            # instance its result is typed by, so the result is not the
            # effect's own type parameter, and a use of it is no second
            # error.  An operation whose signature fixes its result keeps it.
            return UnknownType()
        return return_type

    def _check_closure_operation_lowerable(
        self, op_info: OpInfo, node: ast.Node, mapping: dict[str, Type],
    ) -> bool:
        """E340 (`vera.lowering` rule 7, #1702): a `State` or `Exn`
        operation in a closure's body, outside a handler for its effect
        written inside the closure.  *mapping* is the operation's type
        arguments, which the handler the fix writes is given.  Returns
        whether it lowers."""
        if not self._closure_handler_marks:
            return True
        effect = op_info.parent_effect
        inside = self._handled_effects[self._closure_handler_marks[-1]:]
        if closure_operation_lowerable(
                effect, handled_in_closure=effect in inside):
            return True
        written = (f"{node.qualifier}.{node.name}"
                   if isinstance(node, ast.QualifiedCall) else op_info.name)
        eff_info = self.env.lookup_effect(effect)
        param = (eff_info.type_params or ("T",))[0] if eff_info else "T"
        arg = pretty_type(mapping.get(param, TypeVar(param)))
        handler = (
            f"handle[State<{arg}>](@{arg} = <its initial value>) {{ "
            f"get(@Unit) -> {{ resume(@{arg}.0) }}, put(@{arg}) -> "
            f"{{ resume(()) }} }} in {{ ... }}"
            if effect == "State" else
            f"handle[Exn<{arg}>] {{ throw(@{arg}) -> {{ <the closure's "
            f"result when it throws> }} }} in {{ ... }}")
        article = "an" if effect[:1].upper() in ("A", "E", "I", "O", "U") else "a"
        self._error(
            node,
            f"Code generation cannot lower '{written}' in the body of an "
            f"anonymous function: {article} {effect} operation in a closure "
            f"is lowered only under a handler for {effect} written inside "
            f"the closure.",
            rationale=(
                f"Code generation lifts a closure into a function of its own.  "
                f"{article.capitalize()} {effect} operation needs the "
                + ("cell it reads and writes" if effect == "State"
                   else "tag it throws to")
                + ", which a function's row or a handler in its body "
                "registers, and the lifted closure has none from its row, so "
                "a bare operation there has no route and a qualified one "
                "calls an import the module does not declare.  A handler "
                "written inside the closure registers it in the lifted "
                "function.  A handler around the closure does not: the "
                "closure is compiled apart from it, and can be applied "
                "outside it."
            ),
            fix=(
                f"Perform '{written}' in the enclosing function's body, with "
                f"{effect} in that function's effects clause or under a "
                f"handler there, and pass the closure what it needs; or write "
                f"the handler inside the closure, around the operation: "
                f"{handler}."
            ),
            spec_ref='Chapter 5, Section 5.7 "Anonymous Functions (Closures)"',
            error_code="E340",
        )
        return False

    def _refuse_operation_in_predicate(
        self, op_info: OpInfo, node: ast.Node,
    ) -> bool:
        """E187 (#1708): an operation of a built-in effect, performed in a
        contract predicate where no handler written inside the predicate
        handles the effect, whatever the row in force names.  A
        user-declared effect's operation is E340's.  Returns whether it
        refused."""
        effect = op_info.parent_effect
        if not effect_operation_lowerable(effect):
            return False
        impure = self._impure_in_predicate((effect,))
        if impure is None:
            return False
        written = (f"{node.qualifier}.{node.name}"
                   if isinstance(node, ast.QualifiedCall) else op_info.name)
        self._refuse_impure_predicate(
            node, f"Effect operation '{written}'", f"'{written}'", impure)
        return True

    def _refuse_operation_outside_row(
        self, op_info: OpInfo, arg_types: list[Type | None], node: ast.Node,
    ) -> bool:
        """E125 (#1702): an operation of a built-in effect, performed where
        the row in force does not name the effect.

        The judgement a call to a function is held to (§7.8, E125 above),
        made for an operation, whose row is its effect: the row in force
        must name the effect, by name, at any instance (`<State<Int>>`
        permits `put`; which instance types the call is the operation's
        typing).  A row variable names no effect, so an open row permits
        what its entries name and nothing else.  The row in force is the
        declaration's, a handler's body adds the handled effect to it
        (`_check_handle`), and a closure's body has the closure's own
        (`_check_anon_fn`).  Under `effects(pure)` the declaration that
        performs the operation is refused instead (E122, the purity check),
        so the call draws one code; where no row is in force, a refinement
        predicate checked before its function's row is, it is not judged.
        A user-declared effect's operation is E340's
        (`_check_operation_lowerable`).  Returns whether it refused."""
        effect = op_info.parent_effect
        row = self.env.current_effect_row
        if (not isinstance(row, ConcreteEffectRow)
                or not effect_operation_lowerable(effect)
                or any(e.name == effect for e in row.effects)):
            return False
        written = (f"{node.qualifier}.{node.name}"
                   if isinstance(node, ast.QualifiedCall) else op_info.name)
        inst = self._operation_instance(op_info, arg_types)
        shown = canonical_type_name(inst.name, inst.type_args or None)
        target, declared = self._row_owner or (
            "the enclosing function's effects clause", row)
        entries = (declared.effects if isinstance(declared, ConcreteEffectRow)
                   else frozenset())
        row_var = (declared.row_var
                   if isinstance(declared, ConcreteEffectRow) else None)
        wanted = pretty_effect(ConcreteEffectRow(entries | {inst}, row_var))
        handler = (f"  Or perform it inside a handle[{shown}] block, whose "
                   f"body permits it."
                   if handler_lowerable(effect) else "")
        self._error(
            node,
            f"Effect operation '{written}' requires "
            f"{pretty_effect(ConcreteEffectRow(frozenset({inst})))} but call "
            f"site only allows {pretty_effect(row)}.",
            rationale=(
                "An effect operation performs its effect where it is called, "
                "so the effect row in force there must name the effect, as a "
                "call to a function is held to its declared effects "
                "(subeffecting).  The row in force is the declaring "
                "function's, a closure's own inside the closure's body, and "
                "the row around a handler with the handled effect added "
                "inside the handler's body.  A row variable names no effect, "
                "so it permits no operation the row does not name."
            ),
            fix=f"Add {shown} to {target}: {wanted}.{handler}",
            spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
            error_code="E125",
        )
        return True

    def _operation_instance(
        self, op_info: OpInfo, arg_types: list[Type | None],
    ) -> EffectInstance:
        """The instance of *op_info*'s effect a fix names: the effect, each
        type parameter the type of an argument that fixes it (`put(@Int.0)`
        is `State<Int>`), and the parameter itself where none does (a
        `get`, whose instance only its result would say)."""
        eff_info = self.env.lookup_effect(op_info.parent_effect)
        params = tuple(eff_info.type_params or ()) if eff_info else ()
        fixed: dict[str, Type] = {}
        for formal, actual in zip(op_info.param_types, arg_types):
            if (isinstance(formal, TypeVar) and formal.name in params
                    and actual is not None
                    and not isinstance(actual, UnknownType)
                    and not contains_typevar(actual)):
                fixed.setdefault(formal.name, actual)
        return EffectInstance(
            op_info.parent_effect,
            tuple(fixed.get(p, TypeVar(p)) for p in params))

    def _check_sql_provenance(
        self, op_name: str, args: tuple[ast.Expr, ...], node: ast.Node,
    ) -> None:
        """#309 — reject a non-literal SQL string (E207); numbered/named
        placeholders Vera does not support (E209); and a placeholder/param
        arity mismatch when both are statically sized (E208).

        ``op_name`` is the operation spelling (``query`` / ``execute``) used only
        in diagnostics — a string, not an ``OpInfo``, so the unresolved-spelling
        path (``_check_qualified_call``, Cortex #1147 Finding 1) can gate a
        ``DB.<op>`` call that codegen routes to the host even though a user
        ``effect DB`` never declared the op."""
        if not args:
            return
        sql = resolve_literal_string(args[0], self.env, self._slot_ref_key)
        if sql is None:
            self._error(
                args[0],
                f"The SQL argument to '{op_name}' must be a string "
                "literal or a concatenation of literals, not a runtime-derived "
                "value.",
                rationale=(
                    "A SQL string assembled from a runtime value — a slot, a "
                    "function result, or a \\(expr) interpolation — is the SQL "
                    "injection vector.  Vera makes it a compile-time error: the "
                    "query text is fixed at compile time and all runtime data "
                    "flows through the ? placeholders and the params array."
                ),
                fix=(
                    "Put the runtime value in the params array and reference "
                    "it with a ? placeholder, e.g. "
                    'DB.query("SELECT ... WHERE x = ?", [Some(value)]).'
                ),
                spec_ref='Chapter 9, Section 9.5.7 "DB"',
                error_code="E207",
            )
            return

        # SQL is literal.  ``count_placeholders`` returns None when the SQL uses
        # a numbered (``?NNN``) or named (``:name`` / ``@name`` / ``$name``)
        # placeholder.  Vera's params argument is a POSITIONAL ``Array``, so only
        # anonymous ``?`` has a well-defined binding; the others fail against a
        # positional sequence at run time.  Reject them at compile time (E209)
        # for one canonical placeholder form, rather than defer to a runtime
        # error.
        want = count_placeholders(sql)
        if want is None:
            self._error(
                node,
                f"The SQL passed to '{op_name}' uses a numbered (?NNN) or named "
                "(:name / @name / $name) placeholder; Vera supports only "
                "anonymous '?' placeholders.",
                rationale=(
                    "Parameters bind positionally through the "
                    "Array<Option<String>> params argument, so only anonymous "
                    "'?' placeholders have a well-defined binding; numbered and "
                    "named forms fail against a positional sequence at run time."
                ),
                fix=(
                    "Use anonymous '?' placeholders in order, e.g. "
                    'DB.query("SELECT ... WHERE a = ? AND b = ?", '
                    "[Some(a), Some(b)])."
                ),
                spec_ref='Chapter 9, Section 9.5.7 "DB"',
                error_code="E209",
            )
            return

        # Anonymous ? only: arity-check against a statically-sized params array.
        # ``resolve_array_len`` follows a ``let`` chain (#1160), so a params
        # array written literally is checked whether it is inline at the call
        # site or bound to a slot first.  It returns None when the length is not
        # statically known, deferring the count to the sqlite3 host.
        got = (resolve_array_len(args[1], self.env, self._slot_ref_key)
               if len(args) >= 2 else None)
        if got is not None:
            if want != got:
                self._error(
                    node,
                    f"The SQL has {want} '?' placeholder(s) but "
                    f"{got} parameter(s) were supplied to '{op_name}'.",
                    rationale=(
                        "Each ? placeholder binds one positional parameter, so "
                        "the number of placeholders must equal the length of "
                        "the params array; a mismatch fails at run time."
                    ),
                    fix=(
                        f"Supply exactly {want} parameter(s) to match the "
                        f"{want} placeholder(s), or adjust the SQL's ? count."
                    ),
                    spec_ref='Chapter 9, Section 9.5.7 "DB"',
                    error_code="E208",
                )

    def _effect_type_mapping(self, effect_name: str) -> dict[str, Type]:
        """Get the type argument mapping for an effect — innermost enclosing
        HANDLER first (#1203 determinism: an op inside nested same-name
        handlers resolves against the governing handler's instantiation,
        §7.5.2), then the current effect row IN SOURCE ORDER.

        The row leg used to iterate the row's ``frozenset`` on the premise
        that a declared row cannot meaningfully carry two instantiations of
        one effect.  Spec §7.3.3 says otherwise — ``effects(<State<Int>,
        State<Bool>>)`` is two independent cells — and such a row made a bare
        ``get``'s type a function of PYTHONHASHSEED: the same source checked
        clean on some interpreter starts and failed E121 (`body has type Bool,
        expected Int`) on others.  It now walks `ordered_effect_row()`, the
        same ordered candidate list bare op-NAME resolution uses (#1215), so
        the first instantiation written in the row governs."""
        eff_info = self.env.lookup_effect(effect_name)
        if eff_info is None or not eff_info.type_params:
            return {}
        for inst in reversed(self._handled_effect_insts):
            if inst.name == effect_name and inst.type_args:
                return dict(zip(eff_info.type_params, inst.type_args))
        for ei in self.env.ordered_effect_row():
            if ei.name == effect_name and ei.type_args:
                return dict(zip(eff_info.type_params, ei.type_args))
        return {}

    # -----------------------------------------------------------------
    # Ability operations
    # -----------------------------------------------------------------

    def _check_ability_op_call(self, op_info: OpInfo,
                               args: tuple[ast.Expr, ...],
                               node: ast.Node) -> Type | None:
        """Check a call to an ability operation."""
        arg_types: list[Type | None] = []
        for arg in args:
            arg_types.append(self._synth_expr(arg))
        if not ability_lowerable(op_info.parent_effect):
            # `vera.lowering` rule 4 (#1499): a user ability's operation
            # has no body at any type.  Checked on, so the call's own
            # argument diagnostics are reported too.
            self._refuse_unlowerable_ability(
                node, op_info.parent_effect, op=op_info)

        # Build type mapping from ability params → concrete types
        mapping = self._ability_type_mapping(op_info, arg_types)
        param_types = tuple(
            substitute(p, mapping) for p in op_info.param_types)
        return_type = substitute(op_info.return_type, mapping)

        if len(args) != len(param_types):
            self._error(
                node,
                f"Ability operation '{op_info.name}' expects "
                f"{len(param_types)} argument(s), got {len(args)}.",
                rationale="An ability operation is called like a function and "
                          "must receive exactly the number of arguments "
                          "declared in its 'op' signature.",
                fix=f"Call '{op_info.name}' with exactly {len(param_types)} "
                    f"argument(s) matching the 'op' declaration in its "
                    f"ability.",
                spec_ref='Chapter 9, Section 9.8 "Abilities"',
                error_code="E240",
            )
            return return_type

        for i, (arg_ty, param_ty) in enumerate(
                zip(arg_types, param_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            if not is_subtype(arg_ty, param_ty):
                # #993: the args were synthesized with no expected type, so
                # a bare constructor argument (`eq(x, None)`) minted a fresh
                # ctor var that never met the parameter type.  Re-synth the
                # ctor argument against the resolved param so the #971
                # bidirectional fill can adopt it (works for concrete AND
                # rigid-forall-var parameter args).  Restricted to
                # constructor expressions — re-synthesizing an arbitrary
                # expression could re-emit its own diagnostics — and to a
                # fresh-FREE param: a param still carrying a `$` hole
                # (`eq(None, None)`) is not a resolved type to adopt, and
                # adopting it would let an unresolvable comparison through.
                if (contains_typevar(arg_ty)
                        and not contains_fresh_typevar(param_ty)
                        and isinstance(args[i], (
                            ast.ConstructorCall, ast.NullaryConstructor))):
                    resynth = self._synth_expr(args[i], expected=param_ty)
                    if (resynth is not None
                            and not isinstance(resynth, UnknownType)):
                        arg_ty = resynth
                        arg_types[i] = resynth
                        if is_subtype(arg_ty, param_ty):
                            continue
                self._error(
                    args[i],
                    f"Argument {i} of '{op_info.name}' has type "
                    f"{pretty_inferred_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    rationale="Each argument to an ability operation must be a "
                              "subtype of the parameter type declared in its "
                              "'op' signature, after the ability's type "
                              "variable is instantiated.",
                    fix=f"Pass a value of type {pretty_type(param_ty)} for "
                        f"argument {i} of '{op_info.name}', or ensure the "
                        f"ability's type variable resolves to a type that "
                        f"accepts {pretty_inferred_type(arg_ty)}.",
                    spec_ref='Chapter 9, Section 9.8 "Abilities"',
                    error_code="E241",
                )

        # #921: `Ord`'s `compare` is the ability spelling of the three-way
        # `Ordering` if-chain `a < b ? Less : (a == b ? Equal : Greater)`
        # (§6.4).  Ordering (`<`/`>`/`<=`/`>=`) is defined ONLY on the
        # orderable primitives — Int, Nat, Float64, Byte, String (§4.5) — and
        # `Ord`'s "Satisfied by:" set is exactly those (§9.8.1); ADTs are NOT
        # Ord-derivable in v0.1.0 (unlike Eq/Hash/Show, whose "Satisfied by:"
        # clauses list composite types).  Without this gate, `compare` on a
        # user ADT type-checks (its `op` param is a bare type variable), then
        # codegen lowers `<` to a scalar `i32.lt_s` on the boxed heap pointers
        # — a SILENT WRONG RESULT — and the verifier raw-`<`es two Z3
        # datatypes and crashes.  Rejecting here, the single gate both codegen
        # and the verifier trust, keeps all three in agreement (checkability
        # over silent miscompilation; DESIGN.md §"Checkability").  The direct
        # `MkBox(1) < MkBox(2)` form is already rejected with E143.
        if op_info.parent_effect == "Ord":
            for i, arg_ty in enumerate(arg_types):
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                arg_base = base_type(arg_ty)
                # A bare type variable is deferred: inside a
                # `forall<T where Ord<T>>` body the `Ord<T>` constraint
                # promises orderability, and the check holds each instance's
                # type argument to the orderable set
                # (`vera.lowering.ABILITY_TYPES`) at the call that chooses it
                # (E613, `vera.typed.judge`, #1679).  Any non-Ord
                # instantiation — a user ADT OR `Bool` (§4.5 orders neither) —
                # is refused there, so deferring here can never silently
                # miscompile.  (PR #929 review closed a hole: `Bool` was
                # wrongly in the orderable set, so `Ord<Bool>` satisfied the
                # gate and the clone lowered `compare` on two Bool i32s to a
                # signed `i32.lt_s` — a silent order.)
                # Rejecting the TypeVar here would break the legitimate
                # constrained-generic form (ch09_abilities `cmp_sign`).
                if isinstance(arg_base, TypeVar):
                    continue
                if arg_base not in ORDERABLE_TYPES:
                    self._error(
                        args[i],
                        f"'{op_info.name}' requires an orderable operand, "
                        f"found {pretty_inferred_type(arg_ty)}.",
                        rationale=(
                            "The Ord ability's 'compare' operation is the "
                            "three-way spelling of the ordering operators "
                            "(<, >, <=, >=), which are defined only on the "
                            "orderable types — Int, Nat, Float64, Byte, and "
                            "String. A user-defined ADT is not Ord-derivable, "
                            "so it has no total order to compare by."
                        ),
                        fix=(
                            f"Apply '{op_info.name}' to an orderable value "
                            "(e.g. Int, Nat, Float64, Byte, String); reduce a "
                            "non-orderable type to an orderable key first, or "
                            "use 'eq' for structural equality on an ADT."
                        ),
                        spec_ref='Chapter 9, Section 9.8.1 "Built-in Abilities"',
                        error_code="E242",
                    )

        # #928: `Eq`'s `eq` is the ability spelling of `==` (§9.8.1), so it
        # inherits the same Eq-derivability requirement.  Without this gate the
        # `eq(fn, fn)` / `eq(map_composite, map_composite)` forms type-check
        # (the `op` params are bare type variables) and then codegen silently
        # pointer-compares them — the exact silent miscompile the `==` binop
        # gate (`_check_eq_ability`) closes, reached through the ability-op
        # surface instead.  Route both through the one predicate so the checker
        # rejects exactly what codegen cannot derive (the #928 differential).
        if op_info.parent_effect == "Eq":
            for i, arg_ty in enumerate(arg_types):
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                # A bare/nested type variable is deferred to the caller's
                # `Eq<T>` constraint, judged at each instance (E613, #1679),
                # exactly as the Ord arm above and the `==` binop gate do —
                # `_check_eq_ability` short-circuits on `contains_typevar`.
                self._check_eq_ability(args[i], arg_ty, arg_ty)

        return return_type

    def _ability_type_mapping(
        self, op_info: OpInfo,
        arg_types: list[Type | None],
    ) -> dict[str, Type]:
        """Infer ability type parameter mapping from argument types.

        For ``ability Eq<A>`` with ``op eq(A, A -> Bool)``, if called as
        ``eq(x, y)`` where ``x: Int``, maps ``A → Int``.
        """
        ab_info = self.env.abilities.get(op_info.parent_effect)
        if not ab_info or not ab_info.type_params:
            return {}
        mapping: dict[str, Type] = {}
        for param_ty, arg_ty in zip(op_info.param_types, arg_types):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if (isinstance(param_ty, TypeVar)
                    and param_ty.name in ab_info.type_params):
                # #993 (PR #1009 review): first-arg-wins locked the mapping
                # onto a bare ctor's fresh var — `eq(None, Some(5))` bound
                # A := Option<T$1> and the concrete second argument could
                # never re-anchor it.  A later fresh-FREE candidate
                # overrides a fresh-containing tentative one (the #293
                # precedence); `eq(None, None)` keeps its fresh binding and
                # stays rejected.
                existing = mapping.get(param_ty.name)
                if existing is None or (
                        contains_fresh_typevar(existing)
                        and not contains_fresh_typevar(arg_ty)):
                    mapping[param_ty.name] = arg_ty
        return mapping

    # -----------------------------------------------------------------
    # Constructors
    # -----------------------------------------------------------------

    def _open_variable_refusal(
        self, arg_ty: Type, param_ty: Type, arg: ast.Expr,
    ) -> tuple[str, str, str] | None:
        """Why *arg*, of type *arg_ty*, does not fit *param_ty* where a type
        variable its type leaves open is at fault (#1684): the description's
        tail, the rationale and the fix.  ``None`` for any other mismatch.

        Two shapes, from the join `_fits` asks (`JoinFailure`).  A variable
        that stands at two positions the parameter gives two types: a type
        variable takes one type.  A variable in a function type, which the
        call that made the value left without a type, so the function was
        compiled at a type of its own: a closure that is the argument is
        written at the parameter's type instead, and a value whose type
        holds one, whatever the value holds, is built at it.  The hole an empty literal's element type leaves
        (`?`, `_as_holes`) has no name, and is named as what it is.  A
        variable the enclosing function owns has its own type, and the
        generic refusal says so."""
        if not (contains_typevar(arg_ty) or contains_typevar(param_ty)):
            return None
        failure = self._join_parts(arg_ty, param_ty).failure
        if failure is None or failure.side != 0:
            return None
        name = _variable_name(failure.variable)
        literal = name == "?"
        path, given = failure.second
        if failure.conflict:
            assert failure.first is not None  # noqa: S101 — a conflict has a first binding
            first_path, first_given = failure.first
            subject = ("the element type of an empty literal in it" if literal
                       else f"its type variable {name}")
            unfixed = "the literal's element type" if literal else name
            return (
                f"{subject} stands at {describe_position(first_path)} and at "
                f"{describe_position(path)}, where the parameter's type "
                f"gives it {pretty_type(_named_open(first_given))} and "
                f"{pretty_type(_named_open(given))}, and a type variable "
                f"takes one type.",
                "A type variable an argument's type leaves open stands for "
                "one type, so the parameter must give it the same type at "
                "every position it holds.",
                f"Pass a value of type {pretty_type(_holes_unknown(param_ty))} "
                f"for this argument: no type for {unfixed} gives "
                f"{pretty_type(_named_open(arg_ty))} that type.",
            )
        written = _span_text(self.source, arg.span)
        if written is None:
            return None
        given_base = base_type(given)
        where = describe_position(path)
        if isinstance(given_base, TypeVar) and "$" in given_base.name:
            at = (f"the parameter's type has a type variable no argument "
                  f"fixes at {where}.")
        else:
            at = (f"the parameter's type gives "
                  f"{'that element type' if literal else name} "
                  f"{pretty_type(_named_open(given))} at {where}.")
        # The argument is the closure itself where the parameter asks a
        # function: a variable kept for behaviour stands inside one, never
        # at the argument's root.
        param_fn = base_type(param_ty)
        closure = isinstance(param_fn, FunctionType)
        made = "the closure" if closure else "the value"
        # A value of a data type is judged by its type: whatever this one
        # holds, a function a value of the type holds over the variable is
        # compiled at a type of its own.
        compiled = ("its code was compiled" if closure
                    else "a function a value of this type holds is compiled")
        if literal:
            why = (f"the call that made {made} was given an empty literal, "
                   f"whose element type no argument fixes, so {compiled} at "
                   f"a type of its own, and {at}")
        else:
            why = (f"no argument of the call that made {made} gives {name} "
                   f"a type, so {compiled} at a type of its own, and {at}")
        if closure:
            assert isinstance(param_fn, FunctionType)  # noqa: S101 — narrowed by `closure`
            signature = closure_signature(
                param_fn, frozenset(self.env.type_params))
            return (
                why,
                "A closure a generic call returns is compiled at the types "
                "its call's arguments give its type variables; one they give "
                "no type is compiled at a type of its own, so the closure "
                "cannot stand where the parameter asks another type for that "
                "variable.",
                (f"Write the closure at the parameter's type, "
                 f"`{signature} {{ ... }}`, and pass it in place of "
                 f"`{written}`." if signature is not None else
                 f"Write the closure at the parameter's type, with each of "
                 f"its type variables fixed, and pass it in place of "
                 f"`{written}`."),
            )
        return (
            why,
            "A function a generic call builds is compiled at the types its "
            "call's arguments give its type variables; one they give no type "
            "is compiled at a type of its own.  A value whose type holds a "
            "function over such a variable may hold one compiled so, "
            "whatever this value holds, so it cannot stand where the "
            "parameter asks another type for that variable.",
            f"Build the value at the parameter's type, writing any function "
            f"it holds at that type, in place of `{written}`.",
        )

    def _cross_owner_fix(
        self, fn_name: str, arg_ty: Type, param_ty: Type,
    ) -> str | None:
        """The fix for an argument of one owner's type where another owner's
        type of the same name is expected (#1694), or ``None``.

        Two declarations that share a name are two types, so no conversion
        exists between them: the argument has to be built as a value of the
        type the parameter names.  The fix says whose type that is, how this
        file names it, and which constructors build one.
        """
        arg, param = base_type(arg_ty), base_type(param_ty)
        if not (isinstance(arg, AdtType) and isinstance(param, AdtType)):
            return None
        name = bare_name(param.name)
        if arg.name == param.name or bare_name(arg.name) != name:
            return None
        info = self.env.lookup_type(param.name)
        ctors = ", ".join(
            f"{ctor}(...)" if ci.field_types else ctor
            for ctor, ci in (info.constructors.items() if info else ()))
        build = (f" and pass one of its constructors: {ctors}" if ctors
                 else "")
        if not param.name.startswith("mod$"):
            return (f"'{fn_name}' takes this file's own '{name}', a "
                    f"different type from the imported one of that name. "
                    f"Build the argument with this file's '{name}'{build}.")
        path = tuple(param.name.split("$")[1:-1])
        owner = ".".join(path)
        return (f"'{fn_name}' takes the '{name}' of module '{owner}', a "
                f"different type from the '{name}' this value has. Build the "
                f"argument as a value of that type: name it in this file's "
                f"import, {self._import_line(path, name)},{build}.")

    def _import_line(self, mod_path: tuple[str, ...], name: str) -> str:
        """The import line that brings *name* in from *mod_path* (#1513).

        When this file already imports that module selectively, the line
        is that import with *name* added to its list, so following the fix
        leaves one import of the module rather than a second declaration
        beside the first.
        """
        label = ".".join(mod_path)
        # An import names a type by the name its module declares it under,
        # whatever identity the type carries here (#1694).
        name = bare_name(name)
        existing = self._import_names.get(mod_path)
        names = sorted(existing | {name}) if existing else [name]
        return f"'import {label}({', '.join(names)});'"

    def _stranger_constructor(
        self, name: str,
    ) -> tuple[list[tuple[tuple[str, ...], ConstructorInfo]],
               ConstructorInfo | None]:
        """Resolve a constructor of a type this file does not import (#1513).

        Importing a data type is what brings its constructors into scope
        (§8.3.3, §8.4.2), so a constructor whose type reaches this file only
        through another declaration's signature — `paint(Green)`, with
        `Colour` imported by `paint`'s module and not by this file — is not
        in the environment.  It still denotes exactly one declaration when
        one module's PUBLIC type declares it, and code generation compiles
        it (`_namespace_ctor_projection`'s fallback class, which asks the
        same question of the same modules).

        Returns every module whose public types declare *name*, sorted by
        path, which a message names, and the constructor the resolver pass
        binds the name to here by that rule (:attr:`vera.binding.Binding.
        stranger_ctors`, #1694), or ``None`` when it binds none.  It binds one
        only when exactly one module declares it and its type's name denotes
        one declaration: no data type of that name is declared or imported
        here, and exactly one module the file can see declares one, so a
        second meaning of that name cannot let one value pass for another
        type's.

        A construction and a pattern resolve through here alike, so a
        pattern is typed by the same declaration: its fields bind at their
        declared types, and its match is judged against that type's
        constructors.
        """
        # Sorted by path: a module checker's `_resolved_modules` is built by
        # walking a set of import paths, so its order follows the hash seed.
        candidates = sorted(
            ((mod.path, self._module_constructors[mod.path][name])
             for mod in self._resolved_modules
             if name in self._module_constructors.get(mod.path, {})),
            key=lambda pair: pair[0],
        )
        names = self._names
        owner = self._namespace_owner()
        if (names is None
                or name not in names.stranger_ctors.get(owner, frozenset())):
            return candidates, None
        ident = names.ctors[owner][name]
        return candidates, self._module_constructors.get(
            ident.owner, {}).get(ident.name)

    def _stranger_data_type(self, type_name: str) -> AdtInfo | None:
        """The declaration a data type name this file does not import
        denotes (#1513), or ``None``.

        A value of such a type reaches the file through an imported
        signature (`pick(1)` returning `mb`'s `Colour`), typed by the bare
        name.  The name denotes one declaration only when no data type of
        that name is declared or imported here — the prelude's own does not
        count (#1559) — and exactly one module this file can see declares a
        type of that name, public or private: two would give one bare name
        two types.  The pattern rules
        read it for such a value: which constructors a match on it must
        cover, and which ones can match it at all.
        """
        # A type the file declares or imports bars it; the prelude's own
        # type of the name does not (#1559).  Every file holds `Json`,
        # `Request` and the prelude's other types, so counting them refused
        # every constructor of a module's type named like one: `mk(1)`,
        # returning `a`'s `Json`, was accepted while `MyK(1)`, building the
        # same value, was an error.  Such a value meets the prelude's type
        # by the bare name in this file whichever way it arrives (#1560), so
        # barring the construction guarded nothing.
        # The NAME the type is declared under, which is what this file would
        # write for it: *type_name* may be the type's identity (#1694).
        type_name = bare_name(type_name)
        bound = self.env.lookup_type(type_name)
        if (bound is not None
                and bound is not self._builtin_data_types.get(type_name)):
            return None
        declared = [
            types[type_name]
            for _path, types in sorted(self._module_all_data_types.items())
            if type_name in types
        ]
        if len(declared) != 1:
            return None
        return declared[0]

    def _unknown_ctor_fix(
        self, name: str,
        candidates: list[tuple[tuple[str, ...], ConstructorInfo]],
    ) -> str:
        """The fix for a constructor name that denotes no declaration here."""
        if not candidates:
            return (f"Declare '{name}' as a constructor of a 'data' type in "
                    f"this file, or import the data type that declares it "
                    f"with 'import <module>(<Type>);' — importing a data "
                    f"type is what makes its constructors available (check "
                    f"the spelling and capitalisation too).")
        imports = " or ".join(
            self._import_line(path, ci.parent_type)
            for path, ci in candidates
        )
        return (f"Import the data type that declares '{name}': {imports}.  "
                f"Importing a data type is what makes its constructors "
                f"available; if more than one module declares '{name}', "
                f"import the type of the one you mean.")

    # The stranger-constructor warning's text (#1513), shared by E210 and
    # E214 in a construction and E320 and E322 in a pattern, whose `_error`
    # calls each carry their code as a literal so the warning-site scans
    # (`check_diagnostic_fields.py`, the doc gate's plant table,
    # `test_warning_severity_1513.py`) can read it.
    _STRANGER_CTOR_RATIONALE = (
        "Importing a data type is what brings its constructors into scope.  "
        "This one reaches the file only through another declaration's "
        "signature; the name denotes exactly one declaration, so the program "
        "compiles, but the file does not say where it comes from."
    )

    def _stranger_ctor_message(
        self, name: str, ci: ConstructorInfo,
        candidates: list[tuple[tuple[str, ...], ConstructorInfo]],
    ) -> tuple[str, str]:
        """The description and fix of the stranger-constructor warning."""
        mod_path = candidates[0][0]
        mod_label = ".".join(mod_path)
        type_name = bare_name(ci.parent_type)
        line = self._import_line(mod_path, type_name)
        if self._import_names.get(mod_path):
            fix = (f"Add '{type_name}' to this file's import of "
                   f"'{mod_label}': {line}.")
        else:
            fix = f"Add the import: {line}."
        return (
            f"Constructor '{name}' belongs to data type '{type_name}' "
            f"of module '{mod_label}', which this file does not import.",
            fix,
        )

    @_reported_at_the_stage
    def _check_constructor_call(self, expr: ast.ConstructorCall, *,
                                expected: Type | None = None) -> Type | None:
        """Type-check a constructor call: Ctor(args)."""
        # Tuple is a variadic built-in constructor — handle specially
        if expr.name == "Tuple":
            return self._check_tuple_constructor(expr, expected=expected)

        ci = self.env.lookup_constructor(expr.name)
        if ci is None and expr.name in self._refused_ctor_names:
            # #1497: a constructor of a declaration refused as E158, whose
            # E158 is the one error the program owes.
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()
        if ci is None:
            candidates, ci = self._stranger_constructor(expr.name)
            if ci is not None:
                message, fix = self._stranger_ctor_message(
                    expr.name, ci, candidates)
                self._error(
                    expr, message,
                    rationale=self._STRANGER_CTOR_RATIONALE,
                    fix=fix,
                    severity="warning",
                    spec_ref='Chapter 8, Section 8.5.4 '
                             '"Constructor Resolution"',
                    error_code="E210",
                )
        if ci is None:
            self._error(
                expr,
                f"Unknown constructor '{expr.name}'.",
                rationale="A constructor call must name a constructor declared "
                          "by a 'data' type in scope; no such constructor is "
                          "defined or imported, so the call has no value to "
                          "build and the program cannot compile.",
                fix=self._unknown_ctor_fix(expr.name, candidates),
                spec_ref='Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"',
                error_code="E210",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # Build expected-type mapping for bidirectional inference
        expected_mapping: dict[str, Type] = {}
        if (isinstance(expected, AdtType)
                and ci.parent_type_params
                and expected.name == ci.parent_type
                and len(expected.type_args) == len(ci.parent_type_params)):
            for tv, exp_arg in zip(ci.parent_type_params,
                                   expected.type_args):
                if not isinstance(exp_arg, TypeVar):
                    expected_mapping[tv] = exp_arg

        # Compute field types with expected-type substitution so we can
        # pass them as expected to nested constructor args (e.g. Some(None))
        field_types_for_expected: tuple[Type, ...] | None = None
        if ci.field_types is not None and expected_mapping:
            field_types_for_expected = tuple(
                substitute(ft, expected_mapping) for ft in ci.field_types)

        # Synth arg types, passing resolved field type as expected
        arg_types: list[Type | None] = []
        for i, arg in enumerate(expr.args):
            field_expected: Type | None = None
            if field_types_for_expected and i < len(field_types_for_expected):
                ft = field_types_for_expected[i]
                if not contains_typevar(ft):
                    field_expected = ft
                elif isinstance(
                    arg, (ast.ConstructorCall, ast.NullaryConstructor)
                ):
                    # #979: a NESTED constructor argument whose expected field
                    # type still carries the declared forall var (`Some(None)`
                    # where the field resolves to `Option<T>`) must receive that
                    # expected type so its OWN bidirectional fill can adopt the
                    # declared var — otherwise the inner ctor mints an unrelated
                    # `T$n` and the well-typed program is rejected (E121/E170/
                    # E302).  Feeding a typevar-bearing expected is safe ONLY
                    # into a nested constructor: `_ctor_result_type`'s per-level
                    # `expected.name == ci.parent_type` guard means the inner
                    # ctor adopts a var solely from ITS OWN parent's declared
                    # position, so two ADTs sharing a param name still cannot
                    # cross-contaminate (an inner ctor of a different parent
                    # sees a name mismatch, mints fresh, and the field-type
                    # check then rejects the genuinely ill-typed nesting).
                    field_expected = ft
            arg_types.append(self._synth_expr(arg, expected=field_expected))

        if ci.field_types is None:
            if expr.args:
                self._error(
                    expr,
                    f"Constructor '{expr.name}' is nullary but was given "
                    f"{len(expr.args)} argument(s).",
                    rationale="A constructor declared with no fields takes no "
                              "arguments and must be used as a bare name.",
                    fix=f"Use the constructor without parentheses: "
                        f"'{expr.name}' instead of '{expr.name}(...)'.",
                    spec_ref='Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"',
                    error_code="E211",
                )
            return self._ctor_result_type(ci, arg_types, expected=expected,
                                          args=expr.args)

        if len(expr.args) != len(ci.field_types):
            self._error(
                expr,
                f"Constructor '{expr.name}' expects "
                f"{len(ci.field_types)} field(s), got {len(expr.args)}.",
                rationale="A constructor call must supply exactly one argument "
                          "per declared field; the count does not match the "
                          "'data' declaration.",
                fix=f"Call '{expr.name}' with exactly {len(ci.field_types)} "
                    f"argument(s), one per field in its 'data' declaration.",
                spec_ref=(
                    'Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"'
                ),
                error_code="E212",
            )
            return self._ctor_result_type(ci, arg_types, expected=expected,
                                          args=expr.args)

        # Infer type args for parameterised ADTs from arg types — a
        # literal argument taking its type from the other fields, then from
        # the expected type, then from its own value (#1541).
        soft: dict[str, Type] = {}
        mapping = self._infer_ctor_type_args(ci, arg_types, args=expr.args,
                                             expected=expected, soft_out=soft)
        self._record_literal_soft_result(expr, AdtType(ci.parent_type, tuple(
            soft.get(tv, TypeVar(tv))
            for tv in ci.parent_type_params or ())))

        # Merge expected-type mapping for unresolved vars
        for tv, exp_ty in expected_mapping.items():
            if tv not in mapping:
                mapping[tv] = exp_ty

        field_types = ci.field_types
        if mapping:
            field_types = tuple(substitute(ft, mapping) for ft in field_types)

        # #747, at the constructor door: record each argument's INSTANTIATED
        # field type as its target, whatever the expected type came from.
        # The generic FUNCTION call has recorded this since #747 and the
        # constructor never did, so a field type the checker knows only after
        # inference was invisible to the verifier's narrowing walk, which
        # consults this table whenever the DECLARED field type is a TypeVar.
        #
        # Two shapes measured silent because of it, both with the guard
        # emitted and nothing on the record:
        #
        # * `match Some(0 - 5) { Some(@Nat) -> … }` — the checker infers
        #   `T = Nat` from the argument (`0 - 5` is two non-negative literals,
        #   so `Nat - Nat`), types the construction `Option<Nat>`, and the
        #   narrowing into that `@Nat` field had no target to be read from;
        # * `MkBox([0 - 5])` into an `Array<Pos>` field — a CONCRETE field
        #   type, which the expected-type threading above reaches only when
        #   the constructor is parameterised and the caller supplied an
        #   `expected`, so a monomorphic constructor's field was never a
        #   target either.
        #
        # Recording only — the `expected` threaded to `_synth_expr` above is
        # untouched, so no inference decision and no checker diagnostic moves.
        # A field type still carrying a TypeVar is not recorded, exactly as at
        # the function door: an uninstantiated target is not a target.
        # Filling a GAP, never displacing: an entry already here came from the
        # `expected` the enclosing context forced, which is the instantiation
        # the caller requires and is strictly more authoritative than one
        # inferred from the arguments.  `wrap_opt(@Int -> @Option<Nat>)`
        # returning `Some(@Int.0)` is the case that measures the difference —
        # `_infer_ctor_type_args` reads `T = Int` off the argument and never
        # consults the return, so overwriting lost the `nat_bind` that
        # conformance program exists to pin (the one corpus mover on the
        # first shape of this change).

        if self.expr_target_types is not None:
            for c_arg, c_ft in zip(expr.args, field_types):
                key = ast.span_key(c_arg)
                if key is None or contains_typevar(c_ft):
                    continue
                recorded = self.expr_target_types.setdefault(key, c_ft)
                if (isinstance(c_arg, ast.ConstructorCall)
                        and c_arg.name != "Tuple"):
                    self._record_nested_ctor_targets(c_arg, recorded)
        # #1679: the same gap fill in the table by node identity, which the
        # typed program reads.
        if self.node_target_types is not None:
            for c_arg, c_ft in zip(expr.args, field_types):
                if c_arg.node_id is None or contains_typevar(c_ft):
                    continue
                recorded = self.node_target_types.setdefault(
                    c_arg.node_id, c_ft)
                if (isinstance(c_arg, ast.ConstructorCall)
                        and c_arg.name != "Tuple"):
                    self._record_nested_ctor_targets(
                        c_arg, recorded, by_identity=True)

        for i, (arg_ty, field_ty) in enumerate(zip(arg_types, field_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(field_ty, (TypeVar, UnknownType)):
                continue
            # Re-synth if arg still has unresolved TypeVars and the
            # subtype check would fail (e.g. List<T$2> vs List<Option<Int>>).
            if contains_typevar(arg_ty) and not is_subtype(arg_ty, field_ty):
                arg_ty = self._synth_expr(expr.args[i], expected=field_ty)
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                arg_types[i] = arg_ty
            # #1541: a field whose literals the field type types
            # differently from their own values is checked against it —
            # the function-call door's rule, at the constructor door, for a
            # declared field (`MkBox(Some(0 - 5))` into `Option<Pos>`) as
            # for an instantiated one.  Not where the enclosing context
            # already gave the field its type: the argument was synthesized
            # against that type above, and it is the more authoritative
            # target (`Some(Tuple(x, 5))` returned as an
            # `Option<Tuple<PosInt, Int>>` keeps its `PosInt`).  And only for
            # an argument the field already admits: the re-check places each
            # literal at the type it now has, and must not turn a refusal
            # into an acceptance (a literal in a `@Byte` field stays E213).
            elif (not contains_typevar(field_ty)
                    and is_subtype(arg_ty, field_ty)
                    and not (field_types_for_expected
                             and i < len(field_types_for_expected)
                             and not contains_typevar(
                                 field_types_for_expected[i]))
                    and not types_equal(arg_ty, field_ty)
                    and contains_literal_hole(
                        self._literal_soft_type(expr.args[i], arg_ty)
                        or arg_ty)):
                re = self._synth_expr(expr.args[i], expected=field_ty)
                if (re is not None and not isinstance(re, UnknownType)
                        and is_subtype(re, field_ty)):
                    arg_ty = re
                    arg_types[i] = re
            if not is_subtype(arg_ty, field_ty):
                self._error(
                    expr.args[i],
                    f"Constructor '{expr.name}' field {i} has type "
                    f"{pretty_inferred_type(arg_ty)}, expected "
                    f"{pretty_type(field_ty)}.",
                    rationale="Each constructor argument's type must be a "
                              "subtype of the corresponding field type in the "
                              "'data' declaration.",
                    fix=f"Pass a value of type {pretty_type(field_ty)} for "
                        f"field {i}, or convert the current value to "
                        f"{pretty_type(field_ty)}.",
                    spec_ref=(
                        'Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"'
                    ),
                    error_code="E213",
                )

        return self._ctor_result_type(ci, arg_types, expected=expected,
                                      args=expr.args)

    def _register_arm_pattern_reads(
        self, scrutinee: ast.Expr, pattern: ast.Pattern,
    ) -> None:
        """:py:meth:`_register_pattern_reads` for one `match` arm: a
        constructor pattern reads the scrutinee's components; a binding
        pattern at a composite type binds the whole scrutinee there, which
        is then the context of every construction the scrutinee's value
        flows from."""
        if isinstance(pattern, ast.ConstructorPattern):
            self._register_pattern_reads(
                scrutinee, list(pattern.sub_patterns), _names(pattern.name),
            )
        elif isinstance(pattern, ast.BindingPattern):
            ty = self._pattern_binding_type(pattern.type_expr)
            if ty is None or not isinstance(base_type(ty), AdtType):
                return
            for leaf in narrowing.value_leaves(scrutinee):
                key = ast.span_key(leaf)
                if key is not None:
                    self._pattern_arg_targets.setdefault(key, ty)

    def _register_pattern_reads(
        self,
        source: ast.Expr,
        fields: list[ast.Pattern | ast.TypeExpr],
        ctor_matches: Callable[[str], bool],
    ) -> None:
        """Record the COMPOSITE types a pattern binds the constructor
        arguments its *source* builds at, BEFORE the source is synthesized
        (#1503).

        *fields* are the pattern's positions — a destructure's binding
        types, or a constructor pattern's sub-patterns — and each one's
        argument sources are found the way the pattern's legs find them
        (:func:`vera.narrowing.component_sources`), through nested
        constructor patterns.  An argument bound at a scalar position is
        classified where it is bound, by the pattern's own legs.  One bound
        at a composite type — `W(@Array<Nat>)`, a `@Wrap<Nat>` component —
        is classified by nothing downstream (a composite binding obligates
        no component), and the constructor door records no type it inferred
        from a literal subtraction; so the binding's type is the
        construction's context (``_pattern_arg_targets``, threaded as its
        expected type by ``_synth_expr``).  `match W([0 - 3]) {
        W(@Array<Nat>) -> … }` obligates the `0 - 3` it stores in a `Nat`
        array, and `W(@Array<Int>)` does not."""
        for index, field in enumerate(fields):
            for source_ in narrowing.component_sources(
                    source, index, ctor_matches):
                if not source_.is_argument:
                    continue
                arg = source_.expr
                key = ast.span_key(arg)
                if key is None:
                    continue
                if isinstance(field, ast.ConstructorPattern):
                    self._register_pattern_reads(
                        arg, list(field.sub_patterns),
                        _names(field.name),
                    )
                    continue
                te = (field.type_expr if isinstance(field, ast.BindingPattern)
                      else field if isinstance(field, ast.TypeExpr) else None)
                ty = self._pattern_binding_type(te) if te is not None else None
                if ty is not None and isinstance(base_type(ty), AdtType):
                    self._pattern_arg_targets.setdefault(key, ty)

    def _pattern_binding_type(self, te: ast.TypeExpr) -> Type | None:
        """A pattern binding's type, resolved without reporting: the
        pattern is checked, and its diagnostics raised, where it is bound;
        this looks ahead to it.

        Resolution reports through state that outlives the diagnostic:
        `_error`'s duplicate collapse (`_seen_diag_keys`) and the one-shot
        E154 and removed-alias sets.  Kept while only the diagnostic is
        dropped, that state would deduplicate the binding's own resolution
        away — `match W([()]) { W(@Array<Unit>) -> 1 }` would lose its
        E135, pass `vera check` and `vera verify`, and fail to compile — so
        all of it is restored."""
        before = len(self.errors)
        seen = set(self._seen_diag_keys)
        aliases = set(self._reported_alias_errors)
        reserved = set(self._reported_reserved_type_refs)
        try:
            return self._resolve_type(te)
        finally:
            del self.errors[before:]
            self._seen_diag_keys = seen
            self._reported_alias_errors = aliases
            self._reported_reserved_type_refs = reserved

    def _record_nested_ctor_targets(
        self, ctor: ast.ConstructorCall, target: Type, *,
        by_identity: bool = False,
    ) -> None:
        """Carry a target recorded for a constructor application DOWN to
        its own arguments (#1503).

        A constructor argument is synthesized before its parent records the
        field type it is placed in, so a nested application —
        `MkBox(Some(0 - 5))` into a declared `Option<Pos>` field — instantiated
        its type parameters from its own argument alone.  The gap fill above
        now declines to record such an instantiation when the argument holds
        a pure-literal subtraction (the checker's `Nat` for it is the claim
        the shared classifier refutes), and the parent's field type is the
        instantiation the value is in fact placed at, so it is recorded here
        instead: `0 - 5` is obligated against `Pos`, where it goes.  A gap is
        filled, never displaced — an entry already present came from the
        argument's own expected type or its own inference, and stays.  A
        `Tuple` carrier is left alone: its readers take a component's target
        from the tuple's own node, which the parent has just recorded.
        """
        table: dict[typing.Any, Type] | None = (
            self.node_target_types if by_identity else self.expr_target_types)
        if table is None:
            return
        info = self.env.lookup_constructor(ctor.name)
        base = base_type(target)
        if (info is None or not info.parent_type_params
                or info.field_types is None
                or not isinstance(base, AdtType)
                or base.name != info.parent_type
                or len(base.type_args) != len(info.parent_type_params)):
            return
        mapping = dict(zip(info.parent_type_params, base.type_args))
        for arg, field_ty in zip(ctor.args, info.field_types):
            instantiated = substitute(field_ty, mapping)
            key: object = arg.node_id if by_identity else ast.span_key(arg)
            if key is None or contains_typevar(instantiated):
                continue
            recorded = table.setdefault(key, instantiated)
            if isinstance(arg, ast.ConstructorCall) and arg.name != "Tuple":
                self._record_nested_ctor_targets(
                    arg, recorded, by_identity=by_identity)

    def _check_tuple_constructor(
        self, expr: ast.ConstructorCall, *,
        expected: Type | None = None,
    ) -> Type | None:
        """Type-check a variadic Tuple constructor: Tuple(a, b, ...).

        A component is synthesized with no expected type; where *expected*
        is a tuple whose component is a `Nat` and a generic call in the
        component let a negative literal fix an `Int` there, the component
        is checked against it (``_check_in_literal_context``; PR #1583
        review), so `let @Tuple<Nat, Nat> = Tuple(1, id(0 - 3))` is refused
        (E503) as `let @Nat = id(0 - 3)` is."""
        if not expr.args:
            self._error(
                expr,
                "Tuple constructor requires at least one field.",
                rationale="A tuple is a heterogeneous product of one or more "
                          "components; the empty tuple is not a valid tuple "
                          "type.",
                fix="Provide at least one element, e.g. Tuple(@Int.0), or use "
                    "the unit value () if no payload is needed.",
                spec_ref='Chapter 2, Section 2.3.1 "Tuple Types"',
                error_code="E216",
            )
            return UnknownType()
        components: tuple[Type, ...] | None = None
        base = base_type(expected) if expected is not None else None
        if (isinstance(base, AdtType) and base.name == "Tuple"
                and len(base.type_args) == len(expr.args)):
            components = base.type_args
        arg_types: list[Type] = []
        for i, arg in enumerate(expr.args):
            t = self._synth_expr(arg)
            if components is not None:
                t = self._check_in_literal_context(arg, t, components[i])
            if t is not None and not isinstance(t, UnknownType):
                arg_types.append(t)
            else:
                arg_types.append(UnknownType())
        return AdtType("Tuple", tuple(arg_types))

    def _check_nullary_constructor(self, expr: ast.NullaryConstructor, *,
                                    expected: Type | None = None) -> Type | None:
        """Type-check a nullary constructor: None, Nil, etc."""
        ci = self.env.lookup_constructor(expr.name)
        if ci is None and expr.name in self._refused_ctor_names:
            return UnknownType()  # #1497: see `_check_constructor_call`
        if ci is None:
            candidates, ci = self._stranger_constructor(expr.name)
            if ci is not None:
                message, fix = self._stranger_ctor_message(
                    expr.name, ci, candidates)
                self._error(
                    expr, message,
                    rationale=self._STRANGER_CTOR_RATIONALE,
                    fix=fix,
                    severity="warning",
                    spec_ref='Chapter 8, Section 8.5.4 '
                             '"Constructor Resolution"',
                    error_code="E214",
                )
        if ci is None:
            self._error(
                expr,
                f"Unknown constructor '{expr.name}'.",
                rationale="A nullary constructor reference must name a "
                          "constructor declared by a 'data' type in scope; "
                          "no such constructor is defined or imported, so "
                          "the name has no value and the program cannot "
                          "compile.",
                fix=self._unknown_ctor_fix(expr.name, candidates),
                spec_ref=(
                    'Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"'
                ),
                error_code="E214",
            )
            return UnknownType()

        if ci.field_types is not None:
            self._error(
                expr,
                f"Constructor '{expr.name}' requires "
                f"{len(ci.field_types)} field(s) but was used as nullary.",
                rationale="A constructor declared with fields must be applied "
                          "to arguments; it cannot be used as a bare name.",
                fix=f"Apply '{expr.name}' to {len(ci.field_types)} "
                    f"argument(s): {expr.name}(...).",
                spec_ref=(
                    'Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"'
                ),
                error_code="E215",
            )

        return self._ctor_result_type(ci, [], expected=expected)

    def _fresh_typevar(self, name: str) -> TypeVar:
        """Return a TypeVar with a unique name derived from *name*.

        Fresh names prevent self-referential mappings when constructors
        from different ADTs share a type parameter name (e.g. both
        Option<T> and List<T> use ``T``).
        """
        self._fresh_id += 1
        return TypeVar(f"{name}${self._fresh_id}")

    def _ctor_result_type(self, ci: ConstructorInfo,
                          arg_types: list[Type | None], *,
                          expected: Type | None = None,
                          args: tuple[ast.Expr, ...] | None = None) -> Type:
        """Compute the result type of a constructor call.

        When *expected* is an AdtType with the same parent name, unresolved
        TypeVars are filled from the expected type args (bidirectional).
        Remaining unresolved TypeVars are freshened to avoid collisions.
        """
        if ci.parent_type_params:
            # Try to infer type args from argument types
            mapping = self._infer_ctor_type_args(
                ci, arg_types, args=args, expected=expected)

            # Fill unresolved TypeVars from expected type (bidirectional).
            # The same-ADT guard (expected.name == ci.parent_type) means every
            # exp_arg here is the type the surrounding declaration names for
            # THIS constructor's parent, so adopting it can never pull in
            # another ADT's parameter.  #971: adopt exp_arg even when it is a
            # TypeVar — under `forall<T> ... -> @Option<T>` the declared arg is
            # the forall var itself, and mapping the fresh ctor var to it is
            # exactly the var-to-var unification the expected-type fill
            # otherwise lacks for a nullary constructor (the argument-driven
            # path in _unify_for_inference does record forall-to-forall
            # mappings, but a nullary ctor has no arguments to drive it);
            # without it a bare `None` mints an unrelated `T$n` and the program
            # is rejected against a type that unifies trivially (E121/E170/E302).
            if (isinstance(expected, AdtType)
                    and expected.name == ci.parent_type
                    and len(expected.type_args) == len(ci.parent_type_params)):
                for tv, exp_arg in zip(ci.parent_type_params,
                                       expected.type_args):
                    # #993: a binding whose value is a bare FRESH var is a
                    # tentative non-answer (a nested nullary ctor leaked its
                    # own placeholder, e.g. MkA(None) binding A's param to
                    # None's T$n) — the declared expected arg overrides it,
                    # exactly the #293 fresh-is-tentative precedence
                    # `_unify_for_inference` applies between arguments.
                    existing = mapping.get(tv)
                    if existing is None or (
                            isinstance(existing, TypeVar)
                            and "$" in existing.name):
                        mapping[tv] = exp_arg

            # Use fresh TypeVars for any that remain unresolved — prevents
            # self-referential mappings when different ADTs share a param
            # name (e.g. both Option<T> and List<T> use "T").
            type_args = tuple(
                mapping.get(tv, self._fresh_typevar(tv))
                for tv in ci.parent_type_params
            )
            return AdtType(ci.parent_type, type_args)
        return AdtType(ci.parent_type, ())

    def _infer_ctor_type_args(self, ci: ConstructorInfo,
                              arg_types: list[Type | None], *,
                              args: tuple[ast.Expr, ...] | None = None,
                              expected: Type | None = None,
                              soft_out: dict[str, Type] | None = None,
                              ) -> dict[str, Type]:
        """Infer type arguments for a parameterised constructor.

        With the argument expressions in hand (*args*), a literal field
        takes its type from its context exactly as at a generic call
        (#1541): the other fields, then *expected*, then its own value —
        see ``ResolutionMixin._infer_type_args_in_context``.
        """
        if not ci.parent_type_params or not ci.field_types:
            return {}
        if args is None or len(args) != len(arg_types):
            mapping: dict[str, Type] = {}
            for field_ty, arg_ty in zip(ci.field_types, arg_types):
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                self._unify_for_inference(field_ty, arg_ty, mapping)
            return mapping
        result_pattern = AdtType(ci.parent_type, tuple(
            TypeVar(tv) for tv in ci.parent_type_params))
        mapping, soft = self._infer_type_args_in_context(
            ci.parent_type_params, ci.field_types, arg_types, args,
            result_type=result_pattern,
            expected=(expected if isinstance(expected, AdtType)
                      and expected.name == ci.parent_type else None))
        if soft_out is not None:
            soft_out.update(soft)
        return mapping

    # -----------------------------------------------------------------
    # Qualified / module calls
    # -----------------------------------------------------------------

    def _operation_signature_text(
        self, kind: str, owner: str, op: OpInfo,
    ) -> str:
        """*op*'s signature as a function type's inside, for E340's fix:
        ``T -> Int``.  Read from the program's own declaration of the
        *kind* (``"effect"`` or ``"ability"``) *owner*, which
        `_forward_effect_decls` and `_ns_first_decls` hold on whichever side
        of the use it is declared, so the types read as the program writes
        them and the fix pastes as written (a refinement keeps its
        predicate); from the registered signature
        (:func:`_op_signature_text`) for one the program does not declare.
        """
        decl = (self._forward_effect_decls.get(owner) if kind == "effect"
                else self._ns_first_decls.get(("ability", owner)))
        written = next(
            (o for o in getattr(decl, "operations", ()) if o.name == op.name),
            None)
        if written is None:
            return _op_signature_text(op)
        params = ", ".join(ast.format_type(t) for t in written.param_types)
        return f"{params} -> {ast.format_type(written.return_type)}"

    def _refuse_unlowerable_ability(
        self, node: ast.Node, ability: str, *,
        op: OpInfo | None = None,
        qualified: ast.QualifiedCall | None = None,
    ) -> None:
        """E340 (`vera.lowering` rule 4, #1499): an ability use code
        generation does not lower — a qualified ``Ability.op(...)`` call
        (*qualified*), a bare call to a user-declared ability's operation
        (*op*), or a ``where`` constraint naming a user-declared ability
        (*node* the constraint).

        Abilities as implemented are constraints that the four built-in
        abilities satisfy, with operations code generation compiles for
        each type that satisfies them; nothing implements a user-declared
        ability for a type.
        """
        user_rationale = (
            "Abilities as implemented are constraints that the four "
            "built-in abilities — Eq, Ord, Hash and Show — satisfy, and code "
            "generation compiles their operations for each type that "
            "satisfies them.  No declaration implements an ability for a "
            "type, so a user-declared ability's operation has no body at any "
            "type, and a constraint on one is satisfied by none."
        )
        if qualified is not None and ability_lowerable(ability):
            bare = ast.format_expr(
                ast.FnCall(name=qualified.name, args=qualified.args))
            self._error(
                node,
                f"Code generation cannot lower the qualified call "
                f"'{ability}.{qualified.name}': an ability's operation is "
                f"called bare.",
                rationale=(
                    "A qualifier names an effect, whose operation the call "
                    "performs.  An ability's operations are called bare — at "
                    "any type that satisfies the ability, and through a "
                    "where constraint in a generic body — and code "
                    "generation compiles them per type."
                ),
                fix=f"Call it bare: {bare}.",
                spec_ref='Chapter 9, Section 9.8 "Abilities"',
                error_code="E340",
            )
            return
        if op is None and qualified is None:
            ops = self.env.abilities.get(ability)
            sig = "T -> Int"
            if ops is not None and ops.operations:
                first = next(iter(ops.operations.values()))
                sig = self._operation_signature_text("ability", ability, first)
            tv = getattr(node, "type_var", "T")
            self._error(
                node,
                f"Code generation cannot lower the constraint "
                f"'{ability}<{tv}>': '{ability}' is a user-declared ability, "
                f"and only Eq, Ord, Hash and Show are lowered.",
                rationale=user_rationale,
                fix=(
                    f"Constrain {tv} with a built-in ability (Eq, Ord, Hash "
                    f"or Show), or drop the constraint and take each "
                    f"operation as a function value: type {ability}Op<{tv}> "
                    f"= fn({sig}) effects(pure); then a parameter "
                    f"@{ability}Op<{tv}>, called as apply_fn(@{ability}Op<"
                    f"{tv}>.0, ...)."
                ),
                spec_ref='Chapter 9, Section 9.8 "Abilities"',
                error_code="E340",
            )
            return
        name = qualified.name if qualified is not None else (
            op.name if op is not None else "?")
        written = (f"the qualified call '{ability}.{name}'"
                   if qualified is not None else f"a call to '{name}'")
        sig = (self._operation_signature_text("ability", ability, op)
               if op is not None else "T -> Int")
        self._error(
            node,
            f"Code generation cannot lower {written}: '{name}' is an "
            f"operation of the user-declared ability '{ability}', which "
            f"nothing implements.",
            rationale=user_rationale,
            fix=(
                f"Write the operation as a function under its own name and "
                f"call that in place of '{name}' — private fn "
                f"{name}_of(...) with the operation's signature at this "
                f"call — or, inside a generic, take it as a function value: "
                f"type {ability}Op<T> = fn({sig}) effects(pure); then a "
                f"parameter @{ability}Op<T>, called as "
                f"apply_fn(@{ability}Op<T>.0, ...)."
            ),
            spec_ref='Chapter 9, Section 9.8 "Abilities"',
            error_code="E340",
        )

    def _check_operation_lowerable(
        self, op_info: OpInfo, node: ast.Node,
    ) -> bool:
        """E340 (`vera.lowering` rule 6, #1681): an operation of a
        user-declared effect, called where the row in force does not name
        the effect.

        A row naming the effect is refused at the entry, and a handler for
        it at the handler, which adds the effect to the row its body is
        checked under, so a call under either is not refused twice.  Every
        other call is refused here: under a row that does not name it, a
        pure one too, and where no function's row is in force, a refinement
        predicate of an alias, a data field or a signature, which is checked
        before its function installs its row.  Returns whether it refused;
        a refused call is not one the purity check (E122) counts, so the
        call gets one refusal, the one that says nothing lowers it.  A bare
        call outside a handler is E217's."""
        effect = op_info.parent_effect
        if effect_operation_lowerable(effect):
            return False
        row = self.env.current_effect_row
        if isinstance(row, ConcreteEffectRow) and any(
                e.name == effect for e in row.effects):
            return False
        self._error(
            node,
            f"Code generation cannot lower the operation "
            f"'{effect}.{op_info.name}': '{effect}' is a user-declared "
            f"effect, and nothing implements its operations.",
            rationale=(
                "Code generation lowers the built-in effects' operations "
                "through the host, and State<T> and Exn<E> through their "
                "handlers.  A user-declared effect has neither: a handler for "
                "one is refused (E340), and so is a row naming one, so an "
                "operation of one called where no row names it is the use "
                "left, and it is refused at the call.  A built-in "
                "effect's operation lowers under any row, which holds it to "
                "the effects the row names (E125)."
            ),
            fix=(
                f"Call a function under its own name in place of the "
                f"operation: private fn {op_info.name}_of(...) with the "
                f"operation's signature "
                f"({self._operation_signature_text('effect', effect, op_info)}), "
                f"called as {op_info.name}_of(...) in place of "
                f"{effect}.{op_info.name}(...)."
            ),
            spec_ref='Chapter 7, Section 7.2 "Effect Declarations"',
            error_code="E340",
        )
        return True

    @_reported_at_the_stage
    def _check_qualified_call(self, expr: ast.QualifiedCall) -> Type | None:
        """Type-check a qualified call: Effect.op(args)."""
        # Try as effect operation
        op_info = self.env.lookup_effect_op(expr.name, expr.qualifier)
        if op_info:
            refused = self._check_operation_lowerable(op_info, expr)
            return self._check_op_call(op_info, expr.args, expr,
                                       counted=not refused)

        # #309 (Cortex #1147 Finding 1): op resolution failed, but codegen
        # routes a ``DB.query`` / ``DB.execute`` SPELLING to the host database
        # (``$vera.db_<op>``) by qualifier NAME regardless of resolution — e.g. a
        # user ``effect DB`` that declares only some other op.  So the
        # literal-provenance gate MUST fire on the spelling here too, or a
        # runtime SQL string reaches the host ungated.  (A resolved DB SQL op is
        # gated in ``_check_op_call``; this covers the unresolved spelling.)
        #
        # Since #1149 no Vera source reaches this branch: a user ``effect DB``
        # block is rejected (E152) and never registered, so ``DB.query`` /
        # ``DB.execute`` always resolve against the built-in.  Kept as defence
        # in depth — it holds whatever the registry does, and the gate must not
        # depend on E152 to be complete.
        if (
            expr.qualifier == "DB"
            and expr.name in DB_SQL_OP_NAMES
            and expr.args
        ):
            self._check_sql_provenance(expr.name, tuple(expr.args), expr)

        # `vera.lowering` rule 4 (#1499): a qualifier names an effect, never
        # an ability, whose operation is called bare.  E220's instruction
        # (declare an effect of that name) is false for an ability.
        ability = self.env.abilities.get(expr.qualifier)
        if ability is not None:
            op = ability.operations.get(expr.name)
            if op is not None:
                self._refuse_unlowerable_ability(
                    expr, expr.qualifier, op=op, qualified=expr)
            else:
                # The ability declares no operation of that name, so the
                # call is unresolved, whatever lowers (PR #1687 review): its
                # E340 named `nope` an operation of `Sz`, or told the reader
                # to call it bare, which is E200.
                ops = ", ".join(f"'{name}'" for name in ability.operations)
                call = ast.format_expr(
                    ast.FnCall(name=f"{expr.name}_of", args=expr.args))
                self._error(
                    expr,
                    f"Unresolved qualified call '{expr.qualifier}."
                    f"{expr.name}': the ability '{expr.qualifier}' declares "
                    f"no operation '{expr.name}'.",
                    rationale=(
                        f"A qualified call 'Effect.op' performs an operation "
                        f"of an effect.  '{expr.qualifier}' names an ability, "
                        f"whose operations are {ops}, and none is named "
                        f"'{expr.name}', so the call names nothing to perform "
                        f"and the program cannot compile."
                    ),
                    fix=(
                        f"Write what the call means as a function under its "
                        f"own name and call that: declare private fn "
                        f"{expr.name}_of(...) with the signature this call "
                        f"needs, and write {call} in place of "
                        f"'{expr.qualifier}.{expr.name}(...)'."
                    ),
                    spec_ref='Chapter 9, Section 9.8 "Abilities"',
                    error_code="E220",
                )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # Unresolved — an error (#1513): code generation has no operation
        # to call, and used to fail in the WAT assembler instead.
        self._error(
            expr,
            f"Unresolved qualified call '{expr.qualifier}.{expr.name}'.",
            rationale="A qualified call 'Effect.op' must name an operation of "
                      "an effect that is in scope; no effect named "
                      f"'{expr.qualifier}' declares an op '{expr.name}', so "
                      "there is no operation to perform and the program "
                      "cannot compile.",
            fix=f"Add '{expr.qualifier}' to the function's effects clause and "
                f"declare 'op {expr.name}(...)' in that effect, or correct "
                f"the qualifier or operation name.  A module function is "
                f"called with '::' ('module::fn(...)'), not '.'.",
            spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
            error_code="E220",
        )
        for arg in expr.args:
            self._synth_expr(arg)
        return UnknownType()

    @_reported_at_the_stage
    def _check_module_call(self, expr: ast.ModuleCall, *,
                           expected: Type | None = None) -> Type | None:
        """Type-check a module-qualified call: path.to.fn(args).

        The call is checked against the function the resolver pass bound it
        to (#1694).  A call that binds none is reported by why:
        1. Module not resolved → the file's own path (#1558) or an error.
        2. Name not in selective import list → error.
        2.5. C7c: function is private → error.
        3. Function not found in module → error with available list.
        """
        mod_path = tuple(expr.path)
        fn_name = expr.name
        mod_label = ".".join(expr.path)

        # The function the resolver pass bound the call to (#1694); what
        # follows says why a call that binds none names nothing.
        fn_info = self._bound_function(expr)
        if fn_info is not None:
            return self._check_fn_call_with_info(fn_info, expr.args, expr,
                                                 expected=expected)

        # 1. Module not resolved
        if mod_path not in self._resolved_module_paths:
            if mod_path == self._own_module_path:
                return self._check_own_module_call(expr, expected=expected)
            self._error(
                expr,
                f"Module '{mod_label}' not found. "
                f"Cannot resolve call to '{fn_name}'.",
                rationale=(
                    "No module matching this path is imported by this file, "
                    "and the path does not name the file itself: a file's "
                    "own path is the one its 'module' declaration gives, "
                    "and only where the program reaches the file by that "
                    "path.  So the call names no function and the program "
                    "cannot compile.  A module reached only through another "
                    "module's imports is not visible here."
                ),
                fix=self._unresolved_module_fix(mod_path, fn_name),
                spec_ref='Chapter 8, Section 8.6.5 "Resolution Errors"',
                error_code="E230",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # 2. Selective import filter
        import_filter = self._import_names.get(mod_path)
        if import_filter is not None and fn_name not in import_filter:
            self._error(
                expr,
                f"'{fn_name}' is not imported from module "
                f"'{mod_label}'. "
                f"Imported names: {sorted(import_filter)}.",
                rationale=(
                    "The import declaration uses selective imports. "
                    "Add the name to the import list to use it."
                ),
                fix=(
                    f"Change the import to include '{fn_name}': "
                    f"import {mod_label}"
                    f"({', '.join(sorted(import_filter | {fn_name}))});"
                ),
                spec_ref='Chapter 8, Section 8.3.2 "Selective Import"',
                error_code="E231",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # 2.5 C7c: visibility check — is the function private?
        all_fns = self._module_all_functions.get(mod_path, {})
        fn_all = all_fns.get(fn_name)
        if fn_all is not None and not self._is_public(fn_all.visibility):
            self._error(
                expr,
                f"Function '{fn_name}' in module '{mod_label}' is "
                f"private and cannot be accessed from outside "
                f"its module.",
                rationale=(
                    "Only functions marked 'public' can be called "
                    "from other modules."
                ),
                fix=(
                    f"Mark the function as public in the module: "
                    f"public fn {fn_name}(...)"
                ),
                spec_ref=(
                    'Chapter 8, Section 8.4 "Visibility"'
                ),
                error_code="E232",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # 3. Function not found in module
        mod_fns = self._module_functions.get(mod_path, {})
        available = sorted(mod_fns.keys())
        self._error(
            expr,
            f"Function '{fn_name}' not found in module "
            f"'{mod_label}'."
            + (f" Available functions: {available}." if available else ""),
            rationale="A module-qualified call must name a public function "
                      "declared in the target module; the module was resolved "
                      "but declares no such function, so the program cannot "
                      "compile.",
            fix=f"Define 'public fn {fn_name}(...)' in module '{mod_label}', "
                f"or correct the name to one the module exports"
            + (f" (e.g. {available[0]})." if available else "."),
            spec_ref='Chapter 8, Section 8.5.3 "Module-Qualified Calls"',
            error_code="E233",
        )
        for arg in expr.args:
            self._synth_expr(arg)
        return UnknownType()

    def _check_own_module_call(self, expr: ast.ModuleCall, *,
                               expected: Type | None = None,
                               ) -> Type | None:
        """A module-qualified call to the file's OWN path (#1558).

        `ma::two(3)` inside `module ma;` calls the file's own top-level
        `two`: the path names the module (§8.5.3), and this module is the
        one the path names.  Its private functions are reachable too, since
        the call is inside the module that declares them (§8.4.1).  It is
        checked as the bare call to that top-level function is, with one
        difference that is the point of writing it: a `where` helper of the
        same name does not shadow it, as nothing local shadows a
        module-qualified call — so it reads the top-level table, never the
        lexical helper chain a bare call reads first.
        """
        fn_name = expr.name
        # The bound call was checked before this (`_check_module_call`); a
        # call here binds none.
        if fn_name in self._own_fn_names:
            # A declaration registration refused (E151, E153): its own error
            # is the one the program owes, and this use restates it.
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()
        mod_label = ".".join(expr.path)
        declared = sorted(self._top_level_fn_infos)
        # This file's own helpers only: the index spans every module the
        # file resolves, and another module's helper is no function of this
        # one either way.
        helper_of = sorted(
            parent for parent in self._where_helper_parents.get(fn_name, set())
            if " in module " not in parent)
        if helper_of:
            fix = (f"'{fn_name}' is a 'where' helper of {', '.join(helper_of)}, "
                   f"local to the function that declares it: call it by its "
                   f"bare name from inside that function, or lift it to a "
                   f"top-level function of module '{mod_label}'.")
        else:
            fix = (f"Define 'fn {fn_name}(...)' at the top level of this "
                   f"file, or correct the name to one it declares"
                   + (f" (e.g. {declared[0]})." if declared else "."))
        self._error(
            expr,
            f"Function '{fn_name}' not found in module '{mod_label}', which "
            f"is this file."
            + (f" Its functions: {declared}." if declared else ""),
            rationale="A module-qualified call to the path this file's "
                      "'module' declaration gives names one of the file's "
                      "own top-level functions; the file declares none by "
                      "this name, so the program cannot compile.",
            fix=fix,
            spec_ref='Chapter 8, Section 8.5.3 "Module-Qualified Calls"',
            error_code="E233",
        )
        for arg in expr.args:
            self._synth_expr(arg)
        return UnknownType()

    def _unresolved_module_fix(
        self, mod_path: tuple[str, ...], fn_name: str,
    ) -> str:
        """E230's fix: import the module — unless the path is this file's.

        A file imported as `ma` that declares no path, or declares another,
        has no path of its own (#1558), and adding `import ma;` inside it
        would import the file into itself.  The remedy there is the
        declaration.
        """
        label = ".".join(mod_path)
        resolved = self._resolved_as
        if resolved is not None and mod_path in (
                resolved, self._declared_module_path):
            here = ".".join(resolved)
            if self._declared_module_path is None:
                declares = "declares no module path"
            else:
                declares = ("declares 'module "
                            f"{'.'.join(self._declared_module_path)};'")
            return (f"This file is imported as '{here}' but {declares}, so "
                    f"no path names it.  Declare 'module {here};' at the "
                    f"top of the file and call its own function as "
                    f"'{here}::{fn_name}(...)', or call it by its bare name, "
                    f"'{fn_name}(...)'.")
        return (f"Add 'import {label};' and create the file "
                f"'{label.replace('.', '/')}.vera' relative to the importing "
                f"file or project root.")
