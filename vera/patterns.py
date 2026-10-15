"""A `match` pattern, read to its full depth (#1697).

Two phases read a `match`'s patterns, and both read them here.  The checker
asks whether the arms cover every value of the scrutinee's type (spec
§4.9.2); :func:`missing_cases` answers with the values no arm takes.  The
verifier asks when an arm is taken; :func:`tests` lists what a pattern
requires of a value, position by position, and a value matches the pattern
exactly when it passes every test.  Both readers stopped at a pattern's outer
constructor: `W(Red)` was taken to cover every `W`, so `match W(Green) {
W(Red) -> 1 }` checked clean and ran the `W(Red)` arm (#1540), and
`Some(None)` was taken to match every `Some`, so an arm after it was
unreachable to the proof and an `ensures` was proved that the program fails
(#1562).

A pattern's head (:func:`head`) is what it tests at its own position: a
constructor and its sub-patterns (a nullary pattern is a constructor with
none, and `Tuple` is the one constructor of a tuple type), a literal, or
nothing, for a wildcard and a binding pattern, which take every value.  A
binding pattern at a refinement is no exception: a value its predicate
refuses traps at the bind (§2.6.5) rather than falling through to a later
arm.

What the values at a position are is the caller's to say: *constructors_of*
answers it from the position's type as a domain, a data type's
:class:`Constructors` with their fields' types, `Bool`'s two values
(:class:`Booleans`), or an :class:`Open` domain, whose values no set of
literal or constructor patterns covers and only a catch-all does (`Int`,
`Nat`, `Byte`, `String`, `Float64`, the built-in types with no
constructors, a function type, and a type variable, which may be any of
them), or with ``None`` for a position it does not judge.

Imports ``vera.ast`` only, so either phase imports it without the other.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass
from typing import Generic, TypeVar, Union

from vera import ast

#: The type of a position, which this module never reads: the caller's.
Ty = TypeVar("Ty")


# =====================================================================
# A pattern's head
# =====================================================================


@dataclass(frozen=True)
class CtorHead:
    """A constructor pattern's head: the constructor and its sub-patterns,
    none for a nullary pattern."""

    name: str
    subs: tuple[ast.Pattern, ...]


@dataclass(frozen=True)
class LitHead:
    """A literal pattern's head: the literal's type (``"Int"``, ``"Bool"``
    or ``"String"``) and its value.  The type is part of the head because
    Python's ``True == 1``: a `true` and a `1` are different tests."""

    kind: str
    value: int | bool | str


def head(pattern: ast.Pattern) -> CtorHead | LitHead | None:
    """What *pattern* tests at its own position; ``None`` for a wildcard or a
    binding pattern, which take every value."""
    if isinstance(pattern, ast.ConstructorPattern):
        return CtorHead(pattern.name, pattern.sub_patterns)
    if isinstance(pattern, ast.NullaryPattern):
        return CtorHead(pattern.name, ())
    if isinstance(pattern, ast.BoolPattern):
        return LitHead("Bool", pattern.value)
    if isinstance(pattern, ast.IntPattern):
        return LitHead("Int", pattern.value)
    if isinstance(pattern, ast.StringPattern):
        return LitHead("String", pattern.value)
    if isinstance(pattern, (ast.WildcardPattern, ast.BindingPattern)):
        return None
    # A pattern form the grammar grew and this reading did not.  Taking it
    # for a catch-all would judge a match it leaves uncovered exhaustive.
    raise TypeError(  # pragma: no cover — every `ast.Pattern` is read above
        f"no reading of the pattern form {type(pattern).__name__}")


# =====================================================================
# What a pattern requires of a value: the verifier's reading
# =====================================================================


@dataclass(frozen=True)
class Step:
    """One step from a value into one of its fields: the constructor the
    value is, and the field's index."""

    constructor: str
    index: int


@dataclass(frozen=True)
class PatternTest:
    """One thing a pattern requires of the value it matches: that the value
    reached by *path* is the constructor, or equals the literal, *head*
    names."""

    path: tuple[Step, ...]
    head: CtorHead | LitHead


def tests(pattern: ast.Pattern) -> tuple[PatternTest, ...]:
    """What *pattern* requires of a value, outermost first: a value matches
    *pattern* exactly when it passes every test, so a wildcard or a binding
    pattern requires nothing."""
    found: list[PatternTest] = []

    def visit(pat: ast.Pattern, path: tuple[Step, ...]) -> None:
        at = head(pat)
        if at is None:
            return
        found.append(PatternTest(path, at))
        if isinstance(at, CtorHead):
            for i, sub in enumerate(at.subs):
                visit(sub, (*path, Step(at.name, i)))

    visit(pattern, ())
    return tuple(found)


# =====================================================================
# The values no pattern takes: the checker's reading
# =====================================================================


@dataclass(frozen=True)
class Constructor(Generic[Ty]):
    """One constructor of a position's type: its name and its fields' types."""

    name: str
    fields: tuple[Ty, ...]


@dataclass(frozen=True)
class Constructors(Generic[Ty]):
    """A data type's values: each is one of *constructors*, in declaration
    order, applied to values of its fields' types."""

    constructors: tuple[Constructor[Ty], ...]


@dataclass(frozen=True)
class Booleans:
    """`Bool`'s values, `true` and `false`."""


@dataclass(frozen=True)
class Open:
    """Values no set of literal patterns covers, so only a catch-all does."""


#: What the values at a position are.
Domain = Union[Constructors[Ty], Booleans, Open]

#: Answers a position's domain from its type; ``None`` for a position the
#: caller does not judge.
ConstructorsOf = Callable[[Ty], Union[Domain[Ty], None]]


@dataclass(frozen=True)
class _Any:
    """`_`: some value the patterns leave uncovered, unnamed."""


@dataclass(frozen=True)
class _Literal:
    """A literal value no pattern takes: `true` or `false`."""

    text: str


@dataclass(frozen=True)
class _Built:
    """A constructor applied to its fields' uncovered values.  *missing*:
    no pattern names the constructor at this position, so every field is
    `_`."""

    name: str
    args: tuple[_Uncovered, ...]
    missing: bool


_Uncovered = Union[_Any, _Literal, _Built]
_ANY = _Any()
_WILD = ast.WildcardPattern()
_Row = tuple[ast.Pattern, ...]


def missing_cases(
    patterns: Sequence[ast.Pattern],
    scrutinee_type: Ty,
    constructors_of: ConstructorsOf[Ty],
) -> tuple[str, ...]:
    """The values of *scrutinee_type* that no pattern of *patterns* matches,
    each written as a pattern with `_` for a position where any value is
    uncovered, sorted; empty when the patterns cover every value.

    A value is matched to the full depth of each pattern.  The cases named
    are those at the first position, reading the patterns outermost first,
    that leaves a value uncovered.  At the scrutinee itself they are the
    constructors no pattern names, by their bare names, as E311 has always
    named them.  Inside a constructor they are, where the patterns name
    some of a field's constructors or `Bool` values and not others, each
    one they do not name, its own fields `_`; and `_` where they name none,
    or where the field's type is one no literal covers.  Where the patterns
    name every constructor of a position, the cases are those uncovered
    inside each.  So `W(Red)` over `W(Colour)` leaves `W(Green)`, `Some(3)`
    beside `None` leaves `Some(_)`, and `Tuple(None, @Int)` leaves
    `Tuple(Some(_), _)`.
    """
    found = _uncovered([(p,) for p in patterns], (scrutinee_type,),
                       constructors_of, top=True)
    return tuple(sorted({_render(case[0], top=True) for case in found}))


def _uncovered(
    rows: list[_Row], types: tuple[Ty, ...],
    constructors_of: ConstructorsOf[Ty], *, top: bool = False,
) -> list[tuple[_Uncovered, ...]]:
    """The value vectors of *types* no row of *rows* matches, a row matching
    a vector when each of its patterns matches the value at its position
    (the usefulness computation over a pattern matrix: Maranget, "Warnings
    for pattern matching", 2007).  *top*: the first position is the
    scrutinee itself.  A row of catch-alls matches every vector, so where
    one is left nothing is uncovered, and the positions after it are not
    split, which would visit every combination of the values the other
    rows name there."""
    if any(all(head(p) is None for p in row) for row in rows):
        return []
    if not types:
        return [()]
    rest = types[1:]
    heads = [head(row[0]) for row in rows]
    domain = constructors_of(types[0])
    if domain is None:
        # The caller does not judge this position: every pattern here is
        # read as taking every value, as the check does not judge a
        # scrutinee it has no type for.
        return [(_ANY, *case) for case in _uncovered(
            [row[1:] for row in rows], rest, constructors_of)]
    if isinstance(domain, Constructors):
        return _uncovered_constructors(rows, heads, domain, rest,
                                       constructors_of, top=top)
    if isinstance(domain, Booleans):
        return _uncovered_booleans(rows, heads, rest, constructors_of)
    # An open domain: no literal covers it, so only the catch-alls do.
    return [(_ANY, *case) for case in _uncovered(
        _default(rows, heads), rest, constructors_of)]


def _uncovered_constructors(
    rows: list[_Row], heads: list[CtorHead | LitHead | None],
    domain: Constructors[Ty], rest: tuple[Ty, ...],
    constructors_of: ConstructorsOf[Ty], *, top: bool,
) -> list[tuple[_Uncovered, ...]]:
    """`_uncovered` at a position whose values are *domain*'s constructors.
    A head naming no constructor of the domain (a literal, another type's
    constructor) matches no value here, as the type error reported for it
    says."""
    declared = {c.name for c in domain.constructors}
    named = {h.name for h in heads
             if isinstance(h, CtorHead) and h.name in declared}
    if named == declared:
        found: list[tuple[_Uncovered, ...]] = []
        for ctor in domain.constructors:
            arity = len(ctor.fields)
            for case in _uncovered(
                    _specialise(rows, heads, ctor.name, arity),
                    (*ctor.fields, *rest), constructors_of):
                found.append(
                    (_Built(ctor.name, case[:arity], False), *case[arity:]))
        return found
    after = _uncovered(_default(rows, heads), rest, constructors_of)
    if not named and not top:
        return [(_ANY, *case) for case in after]
    return [(_Built(c.name, (_ANY,) * len(c.fields), True), *case)
            for c in domain.constructors if c.name not in named
            for case in after]


def _uncovered_booleans(
    rows: list[_Row], heads: list[CtorHead | LitHead | None],
    rest: tuple[Ty, ...], constructors_of: ConstructorsOf[Ty],
) -> list[tuple[_Uncovered, ...]]:
    """`_uncovered` at a `Bool` position inside a constructor (a `Bool`
    scrutinee is E312's to judge)."""
    named = {h.value for h in heads
             if isinstance(h, LitHead) and h.kind == "Bool"}
    if named == {True, False}:
        found: list[tuple[_Uncovered, ...]] = []
        for value in (True, False):
            taken = [row[1:] for row, h in zip(rows, heads)
                     if h is None or (isinstance(h, LitHead)
                                      and h.kind == "Bool"
                                      and h.value is value)]
            found.extend((_Literal(_bool_text(value)), *case)
                         for case in _uncovered(taken, rest, constructors_of))
        return found
    after = _uncovered(_default(rows, heads), rest, constructors_of)
    if not named:
        return [(_ANY, *case) for case in after]
    return [(_Literal(_bool_text(value)), *case)
            for value in (True, False) if value not in named
            for case in after]


def _specialise(
    rows: list[_Row], heads: list[CtorHead | LitHead | None],
    name: str, arity: int,
) -> list[_Row]:
    """The rows that can match a value built by constructor *name*, its
    fields in the place of the first position: a row naming *name* gives
    its sub-patterns, and a catch-all gives a wildcard for each field.  A
    row giving *name* another number of sub-patterns than its *arity*
    fields (E321) is read as matching every value it builds, as the check
    read it before it read sub-patterns at all."""
    out: list[_Row] = []
    for row, at in zip(rows, heads):
        if at is None:
            out.append(((_WILD,) * arity) + row[1:])
        elif isinstance(at, CtorHead) and at.name == name:
            subs = at.subs if len(at.subs) == arity else (_WILD,) * arity
            out.append(subs + row[1:])
    return out


def _default(
    rows: list[_Row], heads: list[CtorHead | LitHead | None],
) -> list[_Row]:
    """The rows whose first pattern takes every value, without it."""
    return [row[1:] for row, at in zip(rows, heads) if at is None]


def _bool_text(value: bool) -> str:
    return "true" if value else "false"


def _render(case: _Uncovered, *, top: bool) -> str:
    """*case* written as a pattern; a missing constructor at the scrutinee
    itself (*top*) is written as its bare name."""
    if isinstance(case, _Any):
        return "_"
    if isinstance(case, _Literal):
        return case.text
    if not case.args or (case.missing and top):
        return case.name
    return (f"{case.name}("
            f"{', '.join(_render(a, top=False) for a in case.args)})")
