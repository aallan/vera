"""A type-directed generator of whole Vera programs, version two.

``generate(seed)`` writes a program from a seed: type aliases and
refinements, up to three ``data`` declarations with a generic one and a
recursive one beside them, generic helpers, ``State`` and ``Exn`` helpers
each called under a handler of its cell, two to six functions whose
contracts hold of every input their ``requires`` admits, a module beside the entry holding declarations the entry imports,
and a ``main`` that prints the value of each public function.
``tests/test_program_generator.py`` runs it through check, verify, compile,
load, the reconciliation join, ``vera test --distrust``, and a sequence of
edits through a warm verification session against a fresh one (ROADMAP
Stage 26; TESTING.md § Program Generator).  ``python -m
tests.program_generator SEED`` prints a seed's program.

What makes a program well formed, by construction rather than by retry:

* **Every expression is drawn for a type**, and its static type is the
  checker's (spec §4.4): ``Nat <op> Nat`` is ``Nat``, and any mix with an
  ``Int`` or a literal is ``Int``.  A ``@Nat`` position takes a ``Nat``, or an
  ``Int`` the verifier can show is non-negative: the narrowing is obligated,
  and provable.
* **A slot reference holds its binding, never an index.**  The index is
  computed where the reference is written, as the number of bindings of the
  same slot name pushed after it (DE_BRUIJN.md §4), over the stack the
  function builds: its parameters, then each ``let``, a ``match`` arm's
  binders, a closure's parameters, a handler clause's payload.  An alias
  names its own stack at a slot's head and resolves inside a type argument
  (DE_BRUIJN.md §6.1), so ``@Score`` and ``@Int`` are two stacks and
  ``@Option<Score>`` is ``@Option<Int>``.
* **Contracts are true by construction.**  Each numeric expression carries
  two intervals: what the verifier can see (*V*), and what a run of the
  program can reach (*R*).  A field of a data value is unbounded in *V*; a
  call is what the callee's ``ensures`` states; a ``requires`` or a
  refinement bounds each numeric parameter; a call to a generic, a fold, a
  ``State`` read, an array element, a map's value and a handler's value are
  opaque to the verifier, and so are a ``match`` on a constructor applied in
  place or on ``map_get``'s result and a call taking an argument the
  verifier has no term for (issue #1696), so *V* holds their type alone,
  and a ``let`` of one holds its own type's alone.  A fold's type is its
  initial value's, as the checker gives it.
  So an ``ensures``
  written from *V* holds in the verifier's model, an argument whose *V* lies
  inside the callee's ``requires`` meets it, a ``@Nat`` subtraction whose
  operands' *V* cannot cross is provable, and an *R* far inside the 64-bit
  range means no run overflows.  A refutation, a timeout or a failing check
  is then the generator's bug or the toolchain's, never the program's own.
* **A recursive function's measure decreases by construction.**  A ``@Nat``
  measure is bounded by the ``requires``, the body is ``if`` the measure is
  zero then the base case else the step, and the step's recursive call
  passes the measure less one (inside the step the verifier knows it is
  positive); a structural measure recurses on the tail a constructor
  pattern binds.  The ``ensures`` is the fixpoint of the body's *V* with the
  recursive call assumed at what the ``ensures`` states, widened where a
  side does not settle, or the exact closed form of a linear step; *R* is
  the body unrolled to the measure's bound.
* **An instantiation satisfies its constraints**: a generic is called only
  at a type its ``where`` clause admits, with arguments whose type is the
  instantiation exactly, and a ``State`` cell holds an ``Int`` or a ``Nat``,
  inside :data:`CELL_R` by construction (each ``put`` writes a value whose
  *R* lies inside it), so every read is bounded.

``minimize`` shrinks a program while a predicate holds: it drops functions
(a literal stands in for each call), the module's functions and the module,
unreferenced data declarations, ``main``'s prints, statements and ``let``s
(inlining each), and replaces expressions by smaller ones (a handler, a
recursive call, a fold by a literal of its type), one change at a time,
keeping each the predicate accepts.

``edits`` writes the sequence of edits the warm differential sends a
verification session, each kept well formed.  ``summarize`` reads a night's
records (``VERA_GENERATOR_OUT``) into the report the workflow posts.

Version two leaves out closures beyond ``array_fold``'s argument, effect-row
variables, parameterised aliases, user effects and abilities, ``String``,
``Float64`` and ``Byte`` values beyond ``main``'s output and a map's keys,
relational preconditions, the product of two variables, and an index into
anything but a ``let``-bound array literal (issue #1525's line from #1680:
code generation infers no element type for an array in place).

Some shapes it writes make code generation fail on a program the checker
and the verifier accept, because code generation re-derives a value's type
from its own reading of the expression (issue #1525): an argument at a
generic's type variable, which it instantiates the call at, a fold as a
scrutinee or a constructor's argument, which it finds no type for, and a
branch whose every arm is a fold, a ``throw`` or a handler (#1744 for the
handlers).  :func:`bind_in_place` writes the program with each such value
bound in place by a ``let`` of the type the checker gives it, and a find
that vanishes there is counted under the issue; one that does not vanish
is reported.
"""

from __future__ import annotations

import copy
import json
import random
import re
import sys
from collections.abc import Callable, Collection, Iterator
from dataclasses import dataclass, field, fields, is_dataclass
from pathlib import Path

# =====================================================================
# Intervals
# =====================================================================

#: The magnitude no value a run reaches may pass: far inside the 64-bit
#: range, so no operation of a generated program overflows.
SAFE = 2**40

#: What a run of the program can put in a field, by the field's type: every
#: construction stays inside it, so a binder of the field reads it as *R*.
FIELD_R = {"Int": (-40, 40), "Nat": (0, 40)}

#: The largest bound a recursive function's ``@Nat`` measure takes.
MEASURE_MAX = 10

#: How deep a construction of the recursive data type nests.
CHAIN_DEPTH = 3


@dataclass(frozen=True)
class Iv:
    """A closed interval of integers; ``None`` is unbounded on that side."""

    lo: int | None
    hi: int | None

    def within(self, lo: int | None, hi: int | None) -> bool:
        """Whether every value of this interval lies in ``[lo, hi]``."""
        return ((lo is None or (self.lo is not None and self.lo >= lo))
                and (hi is None or (self.hi is not None and self.hi <= hi)))

    def bounded(self) -> bool:
        return self.lo is not None and self.hi is not None

    def safe(self) -> bool:
        return self.within(-SAFE, SAFE)


ANY = Iv(None, None)
NAT_ANY = Iv(0, None)

#: What a ``State`` cell holds: every ``put`` writes a value inside it.
CELL_R = {"Int": Iv(-100, 100), "Nat": Iv(0, 100)}

#: The divisor a ``put`` takes its value modulo when the value's *R* would
#: leave :data:`CELL_R`.
CELL_MOD = 97


def _opt(f: Callable[[int, int], int], a: int | None, b: int | None) -> int | None:
    return None if a is None or b is None else f(a, b)


def iv_add(a: Iv, b: Iv) -> Iv:
    return Iv(_opt(int.__add__, a.lo, b.lo), _opt(int.__add__, a.hi, b.hi))


def iv_sub(a: Iv, b: Iv) -> Iv:
    return Iv(_opt(int.__sub__, a.lo, b.hi), _opt(int.__sub__, a.hi, b.lo))


def iv_neg(a: Iv) -> Iv:
    return Iv(None if a.hi is None else -a.hi, None if a.lo is None else -a.lo)


def iv_scale(a: Iv, k: int) -> Iv:
    if k >= 0:
        return Iv(None if a.lo is None else a.lo * k,
                  None if a.hi is None else a.hi * k)
    return iv_scale(iv_neg(a), -k)


def trunc_div(x: int, k: int) -> int:
    """Integer division truncating toward zero (spec §4.4)."""
    q = abs(x) // abs(k)
    return q if (x >= 0) == (k > 0) else -q


def iv_div(a: Iv, d: Iv) -> Iv:
    """``a / d`` for a divisor ``d`` with ``d.lo >= 1``: for a fixed positive
    divisor the quotient grows with the dividend, and for a fixed dividend
    its magnitude falls as the divisor grows, so the corners bound it."""
    assert d.lo is not None and d.lo >= 1
    if a.lo is None:
        lo = None
    elif a.lo >= 0:
        lo = a.lo // d.hi if d.hi is not None else 0
    else:
        lo = trunc_div(a.lo, d.lo)
    if a.hi is None:
        hi = None
    elif a.hi >= 0:
        hi = trunc_div(a.hi, d.lo)
    else:
        hi = trunc_div(a.hi, d.hi) if d.hi is not None else 0
    return Iv(lo, hi)


def iv_mod(a: Iv, d: Iv) -> Iv:
    """``a % d`` for ``d.lo >= 1``: the remainder takes the dividend's sign
    and is smaller than the divisor in magnitude (spec §4.4)."""
    assert d.lo is not None and d.lo >= 1
    m = None if d.hi is None else d.hi - 1

    def tighter(values: tuple[int | None, ...], pick: Callable[..., int]) -> int | None:
        known = [v for v in values if v is not None]
        return pick(known) if known else None

    lo = 0 if a.lo is not None and a.lo >= 0 else tighter(
        (a.lo, None if m is None else -m), max)
    hi = 0 if a.hi is not None and a.hi <= 0 else tighter((a.hi, m), min)
    return Iv(lo, hi)


def iv_hull(a: Iv, b: Iv) -> Iv:
    return Iv(_opt(min, a.lo, b.lo), _opt(max, a.hi, b.hi))


def _hull_all(ivs: list[Iv]) -> Iv | None:
    out: Iv | None = None
    for x in ivs:
        out = x if out is None else iv_hull(out, x)
    return out


# =====================================================================
# Types
# =====================================================================

PRIMITIVES = ("Int", "Nat", "Bool")
NUMERIC = ("Int", "Nat")

#: The plain aliases a program may declare, by name and target.
PLAIN_ALIASES = (("Score", "Int"), ("Mark", "Nat"), ("Flag", "Bool"))

#: The refinement aliases a program may declare, by name and base.
REFINED_ALIASES = (("Span", "Int"), ("Cap", "Nat"))

#: The entry's file, and the module's file and path.
ENTRY = "generated.vera"
MODULE_FILE = "gen_lib.vera"
MODULE_NAME = "gen_lib"

#: The keys a map is built from.
MAP_KEYS = ("a", "b", "c", "d")


def split_type(ty: str) -> tuple[str, list[str]]:
    """``Map<String, Int>`` as ``("Map", ["String", "Int"])``."""
    if "<" not in ty:
        return ty, []
    head, rest = ty.split("<", 1)
    inner = rest[:-1]
    parts: list[str] = []
    depth, start = 0, 0
    for n, ch in enumerate(inner):
        if ch == "<":
            depth += 1
        elif ch == ">":
            depth -= 1
        elif ch == "," and depth == 0:
            parts.append(inner[start:n].strip())
            start = n + 1
    parts.append(inner[start:].strip())
    return head, parts


def subst(ty: str, inst: dict[str, str]) -> str:
    """*ty* with each type variable of *inst* replaced."""
    return re.sub(r"\b[A-Z]\b", lambda m: inst.get(m.group(0), m.group(0)), ty)


# =====================================================================
# The program, as the generator holds it
# =====================================================================

@dataclass(eq=False)
class Binding:
    """One slot of the stack: a parameter, a ``let``, a pattern binder, a
    closure's parameter, or a handler clause's payload.

    A parameter or a binder carries its intervals; a ``let`` reads them off
    its value."""

    type: str
    v: Iv | None = None
    r: Iv | None = None
    value: Expr | None = None
    #: The type as the declaration writes it (an alias's name, or a type
    #: argument spelled with one); the type itself when ``None``.
    written: str | None = None
    #: The slot's name, which a reference counts by: an alias at the head
    #: keeps its own name, one inside a type argument resolves; the type
    #: itself when ``None``.
    slot: str | None = None
    #: A refinement alias's interval, which the binding holds by its type.
    refined: Iv | None = None
    #: The binding this one is a narrowed view of (a recursive function's
    #: measure inside the step, where it is positive): written as that one.
    view_of: Binding | None = None

    @property
    def spelled(self) -> str:
        return self.written or self.type

    @property
    def slot_name(self) -> str:
        return self.slot or self.type


@dataclass(eq=False)
class Ctor:
    name: str
    data: str
    fields: list[str]


@dataclass(eq=False)
class Data:
    name: str
    public: bool
    ctors: list[Ctor]
    #: Type parameters (``T``), for a generic data type.
    params: list[str] = field(default_factory=list)
    #: Declared in the module.
    module: bool = False


@dataclass(eq=False)
class Alias:
    """``type Score = Int;``, or a refinement ``type Span = { @Int | … };``."""

    name: str
    target: str
    refined: Iv | None = None


#: The constructors of the prelude's and the built-in types a program uses.
SOME = Ctor("Some", "Option", ["T"])
NONE = Ctor("None", "Option", [])
GREATER = Ctor("Greater", "Ordering", [])


def tuple_ctor(types: list[str]) -> Ctor:
    return Ctor("Tuple", "Tuple", list(types))


class Expr:
    """An expression node."""


@dataclass(eq=False)
class Lit(Expr):
    value: int | bool


@dataclass(eq=False)
class Ref(Expr):
    binding: Binding


@dataclass(eq=False)
class Bin(Expr):
    op: str
    left: Expr
    right: Expr


@dataclass(eq=False)
class Neg(Expr):
    operand: Expr


@dataclass(eq=False)
class Not(Expr):
    operand: Expr


@dataclass(eq=False)
class Let:
    binding: Binding


@dataclass(eq=False)
class Do:
    """An expression statement: a ``put`` or a call to a ``State`` helper."""

    expr: Expr


@dataclass(eq=False)
class Block:
    lets: list[Let | Do]
    result: Expr


@dataclass(eq=False)
class If(Expr):
    cond: Expr
    then: Block
    other: Block


@dataclass(eq=False)
class Pattern:
    """A match arm's pattern: a constructor's, with a binder or ``None``
    (``_``) for each field; an ``Int`` or ``Bool`` literal; or ``_``."""

    ctor: Ctor | None = None
    binders: list[Binding | None] = field(default_factory=list)
    literal: int | bool | None = None


@dataclass(eq=False)
class Arm:
    pattern: Pattern
    body: Expr


@dataclass(eq=False)
class Match(Expr):
    scrutinee: Expr
    arms: list[Arm]


@dataclass(eq=False)
class Call(Expr):
    fn: Function
    args: list[Expr]
    #: A generic's instantiation, by type variable.
    inst: dict[str, str] = field(default_factory=dict)


@dataclass(eq=False)
class Construct(Expr):
    ctor: Ctor
    args: list[Expr]
    #: The constructed type, for a generic one (``Box<Int>``, ``Option<Nat>``).
    ty: str | None = None


@dataclass(eq=False)
class Builtin(Expr):
    """A built-in a generic's template calls: ``compare`` or ``eq``."""

    name: str
    args: list[Expr]
    ty: str


@dataclass(eq=False)
class Get(Expr):
    """``get(())`` of the ``State`` cell in force."""

    cell: str


@dataclass(eq=False)
class Put(Expr):
    """``put(value)``, as a statement or a helper's whole body."""

    cell: str
    value: Expr


@dataclass(eq=False)
class Throw(Expr):
    """``throw(value)`` of the ``Exn`` in force: a branch, never a value."""

    cell: str
    value: Expr


@dataclass(eq=False)
class Handle(Expr):
    """``handle[State<C>](@C = init) {…} in {…}`` with the canonical
    clauses, or ``handle[Exn<C>] { throw(@C) -> { clause } } in {…}``."""

    kind: str
    cell: str
    init: Expr | None
    body: Block
    #: ``Exn``: the clause's payload binder, and the clause's body.
    payload: Binding | None = None
    clause: Expr | None = None


@dataclass(eq=False)
class ArrayLit(Expr):
    elem: str
    items: list[Expr]


@dataclass(eq=False)
class MapBuild(Expr):
    """``map_insert(map_insert(map_new(), "a", v), "b", v)``."""

    entries: list[tuple[str, Expr]]


@dataclass(eq=False)
class SetBuild(Expr):
    """``set_add(set_add(set_new(), v), v)``."""

    items: list[Expr]


@dataclass(eq=False)
class Length(Expr):
    arr: Expr


@dataclass(eq=False)
class Index(Expr):
    """``arr[idx]``, written only inside the :class:`Guarded` that bounds it."""

    arr: Expr
    idx: Expr


@dataclass(eq=False)
class Guarded(Expr):
    """``if idx < array_length(arr) then { then } else { other }``: an index
    under the bound that proves it."""

    arr: Expr
    idx: Expr
    then: Expr
    other: Expr


@dataclass(eq=False)
class Fold(Expr):
    """``array_fold(arr, init, fn(@Int, @Int -> @Int) effects(pure) { body })``:
    the closure's body reads its own two parameters alone."""

    arr: Expr
    init: Expr
    acc: Binding
    elem: Binding
    body: Expr


@dataclass(eq=False)
class MapGet(Expr):
    """``map_get(map, "key")``, written only as a ``match``'s scrutinee."""

    map: Expr
    key: str


@dataclass(eq=False)
class SetHas(Expr):
    set: Expr
    item: Expr


@dataclass(eq=False)
class SetSize(Expr):
    set: Expr


@dataclass(eq=False)
class Bound(Expr):
    """``{ let @T = value; @T.0 }``: *value* bound in place by a ``let`` of
    *type*, the type the checker gives it, which code generation reads off
    the declaration (:func:`bind_in_place`)."""

    value: Expr
    type: str


@dataclass(eq=False)
class Function:
    name: str
    public: bool
    params: list[Binding]
    ret: str
    body: Block
    #: ``exact`` (``@T.result == ...`` over a straight-line body), ``bounds``,
    #: ``lower``, ``upper`` or ``none``; the clause written is the strongest
    #: of these the body supports.
    ensure_style: str = "bounds"
    #: One ``requires`` per parameter, rather than one conjunction.
    split_requires: bool = False
    #: The bounds as two ``ensures``, rather than one conjunction.
    split_ensures: bool = False
    #: The arguments ``main`` and the load differential call it on.
    example: list[int | bool] = field(default_factory=list)
    #: How ``main`` prints its value: ``interp`` or ``concat``.
    print_style: str = "interp"
    #: ``plain``, ``recursive``, ``mutual`` (its helper ``helper``),
    #: ``structural``, ``noncomm``, ``generic``, ``state`` or ``exn``.
    kind: str = "plain"
    #: A generic's type variables and its ``where`` constraints.
    forall: list[str] = field(default_factory=list)
    constraints: list[str] = field(default_factory=list)
    #: ``pure``, or the row a ``State`` or ``Exn`` helper declares.
    effects: str = "pure"
    #: The parameter ``decreases`` names.
    measure: Binding | None = None
    #: The ``where`` block.
    helpers: list[Function] = field(default_factory=list)
    #: The recursion group (the function itself, or a parent and its
    #: helper), whose members' calls to each other are the recursive ones.
    group: list[Function] | None = None
    #: A generic's or a recursion's template.
    template: str = ""
    #: A linear recursion's step constant.
    step: int = 0
    #: A generic's contracts, as written.
    contract: list[str] | None = None
    #: A recursion's fixpoint: what its ``ensures`` states and what a run
    #: reaches.
    summary_v: Iv | None = None
    summary_r: Iv | None = None
    #: What an ``Exn`` helper throws, as a run reaches it.
    throws: Iv | None = None
    #: An edit's broken contract: ``ensures(false)``.
    broken: bool = False
    #: Declared in the module.
    module: bool = False


@dataclass(eq=False)
class Module:
    """The module beside the entry: ``module gen_lib;``."""

    datas: list[Data]
    functions: list[Function]


@dataclass(eq=False)
class Program:
    seed: int
    datas: list[Data]
    functions: list[Function]
    #: The public functions ``main`` prints, in order.
    prints: list[Function]
    aliases: list[Alias] = field(default_factory=list)
    module: Module | None = None

    def render(self) -> str:
        """The entry's text."""
        return render(self)

    def files(self) -> dict[str, str]:
        """Each file of the program by name: the entry, and the module."""
        out = {ENTRY: render(self)}
        if self.module is not None:
            out[MODULE_FILE] = render_module(self)
        return out

    def calls(self) -> list[tuple[str, list[int] | None]]:
        """Every public function, with the arguments to call it on (a
        ``Bool`` as 0 or 1), and ``main``, which takes none."""
        out: list[tuple[str, list[int] | None]] = [
            (f.name, [int(a) for a in f.example])
            for f in self.functions if f.public
        ]
        return out + [("main", None)]

    def shape(self) -> dict[str, int]:
        return shape(self)


def all_functions(prog: Program) -> list[Function]:
    """The module's functions, then the entry's, each ``where`` helper
    after its parent: callees before their callers."""
    out: list[Function] = []
    for fn in (prog.module.functions if prog.module else []) + prog.functions:
        out.append(fn)
        out.extend(fn.helpers)
    return out


def all_datas(prog: Program) -> list[Data]:
    return prog.datas + (prog.module.datas if prog.module else [])


# =====================================================================
# Types and intervals of the program's expressions
# =====================================================================

def static_type(e: Expr) -> str:
    """The checker's type of *e* (spec §4.4)."""
    if isinstance(e, Lit):
        return "Bool" if isinstance(e.value, bool) else "Int"
    if isinstance(e, Ref):
        return e.binding.type
    if isinstance(e, Bin):
        if e.op in ARITH:
            both = static_type(e.left) == static_type(e.right) == "Nat"
            return "Nat" if both else "Int"
        return "Bool"
    if isinstance(e, Neg):
        return "Int"
    if isinstance(e, (Not, SetHas)):
        return "Bool"
    if isinstance(e, If):
        return _join(static_type(e.then.result), static_type(e.other.result))
    if isinstance(e, Guarded):
        return _join(static_type(e.then), static_type(e.other))
    if isinstance(e, Match):
        types = [static_type(arm.body) for arm in e.arms]
        out = types[0]
        for t in types[1:]:
            out = _join(out, t)
        return out
    if isinstance(e, Call):
        return subst(e.fn.ret, e.inst)
    if isinstance(e, Construct):
        return e.ty or e.ctor.data
    if isinstance(e, Builtin):
        return e.ty
    if isinstance(e, Get):
        return e.cell
    if isinstance(e, Put):
        return "Unit"
    if isinstance(e, Throw):
        return "Never"
    if isinstance(e, Handle):
        body = static_type(e.body.result)
        return body if e.clause is None else _join(body, static_type(e.clause))
    if isinstance(e, ArrayLit):
        return f"Array<{e.elem}>"
    if isinstance(e, MapBuild):
        return "Map<String, Int>"
    if isinstance(e, SetBuild):
        return "Set<Nat>"
    if isinstance(e, Fold):
        # The checker binds the accumulator to the initial value's type, so
        # a fold from a `Nat` is a `Nat` over its `Int` closure.
        return "Nat" if static_type(e.init) == "Nat" else "Int"
    if isinstance(e, (Length, SetSize)):
        return "Int"
    if isinstance(e, Index):
        return split_type(static_type(e.arr))[1][0]
    if isinstance(e, MapGet):
        return "Option<Int>"
    if isinstance(e, Bound):
        return e.type
    raise TypeError(e)


def _join(a: str, b: str) -> str:
    if a == "Never":
        return b
    if b == "Never":
        return a
    if a == b:
        return a
    if {a, b} <= {"Int", "Nat"}:
        return "Int"
    raise TypeError(f"no join of {a} and {b}")


ARITH = ("+", "-", "*", "/", "%")
COMPARE = ("<", "<=", ">", ">=", "==", "!=")
LOGIC = ("&&", "||")


def _default(ty: str) -> Iv:
    return NAT_ANY if ty == "Nat" else ANY


def iv(e: Expr, which: str) -> Iv:
    """*e*'s interval: ``"v"``, what the verifier can see, or ``"r"``, what
    a run of the program can reach."""
    if isinstance(e, Lit):
        assert not isinstance(e.value, bool)
        return Iv(e.value, e.value)
    if isinstance(e, Ref):
        b = e.binding
        if b.value is not None:
            out = iv(b.value, which)
            if which == "v" and _untranslated(b.value):
                # A `let` of a value the verifier does not translate holds a
                # fresh value of the `let`'s own type: of a `Nat`, its sign
                # at most (#1696).
                return NAT_ANY if b.type == "Nat" and out.lo is not None and out.lo >= 0 else ANY
            return out
        out = b.v if which == "v" else b.r
        assert out is not None, b
        return out
    if isinstance(e, Bin):
        a = iv(e.left, which)
        if e.op == "+":
            return iv_add(a, iv(e.right, which))
        if e.op == "-":
            return iv_sub(a, iv(e.right, which))
        if e.op == "*":
            assert isinstance(e.right, Lit) and not isinstance(e.right.value, bool)
            return iv_scale(a, e.right.value)
        if e.op == "/":
            return iv_div(a, iv(e.right, which))
        if e.op == "%":
            return iv_mod(a, iv(e.right, which))
        raise TypeError(e.op)
    if isinstance(e, Neg):
        return iv_neg(iv(e.operand, which))
    if isinstance(e, If):
        branches = [b.result for b in (e.then, e.other)
                    if not isinstance(b.result, Throw)]
        out = _hull_all([iv(b, which) for b in branches])
        assert out is not None, e
        return out
    if isinstance(e, Guarded):
        return iv_hull(iv(e.then, which), iv(e.other, which))
    if isinstance(e, Match):
        if which == "v" and _opaque_scrutinee(e.scrutinee):
            # The verifier translates no `match` on a constructor applied in
            # place, on `map_get`'s result or on what it has no term for: its
            # value is unconstrained (#1696).
            return _default(static_type(e))
        out = _hull_all([iv(arm.body, which) for arm in e.arms
                         if not isinstance(arm.body, Throw)])
        assert out is not None, e
        return out
    if isinstance(e, Call):
        if e.fn.forall:
            return (_default(static_type(e)) if which == "v"
                    else _generic_r(e))
        if which == "v" and any(_no_term(a) for a in e.args):
            # A call taking an argument the verifier has no term for does
            # not translate either: its value is unconstrained, and the
            # callee's `ensures` is dropped (#1696).
            return _default(static_type(e))
        return visible(e.fn) if which == "v" else body_r(e.fn)
    if isinstance(e, Get):
        return ANY if which == "v" else CELL_R[e.cell]
    if isinstance(e, Handle):
        if which == "v":
            # The verifier models a handler's value as unconstrained, a
            # `Nat` one included (#1696's `State<Nat>` line).
            return ANY
        out = iv(e.body.result, "r") if not isinstance(e.body.result, Throw) else None
        if e.clause is not None:
            clause = iv(e.clause, "r")
            out = clause if out is None else iv_hull(out, clause)
        assert out is not None, e
        return out
    if isinstance(e, Length):
        lit = _literal_of(e.arr)
        n = len(lit.items)
        if which == "v" and not all(_translatable(x) for x in lit.items):
            # The verifier models a literal holding an expression it cannot
            # translate as an unknown array, whose length it knows nothing
            # of, not even that it is non-negative.
            return ANY
        return Iv(n, n)
    if isinstance(e, Index):
        if which == "v":
            return _default(static_type(e))
        out = _hull_all([iv(x, "r") for x in _literal_of(e.arr).items])
        assert out is not None
        return out
    if isinstance(e, Fold):
        return ANY if which == "v" else _fold_r(e)
    if isinstance(e, SetSize):
        return ANY if which == "v" else Iv(1, len(_set_of(e.set).items))
    if isinstance(e, Bound):
        return iv(e.value, which)
    raise TypeError(e)


def _translatable(e: Expr) -> bool:
    """Whether the verifier models *e*: no call to a generic, no fold, no
    cell read, no handler, no element read, no set's size."""
    return not any(
        isinstance(node, (Fold, Get, Handle, Index, Guarded, MapGet, SetSize))
        or isinstance(node, Call) and node.fn.forall
        for node in _walk(e))


def _no_term(e: Expr) -> bool:
    """Whether the verifier translates *e* to no term at all: a generic's
    call, a fold, a cell's read, a handler, a set's size or a constructor
    of the module's data type anywhere in it, or a slot of a type other
    than ``Int``, ``Nat`` and ``Bool`` bound to one (a ``let`` of one of
    those three holds a fresh value of its type)."""
    for node in _walk(e):
        if (isinstance(node, (Fold, Get, Handle, SetSize))
                or isinstance(node, Call) and node.fn.forall
                or isinstance(node, Construct) and node.ctor.data == TALLY):
            return True
        if (isinstance(node, Ref) and node.binding.value is not None
                and node.binding.type not in PRIMITIVES
                and _no_term(node.binding.value)):
            return True
    return False


def _untranslated(e: Expr) -> bool:
    """Whether the verifier translates *e* to no term: one it has no term
    for, or holding a ``match`` it does not translate."""
    return _no_term(e) or any(
        isinstance(node, Match) and isinstance(node.scrutinee, (Construct, MapGet))
        for node in _walk(e))


def _opaque_scrutinee(e: Expr) -> bool:
    """Whether the verifier translates no ``match`` on *e*: a constructor
    applied in place, ``map_get``'s result, or an expression it has no term
    for."""
    return isinstance(e, (Construct, MapGet)) or _no_term(e)


def _cell_of(fn: Function) -> str:
    """The cell an effect helper's row names: ``Int`` of ``<State<Int>>``."""
    return fn.effects.split("<", 2)[2][:-2]


def _refined_leaf(e: Expr) -> bool:
    """Whether *e*'s type is a refinement: a reference to a refined binding,
    or a branch that is one.  A generic position reads its type off *e*, so
    a refined leaf instantiates it at the refinement."""
    if isinstance(e, Ref):
        b = e.binding.view_of or e.binding
        return b.refined is not None or (b.value is not None and _refined_leaf(b.value))
    if isinstance(e, If):
        return _refined_leaf(e.then.result) or _refined_leaf(e.other.result)
    if isinstance(e, Guarded):
        return _refined_leaf(e.then) or _refined_leaf(e.other)
    if isinstance(e, Match):
        return any(_refined_leaf(arm.body) for arm in e.arms)
    return False


def _literal_of(arr: Expr) -> ArrayLit:
    """The array literal a reference to a ``let``-bound array holds."""
    assert isinstance(arr, Ref) and isinstance(arr.binding.value, ArrayLit), arr
    return arr.binding.value


def _set_of(s: Expr) -> SetBuild:
    assert isinstance(s, Ref) and isinstance(s.binding.value, SetBuild), s
    return s.binding.value


def _map_of(m: Expr) -> MapBuild:
    assert isinstance(m, Ref) and isinstance(m.binding.value, MapBuild), m
    return m.binding.value


def _fold_r(e: Fold) -> Iv:
    """What a fold over the literal's elements reaches: the closure's
    accumulator after each element in turn."""
    items = _literal_of(e.arr).items
    saved_acc, saved_elem = e.acc.r, e.elem.r
    elem_r = _hull_all([iv(x, "r") for x in items]) or Iv(0, 0)
    acc = iv(e.init, "r")
    out = acc
    try:
        e.elem.r = elem_r
        for _ in items:
            e.acc.r = acc
            acc = iv(e.body, "r")
            out = iv_hull(out, acc)
            if not out.safe():
                return out
    finally:
        e.acc.r, e.elem.r = saved_acc, saved_elem
    return out


def _generic_r(e: Call) -> Iv:
    """What a run of a generic's call reaches, by its template: the
    argument it returns, or the field it unwraps."""
    template = e.fn.template
    if template == "choose":
        return iv_hull(iv(e.args[1], "r"), iv(e.args[2], "r"))
    if template == "least":
        return iv_hull(iv(e.args[0], "r"), iv(e.args[1], "r"))
    if template == "unbox":
        ty = e.inst["T"]
        return iv_hull(Iv(*FIELD_R[ty]), iv(e.args[1], "r"))
    raise TypeError(template)


def body_v(fn: Function) -> Iv:
    """What the verifier sees of *fn*'s value: a recursion's fixpoint, or
    its body's *V*.  A recursion that has none (it has left its template)
    has no interval to read."""
    if fn.summary_v is not None:
        return fn.summary_v
    if fn.group is not None:
        raise TypeError(f"{fn.name} has left its recursion's template")
    return iv(fn.body.result, "v")


def body_r(fn: Function) -> Iv:
    if fn.summary_r is not None:
        return fn.summary_r
    if fn.group is not None:
        raise TypeError(f"{fn.name} has left its recursion's template")
    return iv(fn.body.result, "r")


def visible(fn: Function) -> Iv:
    """What the verifier knows of a call's value: what *fn*'s ``ensures``
    states, or its type alone."""
    default = _default(fn.ret)
    style = ensure_style(fn)
    if style == "none":
        return default
    body = body_v(fn)
    if style in ("exact", "bounds"):
        return body
    if style == "lower":
        return Iv(body.lo, default.hi)
    return Iv(default.lo, body.hi)


def ensure_style(fn: Function) -> str:
    """The ``ensures`` *fn* writes: its chosen style where the body supports
    it, else the strongest one it does."""
    if fn.broken or fn.contract is not None or fn.kind in ("state", "exn"):
        return "none"
    if fn.template == "linear":
        return "exact"
    if fn.ret not in NUMERIC:
        if (fn.ret == "Bool" and fn.ensure_style == "exact"
                and fn.group is None and straight(fn.body)):
            return "exact"
        return "none"
    if fn.ensure_style == "exact" and fn.group is None and straight(fn.body):
        return "exact"
    body = body_v(fn)
    lo = body.lo if not (fn.ret == "Nat" and body.lo == 0) else None
    has = {"lower": lo is not None, "upper": body.hi is not None}
    want = fn.ensure_style if fn.ensure_style in ("bounds", "lower", "upper") else "bounds"
    if want == "bounds":
        if has["lower"] and has["upper"]:
            return "bounds"
        want = "lower" if has["lower"] else "upper"
    if has[want]:
        return want
    other = "upper" if want == "lower" else "lower"
    return other if has[other] else "none"


def straight(block: Block) -> bool:
    """Whether *block* is straight-line arithmetic over its parameters, so
    its value is one expression an ``ensures`` can state.

    The ``ensures`` writes each ``let`` as its value, which must not change
    the type a use reads: an ``@Int`` ``let`` of a ``@Nat`` value would put a
    ``@Nat`` where the body had an ``@Int``, and turn an ``@Int`` subtraction
    into an obligated ``@Nat`` one.  (The reverse only drops an obligation:
    a ``@Nat`` ``let`` holds what its ``@Int`` value holds.)"""
    def flat(e: Expr) -> bool:
        if isinstance(e, Ref) and e.binding.value is not None:
            value = e.binding.value
            if e.binding.type == "Int" and static_type(value) == "Nat":
                return False
            return flat(value)
        if isinstance(e, Lit | Ref):
            return True
        if isinstance(e, Bin):
            return flat(e.left) and flat(e.right)
        if isinstance(e, (Neg, Not)):
            return flat(e.operand)
        return False
    if any(isinstance(s, Do) for s in block.lets):
        return False
    return all(flat(let.binding.value) for let in block.lets
               if isinstance(let, Let) and let.binding.value is not None
               ) and flat(block.result)


# =====================================================================
# What the program's recursions and handlers settle to
# =====================================================================

def _base(fn: Function) -> Expr:
    """A recursion's base case: the measure at zero, or the empty chain."""
    body = fn.body.result
    if isinstance(body, If):
        return body.then.result
    assert isinstance(body, Match)
    return body.arms[0].body


def _step(fn: Function) -> Expr:
    body = fn.body.result
    if isinstance(body, If):
        return body.other.result
    assert isinstance(body, Match)
    return body.arms[1].body


def _templated(fn: Function) -> bool:
    """Whether a recursion keeps the shape its measure's proof rests on."""
    body = fn.body.result
    if fn.kind == "structural":
        return (isinstance(body, Match) and isinstance(body.scrutinee, Ref)
                and body.scrutinee.binding is fn.measure and len(body.arms) == 2
                and body.arms[0].pattern.ctor is not None
                and body.arms[1].pattern.ctor is not None)
    return (isinstance(body, If) and isinstance(body.cond, Bin)
            and body.cond.op == "==" and isinstance(body.cond.left, Ref)
            and body.cond.left.binding is fn.measure
            and isinstance(body.cond.right, Lit) and body.cond.right.value == 0
            and not body.then.lets and not body.other.lets)


def settle(group: list[Function]) -> None:
    """A recursion group's summaries: the fixpoint of each member's *V*
    with every call inside the group read at what its ``ensures`` states,
    widened where a side does not settle in four rounds, and *R* unrolled
    to the measure's bound."""
    for f in group:
        f.summary_v = f.summary_r = None
    first = group[0]
    if first.ret not in NUMERIC or not all(_templated(f) for f in group):
        return
    if first.template == "linear":
        c = first.step
        assert first.measure is not None and first.measure.v is not None
        assert first.measure.r is not None
        first.summary_v = iv_add(iv(_base(first), "v"), iv_scale(first.measure.v, c))
        first.summary_r = iv_add(iv(_base(first), "r"), iv_scale(first.measure.r, c))
        return
    e = {f.name: iv(_base(f), "v") for f in group}
    for rounds in range(8):
        for f in group:
            f.summary_v = e[f.name]
        new = {f.name: iv_hull(e[f.name], iv(_step(f), "v")) for f in group}
        if rounds >= 3:
            new = {name: Iv(x.lo if x.lo == e[name].lo else None,
                            x.hi if x.hi == e[name].hi else None)
                   for name, x in new.items()}
        if new == e:
            break
        e = new
    for f in group:
        f.summary_v = e[f.name]
    r = {f.name: iv(_base(f), "r") for f in group}
    measure = first.measure
    rounds_r = (measure.v.hi if measure is not None and measure.type == "Nat"
                and measure.v is not None and measure.v.hi is not None
                else CHAIN_DEPTH)
    for _ in range(rounds_r + 1):
        for f in group:
            f.summary_r = r[f.name]
        r = {f.name: iv_hull(r[f.name], iv(_step(f), "r")) for f in group}
        if not all(x.safe() for x in r.values()):
            break
    for f in group:
        f.summary_r = r[f.name]


def _throws(value: object) -> Iv | None:
    """What the throws below *value* reach: its own, and each ``Exn``
    helper's it calls."""
    out: list[Iv] = []
    for node in _walk(value):
        if isinstance(node, Throw):
            out.append(iv(node.value, "r"))
        elif isinstance(node, Call) and node.fn.throws is not None:
            out.append(node.fn.throws)
    return _hull_all(out)


def refresh(prog: Program) -> None:
    """Every summary read off the program as it now stands: an ``Exn``
    helper's throws, a handler's payload, a recursion's fixpoint."""
    fns = all_functions(prog)
    for fn in fns:
        if fn.kind == "exn":
            fn.throws = _throws(fn.body) or Iv(0, 0)
    for fn in fns:
        for node in _walk(fn.body):
            if isinstance(node, Handle) and node.payload is not None:
                node.payload.r = _throws(node.body) or Iv(0, 0)
    for fn in fns:
        if fn.group is not None and fn.group[0] is fn:
            settle(fn.group)


# =====================================================================
# Writing the program
# =====================================================================

_DATA_NAMES = ("Shape", "Gauge", "Crate")
_CTOR_NAMES = (
    "Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf", "Hotel",
    "India", "Juliet", "Kilo", "Lima", "Mike", "November", "Oscar", "Papa",
    "Quebec", "Romeo", "Sierra", "Tango", "Uniform", "Victor", "Whiskey",
    "Xray", "Yankee", "Zulu")

#: The generic data type, the recursive one and the module's.
BOX = "Box"
CHAIN = "Chain"
TALLY = "Tally"


class _Generator:
    """One program from one seed.  Every choice is the seed's ``Random``."""

    def __init__(self, seed: int) -> None:
        self.seed = seed
        self.rng = random.Random(seed)
        self.datas: list[Data] = []
        self.functions: list[Function] = []
        self.aliases: list[Alias] = []
        self.module: Module | None = None
        self._ctor_names = list(_CTOR_NAMES)
        #: The effects the expression being drawn may perform: the cells of
        #: the handlers around it, or the row of the helper being written.
        self.row: tuple[str, ...] = ()
        #: Drawing a closure's body: its own parameters, and no call.
        self.closure = False
        #: Inside a handler's body: no second handler.
        self.handled = False
        #: The function being written, which no drawn call may name.
        self.current: Function | None = None
        #: Writing the module's declarations.
        self.in_module = False
        self.lib: list[Function] = []
        #: The effect helpers a call drawn so far names: a handler of a
        #: helper's cell calls one no call names yet first.
        self.called: set[int] = set()

    # -- choices -------------------------------------------------------

    def chance(self, p: float) -> bool:
        return self.rng.random() < p

    def pick(self, options: list[tuple[str, float]]) -> str:
        total = sum(w for _, w in options)
        x = self.rng.random() * total
        for name, w in options:
            x -= w
            if x < 0:
                return name
        return options[-1][0]

    def name(self) -> str:
        if self.in_module:
            return f"m{len(self.functions)}"
        return f"f{len(self.functions)}"

    # -- declarations --------------------------------------------------

    def program(self) -> Program:
        self.aliases = self.make_aliases()
        for i in range(self.rng.choice([0, 1, 1, 2, 2, 3])):
            self.datas.append(self.data(i))
        if self.chance(0.35):
            self.datas.append(Data(BOX, False, [
                Ctor("Full", BOX, ["T"]), Ctor("Hollow", BOX, [])], params=["T"]))
        if self.chance(0.35):
            self.datas.append(Data(CHAIN, False, [
                Ctor("End", CHAIN, []),
                Ctor("Link", CHAIN, [self.rng.choice(list(NUMERIC)), CHAIN])]))
        if self.chance(0.4):
            self.make_module()
        for _ in range(self.rng.choice([0, 1, 1, 2])):
            g = self.generic()
            if g is not None:
                self.functions.append(g)
        for _ in range(self.rng.choice([0, 1, 1, 2])):
            self.functions.append(self.effect_helper())
        count = self.rng.randint(2, 6)
        for i in range(count):
            self.functions.append(self.function(last=i == count - 1))
        # A generic no call instantiates has no clone to compile: code
        # generation skips its template (E604), so none is written; nor is
        # an effect helper no handler calls, which would be proved and
        # never run.
        called = {id(node.fn) for fn in self.functions for f in [fn, *fn.helpers]
                  for node in _walk(f.body) if isinstance(node, Call)}
        self.functions = [f for f in self.functions
                          if not (f.forall or f.kind in ("state", "exn"))
                          or id(f) in called]
        prints = [f for f in self.functions if f.public]
        prog = Program(self.seed, self.datas, self.functions, prints,
                       self.aliases, self.module)
        if prog.module is not None and not imports(prog):
            prog.module = None
        refresh(prog)
        return prog

    def make_aliases(self) -> list[Alias]:
        out: list[Alias] = []
        for name, target in PLAIN_ALIASES:
            if self.chance(0.3):
                out.append(Alias(name, target))
        for name, target in REFINED_ALIASES:
            if self.chance(0.3):
                if target == "Int":
                    lo = self.rng.randint(-20, 5)
                else:
                    lo = self.rng.choice([0, 0, 1, 2])
                out.append(Alias(name, target, Iv(lo, lo + self.rng.randint(3, 30))))
        return out

    def data(self, i: int) -> Data:
        name = _DATA_NAMES[i]
        enum = self.chance(0.3)
        ctors: list[Ctor] = []
        for _ in range(self.rng.randint(2, 4) if enum else self.rng.randint(1, 3)):
            ctor = Ctor(self._ctor_names.pop(0), name, [])
            if not enum:
                for _ in range(self.rng.choice([0, 1, 1, 2, 2, 3])):
                    choices = list(PRIMITIVES) + [d.name for d in self.datas]
                    ctor.fields.append(self.rng.choice(choices))
            ctors.append(ctor)
        if not enum and not any(c.fields for c in ctors):
            ctors[0].fields.append(self.rng.choice(list(PRIMITIVES)))
        return Data(name, self.chance(0.5), ctors)

    def make_module(self) -> None:
        """The module's data type and functions, in the module's own scope:
        its own data alone, and none of the entry's aliases."""
        data = Data(TALLY, True, [
            Ctor("Amber", TALLY, [self.rng.choice(list(PRIMITIVES))]),
            Ctor("Basalt", TALLY,
                 [self.rng.choice(list(NUMERIC))] if self.chance(0.5) else [])],
            module=True)
        saved = self.datas, self.functions, self.aliases
        self.datas, self.functions, self.aliases = [data], [], []
        self.in_module = True
        count = self.rng.randint(1, 3)
        for i in range(count):
            fn = self.plain_function(public=i == count - 1 or self.chance(0.6))
            fn.module = True
            self.functions.append(fn)
        self.module = Module([data], self.functions)
        self.lib = [f for f in self.functions if f.public]
        self.datas, self.functions, self.aliases = saved
        self.in_module = False

    def alias(self, name: str) -> Alias | None:
        return next((a for a in self.aliases if a.name == name), None)

    def data_names(self, *, private: bool) -> list[str]:
        """The data types a parameter, a return or a ``let`` may name: the
        program's own, without the generic and recursive ones, and the
        module's."""
        own = [d.name for d in self.datas if not d.params and d.name != CHAIN]
        lib = [d.name for d in (self.module.datas if self.module and not self.in_module else [])]
        return own + lib if private else []

    def scalar_types(self) -> list[str]:
        """The parameter types the tester serves: the primitives and the
        aliases of them."""
        return list(PRIMITIVES) + [a.name for a in self.aliases]

    def param(self, ty: str) -> Binding:
        alias = self.alias(ty)
        if alias is not None:
            if alias.refined is not None:
                return Binding(alias.target, alias.refined, alias.refined,
                               written=alias.name, slot=alias.name,
                               refined=alias.refined)
            b = self.param(alias.target)
            b.written = b.slot = alias.name
            return b
        if ty == "Int":
            lo = self.rng.randint(-30, 10)
            hi = lo + self.rng.randint(0, 40)
            bounds = Iv(lo, hi)
            return Binding(ty, bounds, bounds)
        if ty == "Nat":
            lo = self.rng.choice([0, 0, 0, 1, 5, 10, 20])
            hi = lo + self.rng.randint(0, 30)
            bounds = Iv(lo, hi)
            return Binding(ty, bounds, bounds)
        return Binding(ty)

    def _finish(self, fn: Function) -> Function:
        """*fn*'s styles, its example arguments, and its visibility: a public
        function states a contract other than ``true``."""
        fn.ensure_style = fn.ensure_style or self.pick(
            [("exact", 3), ("bounds", 4), ("lower", 1), ("upper", 1), ("none", 1)])
        fn.split_requires = self.chance(0.4)
        fn.split_ensures = self.chance(0.4)
        fn.print_style = self.rng.choice(["interp", "concat"])
        fn.example = [
            (self.rng.randint(p.v.lo, p.v.hi) if p.v is not None
             and p.v.lo is not None and p.v.hi is not None
             else self.chance(0.5))
            for p in fn.params
        ]
        if fn.public and not _nontrivial(fn):
            fn.public = False
        return fn

    def _style(self) -> str:
        return self.pick([("exact", 3), ("bounds", 4), ("lower", 1),
                          ("upper", 1), ("none", 1)])

    def function(self, *, last: bool) -> Function:
        public = last or self.chance(0.5)
        kinds = [("plain", 5.0), ("recursive", 1.6), ("mutual", 0.7),
                 ("noncomm", 1.0)]
        if any(d.name == CHAIN for d in self.datas):
            kinds.append(("structural", 1.0))
        kind = self.pick(kinds)
        if kind == "recursive":
            fn = self.recursive(public=public)
        elif kind == "mutual":
            fn = self.mutual(public=public)
        elif kind == "structural":
            fn = self.structural()
        elif kind == "noncomm":
            fn = self.noncomm(public=public)
        else:
            fn = self.plain_function(public=public)
        return fn

    def plain_function(self, *, public: bool) -> Function:
        types = self.scalar_types() + self.data_names(private=not public)
        params = [self.param(self.rng.choice(types))
                  for _ in range(self.rng.choice([0, 1, 1, 2, 2, 3]))]
        ret = self.rng.choice(list(PRIMITIVES) + self.data_names(private=not public))
        fn = Function(self.name(), public, params, ret, Block([], Lit(0)),
                      ensure_style=self._style())
        self.current = fn
        fn.body = self.block(ret, list(params), depth=3,
                             lets=self.rng.choice([0, 1, 1, 2, 3]))
        self.current = None
        return self._finish(fn)

    def generic(self) -> Function | None:
        """A private generic helper from a template, instantiated by its
        callers at a type its constraint admits."""
        options = ["choose", "least", "same"]
        if any(d.name == BOX for d in self.datas):
            options += ["unbox", "wrap"]
        template = self.rng.choice(options)
        name = self.name()
        if template == "choose":
            flag, x, y = Binding("Bool"), Binding("T"), Binding("T")
            body = If(Ref(flag), Block([], Ref(x)), Block([], Ref(y)))
            return Function(name, False, [flag, x, y], "T", Block([], body),
                            kind="generic", forall=["T"], template=template,
                            contract=["requires(true)",
                                      "ensures(@T.result == @T.1 || @T.result == @T.0)"])
        if template == "least":
            x, y = Binding("T"), Binding("T")
            body = Match(Builtin("compare", [Ref(x), Ref(y)], "Ordering"), [
                Arm(Pattern(ctor=GREATER), Ref(y)), Arm(Pattern(), Ref(x))])
            return Function(name, False, [x, y], "T", Block([], body),
                            kind="generic", forall=["T"], constraints=["Ord<T>"],
                            template=template,
                            contract=["requires(true)",
                                      "ensures(@T.result == @T.1 || @T.result == @T.0)"])
        if template == "same":
            x, y = Binding("T"), Binding("T")
            body = Builtin("eq", [Ref(x), Ref(y)], "Bool")
            return Function(name, False, [x, y], "Bool", Block([], body),
                            kind="generic", forall=["T"], constraints=["Eq<T>"],
                            template=template,
                            contract=["requires(true)", "ensures(true)"])
        box = next(d for d in self.datas if d.name == BOX)
        if template == "unbox":
            bx, d = Binding("Box<T>"), Binding("T")
            inner = Binding("T")
            body = Match(Ref(bx), [
                Arm(Pattern(ctor=box.ctors[0], binders=[inner]), Ref(inner)),
                Arm(Pattern(ctor=box.ctors[1]), Ref(d))])
            return Function(name, False, [bx, d], "T", Block([], body),
                            kind="generic", forall=["T"], template=template,
                            contract=["requires(true)", "ensures(true)"])
        x = Binding("T")
        body = Construct(box.ctors[0], [Ref(x)], ty="Box<T>")
        return Function(name, False, [x], "Box<T>", Block([], body),
                        kind="generic", forall=["T"], template=template,
                        contract=["requires(true)", "ensures(true)"])

    def effect_helper(self) -> Function:
        """A private ``State`` helper that writes the cell, or an ``Exn``
        helper that throws under a drawn condition."""
        cell = self.rng.choice(list(NUMERIC))
        params = [self.param(self.rng.choice(list(NUMERIC)))
                  for _ in range(self.rng.choice([1, 1, 2]))]
        if self.chance(0.5):
            fn = Function(self.name(), False, params, "Unit", Block([], Lit(0)),
                          kind="state", effects=f"<State<{cell}>>")
            self.current, self.row = fn, (f"State<{cell}>",)
            fn.body = Block([], Put(cell, self.cell_value(cell, list(params), 2)))
        else:
            ret = self.rng.choice(list(NUMERIC))
            fn = Function(self.name(), False, params, ret, Block([], Lit(0)),
                          kind="exn", effects=f"<Exn<{cell}>>")
            self.current, self.row = fn, (f"Exn<{cell}>",)
            cond = self.expr("Bool", list(params), 1) or Lit(True)
            payload = self.value(cell, list(params), 1)
            fn.body = Block([], If(cond, Block([], Throw(cell, payload)),
                                   Block([], self.value(ret, list(params), 2))))
            fn.throws = iv(payload, "r")
        self.current, self.row = None, ()
        return self._finish(fn)

    def _measured(self, public: bool) -> tuple[Binding, list[Binding]]:
        """A ``@Nat`` measure bounded by the ``requires``, and the parameter
        list it stands in, at a drawn position."""
        n = self.rng.randint(3, MEASURE_MAX)
        m = Binding("Nat", Iv(0, n), Iv(0, n))
        others = [self.param(self.rng.choice(self.scalar_types()))
                  for _ in range(self.rng.choice([0, 1, 1, 2]))]
        params = list(others)
        params.insert(self.rng.randint(0, len(others)), m)
        return m, params

    def recursive(self, *, public: bool) -> Function:
        m, params = self._measured(public)
        ret = self.rng.choice(["Int", "Int", "Nat", "Bool"])
        fn = Function(self.name(), public, params, ret, Block([], Lit(0)),
                      kind="recursive", measure=m, ensure_style=self._style())
        fn.group = [fn]
        self.current = fn
        # The base case runs where the measure is zero, so it reads none of
        # it: a linear step's closed form adds the measure to it.
        base = self.value(ret, [p for p in params if p is not m], 2)
        fn.body = Block([], self._recursion(fn, m, params, base, fn, ret))
        self.current = None
        settle(fn.group)
        if not _fn_ok(fn):
            fn.template, fn.step = "pass", 0
            fn.body = Block([], self._recursion(fn, m, params, base, fn, ret,
                                                template="pass"))
            settle(fn.group)
        return self._finish(fn)

    def _recursion(self, fn: Function, m: Binding, params: list[Binding],
                   base: Expr, callee: Function, ret: str, *,
                   template: str | None = None) -> If:
        """``if measure == 0 then { base } else { step }``, the step calling
        *callee* with the measure less one and every other argument passed
        on."""
        view = Binding("Nat", Iv(1, m.v.hi if m.v else 1), Iv(1, m.r.hi if m.r else 1),
                       view_of=m)
        env = [view if p is m else p for p in params]
        args: list[Expr] = []
        for p, q in zip(params, callee.params):
            args.append(Bin("-", Ref(view), Lit(1)) if p is m else Ref(p))
        rec = Call(callee, args)
        fn.summary_v, fn.summary_r = iv_or_none(base, "v"), iv_or_none(base, "r")
        step = self._step(fn, ret, rec, env, base, template)
        fn.summary_v = fn.summary_r = None
        return If(Bin("==", Ref(m), Lit(0)), Block([], base), Block([], step))

    def _step(self, fn: Function, ret: str, rec: Call, env: list[Binding],
              base: Expr, template: str | None) -> Expr:
        if ret == "Bool":
            template = template or self.rng.choice(["pass", "and", "not", "branch"])
            fn.template = template
            if template == "and":
                other = self.expr("Bool", env, 1) or Lit(True)
                return Bin(self.rng.choice(["&&", "||"]), rec, other)
            if template == "not":
                return Not(rec)
            if template == "branch":
                cond = self.expr("Bool", env, 1) or Lit(False)
                return If(cond, Block([], rec), Block([], self.value(ret, env, 1)))
            return rec
        choices = ["pass", "contract", "branch", "accum"]
        if fn.kind == "recursive" and straight(Block([], base)):
            choices += ["linear", "linear"]
        template = template or self.rng.choice(choices)
        fn.template = template
        if template == "linear":
            fn.step = (self.rng.randint(1, 4) if ret == "Nat"
                       else self.rng.choice([-3, -2, -1, 1, 2, 3, 4]))
            return Bin("+", rec, Lit(fn.step))
        if template == "contract":
            return Bin(self.rng.choice(["/", "%"]), rec, Lit(self.rng.randint(2, 7)))
        if template == "branch":
            cond = self.expr("Bool", env, 1) or Lit(False)
            return If(cond, Block([], rec), Block([], self.value(ret, env, 1)))
        if template == "accum":
            if ret == "Nat":
                return Bin("+", rec, Lit(self.rng.randint(0, 5)))
            return Bin(self.rng.choice(["+", "-"]), rec, Lit(self.rng.randint(1, 5)))
        return rec

    def mutual(self, *, public: bool) -> Function:
        """A parent and its ``where`` helper, each measured on a ``@Nat``,
        each step calling the other with the measure less one."""
        m, params = self._measured(public)
        ret = self.rng.choice(["Int", "Nat", "Bool"])
        name = self.name()
        parent = Function(name, public, params, ret, Block([], Lit(0)),
                          kind="mutual", measure=m, ensure_style=self._style())
        hparams = [Binding(p.type, p.v, p.r, written=p.written, slot=p.slot,
                           refined=p.refined) for p in params]
        hm = hparams[params.index(m)]
        helper = Function(f"{name}w", False, hparams, ret, Block([], Lit(0)),
                          kind="helper", measure=hm, ensure_style=self._style())
        parent.helpers = [helper]
        parent.group = helper.group = [parent, helper]
        self.current = parent
        base = self.value(ret, [p for p in params if p is not m], 2)
        parent.body = Block([], self._recursion(parent, m, params, base, helper, ret))
        hbase = self.value(ret, [p for p in hparams if p is not hm], 2)
        helper.body = Block([], self._recursion(helper, hm, hparams, hbase, parent, ret))
        parent.template = helper.template = ""
        self.current = None
        settle(parent.group)
        if not (_fn_ok(parent) and _fn_ok(helper)):
            parent.body = Block([], self._recursion(parent, m, params, base, helper,
                                                    ret, template="pass"))
            helper.body = Block([], self._recursion(helper, hm, hparams, hbase,
                                                    parent, ret, template="pass"))
            parent.template = helper.template = ""
            settle(parent.group)
        helper.example = [0 for _ in hparams]
        return self._finish(parent)

    def structural(self) -> Function:
        """A private function over the recursive data type: ``decreases``
        names it, and the step recurses on the tail its pattern binds."""
        chain = next(d for d in self.datas if d.name == CHAIN)
        c = Binding(CHAIN)
        others = [self.param(self.rng.choice(list(NUMERIC)))
                  for _ in range(self.rng.choice([0, 0, 1]))]
        params = [c] + others
        ret = self.rng.choice(["Int", "Int", "Nat", "Bool"])
        fn = Function(self.name(), False, params, ret, Block([], Lit(0)),
                      kind="structural", measure=c, ensure_style=self._style())
        fn.group = [fn]
        self.current = fn
        end, link = chain.ctors
        field_ty = link.fields[0]
        x = Binding(field_ty, _default(field_ty), Iv(*FIELD_R[field_ty]))
        tail = Binding(CHAIN)
        base = self.value(ret, list(params), 2)
        rec = Call(fn, [Ref(tail) if p is c else Ref(p) for p in params])
        env = list(params) + [x, tail]
        fn.summary_v, fn.summary_r = iv_or_none(base, "v"), iv_or_none(base, "r")
        if ret == "Bool":
            step: Expr = (Bin("||", rec, self.expr("Bool", env, 1) or Lit(False))
                          if self.chance(0.6) else rec)
        else:
            kind = self.rng.choice(["field", "contract", "pass", "branch"])
            if kind == "field" and field_ty == "Nat" and ret == "Nat":
                step = Bin("+", Ref(x), rec)
            elif kind == "field":
                step = Bin("+", Ref(x), rec) if ret == "Int" else rec
            elif kind == "contract":
                step = Bin("%", rec, Lit(self.rng.randint(3, 9)))
            elif kind == "branch":
                cond = self.expr("Bool", env, 1) or Lit(False)
                step = If(cond, Block([], rec), Block([], self.value(ret, env, 1)))
            else:
                step = rec
        fn.summary_v = fn.summary_r = None
        fn.body = Block([], Match(Ref(c), [
            Arm(Pattern(ctor=end), base),
            Arm(Pattern(ctor=link, binders=[x, tail]), step)]))
        self.current = None
        settle(fn.group)
        if not _fn_ok(fn):
            fn.body = Block([], Match(Ref(c), [
                Arm(Pattern(ctor=end), base),
                Arm(Pattern(ctor=link, binders=[x, tail]), rec)]))
            settle(fn.group)
        return self._finish(fn)

    def noncomm(self, *, public: bool) -> Function:
        """Two parameters of one type whose ``requires`` cannot overlap, under
        an operator whose operands' order decides its value: the ``ensures``
        holds for the order the generator meant and not for the other."""
        ty = self.rng.choice(list(NUMERIC))
        lo_b = self.rng.randint(0 if ty == "Nat" else -10, 10)
        small = Iv(lo_b, lo_b + self.rng.randint(0, 8))
        assert small.hi is not None
        lo_a = small.hi + self.rng.randint(1, 10)
        large = Iv(lo_a, lo_a + self.rng.randint(0, 10))
        a, b = Binding(ty, large, large), Binding(ty, small, small)
        params = [a, b] if self.chance(0.5) else [b, a]
        if self.chance(0.3):
            params.insert(self.rng.randint(0, 2),
                          self.param(self.rng.choice(list(PRIMITIVES))))
        op = self.rng.choice(["-", "/", "<", ">"] if (small.lo or 0) >= 1
                             else ["-", "<", ">"])
        result = Bin(op, Ref(a), Ref(b))
        ret = ("Bool" if op in ("<", ">")
               else "Nat" if ty == "Nat" else "Int")
        fn = Function(self.name(), public, params, ret, Block([], result),
                      kind="noncomm",
                      ensure_style="exact" if ret == "Bool" else "bounds")
        return self._finish(fn)

    # -- blocks and expressions -----------------------------------------

    def block(self, ty: str, env: list[Binding], depth: int, lets: int) -> Block:
        scope = list(env)
        out: list[Let | Do] = []
        for _ in range(lets):
            stmt = self.statement(scope, depth)
            if stmt is None:
                continue
            out.append(stmt)
            if isinstance(stmt, Let):
                scope.append(stmt.binding)
        return Block(out, self.value(ty, scope, depth, block=True))

    def let_types(self, scope: list[Binding]) -> list[tuple[str, float]]:
        out = [(t, 2.0) for t in PRIMITIVES]
        out += [(d, 1.0) for d in self.data_names(private=True)]
        out += [(a.name, 1.2) for a in self.aliases]
        if self.closure:
            return out
        score = self.alias("Score")
        out.append(("Array<Score>" if score else "Array<Int>", 1.0))
        if self.refs(scope, "Nat"):
            out += [("Array<Option<Nat>>", 0.7), ("Set<Nat>", 0.6)]
        if self.data_names(private=True):
            out.append(("Array<data>", 0.6))
        out += [("Map<String, Int>", 1.0), ("Tuple", 0.6),
                ("Option<Score>" if score else "Option<Int>", 0.5)]
        if any(d.name == BOX for d in self.datas):
            out.append(("Box", 0.5))
        return out

    def statement(self, scope: list[Binding], depth: int) -> Let | Do | None:
        """A ``let``, or under a ``State`` cell a ``put`` or a call to one of
        its helpers."""
        cells = [r for r in self.row if r.startswith("State<")]
        if cells and self.chance(0.45):
            cell = self.rng.choice(cells)[6:-1]
            helpers = [f for f in self.functions
                       if f.effects == f"<State<{cell}>>" and f is not self.current]
            if helpers and self.chance(0.7):
                return Do(self.call(self._helper(helpers), scope, depth))
            return Do(Put(cell, self.cell_value(cell, scope, depth - 1)))
        kind = self.pick(self.let_types(scope))
        binding = self.let(kind, scope, depth)
        return Let(binding) if binding is not None else None

    def let(self, kind: str, scope: list[Binding], depth: int) -> Binding | None:
        alias = self.alias(kind)
        if alias is not None:
            if alias.refined is not None:
                value = self.value(alias.target, scope, depth - 1, block=True,
                                   fit=alias.refined)
                return Binding(alias.target, value=value, written=alias.name,
                               slot=alias.name, refined=alias.refined)
            value = self.value(alias.target, scope, depth - 1, block=True)
            return Binding(alias.target, value=value, written=alias.name,
                           slot=alias.name)
        if kind in ("Array<Int>", "Array<Score>"):
            items = [self.exact("Int", scope, depth - 1, literal=True)
                     for _ in range(self.rng.randint(1, 4))]
            if any(x is None for x in items):
                return None
            return Binding("Array<Int>", value=ArrayLit("Int", items),  # type: ignore[arg-type]
                           written=kind)
        if kind == "Array<Option<Nat>>":
            firsts = [b for b in self.refs(scope, "Nat") if not _refined_leaf(Ref(b))
                      and iv(Ref(b), "r").within(*FIELD_R["Nat"])]
            if not firsts:
                return None
            first = self.rng.choice(firsts)
            items: list[Expr] = [Construct(SOME, [Ref(first)], ty="Option<Nat>")]
            for _ in range(self.rng.randint(0, 3)):
                if self.chance(0.4):
                    items.append(Construct(NONE, [], ty="Option<Nat>"))
                else:
                    items.append(Construct(SOME, [self.field_value("Nat", scope, depth)],
                                           ty="Option<Nat>"))
            return Binding("Array<Option<Nat>>", value=ArrayLit("Option<Nat>", items))
        if kind == "Array<data>":
            data = self.rng.choice(self.data_names(private=True))
            items = [self.construct(data, scope, depth - 1)
                     for _ in range(self.rng.randint(1, 3))]
            return Binding(f"Array<{data}>", value=ArrayLit(data, items))
        if kind == "Set<Nat>":
            firsts = [b for b in self.refs(scope, "Nat") if not _refined_leaf(Ref(b))]
            if not firsts:
                return None
            first = self.rng.choice(firsts)
            items = [Ref(first)] + [self.field_value("Nat", scope, depth)
                                    for _ in range(self.rng.randint(0, 2))]
            return Binding("Set<Nat>", value=SetBuild(items))
        if kind == "Map<String, Int>":
            # Every value an `Int` exactly: a map's value type is read off
            # the values it is built from, not off the `let`'s annotation.
            keys = self.rng.sample(list(MAP_KEYS), self.rng.randint(1, 3))
            values = [self.exact("Int", scope, depth - 1, literal=True) for _ in keys]
            if any(v is None for v in values):
                return None
            entries = [(k, v) for k, v in zip(keys, values) if v is not None]
            return Binding("Map<String, Int>", value=MapBuild(entries))
        if kind == "Tuple":
            types = [self.rng.choice(list(PRIMITIVES)) for _ in range(2)]
            items = [self.exact(t, scope, depth - 1, literal=True) for t in types]
            if any(x is None for x in items):
                return None
            ty = f"Tuple<{', '.join(types)}>"
            return Binding(ty, value=Construct(tuple_ctor(types), items, ty=ty))  # type: ignore[arg-type]
        if kind in ("Option<Score>", "Option<Int>"):
            inner = self.exact("Int", scope, depth - 1, literal=True)
            if inner is not None and self.chance(0.75):
                value: Expr = Construct(SOME, [inner], ty="Option<Int>")
            else:
                value = Construct(NONE, [], ty="Option<Int>")
            return Binding("Option<Int>", value=value, written=kind)
        if kind == "Box":
            t = self.rng.choice(list(PRIMITIVES))
            return Binding(f"Box<{t}>", value=self.construct(f"Box<{t}>", scope, depth - 1))
        value = self.value(kind, scope, depth - 1, block=True)
        return Binding(kind, value=value)

    def field_value(self, ty: str, env: list[Binding], depth: int) -> Expr:
        """A value of *ty* inside :data:`FIELD_R`, as a field holds."""
        lo, hi = FIELD_R[ty]
        e = self.value(ty, env, max(depth - 1, 0))
        if (not iv(e, "r").within(lo, hi) or (ty == "Nat" and not _nat_value(e))
                or _refined_leaf(e)):
            e = self.literal(ty, Iv(lo if ty == "Nat" else -9, 9))
        return e

    def cell_value(self, cell: str, env: list[Binding], depth: int) -> Expr:
        """A value a ``put`` writes: inside :data:`CELL_R`, taken modulo
        :data:`CELL_MOD` where its *R* would leave it."""
        bound = CELL_R[cell]
        for _ in range(4):
            e = self.value(cell, env, max(depth, 0))
            if cell == "Nat" and not _nat_value(e):
                continue
            if iv(e, "r").within(bound.lo, bound.hi):
                return e
            wrapped = Bin("%", e, Lit(CELL_MOD))
            if cell == "Nat" and not _nat_value(wrapped):
                continue
            if iv(wrapped, "r").within(bound.lo, bound.hi):
                return wrapped
        return self.literal(cell, Iv(0, 9))

    def value(self, ty: str, env: list[Binding], depth: int, *, block: bool = False,
              fit: Iv | None = None) -> Expr:
        """An expression for a position of type *ty*: a ``Nat`` position
        also takes an ``Int`` the verifier sees is non-negative.  With
        *fit*, its *V* lies inside it."""
        for _ in range(4):
            if ty == "Nat" and self.chance(0.35):
                e = self.expr("Int", env, depth, block=block)
            else:
                e = self.expr(ty, env, depth, block=block)
            if e is None:
                continue
            if ty in NUMERIC:
                v = iv(e, "v")
                need = fit if fit is not None else (NAT_ANY if ty == "Nat" else None)
                if need is not None and not v.within(need.lo, need.hi):
                    continue
                if not iv(e, "r").safe():
                    continue
            return e
        return self.literal(ty, fit)

    def literal(self, ty: str, fit: Iv | None = None) -> Expr:
        if ty == "Bool":
            return Lit(self.chance(0.5))
        if ty in NUMERIC:
            lo = fit.lo if fit is not None and fit.lo is not None else (
                0 if ty == "Nat" else -9)
            hi = fit.hi if fit is not None and fit.hi is not None else lo + 9
            return Lit(self.rng.randint(lo, hi))
        return self.construct(ty, [], 0)

    def exact(self, ty: str, env: list[Binding], depth: int, *,
              literal: bool = False) -> Expr | None:
        """An expression whose static type is *ty* exactly (an argument at a
        generic's type variable, an element, a component): no literal for
        a number unless *literal* allows an ``Int`` one."""
        for _ in range(4):
            e = self.expr(ty, env, max(depth, 0))
            if e is None or static_type(e) != ty or _refined_leaf(e):
                continue
            if isinstance(e, Lit) and ty in NUMERIC and not (literal and ty == "Int"):
                continue
            if ty in NUMERIC and not iv(e, "r").within(*FIELD_R[ty]):
                continue
            return e
        if literal and ty == "Int":
            return self.literal("Int", Iv(-9, 9))
        if ty == "Bool":
            return Lit(self.chance(0.5))
        refs = [b for b in env if b.type == ty and not _refined_leaf(Ref(b)) and (
            ty not in NUMERIC or iv(Ref(b), "r").within(*FIELD_R[ty]))]
        return Ref(self.rng.choice(refs)) if refs else None

    def refs(self, env: list[Binding], *types: str) -> list[Binding]:
        return [b for b in env if b.type in types]

    def callees(self, *types: str) -> list[Function]:
        """The functions a call drawn here may name: earlier ones, of the
        module's the public ones, none generic (:meth:`generic_call` draws
        those) and none whose effects the row in force does not admit."""
        if self.closure:
            return []
        pool = self.functions + ([] if self.in_module else self.lib)
        return [f for f in pool
                if f.ret in types and not f.forall and f is not self.current
                and (f.effects == "pure" or f.effects[1:-1] in self.row)]

    def expr(self, ty: str, env: list[Binding], depth: int, *,
             block: bool = False) -> Expr | None:
        """An expression whose static type is *ty* (or ``Nat`` for ``Int``:
        widening is free), or ``None`` when none can be written here."""
        if ty in NUMERIC:
            return self.numeric(ty, env, depth, block)
        if ty == "Bool":
            return self.boolean(env, depth, block)
        return self.adt(ty, env, depth, block)

    def _block_options(self, ty: str, env: list[Binding]) -> list[tuple[str, float]]:
        """The constructs a block position adds: ``if``, ``match``, a guarded
        index, and the handlers."""
        out = [("if", 1.2), ("match", 1.2)]
        if self.closure:
            return out
        if any(self._indexable(b, ty) for b in env):
            out.append(("guard", 3.0))
        if any(isinstance(b.value, MapBuild) for b in env):
            out.append(("mapmatch", 3.0))
        if not self.handled and not self.in_module:
            # A helper no call names yet draws its handler: a helper is
            # written to be called under one.
            waiting = {f.kind for f in self.functions
                       if f.kind in ("state", "exn") and id(f) not in self.called}
            out += [("state", 1.0 + 3.0 * ("state" in waiting)),
                    ("exn", 0.8 + 3.0 * ("exn" in waiting))]
        if any(r.startswith("Exn<") for r in self.row):
            out.append(("throwif", 1.0))
        return out

    def _indexable(self, b: Binding, ty: str) -> bool:
        if not isinstance(b.value, ArrayLit):
            return False
        elem = b.value.elem
        return elem != "Int" or ty == "Int"

    def numeric(self, ty: str, env: list[Binding], depth: int,
                block: bool) -> Expr | None:
        nat = ty == "Nat"
        refs = self.refs(env, "Nat") if nat else self.refs(env, "Int", "Nat")
        calls = self.callees("Nat") if nat else self.callees("Int", "Nat")
        cells = [r[6:-1] for r in self.row if r.startswith("State<")]
        cells = [c for c in cells if c == "Nat" or not nat]
        generics = self.generics_returning(ty)
        options = [("ref", 4.0 if refs else 0.0)]
        if not nat:
            options.append(("lit", 2.0))
        if cells and not self.closure:
            options.append(("get", 2.5))
        if depth > 0:
            options += [("add", 2.0), ("sub", 2.0 if not nat else 1.5),
                        ("call", 2.0 if calls else 0.0)]
            if not nat:
                options += [("mul", 1.5), ("divlit", 0.7), ("modlit", 0.7),
                            ("neg", 0.6)]
                arrays = [b for b in env if isinstance(b.value, ArrayLit)]
                ints = [b for b in arrays if b.value.elem == "Int"]  # type: ignore[union-attr]
                sets = [b for b in env if isinstance(b.value, SetBuild)]
                if arrays and not self.closure:
                    options.append(("length", 1.2))
                if ints and not self.closure:
                    options.append(("fold", 2.0))
                if sets and not self.closure:
                    options.append(("setsize", 0.6))
            if generics and not self.closure:
                options.append(("generic", 1.5))
            options += [("divvar", 0.5), ("modvar", 0.3)]
            if block:
                options += self._block_options(ty, env)
        if sum(w for _, w in options) == 0:
            return None
        kind = self.pick(options)
        sub = "Nat" if nat else "Int"
        if kind == "ref":
            return Ref(self.rng.choice(refs))
        if kind == "lit":
            return Lit(self.rng.randint(-9, 9))
        if kind == "get":
            return Get(self.rng.choice(cells))
        if kind in ("add", "sub"):
            left = self.expr(sub, env, depth - 1)
            right = self.expr(sub, env, depth - 1)
            if left is None or right is None:
                return None
            op = "+" if kind == "add" else "-"
            e = Bin(op, left, right)
            if op == "-" and static_type(e) == "Nat":
                # Two `@Nat` operands make a `@Nat` subtraction wherever it
                # stands, obligated to stay non-negative: written only where
                # the verifier sees the operands cannot cross.
                a, b = iv(left, "v"), iv(right, "v")
                if a.lo is None or b.hi is None or a.lo < b.hi:
                    return None
            if nat and static_type(e) != "Nat":
                return None
            return e if iv(e, "r").safe() else None
        if kind == "mul":
            left = self.expr("Int", env, depth - 1)
            if left is None:
                return None
            e = Bin("*", left, Lit(self.rng.choice([-3, -2, 2, 3, 4])))
            return e if iv(e, "r").safe() else None
        if kind in ("divlit", "modlit"):
            left = self.expr("Int", env, depth - 1)
            if left is None:
                return None
            return Bin("/" if kind == "divlit" else "%", left,
                       Lit(self.rng.randint(2, 9)))
        if kind in ("divvar", "modvar"):
            divisor = self.divisor(env, nat)
            left = self.expr(sub, env, depth - 1)
            if divisor is None or left is None:
                return None
            e = Bin("/" if kind == "divvar" else "%", left, divisor)
            if nat and static_type(e) != "Nat":
                return None
            return e
        if kind == "neg":
            operand = self.expr("Int", env, depth - 1)
            if operand is None:
                return None
            if isinstance(operand, Lit):
                return Lit(-int(operand.value))
            if isinstance(operand, Neg):
                return operand.operand
            return Neg(operand)
        if kind == "call":
            return self.call(self.rng.choice(calls), env, depth)
        if kind == "length":
            arrays = [b for b in env if isinstance(b.value, ArrayLit)]
            return Length(Ref(self.rng.choice(arrays)))
        if kind == "fold":
            return self.fold(env, depth)
        if kind == "setsize":
            sets = [b for b in env if isinstance(b.value, SetBuild)]
            return SetSize(Ref(self.rng.choice(sets)))
        if kind == "generic":
            return self.generic_call(self.rng.choice(generics), ty, env, depth)
        return self.compound(kind, ty, env, depth)

    def compound(self, kind: str, ty: str, env: list[Binding],
                 depth: int) -> Expr | None:
        """A construct of a block position, by its kind."""
        if kind == "if":
            return self.if_(ty, env, depth)
        if kind == "guard":
            return self.guard(ty, env, depth)
        if kind == "state":
            return self.handle_state(ty, env, depth)
        if kind == "exn":
            return self.handle_exn(ty, env, depth)
        if kind == "throwif":
            return self.throw_if(ty, env, depth)
        if kind == "mapmatch":
            return self.match(ty, env, depth, how="map")
        return self.match(ty, env, depth)

    def divisor(self, env: list[Binding], nat: bool) -> Expr | None:
        """A divisor the verifier sees is positive and bounded."""
        candidates = [
            b for b in self.refs(env, "Nat") if b.value is None
        ] if nat else [
            b for b in self.refs(env, "Int", "Nat") if b.value is None
        ]
        fits = [b for b in candidates
                if iv(Ref(b), "v").bounded() and (iv(Ref(b), "v").lo or 0) >= 1]
        return Ref(self.rng.choice(fits)) if fits else None

    def fold(self, env: list[Binding], depth: int) -> Expr | None:
        arrays = [b for b in env if isinstance(b.value, ArrayLit)
                  and b.value.elem == "Int"]
        arr = Ref(self.rng.choice(arrays))
        init = self.value("Int", env, max(depth - 2, 0))
        acc, elem = Binding("Int", ANY, Iv(0, 0)), Binding("Int", ANY, Iv(0, 0))
        saved, self.closure = self.closure, True
        try:
            body = self.value("Int", [acc, elem], 2)
        finally:
            self.closure = saved
        e = Fold(arr, init, acc, elem, body)
        r = iv(e, "r")
        if static_type(e) == "Nat" and (r.lo is None or r.lo < 0):
            # A fold from a `Nat` is a `Nat`: its run stays inside the type.
            return None
        return e if r.safe() else None

    def boolean(self, env: list[Binding], depth: int, block: bool) -> Expr | None:
        refs = self.refs(env, "Bool")
        calls = self.callees("Bool")
        sets = [b for b in env if isinstance(b.value, SetBuild)]
        generics = self.generics_returning("Bool")
        options = [("ref", 3.0 if refs else 0.0), ("lit", 1.0)]
        if depth > 0:
            options += [("cmp", 4.0), ("and", 1.0), ("or", 1.0), ("not", 0.7),
                        ("eq", 0.5 if refs else 0.0),
                        ("call", 1.5 if calls else 0.0)]
            if sets and not self.closure:
                options.append(("sethas", 0.8))
            if generics and not self.closure:
                options.append(("generic", 1.0))
            if block:
                options += [(k, w / 2) for k, w in self._block_options("Bool", env)]
        kind = self.pick(options)
        if kind == "ref":
            return Ref(self.rng.choice(refs))
        if kind == "lit":
            return Lit(self.chance(0.5))
        if kind == "cmp":
            left = self.expr("Int", env, depth - 1)
            right = self.expr("Int", env, depth - 1)
            if left is None or right is None:
                return None
            return Bin(self.rng.choice(list(COMPARE)), left, right)
        if kind in ("and", "or"):
            left = self.expr("Bool", env, depth - 1)
            right = self.expr("Bool", env, depth - 1)
            if left is None or right is None:
                return None
            return Bin("&&" if kind == "and" else "||", left, right)
        if kind == "not":
            operand = self.expr("Bool", env, depth - 1)
            if operand is None or isinstance(operand, Not):
                return None
            if isinstance(operand, Lit):
                return Lit(not operand.value)
            return Not(operand)
        if kind == "eq":
            right = Ref(self.rng.choice(refs)) if self.chance(0.6) else Lit(self.chance(0.5))
            return Bin(self.rng.choice(["==", "!="]), Ref(self.rng.choice(refs)), right)
        if kind == "call":
            return self.call(self.rng.choice(calls), env, depth)
        if kind == "sethas":
            return SetHas(Ref(self.rng.choice(sets)), self.field_value("Nat", env, depth))
        if kind == "generic":
            return self.generic_call(self.rng.choice(generics), "Bool", env, depth)
        return self.compound(kind, "Bool", env, depth)

    def adt(self, ty: str, env: list[Binding], depth: int, block: bool) -> Expr | None:
        refs = self.refs(env, ty)
        calls = self.callees(ty)
        generics = self.generics_returning(ty)
        options = [("ref", 3.0 if refs else 0.0), ("construct", 2.0)]
        if depth > 0:
            options += [("call", 1.5 if calls else 0.0)]
            if generics and not self.closure:
                options.append(("generic", 1.0))
            if block:
                options += [("if", 0.5), ("match", 0.5)]
        kind = self.pick(options)
        if kind == "ref":
            return Ref(self.rng.choice(refs))
        if kind == "construct":
            return self.construct(ty, env, depth)
        if kind == "call":
            return self.call(self.rng.choice(calls), env, depth)
        if kind == "generic":
            return self.generic_call(self.rng.choice(generics), ty, env, depth)
        if kind == "if":
            return self.if_(ty, env, depth)
        return self.match(ty, env, depth)

    def find_data(self, ty: str) -> Data:
        head = split_type(ty)[0]
        pool = self.datas + (self.module.datas if self.module else [])
        return next(d for d in pool if d.name == head)

    def construct(self, ty: str, env: list[Binding], depth: int, *,
                  chain: int = 0) -> Construct:
        data = self.find_data(ty)
        inst = dict(zip(data.params, split_type(ty)[1]))
        ctors = data.ctors
        if data.name == CHAIN and (chain >= CHAIN_DEPTH - 1 or depth <= 0):
            ctors = [c for c in ctors if CHAIN not in c.fields]
        ctor = self.rng.choice(ctors)
        args: list[Expr] = []
        for field_ty in ctor.fields:
            field_ty = subst(field_ty, inst)
            if field_ty in NUMERIC:
                args.append(self.field_value(field_ty, env, depth))
            elif field_ty == CHAIN:
                args.append(self.construct(CHAIN, env, depth - 1, chain=chain + 1))
            else:
                args.append(self.value(field_ty, env, max(depth - 1, 0)))
        return Construct(ctor, args, ty=ty if data.params else None)

    def call(self, fn: Function, env: list[Binding], depth: int) -> Call:
        args: list[Expr] = []
        for p in fn.params:
            if p.type in NUMERIC:
                args.append(self.value(p.type, env, depth - 1, fit=p.v))
            elif p.type == CHAIN:
                args.append(self.construct(CHAIN, env, depth - 1))
            else:
                args.append(self.value(p.type, env, depth - 1))
        return Call(fn, args)

    def generics_returning(self, ty: str) -> list[Function]:
        """The generics a call at *ty* may instantiate."""
        out = []
        for f in self.functions:
            if not f.forall or self.in_module:
                continue
            if f.template in ("choose",) and (ty in PRIMITIVES or ty in self.data_names(private=True)):
                out.append(f)
            elif f.template == "least" and ty in NUMERIC:
                out.append(f)
            elif f.template == "same" and ty == "Bool":
                out.append(f)
            elif f.template == "unbox" and ty in PRIMITIVES:
                out.append(f)
            elif f.template == "wrap" and ty.startswith("Box<"):
                out.append(f)
        return out

    def generic_call(self, fn: Function, ty: str, env: list[Binding],
                     depth: int) -> Expr | None:
        """A call of *fn* at *ty*: every argument at the type variable is of
        the instantiation exactly, which its constraint admits."""
        if fn.template == "same":
            t = self.rng.choice(["Int", "Nat", "Bool"] + self.data_names(private=True))
        elif fn.template == "wrap":
            t = split_type(ty)[1][0]
        else:
            t = ty
        inst = {"T": t}
        args: list[Expr] = []
        for p in fn.params:
            pty = subst(p.type, inst)
            if pty == "Bool" and p.type == "Bool":
                arg = self.expr("Bool", env, max(depth - 1, 0))
            elif pty.startswith("Box<"):
                boxes = self.refs(env, pty)
                arg = (Ref(self.rng.choice(boxes)) if boxes and self.chance(0.7)
                       else Construct(self.find_data(BOX).ctors[1], [], ty=pty))
            else:
                arg = self.exact(pty, env, depth - 1)
            if arg is None:
                return None
            args.append(arg)
        return Call(fn, args, inst)

    def if_(self, ty: str, env: list[Binding], depth: int) -> If | None:
        cond = self.expr("Bool", env, depth - 1)
        if cond is None:
            return None
        then = self.block(ty, env, depth - 1, lets=self.rng.choice([0, 0, 1]))
        other = self.block(ty, env, depth - 1, lets=self.rng.choice([0, 0, 1]))
        e = If(cond, then, other)
        return e if self._keeps(ty, e) else None

    def guard(self, ty: str, env: list[Binding], depth: int) -> Guarded | None:
        """An element read under the bound that proves its index: an
        ``Int`` element itself, or a ``match`` on an ``Option<Nat>`` or a
        data element."""
        arrays = [b for b in env if self._indexable(b, ty)]
        b = self.rng.choice(arrays)
        assert isinstance(b.value, ArrayLit)
        nats = [x for x in self.refs(env, "Nat") if x.value is None]
        idx: Expr = (Ref(self.rng.choice(nats)) if nats and self.chance(0.6)
                     else Lit(self.rng.randint(0, len(b.value.items))))
        arr = Ref(b)
        elem = b.value.elem
        if elem == "Int":
            then: Expr = Index(arr, idx)
        elif elem == "Option<Nat>":
            payloads = [iv(x.args[0], "r") for x in b.value.items  # type: ignore[attr-defined]
                        if isinstance(x, Construct) and x.args]
            # An element read is opaque to the verifier, its sign included.
            n = Binding("Nat", ANY, _hull_all(payloads) or Iv(0, 0))
            then = Match(Index(arr, idx), [
                Arm(Pattern(ctor=SOME, binders=[n]), self.arm_body(ty, env + [n], depth - 1)),
                Arm(Pattern(ctor=NONE), self.arm_body(ty, env, depth - 1))])
        else:
            then = self._data_match(Index(arr, idx), self.find_data(elem), ty, env, depth)
        e = Guarded(arr, idx, then, self.arm_body(ty, env, depth - 1))
        return e if self._keeps(ty, e) else None

    def _data_match(self, scrutinee: Expr, data: Data, ty: str,
                    env: list[Binding], depth: int, inst: dict[str, str] | None = None
                    ) -> Match:
        arms: list[Arm] = []
        ctors = list(data.ctors)
        wildcard_from = (self.rng.randint(1, len(ctors) - 1)
                         if len(ctors) > 1 and self.chance(0.3) else len(ctors))
        for ctor in ctors[:wildcard_from]:
            binders: list[Binding | None] = []
            for field_ty in ctor.fields:
                field_ty = subst(field_ty, inst or {})
                if self.chance(0.2):
                    binders.append(None)
                elif field_ty in NUMERIC:
                    binders.append(Binding(field_ty, _default(field_ty),
                                           Iv(*FIELD_R[field_ty])))
                else:
                    binders.append(Binding(field_ty))
            scope = env + [b for b in binders if b is not None]
            arms.append(Arm(Pattern(ctor=ctor, binders=binders),
                            self.arm_body(ty, scope, depth - 1)))
        if wildcard_from < len(ctors):
            arms.append(Arm(Pattern(), self.arm_body(ty, env, depth - 1)))
        return Match(scrutinee, arms)

    def match(self, ty: str, env: list[Binding], depth: int, *,
              how: str | None = None) -> Match | None:
        adts = [d for d in self.datas + (self.module.datas if self.module and not self.in_module else [])
                if not d.params and d.name != CHAIN
                and (self.refs(env, d.name) or self.chance(0.4))]
        boxes = [b for b in env if b.type.startswith("Box<")]
        tuples = [b for b in env if b.type.startswith("Tuple<")]
        options = [b for b in env if b.type == "Option<Int>"]
        maps = [b for b in env if isinstance(b.value, MapBuild)]
        how = how or self.pick([("adt", 3.0 if adts else 0.0), ("int", 1.0), ("bool", 0.6),
                         ("box", 1.0 if boxes else 0.0),
                         ("tuple", 1.0 if tuples else 0.0),
                         ("option", 1.0 if options else 0.0),
                         ("map", 4.0 if maps else 0.0)])
        if how == "adt":
            data = self.rng.choice(adts)
            refs = self.refs(env, data.name)
            scrutinee: Expr = (Ref(self.rng.choice(refs)) if refs and self.chance(0.7)
                               else self.construct(data.name, env, depth - 1))
            e = self._data_match(scrutinee, data, ty, env, depth)
            return e if self._keeps(ty, e) else None
        if how == "box":
            b = self.rng.choice(boxes)
            inst = {"T": split_type(b.type)[1][0]}
            e = self._data_match(Ref(b), self.find_data(BOX), ty, env, depth, inst)
            return e if self._keeps(ty, e) else None
        if how == "tuple":
            b = self.rng.choice(tuples)
            types = split_type(b.type)[1]
            value = b.value
            binders: list[Binding | None] = []
            for n, t in enumerate(types):
                if t in NUMERIC:
                    r = (iv(value.args[n], "r") if isinstance(value, Construct)
                         else Iv(*FIELD_R[t]))
                    binders.append(Binding(t, _default(t), r))
                else:
                    binders.append(Binding(t))
            scope = env + [x for x in binders if x is not None]
            e = Match(Ref(b), [Arm(Pattern(ctor=tuple_ctor(types), binders=binders),
                                   self.arm_body(ty, scope, depth - 1))])
            return e if self._keeps(ty, e) else None
        if how in ("option", "map"):
            if how == "option":
                b = self.rng.choice(options)
                inner = b.value.args if isinstance(b.value, Construct) else []
                r = iv(inner[0], "r") if inner else Iv(*FIELD_R["Int"])
                scrutinee = Ref(b)
            else:
                b = self.rng.choice(maps)
                m = _map_of(Ref(b))
                r = _hull_all([iv(v, "r") for _, v in m.entries]) or Iv(0, 0)
                keys = [k for k, _ in m.entries]
                key = self.rng.choice(keys) if self.chance(0.75) else self.rng.choice(list(MAP_KEYS))
                scrutinee = MapGet(Ref(b), key)
            n = Binding("Int", ANY, r)
            e = Match(scrutinee, [
                Arm(Pattern(ctor=SOME, binders=[n]), self.arm_body(ty, env + [n], depth - 1)),
                Arm(Pattern(ctor=NONE), self.arm_body(ty, env, depth - 1))])
            return e if self._keeps(ty, e) else None
        if how == "int":
            number = self.expr("Int", env, max(depth - 2, 0))
            if number is None:
                return None
            # Distinct literals drawn from a pool by `randrange` alone, whose
            # sequence every Python version keeps for a seed.
            pool = list(range(0, 6))
            literals = sorted(pool.pop(self.rng.randrange(len(pool)))
                              for _ in range(self.rng.randint(1, 3)))
            arms = [Arm(Pattern(literal=n), self.arm_body(ty, env, depth - 1))
                    for n in literals]
            arms.append(Arm(Pattern(), self.arm_body(ty, env, depth - 1)))
            e = Match(number, arms)
            return e if self._keeps(ty, e) else None
        flag = self.expr("Bool", env, max(depth - 2, 0))
        if flag is None:
            return None
        arms = [Arm(Pattern(literal=True), self.arm_body(ty, env, depth - 1)),
                Arm(Pattern(literal=False), self.arm_body(ty, env, depth - 1))]
        e = Match(flag, arms)
        return e if self._keeps(ty, e) else None

    def handle_state(self, ty: str, env: list[Binding], depth: int) -> Handle | None:
        """``handle[State<C>]`` with the canonical clauses, over a body that
        writes the cell first and reads it after: by a helper's call where
        one of its cell is declared, and the cell of a helper no call names
        yet, first."""
        waiting = [f for f in self.functions if f.kind == "state" and id(f) not in self.called]
        cell = (_cell_of(self.rng.choice(waiting)) if waiting and self.chance(0.8)
                else self.rng.choice(list(NUMERIC)))
        init = self.cell_value(cell, env, depth - 2)
        saved = self.row, self.handled
        self.row, self.handled = self.row + (f"State<{cell}>",), True
        try:
            helpers = [f for f in self.functions if f.effects == f"<State<{cell}>>"]
            first: Do = (Do(self.call(self._helper(helpers), env, depth - 1))
                         if helpers and self.chance(0.9)
                         else Do(Put(cell, self.cell_value(cell, env, depth - 2))))
            rest = self.block(ty, env, depth - 1, lets=self.rng.choice([0, 1, 2]))
        finally:
            self.row, self.handled = saved
        e = Handle("State", cell, init, Block([first] + rest.lets, rest.result))
        return e if self._keeps(ty, e) else None

    def handle_exn(self, ty: str, env: list[Binding], depth: int) -> Handle | None:
        """``handle[Exn<C>]`` over a body that may throw, directly or through
        a helper, and a clause over the payload: the cell of a helper no
        call names yet, first, where its value fits the position."""
        def fits(f: Function) -> bool:
            return f.kind == "exn" and (f.ret == ty or ty == "Int" and f.ret == "Nat")

        waiting = [f for f in self.functions if fits(f) and id(f) not in self.called]
        cell = (_cell_of(self.rng.choice(waiting)) if waiting and self.chance(0.8)
                else self.rng.choice(list(NUMERIC)))
        saved = self.row, self.handled
        self.row, self.handled = self.row + (f"Exn<{cell}>",), True
        try:
            helpers = [f for f in self.functions
                       if fits(f) and f.effects == f"<Exn<{cell}>>"]
            if helpers and self.chance(0.9):
                body = Block([], self.call(self._helper(helpers), env, depth - 1))
            else:
                body = self.block(ty, env, depth - 1, lets=self.rng.choice([0, 1]))
                if not _throws(body) and self.chance(0.6):
                    thrown = self.throw_if(ty, env, depth - 1)
                    if thrown is not None:
                        body = Block(body.lets, thrown)
        finally:
            self.row, self.handled = saved
        payload = Binding(cell, ANY, _throws(body) or Iv(0, 0))
        clause = self.value(ty, env + [payload], max(depth - 2, 0))
        e = Handle("Exn", cell, None, body, payload, clause)
        return e if self._keeps(ty, e) else None

    def _helper(self, helpers: list[Function]) -> Function:
        """One of *helpers* for a call, one no call names yet first."""
        fresh = [f for f in helpers if id(f) not in self.called]
        helper = self.rng.choice(fresh or helpers)
        self.called.add(id(helper))
        return helper

    def throw_if(self, ty: str, env: list[Binding], depth: int) -> If | None:
        cells = [r[4:-1] for r in self.row if r.startswith("Exn<")]
        if not cells:
            return None
        cell = self.rng.choice(cells)
        cond = self.expr("Bool", env, max(depth - 1, 0))
        if cond is None:
            return None
        payload = self.field_value(cell, env, depth)
        e = If(cond, Block([], Throw(cell, payload)),
               Block([], self.value(ty, env, max(depth - 1, 0))))
        return e if self._keeps(ty, e) else None

    def arm_body(self, ty: str, env: list[Binding], depth: int) -> Expr:
        """An arm's body: an expression, or an ``if``, a ``match`` or a
        handler, with no ``let`` of its own."""
        return self.value(ty, env, depth, block=self.chance(0.25))

    def _keeps(self, ty: str, e: Expr) -> bool:
        """Whether *e*, built for a *ty* position, still has a type that
        position takes and an *R* no run overflows."""
        try:
            t = static_type(e)
        except TypeError:
            return False
        if ty == "Nat" and t != "Nat":
            return False
        if ty in NUMERIC:
            return iv(e, "r").safe()
        return t == ty


def iv_or_none(e: Expr, which: str) -> Iv | None:
    try:
        return iv(e, which)
    except (AssertionError, TypeError, KeyError):
        return None


def _nontrivial(fn: Function) -> bool:
    """Whether *fn* states a contract other than ``true``: the tester
    skips a function that does not."""
    return (any(p.type in NUMERIC and p.refined is None for p in fn.params)
            or any(p.refined is not None for p in fn.params)
            or ensure_style(fn) != "none" or fn.measure is not None)


def generate(seed: int) -> Program:
    """The program *seed* writes."""
    return _Generator(seed).program()


def program(seed: int) -> str:
    """The text of the entry *seed* writes."""
    return generate(seed).render()


def imports(prog: Program) -> list[str]:
    """What the entry imports from the module: each module function it
    calls, then the data type when it names it, in declaration order."""
    if prog.module is None:
        return []
    called: set[int] = set()
    names_data = False
    lib = {id(f) for f in prog.module.functions}
    tally = {d.name for d in prog.module.datas}
    for fn in prog.functions:
        for f in [fn, *fn.helpers]:
            if any(p.type in tally for p in f.params) or f.ret in tally:
                names_data = True
            for node in _walk(f.body):
                if isinstance(node, Call) and id(node.fn) in lib:
                    called.add(id(node.fn))
                elif isinstance(node, Construct) and node.ctor.data in tally:
                    names_data = True
                elif isinstance(node, Pattern) and node.ctor is not None and (
                        node.ctor.data in tally):
                    names_data = True
                elif isinstance(node, Let) and split_type(node.binding.type)[0] in tally:
                    names_data = True
                elif isinstance(node, Let) and any(
                        a in tally for a in split_type(node.binding.type)[1]):
                    names_data = True
    out = [f.name for f in prog.module.functions if id(f) in called]
    if names_data:
        out += [d.name for d in prog.module.datas]
    return out


# =====================================================================
# Rendering, in vera fmt's canonical form
# =====================================================================

PREC = {"||": 3, "&&": 4, "==": 5, "!=": 5, "<": 6, "<=": 6, ">": 6,
        ">=": 6, "+": 7, "-": 7, "*": 8, "/": 8, "%": 8}


class RenderError(Exception):
    """The program cannot be written: a reference outside its scope."""


def _prec(e: Expr) -> int:
    if isinstance(e, Bin):
        return PREC[e.op]
    if isinstance(e, (Neg, Not)):
        return 9
    if isinstance(e, Lit) and not isinstance(e.value, bool) and e.value < 0:
        return 9
    return 10


def _slot(b: Binding, env: list[Binding]) -> str:
    if b.view_of is not None:
        b = b.view_of
    for n in range(len(env) - 1, -1, -1):
        if env[n] is b:
            index = sum(1 for later in env[n + 1:] if later.slot_name == b.slot_name)
            return f"@{b.slot_name}.{index}"
    raise RenderError(f"a @{b.slot_name} binding is referenced outside its scope")


def _args(args: list[Expr], env: list[Binding], contract: bool) -> str:
    return ", ".join(inline(a, env, contract=contract) for a in args)


def inline(e: Expr, env: list[Binding], *, contract: bool = False) -> str:
    """*e* on one line.  In a contract, a ``let`` is written as its value,
    since a contract sees only the parameters."""
    if isinstance(e, Lit):
        if isinstance(e.value, bool):
            return "true" if e.value else "false"
        return str(e.value)
    if isinstance(e, Ref):
        if contract and e.binding.value is not None:
            return inline(_Paren(e.binding.value), env, contract=True)
        return _slot(e.binding, env)
    if isinstance(e, _Paren):
        return inline(e.inner, env, contract=contract)
    if isinstance(e, Bin):
        p = PREC[e.op]
        left = inline(e.left, env, contract=contract)
        right = inline(e.right, env, contract=contract)
        # The arithmetic and logical operators group to the left; a
        # comparison groups with nothing (spec §1.5), so a comparison
        # standing as either operand of one at its level is parenthesised:
        # `(0 == -5) != true`, never `0 == -5 != true`, which the parser
        # refuses (E005).
        if _effective_prec(e.left, contract) < p or (
                e.op in COMPARE and _effective_prec(e.left, contract) == p):
            left = f"({left})"
        if _effective_prec(e.right, contract) <= p:
            right = f"({right})"
        return f"{left} {e.op} {right}"
    if isinstance(e, (Neg, Not)):
        inner = inline(e.operand, env, contract=contract)
        if _effective_prec(e.operand, contract) < 10:
            inner = f"({inner})"
        return ("-" if isinstance(e, Neg) else "!") + inner
    if isinstance(e, Call):
        return f"{e.fn.name}({_args(e.args, env, contract)})"
    if isinstance(e, Construct):
        if not e.args:
            return e.ctor.name
        return f"{e.ctor.name}({_args(e.args, env, contract)})"
    if isinstance(e, Builtin):
        return f"{e.name}({_args(e.args, env, contract)})"
    if isinstance(e, Get):
        return "get(())"
    if isinstance(e, Put):
        return f"put({inline(e.value, env, contract=contract)})"
    if isinstance(e, Throw):
        return f"throw({inline(e.value, env, contract=contract)})"
    if isinstance(e, ArrayLit):
        return f"[{_args(e.items, env, contract)}]"
    if isinstance(e, MapBuild):
        out = "map_new()"
        for key, value in e.entries:
            out = f'map_insert({out}, "{key}", {inline(value, env, contract=contract)})'
        return out
    if isinstance(e, SetBuild):
        out = "set_new()"
        for item in e.items:
            out = f"set_add({out}, {inline(item, env, contract=contract)})"
        return out
    if isinstance(e, Length):
        return f"array_length({inline(e.arr, env, contract=contract)})"
    if isinstance(e, Index):
        return (f"{inline(e.arr, env, contract=contract)}"
                f"[{inline(e.idx, env, contract=contract)}]")
    if isinstance(e, Fold):
        body = inline(e.body, env + [e.acc, e.elem], contract=contract)
        return (f"array_fold({inline(e.arr, env, contract=contract)}, "
                f"{inline(e.init, env, contract=contract)}, "
                f"fn(@Int, @Int -> @Int) effects(pure) {{ {body} }})")
    if isinstance(e, MapGet):
        return f'map_get({inline(e.map, env, contract=contract)}, "{e.key}")'
    if isinstance(e, SetHas):
        return (f"set_contains({inline(e.set, env, contract=contract)}, "
                f"{inline(e.item, env, contract=contract)})")
    if isinstance(e, SetSize):
        return f"set_size({inline(e.set, env, contract=contract)})"
    if isinstance(e, Bound):
        return (f"{{ let @{e.type} = {inline(e.value, env, contract=contract)}; "
                f"@{e.type}.0 }}")
    raise RenderError(f"{type(e).__name__} cannot be written on one line")


@dataclass(eq=False)
class _Paren(Expr):
    """A ``let``'s value standing for its reference in a contract."""

    inner: Expr


def _effective_prec(e: Expr, contract: bool) -> int:
    if contract and isinstance(e, Ref) and e.binding.value is not None:
        return _effective_prec(e.binding.value, contract)
    if isinstance(e, _Paren):
        return _effective_prec(e.inner, contract)
    return _prec(e)


def _expr_lines(e: Expr, env: list[Binding], ind: str, head: str,
                tail: str) -> list[str]:
    """*e* written from the end of *head*, a line indented *ind*, closing
    with *tail*: on one line, or an ``if``, ``match`` or ``handle`` laid out
    as ``vera fmt`` lays it out."""
    inner = ind + "  "
    if isinstance(e, If):
        return (
            [f"{head}if {inline(e.cond, env)} then {{"]
            + _block_lines(e.then, env, inner)
            + [f"{ind}}} else {{"]
            + _block_lines(e.other, env, inner)
            + [f"{ind}}}{tail}"])
    if isinstance(e, Guarded):
        cond = Bin("<", e.idx, Length(e.arr))
        return (
            [f"{head}if {inline(cond, env)} then {{"]
            + _block_lines(Block([], e.then), env, inner)
            + [f"{ind}}} else {{"]
            + _block_lines(Block([], e.other), env, inner)
            + [f"{ind}}}{tail}"])
    if isinstance(e, Match):
        lines = [f"{head}match {inline(e.scrutinee, env)} {{"]
        for n, arm in enumerate(e.arms):
            scope = env + [b for b in arm.pattern.binders if b is not None]
            comma = "," if n < len(e.arms) - 1 else ""
            lines += _expr_lines(arm.body, scope, inner,
                                 f"{inner}{_pattern(arm.pattern)} -> ", comma)
        return lines + [f"{ind}}}{tail}"]
    if isinstance(e, Handle):
        cell = f"@{e.cell}"
        if e.kind == "State":
            assert e.init is not None
            lines = [f"{head}handle[State<{e.cell}>]({cell} = {inline(e.init, env)}) {{",
                     f"{inner}get(@Unit) -> {{ resume({cell}.0) }},",
                     f"{inner}put({cell}) -> {{ resume(()) }}"]
        else:
            assert e.payload is not None and e.clause is not None
            clause = inline(e.clause, env + [e.payload])
            lines = [f"{head}handle[Exn<{e.cell}>] {{",
                     f"{inner}throw({cell}) -> {{ {clause} }}"]
        return (lines + [f"{ind}}} in {{"] + _block_lines(e.body, env, inner)
                + [f"{ind}}}{tail}"])
    if isinstance(e, Bound) and isinstance(e.value, (If, Guarded, Match, Handle)):
        return ([f"{head}{{"]
                + _expr_lines(e.value, env, inner, f"{inner}let @{e.type} = ", ";")
                + [f"{inner}@{e.type}.0", f"{ind}}}{tail}"])
    return [f"{head}{inline(e, env)}{tail}"]


def _pattern(p: Pattern) -> str:
    if p.ctor is not None:
        if not p.ctor.fields:
            return p.ctor.name
        parts = [f"@{b.spelled}" if b is not None else "_" for b in p.binders]
        return f"{p.ctor.name}({', '.join(parts)})"
    if p.literal is None:
        return "_"
    if isinstance(p.literal, bool):
        return "true" if p.literal else "false"
    return str(p.literal)


def _block_lines(block: Block, env: list[Binding], ind: str) -> list[str]:
    scope = list(env)
    lines: list[str] = []
    for stmt in block.lets:
        if isinstance(stmt, Do):
            lines += _expr_lines(stmt.expr, scope, ind, ind, ";")
            continue
        b = stmt.binding
        assert b.value is not None
        lines += _expr_lines(b.value, scope, ind, f"{ind}let @{b.spelled} = ", ";")
        scope.append(b)
    return lines + _expr_lines(block.result, scope, ind, ind, "")


def _type(t: str) -> str:
    return f"@{t}"


def _requires(fn: Function) -> list[str]:
    if fn.contract is not None:
        return [c for c in fn.contract if c.startswith("requires")]
    parts: list[str] = []
    for p in fn.params:
        if p.type not in NUMERIC or p.v is None or p.refined is not None:
            continue
        ref = _slot(p, fn.params)
        if p.type == "Nat" and p.v.lo == 0:
            parts.append(f"{ref} <= {p.v.hi}")
        else:
            parts.append(f"{ref} >= {p.v.lo} && {ref} <= {p.v.hi}")
    if not parts:
        return ["requires(true)"]
    if fn.split_requires:
        return [f"requires({part})" for part in parts]
    return [f"requires({' && '.join(parts)})"]


def closed_form(fn: Function) -> Expr:
    """A linear recursion's value: its base case plus the measure times its
    step."""
    assert fn.measure is not None
    return Bin("+", _base(fn), Bin("*", Ref(fn.measure), Lit(fn.step)))


def _ensures(fn: Function) -> list[str]:
    if fn.broken:
        return ["ensures(false)"]
    if fn.contract is not None:
        return [c for c in fn.contract if c.startswith("ensures")]
    style = ensure_style(fn)
    result = f"@{fn.ret}.result"
    if style == "none":
        return ["ensures(true)"]
    if style == "exact":
        # A contract sees the parameters alone: each `let` is written as its
        # value, so every reference left is a parameter's.
        stated_expr = closed_form(fn) if fn.template == "linear" else fn.body.result
        stated = inline(stated_expr, list(fn.params), contract=True)
        return [f"ensures({result} == {_wrap_compare(stated_expr, stated)})"]
    body = body_v(fn)
    lower = f"{result} >= {body.lo}"
    upper = f"{result} <= {body.hi}"
    if style == "lower":
        return [f"ensures({lower})"]
    if style == "upper":
        return [f"ensures({upper})"]
    if fn.split_ensures:
        return [f"ensures({lower})", f"ensures({upper})"]
    return [f"ensures({lower} && {upper})"]


def _wrap_compare(e: Expr, text: str) -> str:
    """The right operand of ``==``: parenthesised where its operator binds
    no tighter than ``==`` (a comparison or a logical one)."""
    return f"({text})" if _effective_prec(e, True) <= PREC["=="] else text


def _signature(fn: Function, *, helper: bool = False) -> str:
    params = ", ".join(_type(p.spelled) for p in fn.params)
    arrow = f"{params} -> " if params else "-> "
    head = "" if helper else ("public " if fn.public else "private ")
    if fn.forall:
        where = f" where {', '.join(fn.constraints)}" if fn.constraints else ""
        head += f"forall<{', '.join(fn.forall)}{where}> "
    return f"{head}fn {fn.name}({arrow}{_type(fn.ret)})"


def _function_lines(fn: Function, *, helper: bool = False) -> list[str]:
    lines = [_signature(fn, helper=helper)]
    clauses = _requires(fn) + _ensures(fn)
    if fn.measure is not None:
        clauses.append(f"decreases({_slot(fn.measure, fn.params)})")
    lines += [f"  {clause}" for clause in clauses]
    lines += [f"  effects({fn.effects})", "{"]
    lines += _block_lines(fn.body, list(fn.params), "  ")
    lines.append("}")
    if fn.helpers:
        lines.append("where {")
        for n, h in enumerate(fn.helpers):
            if n:
                lines.append("")
            lines += [f"  {line}" if line else "" for line in _function_lines(h, helper=True)]
        lines.append("}")
    return lines


def _literal(value: int | bool) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    return str(value)


def _print(fn: Function) -> str:
    call = f"{fn.name}({', '.join(_literal(a) for a in fn.example)})"
    if fn.print_style == "interp":
        return f'  IO.print("\\({call})\\n");'
    show = {"Int": "int_to_string", "Nat": "nat_to_string",
            "Bool": "bool_to_string"}[fn.ret]
    return f'  IO.print(string_concat({show}({call}), "\\n"));'


def _main_lines(prog: Program) -> list[str]:
    return (["public fn main(@Unit -> @Unit)", "  requires(true)",
             "  ensures(true)", "  effects(<IO>)", "{"]
            + [_print(fn) for fn in prog.prints]
            + ["  ()", "}"])


def _data_lines(data: Data) -> list[str]:
    visibility = "public" if data.public else "private"
    params = f"<{', '.join(data.params)}>" if data.params else ""
    lines = [f"{visibility} data {data.name}{params} {{"]
    for n, ctor in enumerate(data.ctors):
        comma = "," if n < len(data.ctors) - 1 else ""
        fields_ = f"({', '.join(ctor.fields)})" if ctor.fields else ""
        lines.append(f"  {ctor.name}{fields_}{comma}")
    return lines + ["}"]


def _alias_lines(alias: Alias) -> list[str]:
    if alias.refined is None:
        return [f"type {alias.name} = {alias.target};"]
    t, r = alias.target, alias.refined
    if t == "Nat" and r.lo == 0:
        pred = f"@Nat.0 <= {r.hi}"
    else:
        pred = f"@{t}.0 >= {r.lo} && @{t}.0 <= {r.hi}"
    return [f"type {alias.name} = {{ @{t} | {pred} }};"]


def render(prog: Program) -> str:
    """*prog*'s entry, as ``vera fmt`` writes it."""
    blocks: list[list[str]] = []
    names = imports(prog)
    if names:
        blocks.append([f"import {MODULE_NAME}({', '.join(names)});"])
    blocks += [_alias_lines(a) for a in prog.aliases]
    blocks += [_data_lines(d) for d in prog.datas]
    blocks += [_function_lines(f) for f in prog.functions]
    blocks.append(_main_lines(prog))
    return "\n\n".join("\n".join(b) for b in blocks) + "\n"


def render_module(prog: Program) -> str:
    """The module's text, as ``vera fmt`` writes it."""
    assert prog.module is not None
    blocks = [[f"module {MODULE_NAME};"]]
    blocks += [_data_lines(d) for d in prog.module.datas]
    blocks += [_function_lines(f) for f in prog.module.functions]
    return "\n\n".join("\n".join(b) for b in blocks) + "\n"


# =====================================================================
# The counterfactual of #1525's class
# =====================================================================

def name_constructed_types(prog: Program) -> Program | None:
    """*prog* with each function first binding an unused ``let @D`` for
    every data type ``D`` it constructs and does not name in its signature,
    or ``None`` when no function constructs one.

    The verifier finds a data type's sort by walking a function's signature
    and its ``let``s rather than reading the checker's types (#1525), so a
    construction of a type the function names nowhere does not translate,
    and a call taking it loses the callee's postcondition.  The ``let`` is a
    construction of literals, legal at the function's start, and adds one
    binding of ``D`` and of no other type, so nothing else of the program
    moves."""
    cand = copy.deepcopy(prog)
    changed = False
    datas = all_datas(cand)
    for fn in all_functions(cand):
        if fn.forall:
            continue
        named = {p.type for p in fn.params} | {fn.ret}
        built: list[str] = []
        for node in _walk(fn.body):
            if isinstance(node, Construct) and node.ctor.data not in (
                    "Option", "Tuple", "Ordering"):
                ty = node.ty or node.ctor.data
                if ty not in named and ty not in built:
                    built.append(ty)
        for ty in reversed(built):
            fn.body.lets.insert(0, Let(Binding(ty, value=_stand_in(ty, None, datas))))
            changed = True
    return cand if changed else None


# =====================================================================
# The counterfactual of code generation's own reading of a value's type
# =====================================================================

#: What :func:`bind_in_place` binds: each fold that is not a ``let``'s
#: value, which code generation finds no type for as a scrutinee, a
#: constructor's argument or a branch's arm, and each argument at a
#: generic's type variable (#1525's class), and each handler that is a
#: branch's value (#1744's).  Each is bound at the type the checker gives
#: it, a fold's being its initial value's.
BIND_FOLD = "fold"
BIND_ARGUMENT = "argument"
BIND_HANDLER_ARM = "handler_arm"
BIND_KINDS = (BIND_FOLD, BIND_ARGUMENT, BIND_HANDLER_ARM)


def _mentions(ty: str, variables: list[str]) -> bool:
    return any(re.search(rf"\b{re.escape(v)}\b", ty) for v in variables)


def bind_in_place(prog: Program, kinds: Collection[str]) -> Program | None:
    """*prog* with each value of *kinds* (:data:`BIND_KINDS`) bound in place
    by a ``let`` of the type the checker gives it, ``{ let @Int = ...;
    @Int.0 }``, which code generation reads off the declaration, and every
    contract as *prog* writes it; ``None`` when *prog* holds no such value.

    The ``let`` holds the value where it stood, so the program computes what
    *prog* computes and the verifier sees what it saw: a find *prog* makes
    and this program does not is code generation's own reading of the
    value's type (#1525's class, or #1744's for a handler)."""
    cand = copy.deepcopy(prog)
    functions = all_functions(cand)
    # Every contract is read before any is fixed: a fixed one is written as
    # given, and a caller's `ensures` reads its callee's as the verifier does.
    contracts = [_requires(fn) + _ensures(fn) for fn in functions]
    for fn, contract in zip(functions, contracts):
        fn.contract = contract
    changed = False

    def bind(e: Expr, ty: str) -> Expr:
        nonlocal changed
        changed = True
        return Bound(e, ty)

    def arm(e: Expr) -> Expr:
        e = walk(e)
        if BIND_HANDLER_ARM in kinds and isinstance(e, Handle):
            return bind(e, static_type(e))
        return e

    def block(b: Block, *, branch: bool = False) -> None:
        for stmt in b.lets:
            if isinstance(stmt, Do):
                stmt.expr = walk(stmt.expr)
            elif stmt.binding.value is not None:
                stmt.binding.value = walk(stmt.binding.value, let=True)
        b.result = arm(b.result) if branch else walk(b.result)

    def walk(e: Expr, *, let: bool = False) -> Expr:
        if isinstance(e, If):
            e.cond = walk(e.cond)
            block(e.then, branch=True)
            block(e.other, branch=True)
            return e
        if isinstance(e, Match):
            e.scrutinee = walk(e.scrutinee)
            for a in e.arms:
                a.body = arm(a.body)
            return e
        if isinstance(e, Guarded):
            e.then, e.other = arm(e.then), arm(e.other)
            return e
        if isinstance(e, Handle):
            if e.init is not None:
                e.init = walk(e.init)
            block(e.body)
            if e.clause is not None:
                e.clause = walk(e.clause)
            return e
        if isinstance(e, Fold):
            # The closure's body reads its own two parameters alone.
            e.init = walk(e.init)
            return bind(e, static_type(e)) if BIND_FOLD in kinds and not let else e
        for f in fields(e):
            value = getattr(e, f.name)
            if isinstance(value, Expr):
                setattr(e, f.name, walk(value))
            elif isinstance(value, list):
                setattr(e, f.name, [
                    walk(x) if isinstance(x, Expr)
                    else (x[0], walk(x[1])) if isinstance(x, tuple) else x
                    for x in value])
        if isinstance(e, Call) and e.fn.forall and BIND_ARGUMENT in kinds:
            e.args = [bind(a, subst(p.type, e.inst)) if _mentions(p.type, e.fn.forall)
                      else a for p, a in zip(e.fn.params, e.args)]
        return e

    for fn in functions:
        block(fn.body)
    return cand if changed else None


# =====================================================================
# What the generator expects of a program
# =====================================================================

def slot_names(fn: Function) -> list[str]:
    """Each parameter's slot, as a contract and the tester spell it."""
    return [_slot(p, fn.params) for p in fn.params]


def evaluate(fn: Function, args: list[int | bool]) -> int | bool | None:
    """*fn*'s value on *args*, where its ``ensures`` is exact (a
    straight-line body, or a linear recursion's closed form); ``None``
    where it is not."""
    if ensure_style(fn) != "exact" or len(args) != len(fn.params):
        return None
    values: dict[int, int | bool] = {
        id(p): (bool(a) if p.type == "Bool" else int(a))
        for p, a in zip(fn.params, args)}

    def run(e: Expr) -> int | bool:
        if isinstance(e, Lit):
            return e.value
        if isinstance(e, Ref):
            bound = e.binding.view_of or e.binding
            if id(bound) in values:
                return values[id(bound)]
            assert bound.value is not None
            return run(bound.value)
        if isinstance(e, Neg):
            return -int(run(e.operand))
        if isinstance(e, Not):
            return not run(e.operand)
        assert isinstance(e, Bin)
        left, right = run(e.left), run(e.right)
        if e.op == "&&":
            return bool(left) and bool(right)
        if e.op == "||":
            return bool(left) or bool(right)
        if e.op in ("==", "!="):
            return (left == right) == (e.op == "==")
        x, y = int(left), int(right)
        if e.op in ("<", "<=", ">", ">="):
            return {"<": x < y, "<=": x <= y, ">": x > y, ">=": x >= y}[e.op]
        if e.op == "+":
            return x + y
        if e.op == "-":
            return x - y
        if e.op == "*":
            return x * y
        if e.op == "/":
            return trunc_div(x, y)
        return x - trunc_div(x, y) * y

    return run(closed_form(fn) if fn.template == "linear" else fn.body.result)


def expectations(prog: Program, focus: str = "",
                 args: list[int | bool] | None = None) -> list[dict[str, object]]:
    """What the generator wrote each function of *prog* to satisfy: its
    contract as written, the interval the verifier can see and the one a
    run can reach, and, for *focus* on *args*, the value an exact
    ``ensures`` states."""
    out: list[dict[str, object]] = []
    for fn in all_functions(prog):
        entry: dict[str, object] = {
            "function": fn.name, "signature": _signature(fn),
            "requires": _requires(fn), "ensures": _ensures(fn),
            "style": ensure_style(fn),
        }
        if fn.ret in NUMERIC and not fn.forall:
            v, r = iv_or_none(fn.body.result, "v"), iv_or_none(fn.body.result, "r")
            v = body_v(fn) if fn.summary_v is not None else v
            r = body_r(fn) if fn.summary_r is not None else r
            entry["visible"] = [v.lo, v.hi] if v is not None else None
            entry["reach"] = [r.lo, r.hi] if r is not None else None
        if fn.name == focus and args is not None:
            entry["args"] = list(args)
            entry["expected"] = evaluate(fn, args)
        out.append(entry)
    return out


# =====================================================================
# Shape: what a program is made of
# =====================================================================

#: Every construct the grammar writes, as :func:`shape` counts it: version
#: one's, then version two's.
CONSTRUCTS = (
    "data_enum", "data_fields", "data_nested", "fn_public", "fn_private",
    "param_Int", "param_Nat", "param_Bool", "param_data", "nullary",
    "let", "let_narrowing", "if", "match_ctor", "match_wildcard",
    "match_literal", "binder", "call", "construct", "+", "-", "*", "/lit",
    "%lit", "/var", "%var", "nat_sub", "neg", "compare", "&&", "||", "!",
    "ensures_exact", "ensures_bounds", "ensures_one_side", "print",
    "fn_recursive", "decreases_nat", "decreases_data", "mutual_where",
    "fn_generic", "forall_ord", "forall_eq", "data_generic", "data_recursive",
    "alias_head", "alias_argument", "alias_refined", "refined_param",
    "refined_let", "module", "import_fn", "import_data", "array_int",
    "array_option_nat", "array_data", "map_string_int", "set_nat", "tuple",
    "array_length", "index_guarded", "array_fold", "map_get_match",
    "handle_state_int", "handle_state_nat", "handle_exn", "throw",
    "state_helper", "exn_helper", "noncommutative",
)


def _walk(value: object) -> Iterator[object]:
    """Every IR node below *value*, a ``let``'s value included, each once: a
    ``let``'s value is reached through its :class:`Let`, never again through
    a reference to it."""
    if isinstance(value, (Function, Ctor, Data, Program, Module, Alias)):
        return
    if isinstance(value, Ref):
        yield value
        return
    if isinstance(value, Binding):
        if value.value is not None:
            yield from _walk(value.value)
        return
    if is_dataclass(value):
        yield value
        for f in fields(value):
            yield from _walk(getattr(value, f.name))
    elif isinstance(value, (list, tuple)):
        for item in value:
            yield from _walk(item)
    elif isinstance(value, dict):
        for item in value.values():
            yield from _walk(item)


def _alias_names(prog: Program) -> set[str]:
    return {a.name for a in prog.aliases}


def shape(prog: Program) -> dict[str, int]:
    """How many of each construct of :data:`CONSTRUCTS` *prog* holds."""
    count = dict.fromkeys(CONSTRUCTS, 0)
    aliases = _alias_names(prog)
    refined = {a.name for a in prog.aliases if a.refined is not None}
    for d in all_datas(prog):
        if d.params:
            count["data_generic"] += 1
        elif d.name == CHAIN:
            count["data_recursive"] += 1
        elif all(not c.fields for c in d.ctors):
            count["data_enum"] += 1
        else:
            count["data_fields"] += 1
        if any(t not in PRIMITIVES and t != CHAIN and t not in d.params
               for c in d.ctors for t in c.fields):
            count["data_nested"] += 1
    count["alias_refined"] = len(refined)
    if prog.module is not None:
        count["module"] = 1
        names = imports(prog)
        count["import_data"] = sum(1 for n in names if n == TALLY)
        count["import_fn"] = len(names) - count["import_data"]
    for fn in all_functions(prog):
        count["fn_public" if fn.public else "fn_private"] += 1
        if not fn.params:
            count["nullary"] += 1
        for p in fn.params:
            _count_binding(p, count, aliases, refined, param=True)
            count[f"param_{p.type}" if p.type in PRIMITIVES else "param_data"] += 1
        if fn.measure is not None:
            count["fn_recursive"] += 1
            count["decreases_nat" if fn.measure.type == "Nat" else "decreases_data"] += 1
        if fn.helpers:
            count["mutual_where"] += 1
        if fn.forall:
            count["fn_generic"] += 1
            count["forall_ord"] += "Ord<T>" in fn.constraints
            count["forall_eq"] += "Eq<T>" in fn.constraints
        if fn.kind == "noncomm":
            count["noncommutative"] += 1
        style = ensure_style(fn)
        if style == "exact":
            count["ensures_exact"] += 1
        elif style == "bounds":
            count["ensures_bounds"] += 1
        elif style in ("lower", "upper"):
            count["ensures_one_side"] += 1
        for node in _walk(fn.body):
            _count_node(node, count, aliases, refined)
    count["print"] = len(prog.prints)
    return count


def _count_binding(b: Binding, count: dict[str, int], aliases: set[str],
                   refined: set[str], *, param: bool) -> None:
    written = b.spelled
    if written in refined:
        count["refined_param" if param else "refined_let"] += 1
    elif written in aliases:
        count["alias_head"] += 1
    elif any(a in aliases for a in split_type(written)[1]):
        count["alias_argument"] += 1


def _count_node(node: object, count: dict[str, int], aliases: set[str],
                refined: set[str]) -> None:
    if isinstance(node, Let):
        count["let"] += 1
        _count_binding(node.binding, count, aliases, refined, param=False)
        value = node.binding.value
        if node.binding.type == "Nat" and value is not None and static_type(value) == "Int":
            count["let_narrowing"] += 1
        container = {"Array<Int>": "array_int", "Array<Option<Nat>>": "array_option_nat",
                     "Map<String, Int>": "map_string_int", "Set<Nat>": "set_nat"}
        ty = node.binding.type
        if ty in container:
            count[container[ty]] += 1
        elif ty.startswith("Array<"):
            count["array_data"] += 1
        elif ty.startswith("Tuple<"):
            count["tuple"] += 1
    elif isinstance(node, If):
        count["if"] += 1
    elif isinstance(node, Match):
        first = node.arms[0].pattern
        if isinstance(node.scrutinee, MapGet):
            count["map_get_match"] += 1
        if first.ctor is not None:
            count["match_ctor"] += 1
            if node.arms[-1].pattern.ctor is None:
                count["match_wildcard"] += 1
        else:
            count["match_literal"] += 1
        count["binder"] += sum(
            1 for arm in node.arms for b in arm.pattern.binders if b is not None)
    elif isinstance(node, Call):
        count["call"] += 1
        if node.fn.kind in ("state", "exn"):
            count[f"{node.fn.kind}_helper"] += 1
    elif isinstance(node, Construct):
        count["construct"] += 1
    elif isinstance(node, Bin):
        if node.op in ("/", "%"):
            literal = isinstance(node.right, Lit)
            count[f"{node.op}{'lit' if literal else 'var'}"] += 1
        elif node.op == "-" and static_type(node) == "Nat":
            count["nat_sub"] += 1
            count["-"] += 1
        elif node.op in ("+", "-", "*", "&&", "||"):
            count[node.op] += 1
        else:
            count["compare"] += 1
    elif isinstance(node, Neg):
        count["neg"] += 1
    elif isinstance(node, Not):
        count["!"] += 1
    elif isinstance(node, Length):
        count["array_length"] += 1
    elif isinstance(node, Guarded):
        count["index_guarded"] += 1
        count["array_length"] += 1
    elif isinstance(node, Fold):
        count["array_fold"] += 1
    elif isinstance(node, Handle):
        count["handle_exn" if node.kind == "Exn"
              else f"handle_state_{node.cell.lower()}"] += 1
    elif isinstance(node, Throw):
        count["throw"] += 1


def nodes(fn: Function) -> Iterator[object]:
    """Every IR node of *fn*'s body, each once."""
    return _walk(fn.body)


def size(prog: Program) -> int:
    """How much *prog* holds: declarations, prints and expression nodes."""
    fns = all_functions(prog)
    count = sum(1 for fn in fns for _ in _walk(fn.body))
    return (len(all_datas(prog)) + len(prog.aliases) + len(fns)
            + len(prog.prints) + count)


# =====================================================================
# Minimising a program while a find holds
# =====================================================================

def _stand_in(ty: str, r: Iv | None, datas: list[Data]) -> Expr:
    """A literal (or a construction of literals) of type *ty* inside *r*."""
    if ty == "Bool":
        return Lit(True)
    if ty in NUMERIC:
        assert r is not None and r.lo is not None and r.hi is not None
        return Lit(min(max(0, r.lo), r.hi))
    head, args = split_type(ty)
    data = next(d for d in datas if d.name == head)
    inst = dict(zip(data.params, args))
    ctor = min(data.ctors, key=lambda c: len(c.fields))
    return Construct(ctor, [
        _stand_in(subst(t, inst), Iv(*FIELD_R[subst(t, inst)])
                  if subst(t, inst) in NUMERIC else None, datas)
        for t in ctor.fields
    ], ty=ty if data.params else None)


def _replace(value: object, old: object, new: Expr) -> object:
    """*value* with every occurrence of the node *old* replaced by *new*
    (a reference to a binding, *old* a :class:`Binding`, by a copy of
    *new*)."""
    if isinstance(old, Binding) and isinstance(value, Ref) and value.binding is old:
        return _clone(new)
    if value is old:
        return new
    if isinstance(value, (Function, Ctor, Data, Module, Alias)):
        return value
    if isinstance(value, Binding):
        if value.value is not None:
            value.value = _replace(value.value, old, new)  # type: ignore[assignment]
        return value
    if is_dataclass(value) and not isinstance(value, type):
        for f in fields(value):
            setattr(value, f.name, _replace(getattr(value, f.name), old, new))
        return value
    if isinstance(value, list):
        return [_replace(item, old, new) for item in value]
    if isinstance(value, tuple):
        return tuple(_replace(item, old, new) for item in value)
    return value


def _clone(e: Expr) -> Expr:
    """A copy of *e* sharing the bindings it reads but owning the ones it
    defines (a pattern's binders, a branch's ``let``s)."""
    memo: dict[int, object] = {}

    def keep(value: object) -> None:
        if isinstance(value, (Function, Ctor, Data, Module, Alias)):
            memo[id(value)] = value
        elif isinstance(value, Ref) and not _defined_inside(value.binding, e):
            memo[id(value.binding)] = value.binding
            if value.binding.view_of is not None:
                memo[id(value.binding.view_of)] = value.binding.view_of
        elif isinstance(value, Binding):
            if value.value is not None:
                keep(value.value)
        if is_dataclass(value) and not isinstance(value, (type, Function, Ctor, Data, Binding)):
            for f in fields(value):
                keep(getattr(value, f.name))
        elif isinstance(value, (list, tuple)):
            for item in value:
                keep(item)

    keep(e)
    return copy.deepcopy(e, memo)


def _defined_inside(b: Binding, e: object) -> bool:
    for node in _walk(e):
        if isinstance(node, Pattern) and any(x is b for x in node.binders):
            return True
        if isinstance(node, Let) and node.binding is b:
            return True
        if isinstance(node, Fold) and b in (node.acc, node.elem):
            return True
        if isinstance(node, Handle) and node.payload is b:
            return True
    return False


def _references(prog: Program, data: Data) -> bool:
    if any(data.name in c.fields for d in all_datas(prog) for c in d.ctors
           if d is not data):
        return True
    for fn in all_functions(prog):
        if any(split_type(p.type)[0] == data.name for p in fn.params) or (
                split_type(fn.ret)[0] == data.name):
            return True
        for node in _walk(fn.body):
            if isinstance(node, Construct) and node.ctor.data == data.name:
                return True
            if isinstance(node, Pattern) and node.ctor is not None and (
                    node.ctor.data == data.name):
                return True
            if isinstance(node, Let) and data.name in node.binding.type:
                return True
            if isinstance(node, ArrayLit) and node.elem == data.name:
                return True
    return False


def _expressions(prog: Program) -> Iterator[tuple[Function, Expr]]:
    """Every expression of every function, outermost first."""
    for fn in all_functions(prog):
        for node in _walk(fn.body):
            if isinstance(node, Expr):
                yield fn, node


def _smaller(e: Expr, prog: Program) -> list[Expr]:
    """Simpler expressions that could stand where *e* stands: a branch, an
    operand, a handler's or a fold's literal of its type."""
    out: list[Expr] = []
    try:
        ty = static_type(e)
    except TypeError:
        return out
    if ty in ("Unit", "Never") or ty.startswith(("Array<", "Map<", "Set<", "Tuple<",
                                                  "Option<", "Ordering")):
        return out
    if "T" in split_type(ty)[1] or ty == "T":
        return out
    if isinstance(e, If):
        out += [b.result for b in (e.then, e.other)
                if not b.lets and not isinstance(b.result, Throw)]
    if isinstance(e, Guarded):
        out.append(e.other)
    if isinstance(e, Match):
        out += [arm.body for arm in e.arms if not any(arm.pattern.binders)]
    if isinstance(e, Bin) and e.op in ARITH + LOGIC:
        out += [e.left, e.right] if e.op not in ("*",) else [e.left]
    if isinstance(e, (Neg, Not)):
        out.append(e.operand)
    if not isinstance(e, (Lit, Ref)) or isinstance(e, Ref) and ty in NUMERIC:
        r = iv_or_none(e, "r") if ty in NUMERIC else None
        if ty not in NUMERIC or (r is not None and r.bounded()):
            try:
                out.append(_stand_in(ty, r, all_datas(prog)))
            except StopIteration:
                pass
    return out


def _drop_calls(cand: Program, gone: Function) -> None:
    """Every call of *gone* in *cand* replaced by a literal of its type."""
    for _, node in list(_expressions(cand)):
        if isinstance(node, Call) and node.fn is gone:
            ty = static_type(node)
            if ty in ("Unit",):
                continue
            _replace_everywhere(cand, node, _stand_in(
                ty, iv_or_none(node, "r") if ty in NUMERIC else None, all_datas(cand)))
    for fn in all_functions(cand):
        for block in [fn.body, *(n for n in _walk(fn.body) if isinstance(n, Block))]:
            block.lets = [s for s in block.lets
                          if not (isinstance(s, Do) and isinstance(s.expr, Call)
                                  and s.expr.fn is gone)]


def reductions(prog: Program) -> Iterator[Program]:
    """Every program one step smaller than *prog*, the largest steps first:
    a function dropped (a literal standing in for each call), a module
    function and the module, a data declaration nothing names, one of
    ``main``'s prints, a statement, a ``let`` (inlined), a public function
    made private, an expression replaced by a smaller one.  Each is a copy;
    *prog* is left as it was."""
    for n in range(len(prog.functions) - 1, -1, -1):
        cand = copy.deepcopy(prog)
        gone = cand.functions[n]
        _drop_calls(cand, gone)
        cand.functions.pop(n)
        cand.prints = [f for f in cand.prints if f is not gone]
        yield cand
    if prog.module is not None:
        for n in range(len(prog.module.functions) - 1, -1, -1):
            cand = copy.deepcopy(prog)
            assert cand.module is not None
            gone = cand.module.functions[n]
            if len(cand.module.functions) == 1:
                continue
            _drop_calls(cand, gone)
            cand.module.functions.pop(n)
            yield cand
        if not imports(prog):
            cand = copy.deepcopy(prog)
            cand.module = None
            yield cand
    for n in range(len(prog.datas) - 1, -1, -1):
        cand = copy.deepcopy(prog)
        if not _references(cand, cand.datas[n]):
            cand.datas.pop(n)
            yield cand
    for n in range(len(prog.aliases) - 1, -1, -1):
        cand = copy.deepcopy(prog)
        name = cand.aliases[n].name
        used = any(
            b.spelled == name or name in split_type(b.spelled)[1]
            for fn in all_functions(cand)
            for b in fn.params + [node.binding for node in _walk(fn.body)
                                  if isinstance(node, Let)])
        if not used:
            cand.aliases.pop(n)
            yield cand
    for n in range(len(prog.prints) - 1, -1, -1):
        cand = copy.deepcopy(prog)
        cand.prints.pop(n)
        yield cand
    for i, fn in enumerate(all_functions(prog)):
        for j, stmt in enumerate(_statements(fn)):
            if isinstance(stmt, Do):
                cand = copy.deepcopy(prog)
                target = _statements(all_functions(cand)[i])[j]
                _drop_stmt(all_functions(cand)[i], target)
                yield cand
    for i, fn in enumerate(all_functions(prog)):
        for j in range(len(_lets(fn))):
            cand = copy.deepcopy(prog)
            target = _lets(all_functions(cand)[i])[j]
            value = target.binding.value
            assert value is not None
            _drop_stmt(all_functions(cand)[i], target)
            _replace_everywhere(cand, target.binding, value)
            yield cand
    for i, fn in enumerate(prog.functions):
        if fn.public:
            cand = copy.deepcopy(prog)
            cand.functions[i].public = False
            cand.prints = [f for f in cand.prints if f is not cand.functions[i]]
            yield cand
    for k, (_fn, e) in enumerate(list(_expressions(prog))):
        for m, _ in enumerate(_smaller(e, prog)):
            cand = copy.deepcopy(prog)
            node = list(_expressions(cand))[k][1]
            replacement = _smaller(node, cand)[m]
            _replace_everywhere(cand, node, replacement)
            yield cand


def _statements(fn: Function) -> list[Let | Do]:
    out: list[Let | Do] = []
    for node in [fn.body, *_walk(fn.body)]:
        if isinstance(node, Block):
            out.extend(node.lets)
    return out


def _lets(fn: Function) -> list[Let]:
    return [node for node in _walk(fn.body) if isinstance(node, Let)]


def _drop_stmt(fn: Function, target: Let | Do) -> None:
    for node in [fn.body, *_walk(fn.body)]:
        if isinstance(node, Block) and target in node.lets:
            node.lets.remove(target)
            return


def _drop_let(fn: Function, target: Let) -> None:
    _drop_stmt(fn, target)


def _replace_everywhere(prog: Program, old: object, new: Expr) -> None:
    for fn in all_functions(prog):
        fn.body = _replace(fn.body, old, new)  # type: ignore[assignment]


def well_formed(prog: Program) -> bool:
    """Whether *prog* keeps the invariants the generator writes by, which
    the checker cannot see: a value in a ``@Nat`` position the verifier can
    show is non-negative, an argument inside its callee's ``requires``, a
    ``@Nat`` subtraction whose operands cannot cross, a divisor the verifier
    sees is positive, a field inside its construction range, a cell's value
    inside :data:`CELL_R`, a fold from a ``Nat`` whose run stays
    non-negative, a recursion in its template with its measure
    decreasing, an instantiation its constraint admits, an effect only where
    a handler or a row admits it, an index only under its bound, a fold's
    closure reading its own parameters alone, and no value a run can reach
    beyond :data:`SAFE`.  The minimiser keeps to them, so a minimal program
    is one the generator could have written, and a find cannot slide to a
    program whose contract is false."""
    try:
        refresh(prog)
        for fn in all_functions(prog):
            if not _fn_ok(fn):
                return False
        for fn in prog.prints:
            if not fn.public:
                return False
    except (AssertionError, TypeError, StopIteration, KeyError, IndexError):
        return False
    return True


def _fn_ok(fn: Function) -> bool:
    """Whether *fn* keeps the generator's invariants (:func:`well_formed`)."""
    if fn.group is not None and not _templated(fn):
        return False
    if fn.ret == "Nat" and not fn.forall and not _nat_value(fn.body.result):
        return False
    if fn.ret in NUMERIC and not fn.forall and not body_r(fn).safe():
        return False
    if fn.group is not None and not _templated(fn):
        return False
    if fn.group is not None and fn.ret in NUMERIC:
        v = body_v(fn)
        if not iv(_base(fn), "v").within(v.lo, v.hi):
            return False
    for stmt in fn.body.lets:
        if isinstance(stmt, Let) and stmt.binding.value is None:
            return False
    row = (fn.effects[1:-1],) if fn.effects != "pure" else ()
    return _ok(fn.body, row, set(), fn)


def _key(e: Expr) -> object:
    if isinstance(e, Ref):
        return ("ref", id(e.binding.view_of or e.binding))
    if isinstance(e, Lit):
        return ("lit", e.value)
    return ("node", id(e))


def _ok(value: object, row: tuple[str, ...], guards: set[tuple[object, object]],
        fn: Function) -> bool:
    """Whether every node below *value* keeps the invariants, under the
    effects *row* admits and the indexes *guards* bound."""
    if isinstance(value, (Function, Ctor, Data, Module, Alias)):
        return True
    if isinstance(value, Ref):
        return True
    if isinstance(value, Binding):
        return value.value is None or _ok(value.value, row, guards, fn)
    if isinstance(value, Handle):
        if not _node_ok(value, row, fn):
            return False
        inner = row + (f"{value.kind}<{value.cell}>",)
        return ((value.init is None or _ok(value.init, row, guards, fn))
                and _ok(value.body, inner, guards, fn)
                and (value.clause is None or _ok(value.clause, row, guards, fn)))
    if isinstance(value, Guarded):
        if not _node_ok(value, row, fn):
            return False
        bound = guards | {(_key(value.arr), _key(value.idx))}
        return (_ok(value.idx, row, guards, fn) and _ok(value.then, row, bound, fn)
                and _ok(value.other, row, guards, fn))
    if isinstance(value, Index):
        return (_key(value.arr), _key(value.idx)) in guards
    if isinstance(value, Fold):
        if not _node_ok(value, row, fn):
            return False
        return _ok(value.init, row, guards, fn) and _closure_ok(value)
    if is_dataclass(value) and not isinstance(value, type):
        if not _node_ok(value, row, fn):
            return False
        return all(_ok(getattr(value, f.name), row, guards, fn) for f in fields(value))
    if isinstance(value, (list, tuple)):
        return all(_ok(item, row, guards, fn) for item in value)
    if isinstance(value, dict):
        return all(_ok(item, row, guards, fn) for item in value.values())
    return True


def _closure_ok(fold: Fold) -> bool:
    for node in _walk(fold.body):
        if isinstance(node, Ref) and node.binding not in (fold.acc, fold.elem):
            return False
        if isinstance(node, (Call, Get, Throw, Handle, Fold, Guarded, Match, If)):
            return False
        if isinstance(node, Bin) and node.op in ("/", "%") and not isinstance(node.right, Lit):
            return False
    return True


def _chain_depth(e: Expr) -> int:
    if isinstance(e, Construct) and e.ctor.data == CHAIN and e.args:
        return 1 + max(_chain_depth(a) for a in e.args)
    return 0


def _nat_value(e: Expr) -> bool:
    t = static_type(e)
    if t == "Nat":
        return True
    v = iv(e, "v")
    return t == "Int" and v.lo is not None and v.lo >= 0


def _node_ok(node: object, row: tuple[str, ...], fn: Function) -> bool:
    if isinstance(node, Let):
        value = node.binding.value
        if value is None:
            return False
        if node.binding.type == "Nat" and not _nat_value(value):
            return False
        if node.binding.refined is not None:
            r = node.binding.refined
            if not iv(value, "v").within(r.lo, r.hi):
                return False
        return True
    if isinstance(node, Expr) and not isinstance(node, (Throw, Put, Index)):
        ty = static_type(node)
        if ty in NUMERIC and not iv(node, "r").safe():
            return False
    if isinstance(node, Bin):
        if node.op == "-" and static_type(node) == "Nat":
            a, b = iv(node.left, "v"), iv(node.right, "v")
            if a.lo is None or b.hi is None or a.lo < b.hi:
                return False
        if node.op in ("/", "%"):
            if isinstance(node.right, Lit):
                return int(node.right.value) >= 1
            d = iv(node.right, "v")
            return d.bounded() and (d.lo or 0) >= 1
        if node.op == "*":
            return isinstance(node.right, Lit)
    if isinstance(node, Fold) and static_type(node) == "Nat":
        # A fold from a `Nat` is a `Nat`: its run stays inside the type.
        r = iv(node, "r")
        return r.lo is not None and r.lo >= 0
    if isinstance(node, Get):
        return f"State<{node.cell}>" in row
    if isinstance(node, Put):
        r = CELL_R[node.cell]
        return (f"State<{node.cell}>" in row and iv(node.value, "r").within(r.lo, r.hi)
                and (node.cell != "Nat" or _nat_value(node.value)))
    if isinstance(node, Throw):
        return (f"Exn<{node.cell}>" in row
                and (node.cell != "Nat" or _nat_value(node.value)))
    if isinstance(node, Call):
        callee = node.fn
        if callee.effects != "pure" and callee.effects[1:-1] not in row:
            return False
        if callee.forall:
            return _instance_ok(node)
        for p, arg in zip(callee.params, node.args):
            if p.type in NUMERIC:
                assert p.v is not None
                if p.type == "Nat" and not _nat_value(arg):
                    return False
                if not iv(arg, "v").within(p.v.lo, p.v.hi):
                    return False
        if fn.group is not None and callee in fn.group:
            k = callee.params.index(callee.measure) if callee.measure else -1
            arg = node.args[k]
            if callee.measure is not None and callee.measure.type == "Nat":
                if not (isinstance(arg, Bin) and arg.op == "-"
                        and isinstance(arg.left, Ref) and arg.left.binding.view_of is not None
                        and isinstance(arg.right, Lit) and arg.right.value == 1):
                    return False
            elif not (isinstance(arg, Ref) and arg.binding.type == CHAIN
                      and arg.binding not in fn.params):
                return False
    if isinstance(node, Construct):
        if node.ctor.data == CHAIN and _chain_depth(node) > CHAIN_DEPTH:
            return False
        inst = {}
        if node.ty is not None:
            data_params = ["T"] if node.ctor.data in (BOX, "Option") else []
            inst = dict(zip(data_params, split_type(node.ty)[1]))
        for t, arg in zip(node.ctor.fields, node.args):
            t = subst(t, inst)
            if t in NUMERIC:
                lo, hi = FIELD_R[t]
                if t == "Nat" and not _nat_value(arg):
                    return False
                if not iv(arg, "r").within(lo, hi):
                    return False
    return True


def _instance_ok(call: Call) -> bool:
    """Whether a generic's call is at an instantiation its constraint
    admits, every argument at the type variable of that type exactly."""
    t = call.inst.get("T")
    if t is None:
        return False
    if "Ord<T>" in call.fn.constraints and t not in NUMERIC:
        return False
    if "Eq<T>" in call.fn.constraints and t not in PRIMITIVES and not t[:1].isupper():
        return False
    for p, arg in zip(call.fn.params, call.args):
        if p.type == "T":
            if static_type(arg) != t:
                return False
        elif p.type == "Box<T>" and static_type(arg) != f"Box<{t}>":
            return False
    return True


def minimize(prog: Program, holds: Callable[[Program], bool], *,
             budget: int = 300) -> Program:
    """The smallest program :func:`reductions` reaches from *prog* while
    *holds* stays true, trying at most *budget* candidates, each of them
    :func:`well_formed` and none the program already held: a nullary
    constructor, or a construction at its stand-in values, is its own
    stand-in, and taking it as a step would restart the reductions on the
    same program.  *prog* itself must hold."""
    current = prog
    held = _text(prog)
    tried = 0
    progress = True
    while progress and tried < budget:
        progress = False
        for cand in reductions(current):
            # Well formed first: the check settles the candidate's summaries,
            # which its contracts are written from.
            if not well_formed(cand):
                continue
            try:
                text = _text(cand)
            except (RenderError, TypeError, AssertionError, KeyError):
                continue
            if text == held:
                continue
            tried += 1
            try:
                ok = holds(cand)
            except Exception:  # noqa: BLE001 — a candidate that crashes a stage is not the find
                ok = False
            if ok:
                current, held = cand, text
                progress = True
                break
            if tried >= budget:
                break
    return current


def _text(prog: Program) -> str:
    """Every file of *prog*, as one text to compare candidates by."""
    return "\n\x00\n".join(prog.files().values())


# =====================================================================
# Edits: the sequence the warm differential sends a session
# =====================================================================

@dataclass(eq=False)
class Edit:
    """One state of the document the sequence moves through: what changed,
    and the program after it."""

    name: str
    program: Program


#: How many edits a sequence makes after the program as written.
EDITS = 4


def edits(prog: Program, count: int = EDITS) -> list[Edit]:
    """The program as written, then *count* edits, each kept well formed:
    a literal moved inside its interval, a ``let`` added, a non-commutative
    pair's operands swapped (its ``ensures`` follows), a function added with
    a call to it, a ``requires`` tightened inside every caller's argument,
    and a contract broken and then restored.  The sequence is the seed's:
    the same program writes the same edits."""
    rng = random.Random(prog.seed * 7919 + 17)
    out = [Edit("the program as written", prog)]
    current = prog
    broken: str | None = None
    tries = 0
    while len(out) < count + 1 and tries < 60:
        tries += 1
        if broken is not None:
            cand = copy.deepcopy(current)
            fn = next(f for f in all_functions(cand) if f.name == broken)
            fn.broken = False
            out.append(Edit(f"restore the ensures of {broken}", cand))
            current, broken = cand, None
            continue
        kind = rng.choice(["literal", "let", "swap", "function", "requires", "break"])
        made = _edit(current, kind, rng)
        if made is None:
            continue
        name, cand = made
        out.append(Edit(name, cand))
        current = cand
        if kind == "break":
            broken = name.rsplit(" ", 1)[-1]
    return out


def _editable(prog: Program) -> list[Function]:
    return [f for f in prog.functions if not f.forall and f.kind not in ("state", "exn")]


def _edit(prog: Program, kind: str, rng: random.Random) -> tuple[str, Program] | None:
    cand = copy.deepcopy(prog)
    fns = _editable(cand)
    if not fns:
        return None
    if kind == "literal":
        sites = [(fn, node) for fn in fns for node in _walk(fn.body)
                 if isinstance(node, Lit) and not isinstance(node.value, bool)]
        rng.shuffle(sites)
        for fn, node in sites[:8]:
            old = node.value
            node.value = int(old) + rng.choice([-1, 1])
            if well_formed(cand) and _renders(cand):
                return f"move a literal of {fn.name} from {old} to {node.value}", cand
            node.value = old
        return None
    if kind == "let":
        fn = rng.choice(fns)
        fn.body.lets.insert(0, Let(Binding("Int", value=Lit(rng.randint(-9, 9)))))
        return (f"add a let to {fn.name}", cand) if well_formed(cand) and _renders(cand) else None
    if kind == "swap":
        swaps = [f for f in fns if f.kind == "noncomm"
                 and isinstance(f.body.result, Bin)]
        if not swaps:
            return None
        fn = rng.choice(swaps)
        e = fn.body.result
        assert isinstance(e, Bin)
        e.left, e.right = e.right, e.left
        return (f"swap the operands of {fn.name}", cand) if well_formed(cand) and _renders(cand) else None
    if kind == "function":
        lo = rng.randint(-10, 10)
        hi = lo + rng.randint(0, 10)
        k = rng.randint(-5, 5)
        p = Binding("Int", Iv(lo, hi), Iv(lo, hi))
        new = Function(f"f{len(cand.functions)}e", False, [p], "Int",
                       Block([], Bin("+", Ref(p), Lit(k))), ensure_style="bounds")
        cand.functions.insert(0, new)
        caller = rng.choice(fns)
        caller.body.lets.insert(0, Let(Binding("Int", value=Call(new, [Lit(rng.randint(lo, hi))]))))
        return (f"add {new.name} and a call to it in {caller.name}", cand) if (
            well_formed(cand) and _renders(cand)) else None
    if kind == "requires":
        options = [(fn, p) for fn in fns for p in fn.params
                   if p.type in NUMERIC and p.refined is None and p.v is not None
                   and p.v.bounded() and (p.v.hi or 0) - (p.v.lo or 0) >= 2]
        rng.shuffle(options)
        for fn, p in options[:6]:
            assert p.v is not None and p.v.lo is not None and p.v.hi is not None
            old = p.v
            p.v = p.r = Iv(p.v.lo, p.v.hi - 1)
            examples_fit = all(
                not isinstance(a, bool) and p.v.lo <= int(a) <= p.v.hi  # type: ignore[operator]
                for q, a in zip(fn.params, fn.example) if q is p)
            if examples_fit and well_formed(cand) and _renders(cand):
                return f"tighten a requires of {fn.name}", cand
            p.v = p.r = old
        return None
    breakable = [f for f in fns if f.ret in PRIMITIVES and f.kind != "helper"]
    if not breakable:
        return None
    fn = rng.choice(breakable)
    fn.broken = True
    return f"break the ensures of {fn.name}", cand


def _renders(prog: Program) -> bool:
    try:
        prog.files()
    except RenderError:
        return False
    return True


# =====================================================================
# The night's report
# =====================================================================

def summarize(directory: Path) -> str:
    """The night's report from the records the generator's cells wrote under
    *directory*: what ran and what it cost, every find with what the
    generator expected and its minimal program, the known classes by issue,
    and what the programs were made of."""
    records = [
        json.loads(p.read_text(encoding="utf-8"))
        for p in sorted((directory / "records").glob("seed-*.json"))
    ]
    found = [r for r in records if "find" in r]
    lines = [f"Programs generated and run: {len(records)}; "
             f"with a find outside the known classes: {len(found)}"]
    if records:
        seeds = sorted(r["seed"] for r in records)
        seconds = [r.get("seconds", 0.0) for r in records]
        lines.append(f"Seeds: {seeds[0]} to {seeds[-1]}; seconds per program: "
                     f"mean {sum(seconds) / len(seconds):.2f}, "
                     f"max {max(seconds):.2f}")
        stats: dict[str, int] = {}
        for r in records:
            for name, n in r.get("stats", {}).items():
                stats[name] = stats.get(name, 0) + n
        lines.append(
            "Distrust run: {tested} of {public} public functions tested, "
            "{exercised} proofs exercised, {trials} trials".format(
                tested=stats.get("public_tested", 0),
                public=stats.get("public", 0),
                exercised=stats.get("proofs_exercised", 0),
                trials=stats.get("trials", 0)))
        lines.append(
            "Warm differential: {edits} edits, {replayed} functions replayed "
            "warm".format(edits=stats.get("warm_edits", 0),
                          replayed=stats.get("warm_replayed_fns", 0)))
        statuses = sorted(k for k in stats if k.startswith("obligation_"))
        lines.append("Obligations: " + ", ".join(
            f"{k.removeprefix('obligation_')} {stats[k]}" for k in statuses))
    known: dict[tuple[str, str], list[int]] = {}
    for r in records:
        for f in r["finds"]:
            if f["known"]:
                known.setdefault((f["known"], f.get("cls", "")), []).append(r["seed"])
    if known:
        lines += ["", "Known classes (counted, not failures):", "",
                  "| Issue | Class | Finds | Programs | Seeds |", "|---|---|---:|---:|---|"]
        for issue, cls in sorted(known):
            seeds = sorted(set(known[(issue, cls)]))
            shown = ", ".join(str(s) for s in seeds[:5])
            if len(seeds) > 5:
                shown += f" and {len(seeds) - 5} more"
            lines.append(f"| {issue} | {cls} | {len(known[(issue, cls)])} | "
                         f"{len(seeds)} | {shown} |")
    if records:
        totals: dict[str, int] = {}
        for r in records:
            for name, n in r["shape"].items():
                totals[name] = totals.get(name, 0) + n
        lines += ["", "Constructs written:", "",
                  ", ".join(f"{name} {totals[name]}" for name in sorted(totals))]
    for r in found:
        find = r["find"]
        lines += ["", f"### Seed {r['seed']}: the {find['differential']} "
                      f"differential, {' '.join(find['signature'])}", "",
                  "```text", find["detail"][:3000], "```", "",
                  "What the generator expected of the minimal program:", "",
                  "| Function | Contract | Visible | Reach | Expected |",
                  "|---|---|---|---|---|"]
        for e in find["expected"]:
            contract = "; ".join(e["requires"] + e["ensures"])
            expected = (f"`{e['expected']}` on {e['args']}"
                        if "expected" in e and e["expected"] is not None
                        else "")
            lines.append(
                f"| `{e['function']}` | `{contract}` | {e.get('visible', '')} | "
                f"{e.get('reach', '')} | {expected} |")
        lines += ["", "Minimal program:", "", "```vera",
                  find["minimal"].rstrip("\n"), "```"]
    return "\n".join(lines) + "\n"


def main(argv: list[str]) -> int:
    if len(argv) == 2 and argv[0] == "summarize":
        sys.stdout.write(summarize(Path(argv[1])))
        return 0
    if len(argv) == 1 and argv[0].isdigit():
        files = generate(int(argv[0])).files()
        if len(files) == 1:
            sys.stdout.write(files[ENTRY])
        else:
            sys.stdout.write("\n".join(f"-- {name}\n{text}" for name, text in files.items()))
        return 0
    sys.stderr.write(
        "usage: python -m tests.program_generator SEED\n"
        "       python -m tests.program_generator summarize DIRECTORY\n")
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
