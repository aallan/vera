"""A type-directed generator of whole Vera programs, version one.

``generate(seed)`` writes a program from a seed: up to three ``data``
declarations, up to six functions whose contracts hold of every input their
``requires`` admits, and a ``main`` that prints the value of each public
function.  ``tests/test_program_generator.py`` runs it through check, verify,
compile, load, the reconciliation join and ``vera test --distrust`` (ROADMAP
Stage 25; TESTING.md § Program Generator).  ``python -m
tests.program_generator SEED`` prints a seed's program.

What makes a program well formed, by construction rather than by retry:

* **Every expression is drawn for a type**, and its static type is the
  checker's (spec §4.4): ``Nat <op> Nat`` is ``Nat``, and any mix with an
  ``Int`` or a literal is ``Int``.  A ``@Nat`` position takes a ``Nat``, or an
  ``Int`` the verifier can show is non-negative: the narrowing is obligated,
  and provable.
* **A slot reference holds its binding, never an index.**  The index is
  computed where the reference is written, as the number of bindings of the
  same type pushed after it (DE_BRUIJN.md §4), over the stack the function
  builds: its parameters, then each ``let``, and inside a ``match`` arm the
  binders of its pattern, left to right.
* **Contracts are true by construction.**  Each numeric expression carries
  two intervals: what the verifier can see (*V*), and what a run of the
  program can reach (*R*).  A field of a data value is unbounded in *V*,
  since the verifier quantifies over every value of the type; a call is what
  the callee's ``ensures`` states; a ``requires`` bounds each numeric
  parameter.  So an ``ensures`` written from *V* holds in the verifier's
  model, an argument whose *V* lies inside the callee's ``requires`` meets
  it, a ``@Nat`` subtraction whose operands' *V* cannot cross is provable,
  and an *R* far inside the 64-bit range means no run overflows.  A
  refutation, a timeout or a failing check is then the generator's bug or
  the toolchain's, never the program's own.

``minimize`` shrinks a program while a predicate holds: it drops functions
(a literal stands in for each call), unreferenced data declarations,
``main``'s prints and ``let``s (inlining each), and replaces expressions by
smaller ones, one change at a time, keeping each the predicate accepts.

``summarize`` reads a night's records (``VERA_GENERATOR_OUT``) into the
report the workflow posts.

Version one leaves out recursion and ``decreases``, generics, type aliases and
refinements, imports, arrays, maps, sets and tuples, ``State`` and ``Exn``
handlers, closures, ``String``, ``Float64`` and ``Byte`` values beyond
``main``'s output, relational preconditions, and the product of two
variables.
"""

from __future__ import annotations

import copy
import json
import random
import sys
from collections.abc import Callable, Iterator
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


# =====================================================================
# The program, as the generator holds it
# =====================================================================

PRIMITIVES = ("Int", "Nat", "Bool")
NUMERIC = ("Int", "Nat")


@dataclass(eq=False)
class Binding:
    """One slot of the stack: a parameter, a ``let``, or a pattern binder.

    A parameter or a binder carries its intervals; a ``let`` reads them off
    its value."""

    type: str
    v: Iv | None = None
    r: Iv | None = None
    value: Expr | None = None


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
class Block:
    lets: list[Let]
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


@dataclass(eq=False)
class Construct(Expr):
    ctor: Ctor
    args: list[Expr]


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


@dataclass(eq=False)
class Program:
    seed: int
    datas: list[Data]
    functions: list[Function]
    #: The public functions ``main`` prints, in order.
    prints: list[Function]

    def render(self) -> str:
        return render(self)

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
    if isinstance(e, Not):
        return "Bool"
    if isinstance(e, If):
        return _join(static_type(e.then.result), static_type(e.other.result))
    if isinstance(e, Match):
        types = [static_type(arm.body) for arm in e.arms]
        out = types[0]
        for t in types[1:]:
            out = _join(out, t)
        return out
    if isinstance(e, Call):
        return e.fn.ret
    if isinstance(e, Construct):
        return e.ctor.data
    raise TypeError(e)


def _join(a: str, b: str) -> str:
    if a == b:
        return a
    if {a, b} <= {"Int", "Nat"}:
        return "Int"
    raise TypeError(f"no join of {a} and {b}")


ARITH = ("+", "-", "*", "/", "%")
COMPARE = ("<", "<=", ">", ">=", "==", "!=")
LOGIC = ("&&", "||")


def iv(e: Expr, which: str) -> Iv:
    """*e*'s interval: ``"v"``, what the verifier can see, or ``"r"``, what
    a run of the program can reach."""
    if isinstance(e, Lit):
        assert not isinstance(e.value, bool)
        return Iv(e.value, e.value)
    if isinstance(e, Ref):
        b = e.binding
        if b.value is not None:
            return iv(b.value, which)
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
        return iv_hull(iv(e.then.result, which), iv(e.other.result, which))
    if isinstance(e, Match):
        out = iv(e.arms[0].body, which)
        for arm in e.arms[1:]:
            out = iv_hull(out, iv(arm.body, which))
        return out
    if isinstance(e, Call):
        return visible(e.fn) if which == "v" else iv(e.fn.body.result, "r")
    raise TypeError(e)


def visible(fn: Function) -> Iv:
    """What the verifier knows of a call's value: what *fn*'s ``ensures``
    states, or its type alone."""
    default = NAT_ANY if fn.ret == "Nat" else ANY
    style = ensure_style(fn)
    if style == "none":
        return default
    body = iv(fn.body.result, "v")
    if style in ("exact", "bounds"):
        return body
    if style == "lower":
        return Iv(body.lo, default.hi)
    return Iv(default.lo, body.hi)


def ensure_style(fn: Function) -> str:
    """The ``ensures`` *fn* writes: its chosen style where the body supports
    it, else the strongest one it does."""
    if fn.ret not in NUMERIC:
        if fn.ret == "Bool" and fn.ensure_style == "exact" and straight(fn.body):
            return "exact"
        return "none"
    if fn.ensure_style == "exact" and straight(fn.body):
        return "exact"
    body = iv(fn.body.result, "v")
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
    return all(flat(let.binding.value) for let in block.lets
               if let.binding.value is not None) and flat(block.result)


# =====================================================================
# Writing the program
# =====================================================================

_DATA_NAMES = ("Shape", "Gauge", "Crate")
_CTOR_NAMES = (
    "Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf", "Hotel",
    "India", "Juliet", "Kilo", "Lima", "Mike", "November", "Oscar", "Papa",
    "Quebec", "Romeo", "Sierra", "Tango", "Uniform", "Victor", "Whiskey",
    "Xray", "Yankee", "Zulu")


class _Generator:
    """One program from one seed.  Every choice is the seed's ``Random``."""

    def __init__(self, seed: int) -> None:
        self.seed = seed
        self.rng = random.Random(seed)
        self.datas: list[Data] = []
        self.functions: list[Function] = []
        self._ctor_names = list(_CTOR_NAMES)

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

    # -- declarations --------------------------------------------------

    def program(self) -> Program:
        for i in range(self.rng.choice([0, 1, 1, 2, 2, 3])):
            self.datas.append(self.data(i))
        count = self.rng.randint(2, 6)
        for i in range(count):
            self.functions.append(self.function(i, last=i == count - 1))
        prints = [f for f in self.functions if f.public]
        return Program(self.seed, self.datas, self.functions, prints)

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

    def param(self, ty: str) -> Binding:
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

    def function(self, i: int, *, last: bool) -> Function:
        public = last or self.chance(0.5)
        types = list(PRIMITIVES) + ([] if public else [d.name for d in self.datas])
        params = [self.param(self.rng.choice(types))
                  for _ in range(self.rng.choice([0, 1, 1, 2, 2, 3]))]
        ret = self.rng.choice(types)
        env = list(params)
        body = self.block(ret, env, depth=3, lets=self.rng.choice([0, 1, 1, 2, 3]))
        fn = Function(
            name=f"f{i}", public=public, params=params, ret=ret, body=body,
            ensure_style=self.pick([("exact", 3), ("bounds", 4), ("lower", 1),
                                    ("upper", 1), ("none", 1)]),
            split_requires=self.chance(0.4), split_ensures=self.chance(0.4),
            print_style=self.rng.choice(["interp", "concat"]))
        fn.example = [
            (self.rng.randint(p.v.lo, p.v.hi) if p.v is not None
             and p.v.lo is not None and p.v.hi is not None
             else self.chance(0.5))
            for p in params
        ]
        if public and not _nontrivial(fn):
            fn.public = False
        return fn

    # -- blocks and expressions -----------------------------------------

    def block(self, ty: str, env: list[Binding], depth: int, lets: int) -> Block:
        scope = list(env)
        out: list[Let] = []
        for _ in range(lets):
            let_ty = self.rng.choice(list(PRIMITIVES) + [d.name for d in self.datas])
            value = self.value(let_ty, scope, depth - 1, block=True)
            binding = Binding(let_ty, value=value)
            out.append(Let(binding))
            scope.append(binding)
        return Block(out, self.value(ty, scope, depth, block=True))

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

    def refs(self, env: list[Binding], *types: str) -> list[Binding]:
        return [b for b in env if b.type in types]

    def callees(self, *types: str) -> list[Function]:
        return [f for f in self.functions if f.ret in types]

    def expr(self, ty: str, env: list[Binding], depth: int, *,
             block: bool = False) -> Expr | None:
        """An expression whose static type is *ty* (or ``Nat`` for ``Int``:
        widening is free), or ``None`` when none can be written here."""
        if ty in NUMERIC:
            return self.numeric(ty, env, depth, block)
        if ty == "Bool":
            return self.boolean(env, depth, block)
        return self.adt(ty, env, depth, block)

    def numeric(self, ty: str, env: list[Binding], depth: int,
                block: bool) -> Expr | None:
        nat = ty == "Nat"
        refs = self.refs(env, "Nat") if nat else self.refs(env, "Int", "Nat")
        calls = self.callees("Nat") if nat else self.callees("Int", "Nat")
        options = [("ref", 4.0 if refs else 0.0)]
        if not nat:
            options.append(("lit", 2.0))
        if depth > 0:
            options += [("add", 2.0), ("sub", 2.0 if not nat else 1.5),
                        ("call", 2.0 if calls else 0.0)]
            if not nat:
                options += [("mul", 1.5), ("divlit", 0.7), ("modlit", 0.7),
                            ("neg", 0.6)]
            options += [("divvar", 0.5), ("modvar", 0.3)]
            if block:
                options += [("if", 1.2), ("match", 1.2)]
        if sum(w for _, w in options) == 0:
            return None
        kind = self.pick(options)
        sub = "Nat" if nat else "Int"
        if kind == "ref":
            return Ref(self.rng.choice(refs))
        if kind == "lit":
            return Lit(self.rng.randint(-9, 9))
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
        if kind == "if":
            return self.if_(ty, env, depth)
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

    def boolean(self, env: list[Binding], depth: int, block: bool) -> Expr | None:
        refs = self.refs(env, "Bool")
        calls = self.callees("Bool")
        options = [("ref", 3.0 if refs else 0.0), ("lit", 1.0)]
        if depth > 0:
            options += [("cmp", 4.0), ("and", 1.0), ("or", 1.0), ("not", 0.7),
                        ("eq", 0.5 if refs else 0.0),
                        ("call", 1.5 if calls else 0.0)]
            if block:
                options += [("if", 0.6), ("match", 0.6)]
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
        if kind == "if":
            return self.if_("Bool", env, depth)
        return self.match("Bool", env, depth)

    def adt(self, ty: str, env: list[Binding], depth: int, block: bool) -> Expr | None:
        refs = self.refs(env, ty)
        calls = self.callees(ty)
        options = [("ref", 3.0 if refs else 0.0), ("construct", 2.0)]
        if depth > 0:
            options += [("call", 1.5 if calls else 0.0)]
            if block:
                options += [("if", 0.5), ("match", 0.5)]
        kind = self.pick(options)
        if kind == "ref":
            return Ref(self.rng.choice(refs))
        if kind == "construct":
            return self.construct(ty, env, depth)
        if kind == "call":
            return self.call(self.rng.choice(calls), env, depth)
        if kind == "if":
            return self.if_(ty, env, depth)
        return self.match(ty, env, depth)

    def construct(self, ty: str, env: list[Binding], depth: int) -> Construct:
        data = next(d for d in self.datas if d.name == ty)
        ctor = self.rng.choice(data.ctors)
        args: list[Expr] = []
        for field_ty in ctor.fields:
            if field_ty in NUMERIC:
                lo, hi = FIELD_R[field_ty]
                e = self.value(field_ty, env, depth - 1, fit=None)
                if not iv(e, "r").within(lo, hi):
                    e = self.literal(field_ty, Iv(lo if field_ty == "Nat" else -9, 9))
                args.append(e)
            else:
                args.append(self.value(field_ty, env, max(depth - 1, 0)))
        return Construct(ctor, args)

    def call(self, fn: Function, env: list[Binding], depth: int) -> Call:
        args = [
            self.value(p.type, env, depth - 1, fit=p.v) if p.type in NUMERIC
            else self.value(p.type, env, depth - 1)
            for p in fn.params
        ]
        return Call(fn, args)

    def if_(self, ty: str, env: list[Binding], depth: int) -> If | None:
        cond = self.expr("Bool", env, depth - 1)
        if cond is None:
            return None
        then = self.block(ty, env, depth - 1, lets=self.rng.choice([0, 0, 1]))
        other = self.block(ty, env, depth - 1, lets=self.rng.choice([0, 0, 1]))
        e = If(cond, then, other)
        return e if self._keeps(ty, e) else None

    def match(self, ty: str, env: list[Binding], depth: int) -> Match | None:
        adts = [d for d in self.datas
                if self.refs(env, d.name) or self.chance(0.4)]
        how = self.pick([("adt", 3.0 if adts else 0.0), ("int", 1.0), ("bool", 0.6)])
        if how == "adt":
            data = self.rng.choice(adts)
            refs = self.refs(env, data.name)
            scrutinee: Expr = (Ref(self.rng.choice(refs)) if refs and self.chance(0.7)
                               else self.construct(data.name, env, depth - 1))
            arms: list[Arm] = []
            ctors = list(data.ctors)
            wildcard_from = (self.rng.randint(1, len(ctors) - 1)
                             if len(ctors) > 1 and self.chance(0.3) else len(ctors))
            for ctor in ctors[:wildcard_from]:
                binders: list[Binding | None] = []
                for field_ty in ctor.fields:
                    if self.chance(0.2):
                        binders.append(None)
                        continue
                    if field_ty in NUMERIC:
                        r = Iv(*FIELD_R[field_ty])
                        binders.append(Binding(
                            field_ty, NAT_ANY if field_ty == "Nat" else ANY, r))
                    else:
                        binders.append(Binding(field_ty))
                scope = env + [b for b in binders if b is not None]
                body = self.arm_body(ty, scope, depth - 1)
                arms.append(Arm(Pattern(ctor=ctor, binders=binders), body))
            if wildcard_from < len(ctors):
                arms.append(Arm(Pattern(), self.arm_body(ty, env, depth - 1)))
            e = Match(scrutinee, arms)
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

    def arm_body(self, ty: str, env: list[Binding], depth: int) -> Expr:
        """An arm's body: an expression, or an ``if`` or ``match``, with no
        ``let`` of its own."""
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


def _nontrivial(fn: Function) -> bool:
    """Whether *fn* states a contract other than ``true``: the tester
    skips a function that does not."""
    return any(p.type in NUMERIC for p in fn.params) or ensure_style(fn) != "none"


def generate(seed: int) -> Program:
    """The program *seed* writes."""
    return _Generator(seed).program()


def program(seed: int) -> str:
    """The text of the program *seed* writes."""
    return generate(seed).render()


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
    for n in range(len(env) - 1, -1, -1):
        if env[n] is b:
            index = sum(1 for later in env[n + 1:] if later.type == b.type)
            return f"@{b.type}.{index}"
    raise RenderError(f"a @{b.type} binding is referenced outside its scope")


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
        if _effective_prec(e.left, contract) < p:
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
        return f"{e.fn.name}({', '.join(inline(a, env, contract=contract) for a in e.args)})"
    if isinstance(e, Construct):
        if not e.args:
            return e.ctor.name
        return f"{e.ctor.name}({', '.join(inline(a, env, contract=contract) for a in e.args)})"
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
    with *tail*: on one line, or an ``if`` or ``match`` laid out as
    ``vera fmt`` lays it out."""
    if isinstance(e, If):
        inner = ind + "  "
        return (
            [f"{head}if {inline(e.cond, env)} then {{"]
            + _block_lines(e.then, env, inner)
            + [f"{ind}}} else {{"]
            + _block_lines(e.other, env, inner)
            + [f"{ind}}}{tail}"])
    if isinstance(e, Match):
        inner = ind + "  "
        lines = [f"{head}match {inline(e.scrutinee, env)} {{"]
        for n, arm in enumerate(e.arms):
            scope = env + [b for b in arm.pattern.binders if b is not None]
            comma = "," if n < len(e.arms) - 1 else ""
            lines += _expr_lines(arm.body, scope, inner,
                                 f"{inner}{_pattern(arm.pattern)} -> ", comma)
        return lines + [f"{ind}}}{tail}"]
    return [f"{head}{inline(e, env)}{tail}"]


def _pattern(p: Pattern) -> str:
    if p.ctor is not None:
        if not p.ctor.fields:
            return p.ctor.name
        parts = [f"@{b.type}" if b is not None else "_" for b in p.binders]
        return f"{p.ctor.name}({', '.join(parts)})"
    if p.literal is None:
        return "_"
    if isinstance(p.literal, bool):
        return "true" if p.literal else "false"
    return str(p.literal)


def _block_lines(block: Block, env: list[Binding], ind: str) -> list[str]:
    scope = list(env)
    lines: list[str] = []
    for let in block.lets:
        b = let.binding
        assert b.value is not None
        lines += _expr_lines(b.value, scope, ind, f"{ind}let @{b.type} = ", ";")
        scope.append(b)
    return lines + _expr_lines(block.result, scope, ind, ind, "")


def _type(t: str) -> str:
    return f"@{t}"


def _requires(fn: Function) -> list[str]:
    parts: list[str] = []
    for p in fn.params:
        if p.type not in NUMERIC or p.v is None:
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


def _ensures(fn: Function) -> list[str]:
    style = ensure_style(fn)
    result = f"@{fn.ret}.result"
    if style == "none":
        return ["ensures(true)"]
    if style == "exact":
        # A contract sees the parameters alone: each `let` is written as its
        # value, so every reference left is a parameter's.
        stated = inline(fn.body.result, list(fn.params), contract=True)
        return [f"ensures({result} == {_wrap_compare(fn.body.result, stated)})"]
    body = iv(fn.body.result, "v")
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


def _signature(fn: Function) -> str:
    params = ", ".join(_type(p.type) for p in fn.params)
    arrow = f"{params} -> " if params else "-> "
    visibility = "public" if fn.public else "private"
    return f"{visibility} fn {fn.name}({arrow}{_type(fn.ret)})"


def _function_lines(fn: Function) -> list[str]:
    lines = [_signature(fn)]
    lines += [f"  {clause}" for clause in _requires(fn) + _ensures(fn)]
    lines += ["  effects(pure)", "{"]
    lines += _block_lines(fn.body, list(fn.params), "  ")
    return lines + ["}"]


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
    lines = [f"{visibility} data {data.name} {{"]
    for n, ctor in enumerate(data.ctors):
        comma = "," if n < len(data.ctors) - 1 else ""
        fields_ = f"({', '.join(ctor.fields)})" if ctor.fields else ""
        lines.append(f"  {ctor.name}{fields_}{comma}")
    return lines + ["}"]


def render(prog: Program) -> str:
    """*prog*'s text, as ``vera fmt`` writes it."""
    blocks = [_data_lines(d) for d in prog.datas]
    blocks += [_function_lines(f) for f in prog.functions]
    blocks.append(_main_lines(prog))
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
    for fn in cand.functions:
        named = {p.type for p in fn.params} | {fn.ret}
        built: list[str] = []
        for node in _walk(fn.body):
            if isinstance(node, Construct) and node.ctor.data not in named:
                if node.ctor.data not in built:
                    built.append(node.ctor.data)
        for ty in reversed(built):
            fn.body.lets.insert(0, Let(Binding(ty, value=_stand_in(ty, None, cand.datas))))
            changed = True
    return cand if changed else None


# =====================================================================
# What the generator expects of a program
# =====================================================================

def slot_names(fn: Function) -> list[str]:
    """Each parameter's slot, as a contract and the tester spell it."""
    return [_slot(p, fn.params) for p in fn.params]


def evaluate(fn: Function, args: list[int | bool]) -> int | bool | None:
    """*fn*'s value on *args*, where its ``ensures`` is exact (a
    straight-line body); ``None`` where it is not."""
    if ensure_style(fn) != "exact" or len(args) != len(fn.params):
        return None
    values: dict[int, int | bool] = {
        id(p): (bool(a) if p.type == "Bool" else int(a))
        for p, a in zip(fn.params, args)}

    def run(e: Expr) -> int | bool:
        if isinstance(e, Lit):
            return e.value
        if isinstance(e, Ref):
            bound = e.binding
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

    return run(fn.body.result)


def expectations(prog: Program, focus: str = "",
                 args: list[int | bool] | None = None) -> list[dict[str, object]]:
    """What the generator wrote each function of *prog* to satisfy: its
    contract as written, the interval the verifier can see and the one a
    run can reach, and, for *focus* on *args*, the value an exact
    ``ensures`` states."""
    out: list[dict[str, object]] = []
    for fn in prog.functions:
        entry: dict[str, object] = {
            "function": fn.name, "signature": _signature(fn),
            "requires": _requires(fn), "ensures": _ensures(fn),
            "style": ensure_style(fn),
        }
        if fn.ret in NUMERIC:
            v, r = iv(fn.body.result, "v"), iv(fn.body.result, "r")
            entry["visible"] = [v.lo, v.hi]
            entry["reach"] = [r.lo, r.hi]
        if fn.name == focus and args is not None:
            entry["args"] = list(args)
            entry["expected"] = evaluate(fn, args)
        out.append(entry)
    return out


# =====================================================================
# Shape: what a program is made of
# =====================================================================

#: Every construct version one's grammar writes, as :func:`shape` counts it.
CONSTRUCTS = (
    "data_enum", "data_fields", "data_nested", "fn_public", "fn_private",
    "param_Int", "param_Nat", "param_Bool", "param_data", "nullary",
    "let", "let_narrowing", "if", "match_ctor", "match_wildcard",
    "match_literal", "binder", "call", "construct", "+", "-", "*", "/lit",
    "%lit", "/var", "%var", "nat_sub", "neg", "compare", "&&", "||", "!",
    "ensures_exact", "ensures_bounds", "ensures_one_side", "print",
)


def _walk(value: object) -> Iterator[object]:
    """Every IR node below *value*, a ``let``'s value included."""
    if isinstance(value, (Function, Ctor, Data, Program)):
        return
    if isinstance(value, Binding):
        if value.value is not None:
            yield from _walk(value.value)
        return
    if is_dataclass(value):
        yield value
        for f in fields(value):
            yield from _walk(getattr(value, f.name))
    elif isinstance(value, list):
        for item in value:
            yield from _walk(item)


def shape(prog: Program) -> dict[str, int]:
    """How many of each construct of :data:`CONSTRUCTS` *prog* holds."""
    count = dict.fromkeys(CONSTRUCTS, 0)
    for d in prog.datas:
        if all(not c.fields for c in d.ctors):
            count["data_enum"] += 1
        else:
            count["data_fields"] += 1
        if any(t not in PRIMITIVES for c in d.ctors for t in c.fields):
            count["data_nested"] += 1
    for fn in prog.functions:
        count["fn_public" if fn.public else "fn_private"] += 1
        if not fn.params:
            count["nullary"] += 1
        for p in fn.params:
            count[f"param_{p.type}" if p.type in PRIMITIVES else "param_data"] += 1
        style = ensure_style(fn)
        if style == "exact":
            count["ensures_exact"] += 1
        elif style == "bounds":
            count["ensures_bounds"] += 1
        elif style in ("lower", "upper"):
            count["ensures_one_side"] += 1
        for node in _walk(fn.body):
            _count_node(node, count)
    count["print"] = len(prog.prints)
    return count


def _count_node(node: object, count: dict[str, int]) -> None:
    if isinstance(node, Let):
        count["let"] += 1
        value = node.binding.value
        if node.binding.type == "Nat" and value is not None and static_type(value) == "Int":
            count["let_narrowing"] += 1
    elif isinstance(node, If):
        count["if"] += 1
    elif isinstance(node, Match):
        first = node.arms[0].pattern
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


def size(prog: Program) -> int:
    """How much *prog* holds: declarations, prints and expression nodes."""
    nodes = sum(1 for fn in prog.functions for _ in _walk(fn.body))
    return len(prog.datas) + len(prog.functions) + len(prog.prints) + nodes


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
    data = next(d for d in datas if d.name == ty)
    ctor = min(data.ctors, key=lambda c: len(c.fields))
    return Construct(ctor, [
        _stand_in(t, Iv(*FIELD_R[t]) if t in NUMERIC else None, datas)
        for t in ctor.fields
    ])


def _replace(value: object, old: object, new: Expr) -> object:
    """*value* with every occurrence of the node *old* replaced by *new*
    (a reference to a binding, *old* a :class:`Binding`, by a copy of
    *new*)."""
    if isinstance(old, Binding) and isinstance(value, Ref) and value.binding is old:
        return _clone(new)
    if value is old:
        return new
    if isinstance(value, (Function, Ctor, Data)):
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
    return value


def _clone(e: Expr) -> Expr:
    """A copy of *e* sharing the bindings it reads but owning the ones it
    defines (a pattern's binders, a branch's ``let``s)."""
    memo: dict[int, object] = {}

    def keep(value: object) -> None:
        if isinstance(value, (Function, Ctor, Data)):
            memo[id(value)] = value
        elif isinstance(value, Ref) and not _defined_inside(value.binding, e):
            memo[id(value.binding)] = value.binding
        elif isinstance(value, Binding):
            if value.value is not None:
                keep(value.value)
        if is_dataclass(value) and not isinstance(value, (type, Function, Ctor, Data, Binding)):
            for f in fields(value):
                keep(getattr(value, f.name))
        elif isinstance(value, list):
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
    return False


def _references(prog: Program, data: Data) -> bool:
    if any(data.name in c.fields for d in prog.datas for c in d.ctors):
        return True
    for fn in prog.functions:
        if fn.ret == data.name or any(p.type == data.name for p in fn.params):
            return True
        for node in _walk(fn.body):
            if isinstance(node, Construct) and node.ctor.data == data.name:
                return True
            if isinstance(node, Pattern) and node.ctor is not None and (
                    node.ctor.data == data.name):
                return True
            if isinstance(node, Let) and node.binding.type == data.name:
                return True
    return False


def _expressions(prog: Program) -> Iterator[tuple[Function, Expr]]:
    """Every expression of every function, outermost first."""
    for fn in prog.functions:
        for node in _walk(fn.body):
            if isinstance(node, Expr):
                yield fn, node


def _smaller(e: Expr, prog: Program) -> list[Expr]:
    """Simpler expressions that could stand where *e* stands."""
    out: list[Expr] = []
    ty = static_type(e)
    if isinstance(e, If):
        out += [b.result for b in (e.then, e.other) if not b.lets]
    if isinstance(e, Match):
        out += [arm.body for arm in e.arms if not any(arm.pattern.binders)]
    if isinstance(e, Bin) and e.op in ARITH + LOGIC:
        out += [e.left, e.right] if e.op not in ("*",) else [e.left]
    if isinstance(e, (Neg, Not)):
        out.append(e.operand)
    if not isinstance(e, (Lit, Ref)) or isinstance(e, Ref) and ty in NUMERIC:
        r = iv(e, "r") if ty in NUMERIC else None
        out.append(_stand_in(ty, r, prog.datas))
    return out


def reductions(prog: Program) -> Iterator[Program]:
    """Every program one step smaller than *prog*, the largest steps first:
    a function dropped (a literal standing in for each call), a data
    declaration nothing names, one of ``main``'s prints, a ``let`` (inlined),
    a public function made private, an expression replaced by a smaller one.
    Each is a copy; *prog* is left as it was."""
    for n in range(len(prog.functions) - 1, -1, -1):
        cand = copy.deepcopy(prog)
        gone = cand.functions[n]
        for fn in cand.functions:
            for _, node in list(_expressions(cand)):
                if isinstance(node, Call) and node.fn is gone:
                    _replace_everywhere(cand, node, _stand_in(
                        gone.ret, iv(node, "r") if gone.ret in NUMERIC else None,
                        cand.datas))
            break
        cand.functions.pop(n)
        cand.prints = [f for f in cand.prints if f is not gone]
        yield cand
    for n in range(len(prog.datas) - 1, -1, -1):
        cand = copy.deepcopy(prog)
        if not _references(cand, cand.datas[n]):
            cand.datas.pop(n)
            yield cand
    for n in range(len(prog.prints) - 1, -1, -1):
        cand = copy.deepcopy(prog)
        cand.prints.pop(n)
        yield cand
    for i, fn in enumerate(prog.functions):
        for j in range(len(_lets(fn))):
            cand = copy.deepcopy(prog)
            target = _lets(cand.functions[i])[j]
            value = target.binding.value
            assert value is not None
            _drop_let(cand.functions[i], target)
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


def _lets(fn: Function) -> list[Let]:
    return [node for node in _walk(fn.body) if isinstance(node, Let)]


def _drop_let(fn: Function, target: Let) -> None:
    for node in [fn.body, *_walk(fn.body)]:
        if isinstance(node, Block) and target in node.lets:
            node.lets.remove(target)
            return


def _replace_everywhere(prog: Program, old: object, new: Expr) -> None:
    for fn in prog.functions:
        fn.body = _replace(fn.body, old, new)  # type: ignore[assignment]


def well_formed(prog: Program) -> bool:
    """Whether *prog* keeps the invariants the generator writes by, which
    the checker cannot see: a value in a ``@Nat`` position the verifier can
    show is non-negative, an argument inside its callee's ``requires``, a
    ``@Nat`` subtraction whose operands cannot cross, a divisor the verifier
    sees is positive, a field inside its construction range, and no value a
    run can reach beyond :data:`SAFE`.  The minimiser keeps to them, so a
    minimal program is one the generator could have written, and a find
    cannot slide to a program whose contract is false."""
    try:
        for fn in prog.functions:
            if fn.ret == "Nat" and not _nat_value(fn.body.result):
                return False
            if not all(_node_ok(node) for node in _walk(fn.body)):
                return False
    except (AssertionError, TypeError):
        return False
    return True


def _nat_value(e: Expr) -> bool:
    t = static_type(e)
    if t == "Nat":
        return True
    v = iv(e, "v")
    return t == "Int" and v.lo is not None and v.lo >= 0


def _node_ok(node: object) -> bool:
    if isinstance(node, Let):
        value = node.binding.value
        return value is not None and (
            node.binding.type != "Nat" or _nat_value(value))
    if isinstance(node, Expr) and static_type(node) in NUMERIC and not iv(
            node, "r").safe():
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
    if isinstance(node, Call):
        for p, arg in zip(node.fn.params, node.args):
            if p.type in NUMERIC:
                assert p.v is not None
                if p.type == "Nat" and not _nat_value(arg):
                    return False
                if not iv(arg, "v").within(p.v.lo, p.v.hi):
                    return False
    if isinstance(node, Construct):
        for t, arg in zip(node.ctor.fields, node.args):
            if t in NUMERIC:
                lo, hi = FIELD_R[t]
                if t == "Nat" and not _nat_value(arg):
                    return False
                if not iv(arg, "r").within(lo, hi):
                    return False
    return True


def minimize(prog: Program, holds: Callable[[Program], bool], *,
             budget: int = 300) -> Program:
    """The smallest program :func:`reductions` reaches from *prog* while
    *holds* stays true, trying at most *budget* candidates, each of them
    :func:`well_formed`.  *prog* itself must hold."""
    current = prog
    tried = 0
    progress = True
    while progress and tried < budget:
        progress = False
        for cand in reductions(current):
            try:
                cand.render()
            except RenderError:
                continue
            if not well_formed(cand):
                continue
            tried += 1
            try:
                ok = holds(cand)
            except Exception:  # noqa: BLE001 — a candidate that crashes a stage is not the find
                ok = False
            if ok:
                current = cand
                progress = True
                break
            if tried >= budget:
                break
    return current


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
        statuses = sorted(k for k in stats if k.startswith("obligation_"))
        lines.append("Obligations: " + ", ".join(
            f"{k.removeprefix('obligation_')} {stats[k]}" for k in statuses))
    known: dict[str, list[int]] = {}
    for r in records:
        for f in r["finds"]:
            if f["known"]:
                known.setdefault(f["known"], []).append(r["seed"])
    if known:
        lines += ["", "Known classes (counted, not failures):", "",
                  "| Issue | Mismatches | Programs |", "|---|---:|---:|"]
        lines += [f"| {issue} | {len(known[issue])} | "
                  f"{len(set(known[issue]))} |" for issue in sorted(known)]
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
        sys.stdout.write(program(int(argv[0])))
        return 0
    sys.stderr.write(
        "usage: python -m tests.program_generator SEED\n"
        "       python -m tests.program_generator summarize DIRECTORY\n")
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
