"""`Nat` is the non-negative i64 that spec §2.2 defines, and every integer
literal is an `Int` (v0.2.3).

`Nat` is `{ @Int | @Int.0 >= 0 }` in its representation as in its type: an
i64 holding `0 .. 2^63 - 1`.  Widening a `@Nat` into an `@Int` is a no-op at
the value level, so nothing obligates or guards it, and every `@Nat`
operation runs on the signed i64 instructions an `@Int` one runs on.  A
literal is an `Int` wherever it is written; in a `@Nat` or refined context
it is a narrowing, obligated as any `@Int` narrowing is, and a literal above
`2^63 - 1` is E149 in every context.

The class is every place a `@Nat` met an `@Int` at two widths: the u64 range
(literals, arithmetic, rendering, comparison, division), the widening
coercion and its guards, and the typing of a literal by its value.  The
instrument crosses:

- every reported instance (the fourteen issues), unparametrised;
- the literal matrix: literal values at both edges of the i64 range and
  past them, in every context a literal can be written in, through check,
  verify, compile and run;
- the operations matrix: `@Nat` values at both ends of the range, through a
  parameter, under every operation a `@Nat` can meet an `@Int` in;
- the negative space of each refusal: the nearest accepted neighbour of
  every refused shape.
"""

from __future__ import annotations

import functools
import re
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline
from vera.codegen.api import CompileResult, execute
from vera.reconcile import ReconcileRun, reconcile_file

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file
# or a module that decides its class: the literal's type and range, the
# `@Nat` value's representation in the verifier and in code generation, its
# operations, guards and host boundary.
pytestmark = pytest.mark.matrix(
    decides=[
        "vera/binders.py",
        "vera/browser/runtime.mjs",
        "vera/checker/calls.py",
        "vera/checker/control.py",
        "vera/checker/core.py",
        "vera/checker/expressions.py",
        "vera/checker/resolution.py",
        "vera/cli.py",
        "vera/codegen/api.py",
        "vera/codegen/closures.py",
        "vera/codegen/contracts.py",
        "vera/codegen/core.py",
        "vera/codegen/functions.py",
        "vera/codegen/memory.py",
        "vera/codegen/modules.py",
        "vera/codegen/registration.py",
        "vera/monomorphize.py",
        "vera/narrowing.py",
        "vera/obligations/core.py",
        "vera/reconcile.py",
        "vera/runtime/traps.py",
        "vera/smt.py",
        "vera/tester.py",
        "vera/trap_registry.py",
        "vera/typed.py",
        "vera/types.py",
        "vera/verifier.py",
        "vera/wasm/calls.py",
        "vera/wasm/calls_arrays.py",
        "vera/wasm/calls_containers.py",
        "vera/wasm/calls_handlers.py",
        "vera/wasm/calls_markup.py",
        "vera/wasm/calls_math.py",
        "vera/wasm/calls_parsing.py",
        "vera/wasm/closures.py",
        "vera/wasm/context.py",
        "vera/wasm/data.py",
        "vera/wasm/inference.py",
        "vera/wasm/operators.py",
    ],
)

I64_MAX = 2**63 - 1
I64_MIN = -(2**63)
U64_MAX = 2**64 - 1


# =====================================================================
# Helpers
# =====================================================================


def _codes(stage: pipeline.Checked | pipeline.Verified) -> list[str]:
    """The error codes *stage* reported, in order."""
    return [d.error_code for d in stage.errors]


def _kinds(verified: pipeline.Verified) -> list[tuple[str, str]]:
    """Every obligation's (kind, status), in the order the verifier recorded
    them, contracts left out (each program's `requires`/`ensures` are
    `true`)."""
    return [(o.kind, o.status) for o in verified.obligations
            if o.kind not in ("requires", "ensures")]


def _run(source: str, fn: str, *args: int | str) -> pipeline.Ran:
    """Run *fn* with *args* as `vera run --fn fn -- args` passes them."""
    return pipeline.run(source, fn=fn, raw_args=[str(a) for a in args])


def _value(source: str, fn: str, *args: int | str) -> object:
    """The value *fn* returns for *args*; a trap fails the caller."""
    ran = _run(source, fn, *args)
    assert ran.trap is None, f"{fn}{args} trapped: {ran.trap}"
    return ran.value


def _trap_kind(source: str, fn: str, *args: int | str) -> str:
    """The kind of the trap *fn* ends in for *args*; a value fails it."""
    ran = _run(source, fn, *args)
    assert ran.trap is not None, f"{fn}{args} returned {ran.value!r}"
    return ran.trap.kind


def _refuses_argument(source: str, fn: str, *args: int | str) -> None:
    """`vera run` refuses *args* before the call, naming the `@Nat`
    parameter's range: no `@Nat` above `2^63 - 1` or below 0 enters."""
    with pytest.raises(RuntimeError,
                       match=r"out of range for parameter type @Nat"):
        _run(source, fn, *args)


# =====================================================================
# The reported instances
# =====================================================================


_DIVIDE_COMPARE_RENDER = """\
public fn halve(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result <= @Nat.0)
  effects(pure)
{
  @Nat.0 / 2
}

public fn below_max(@Nat -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0 < MAX
}

public fn last_digit(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result < 10)
  effects(pure)
{
  @Nat.0 % 10
}

public fn render(@Nat -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  "\\(@Nat.0) \\(nat_to_string(@Nat.0)) \\(show(@Nat.0))"
}
"""


def test_repro_1504_a_nat_compares_divides_and_renders_as_the_value_it_is() -> None:
    """#1504: a `@Nat` above i64.MAX was compared, divided and printed as
    the negative number its bits spell.  No `@Nat` holds one now: the u64
    literal is E149, an argument above i64.MAX is refused, and at the top of
    the range every operation reads the value."""
    u64 = _DIVIDE_COMPARE_RENDER.replace("MAX", str(U64_MAX))
    assert _codes(pipeline.check(u64)) == ["E149"]
    i64 = _DIVIDE_COMPARE_RENDER.replace("MAX", str(I64_MAX))
    assert pipeline.verify(i64).ok
    assert _value(i64, "halve", I64_MAX) == I64_MAX // 2
    assert _value(i64, "below_max", 100) == 1
    assert _value(i64, "below_max", I64_MAX) == 0
    assert _value(i64, "last_digit", I64_MAX) == 7
    assert _value(i64, "render", I64_MAX) == " ".join([str(I64_MAX)] * 3)
    _refuses_argument(i64, "halve", I64_MAX + 1)
    _refuses_argument(i64, "halve", U64_MAX)
    _refuses_argument(i64, "halve", -1)


_COMPOSITE_WIDEN = """\
private data Wrap<A> { W(A) }

public fn widen(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Wrap<Int>> = [W(@Nat.0)];
  match @Array<Wrap<Int>>.0[0] { W(@Int) -> @Int.0 }
}
"""


def test_repro_1542_a_nat_component_read_at_int_keeps_its_value() -> None:
    """#1542's widening half: a `@Nat` component read back from an `@Int`
    slot came back as -1 at u64.MAX.  The widening is a no-op: the top of
    the range comes back unchanged, and u64.MAX cannot be passed."""
    assert _kinds(pipeline.verify(_COMPOSITE_WIDEN)) == [
        ("index_bounds", "tier3")]
    assert _value(_COMPOSITE_WIDEN, "widen", I64_MAX) == I64_MAX
    _refuses_argument(_COMPOSITE_WIDEN, "widen", U64_MAX)


_PLUS_LITERAL = """\
public fn next(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = @Nat.0 + 1;
  @Int.0
}
"""


def test_repro_1543_nat_plus_a_literal_overflows_at_the_i64_edge() -> None:
    """#1543: `@Nat.0 + 1` at i64.MAX ran at the unsigned width and its
    2^63 came back from an `@Int` slot as -2^63, with no obligation.  The
    literal is an `Int`, the sum an `@Int` addition checked against the i64
    range, and i64.MAX + 1 traps."""
    assert _kinds(pipeline.verify(_PLUS_LITERAL)) == [
        ("int_overflow", "tier3")]
    assert _value(_PLUS_LITERAL, "next", 5) == 6
    assert _value(_PLUS_LITERAL, "next", I64_MAX - 1) == I64_MAX
    assert _trap_kind(_PLUS_LITERAL, "next", I64_MAX) == "overflow"


_HETEROGENEOUS_JOINS = """\
public fn comp(@Int, @Nat, @Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = if @Bool.0 then { Tuple(1, @Nat.0) } else { Tuple(1, @Int.0) };
  @Int.0
}

public fn hnd(@Int, @Nat, @Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = handle[Exn<Int>] { throw(@Int) -> @Int.0 } in { @Nat.0 };
  @Int.0
}
"""


def test_repro_1546_a_heterogeneous_join_read_at_int_keeps_its_value() -> None:
    """#1546: a join of a `@Nat` and an `@Int`, built as a tuple component
    or produced by a `handle`, returned u64.MAX as -1.  Neither join has a
    widening to check now: no obligation, no check, and the top of the
    range comes back unchanged."""
    verified = pipeline.verify(_HETEROGENEOUS_JOINS)
    assert verified.ok and _kinds(verified) == []
    assert pipeline.compile(_HETEROGENEOUS_JOINS).checks() == ()
    assert _value(_HETEROGENEOUS_JOINS, "comp", -4, 5, "false") == -4
    assert _value(_HETEROGENEOUS_JOINS, "comp", 0, I64_MAX, "true") == I64_MAX
    assert _value(_HETEROGENEOUS_JOINS, "hnd", 0, I64_MAX, "true") == I64_MAX
    _refuses_argument(_HETEROGENEOUS_JOINS, "hnd", 0, U64_MAX, "true")


_EARLIER_ARM = """\
private data K { KA, KB }

public fn f(@Nat, @Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match (if @Bool.0 then { Tuple(KA, 0 - 3) } else { Tuple(KB, @Nat.0) }) {
    Tuple(KB, @Nat) -> 5,
    Tuple(KA, @Int) -> @Int.0
  }
}
"""


def test_repro_1586_an_int_binder_guards_no_nat_an_earlier_arm_takes() -> None:
    """#1586: the second arm's `@Int` binder guarded the `@Nat` the first
    arm takes, so a valid program trapped above i64.MAX.  Reading a `@Nat`
    at `@Int` checks nothing now: the module holds the `@Int` subtraction
    `0 - 3`'s overflow check (proved) and the first arm's `@Nat` binder's
    narrowing check (`0 - 3` is one of its sources), and no widening
    check."""
    assert _kinds(pipeline.verify(_EARLIER_ARM)) == [
        ("int_overflow", "verified"), ("nat_bind", "tier3")]
    assert [c.kind for c in pipeline.compile(_EARLIER_ARM).checks()] == [
        "overflow", "nat_guard"]
    assert _value(_EARLIER_ARM, "f", I64_MAX, "false") == 5
    assert _value(_EARLIER_ARM, "f", 5, "true") == -3


_BELOW_INT_MIN = """\
public fn main(-> @Int)
  requires(true)
  ensures(@Int.result < 0)
  effects(pure)
{
  0 - 18446744073709551615
}
"""


def test_repro_1587_a_literal_above_i64_is_refused_wherever_it_is_written() -> None:
    """#1587: `0 - 18446744073709551615` proved `ensures(@Int.result < 0)`
    and returned 1, its operand a u64 literal.  A literal above i64.MAX is
    E149 in every context, so the expression never reaches the verifier."""
    assert _codes(pipeline.check(_BELOW_INT_MIN)) == ["E149"]
    assert pipeline.check(
        _BELOW_INT_MIN.replace("18446744073709551615", str(I64_MAX))).ok


_BIND_OUT_OF = {
    "tuple": """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Bool> = Tuple(@Nat.0, true);
  @Nat.0
}
""",
    "constructor": """\
private data NatBox { NB(Nat) }

public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @NatBox = NB(@Nat.0);
  match @NatBox.0 {
    NB(@Nat) -> @Nat.0
  }
}
""",
    "index": """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Nat> = [@Nat.0];
  @Array<Nat>.0[0]
}
""",
}


@pytest.mark.parametrize("shape", sorted(_BIND_OUT_OF))
def test_repro_1589_a_nat_bound_out_of_a_composite_keeps_its_value(
        shape: str) -> None:
    """#1589: a `@Nat` above i64.MAX bound out of a tuple, a constructor
    pattern or an array trapped as a negative value.  No `@Nat` holds one:
    the top of the range binds unchanged, and 2^63 + 5 cannot be passed."""
    source = _BIND_OUT_OF[shape]
    assert pipeline.verify(source).ok
    assert _value(source, "f", I64_MAX) == I64_MAX
    _refuses_argument(source, "f", 2**63 + 5)


_NAT_TO_INT_OPERAND = """\
public fn f(@Nat -> @Int)
  requires(true)
  ensures(@Int.result >= 0 - 1)
  effects(pure)
{
  nat_to_int(@Nat.0) + (0 - 1)
}
"""


def test_repro_1590_nat_to_int_is_the_identity_at_every_value() -> None:
    """#1590: `nat_to_int` of a `@Nat` above i64.MAX was read as a negative
    `@Int`, and the Tier-1 `ensures` failed at run time.  It is the identity
    on `0 .. 2^63 - 1`, the proof holds on every value a `@Nat` holds, and
    2^63 cannot be passed."""
    assert pipeline.verify(_NAT_TO_INT_OPERAND).ok
    assert _value(_NAT_TO_INT_OPERAND, "f", 0) == -1
    assert _value(_NAT_TO_INT_OPERAND, "f", 5) == 4
    assert _value(_NAT_TO_INT_OPERAND, "f", I64_MAX) == I64_MAX - 1
    _refuses_argument(_NAT_TO_INT_OPERAND, "f", I64_MAX + 1)


_SUM_WITH_NEGATIVE_PART = """\
public fn f(@Nat, @Int, @Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  (@Nat.0 + (if @Bool.0 then { 0 - 3 } else { 0 })) + @Int.0
}
"""


def test_repro_1591_a_nat_sum_with_a_negative_literal_part_is_an_int_sum() -> None:
    """#1591: the `if` over literals was a `@Nat`, its -3 summed at the
    unsigned width, and a `@Nat` above i64.MAX in it was read as negative.
    The `if` is an `Int`, both sums are `@Int` sums, and each value is the
    true one or an overflow trap."""
    src = _SUM_WITH_NEGATIVE_PART
    assert _value(src, "f", 5, 1, "true") == 3
    assert _value(src, "f", 5, 1, "false") == 6
    assert _value(src, "f", I64_MAX, -1, "false") == I64_MAX - 1
    assert _value(src, "f", I64_MAX, -4, "true") == I64_MAX - 7
    assert _trap_kind(src, "f", I64_MAX, 1, "false") == "overflow"


_NEGATION = """\
public fn neg(@Nat -> @Int)
  requires(true)
  ensures(@Int.result <= 0)
  effects(pure)
{
  -@Nat.0
}
"""


def test_repro_1592_negating_a_nat_is_exact_on_its_whole_range() -> None:
    """#1592: `-@Nat.0` at 2^63 + 5 returned 9223372036854775803 and the
    Tier-1 `ensures(@Int.result <= 0)` failed at run time.  Every `@Nat`
    negates to an `@Int` exactly, so the proof holds at both ends."""
    assert pipeline.verify(_NEGATION).ok
    assert _value(_NEGATION, "neg", 0) == 0
    assert _value(_NEGATION, "neg", I64_MAX) == -I64_MAX
    _refuses_argument(_NEGATION, "neg", 2**63 + 5)


_PLUS_NEGATIVE_BRANCH = """\
public fn f(@Nat, @Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0 + (if @Bool.0 then { 0 - 1 } else { 0 })
}
"""


def test_repro_1593_a_nat_plus_a_negative_branch_is_the_int_sum() -> None:
    """#1593: the `if` over `0 - 1` and `0` was typed `@Nat`, the sum ran
    at the unsigned width, and 5 + (-1) trapped as an overflow.  The `if` is
    an `Int` and the sum the `@Int` sum."""
    assert _value(_PLUS_NEGATIVE_BRANCH, "f", 5, "true") == 4
    assert _value(_PLUS_NEGATIVE_BRANCH, "f", 0, "true") == -1
    assert _value(_PLUS_NEGATIVE_BRANCH, "f", I64_MAX, "true") == I64_MAX - 1
    assert _value(_PLUS_NEGATIVE_BRANCH, "f", I64_MAX, "false") == I64_MAX


_GENERIC_OPERAND = """\
private forall<T> fn id(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = id(0 - 3) + 1;
  nat_to_int(@Nat.0)
}
"""


def test_rule_an_arithmetic_operand_is_given_no_expected_type() -> None:
    """The rule #1596 asks about: an arithmetic operand takes no expected
    type (spec §4.4), so the context of the `@Nat` binding does not reach
    `id(0 - 3)` through `+ 1`.  `id` is `id` at `Int`, the sum is an `Int`,
    and its narrowing into the `@Nat` binding is obligated, Tier 3 through
    the opaque `id`, and guarded: the run traps.  The literal subtraction
    `0 - 3` is an `@Int` one whose overflow obligation is proved."""
    assert _kinds(pipeline.verify(_GENERIC_OPERAND)) == [
        ("int_overflow", "verified"), ("int_overflow", "tier3"),
        ("nat_bind", "tier3")]
    assert _trap_kind(_GENERIC_OPERAND, "f", 0) == "nat_guard"


_SLICE_IN_NAT_CONTEXT = """\
public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Nat> = array_slice([-3, 5], 1, 2);
  array_fold(@Array<Nat>.0, 0, fn(@Nat, @Nat -> @Nat) effects(pure) { @Nat.0 + @Nat.1 })
}
"""


def test_rule_an_expected_nat_fixes_a_type_argument_whatever_the_signs() -> None:
    """The rule #1605 meets: the type a call's result is expected at fixes
    a type argument its literals leave open, whatever their signs (spec
    §4.2 rule 2), so `let @Array<Nat> = array_slice([-3, 5], 1, 2)` makes
    `[-3, 5]` an `Array<Nat>` and the -3 a refuted narrowing (E503), though
    the slice holds no negative; with `[3, 5]` it verifies and runs."""
    verified = pipeline.verify(_SLICE_IN_NAT_CONTEXT)
    assert _codes(verified) == ["E503"]
    accepted = _SLICE_IN_NAT_CONTEXT.replace("[-3, 5]", "[3, 5]")
    assert pipeline.verify(accepted).ok
    assert _value(accepted, "f", 0) == 5


_BUILTIN_INT_ARGUMENT = """\
public fn f(@Nat -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
{
  int_to_float(nat_to_int(@Nat.0))
}

public fn g(@Nat -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  to_string(@Nat.0)
}
"""


def test_repro_1628_a_nat_widened_into_a_builtin_needs_no_check() -> None:
    """#1628: a `@Nat` passed to a built-in's `@Int` parameter was recorded
    `tier3` with no check emitted, and returned -1.0 at u64.MAX.  The
    widening is the identity: no obligation, no check, and the top of the
    range converts and renders as its value."""
    verified = pipeline.verify(_BUILTIN_INT_ARGUMENT)
    assert verified.ok and _kinds(verified) == []
    assert _value(_BUILTIN_INT_ARGUMENT, "f", I64_MAX) == float(I64_MAX)
    assert _value(_BUILTIN_INT_ARGUMENT, "g", I64_MAX) == str(I64_MAX)
    _refuses_argument(_BUILTIN_INT_ARGUMENT, "f", U64_MAX)
    _refuses_argument(_BUILTIN_INT_ARGUMENT, "g", U64_MAX)


# =====================================================================
# The literal matrix
# =====================================================================
#
# Every literal value at both edges of the i64 range and one past each, in
# every context a literal can be written in, through the check, the
# verifier's obligations, the emitted checks and a run.  The expectation is
# the rule below, written from spec §2.2 and §4.2, never read back from the
# checker:
#
# 1. A literal is written without a sign; `-n` negates the literal `n`, and
#    a pattern has no negation (a parse error, E005).
# 2. The range is i64's in every context, `9223372036854775807` the
#    largest and `-9223372036854775808` the smallest (its magnitude is
#    allowed under the negation alone): E149 past either, once per literal
#    written, a pattern's included.  In a `Byte` context, and over a `Byte`
#    scrutinee, the range is `Byte`'s, 0..255; a negated literal there is an
#    `Int` (E170).
# 3. In range, every literal is an `Int`.  In a `@Nat` context it is a
#    narrowing: a negative literal is refuted (E503, `nat_bind` violated)
#    and its guard traps; a non-negative one records nothing.  In a refined
#    context it is the refinement's narrowing (`refine_bind`, E505 refuted).
#    Anywhere else it is the `Int` it is.


@dataclass(frozen=True)
class _Literal:
    text: str
    value: int


_LITERALS = {
    "0": _Literal("0", 0),
    "1": _Literal("1", 1),
    "i64.MAX": _Literal(str(I64_MAX), I64_MAX),
    "i64.MAX+1": _Literal(str(I64_MAX + 1), I64_MAX + 1),
    "u64.MAX": _Literal(str(U64_MAX), U64_MAX),
    "-1": _Literal("-1", -1),
    "i64.MIN": _Literal(f"-{-I64_MIN}", I64_MIN),
    "i64.MIN-1": _Literal(f"-{-I64_MIN + 1}", I64_MIN - 1),
}


def _fn(sig: str, body: str, *, name: str = "f", vis: str = "public",
        requires: str = "true", ensures: str = "true",
        decreases: str | None = None, effects: str = "pure") -> str:
    measure = f"\n  decreases({decreases})" if decreases else ""
    return (f"{vis} fn {name}({sig})\n  requires({requires})\n"
            f"  ensures({ensures}){measure}\n  effects({effects})\n"
            f"{{\n  {body}\n}}\n")


_ID = ("private forall<T> fn id(@T -> @T)\n  requires(true)\n  ensures(true)\n"
       "  effects(pure)\n{\n  @T.0\n}\n\n")
#: Returns its first argument (`@T.1`: the earlier of the two `@T`s).
_PICK = ("private forall<T> fn pick(@T, @T -> @T)\n  requires(true)\n"
         "  ensures(true)\n  effects(pure)\n{\n  @T.1\n}\n\n")
#: Stores its argument in an `Array<T>`.
_WRAP = ("private forall<T> fn wrap(@T -> @Array<T>)\n  requires(true)\n"
         "  ensures(true)\n  effects(pure)\n{\n  [@T.0]\n}\n\n")
_G_NAT = _fn("@Nat -> @Nat", "@Nat.0", name="g", vis="private") + "\n"
_NB = "private data NB { NB(Nat) }\n\n"

#: A generic call whose type argument the `@Nat` it is returned or bound
#: into fixes, `ARG` its argument: each is a site the instantiated `@Nat`
#: formal makes a narrowing.  `f(0)` returns the argument's value.
_GENERIC_AT_NAT: dict[str, str] = {
    "a @Nat return": _PICK + _fn("@Int -> @Nat", "pick(ARG, 5)"),
    "an if arm at a @Nat return": _PICK + _fn(
        "@Int -> @Nat", "if @Int.0 > 0 then { 5 } else { pick(ARG, 5) }"),
    "a closure's @Nat return": _PICK + _fn(
        "@Int -> @Int",
        "let @Nat = apply_fn(fn(@Int -> @Nat) effects(pure) { pick(ARG, 5) }"
        ", 0);\n  nat_to_int(@Nat.0)"),
    "a generic argument at a @Nat return": _PICK + _ID + _fn(
        "@Int -> @Nat", "pick(id(ARG), 5)"),
    "a generic beside a @Nat argument": _PICK + _fn(
        "@Int -> @Int",
        "let @Int = pick(ARG, string_length(\"ab\"));\n  @Int.0"),
}


@dataclass(frozen=True)
class _Context:
    """A program with `LIT` where the literal goes, and `f(0)` to run."""

    source: str
    #: What the literal's context is: `none`, `int`, `nat`, `refined`,
    #: `byte`, `pattern`, `byte pattern`, `predicate`, `contract` or
    #: `measure`.
    target: str
    #: Whether code generation reads the narrowed value back at run time
    #: (an argument, a component, a generic call) rather than the literal.
    reads_value: bool = False
    #: How many times the literal is written.
    occurrences: int = 1
    #: What `f(0)` returns for the literal's value (a trap kind as `!kind`).
    run: Callable[[int], object] = lambda v: v


_CONTEXTS: dict[str, _Context] = {
    "no context": _Context(
        _fn("@Int -> @Int", "if LIT == 0 then { 0 } else { 1 }"), "none",
        run=lambda v: int(v != 0)),
    "let @Nat": _Context(
        _fn("@Int -> @Int", "let @Nat = LIT;\n  nat_to_int(@Nat.0)"), "nat"),
    "let @Int": _Context(
        _fn("@Int -> @Int", "let @Int = LIT;\n  @Int.0"), "int"),
    "@Nat argument": _Context(
        _fn("@Nat -> @Nat", "@Nat.0", name="g", vis="private") + "\n"
        + _fn("@Int -> @Int", "nat_to_int(g(LIT))"), "nat", reads_value=True),
    "@Int argument": _Context(
        _fn("@Int -> @Int", "@Int.0", name="g", vis="private") + "\n"
        + _fn("@Int -> @Int", "g(LIT)"), "int"),
    "@Nat return": _Context(_fn("@Int -> @Nat", "LIT"), "nat"),
    "@Int return": _Context(_fn("@Int -> @Int", "LIT"), "int"),
    "@Nat array element": _Context(
        _fn("@Int -> @Int",
            "let @Array<Nat> = [LIT];\n  array_length(@Array<Nat>.0)"),
        "nat", run=lambda v: 1),
    "@Int array element": _Context(
        _fn("@Int -> @Int",
            "let @Array<Int> = [LIT];\n  array_length(@Array<Int>.0)"),
        "int", run=lambda v: 1),
    "@Nat tuple component": _Context(
        _fn("@Int -> @Int", "let Tuple<@Nat, @Bool> = Tuple(LIT, true);\n"
            "  nat_to_int(@Nat.0)"), "nat", reads_value=True),
    "@Nat constructor field": _Context(
        "private data NB { NB(Nat) }\n\n" + _fn(
            "@Int -> @Int",
            "match NB(LIT) {\n    NB(@Nat) -> nat_to_int(@Nat.0)\n  }"),
        "nat", reads_value=True),
    # The call's clone is at `Nat` (#1679): the literal enters a `Nat`
    # formal and the result is one, so nothing is read back unchecked.
    "generic argument at an expected @Nat": _Context(
        _ID + _fn("@Int -> @Int", "let @Nat = id(LIT);\n  nat_to_int(@Nat.0)"),
        "nat"),
    "generic argument with no expected type": _Context(
        _ID + _fn("@Int -> @Int", "if id(LIT) == 0 then { 0 } else { 1 }"),
        "none", run=lambda v: int(v != 0)),
    # The generic call whose type argument the `@Nat` its result reaches
    # fixes: the literal narrows into the instantiated `@Nat` formal, and is
    # refuted and guarded there, whether the result is returned, returned
    # through an arm or a closure, or bound.
    **{f"generic argument at {site}": _Context(
        source.replace("ARG", "LIT"), "nat")
       for site, source in _GENERIC_AT_NAT.items()},
    "generic argument piped at a @Nat return": _Context(
        _PICK + _fn("@Int -> @Nat", "LIT |> pick(5)"), "nat"),
    # The call's clone is at `Nat` (#1679), the type the result is bound or
    # stored at: nothing is read back unchecked.
    "generic call bound by a let @Nat": _Context(
        _PICK + _fn("@Int -> @Int",
                    "let @Nat = pick(LIT, 5);\n  nat_to_int(@Nat.0)"),
        "nat"),
    "generic call as a @Nat argument": _Context(
        _PICK + _G_NAT + _fn("@Int -> @Int", "nat_to_int(g(pick(LIT, 5)))"),
        "nat", reads_value=True),
    "generic call as a @Nat constructor field": _Context(
        _NB + _PICK + _fn(
            "@Int -> @Int",
            "match NB(pick(LIT, 5)) {\n    NB(@Nat) -> nat_to_int(@Nat.0)\n"
            "  }"),
        "nat", reads_value=True),
    "generic call as a @Nat array element": _Context(
        _PICK + _fn("@Int -> @Int",
                    "let @Array<Nat> = [pick(LIT, 5)];\n"
                    "  array_length(@Array<Nat>.0)"),
        "nat", run=lambda v: 1),
    "generic call as a @Nat tuple component": _Context(
        _PICK + _fn("@Int -> @Int",
                    "let Tuple<@Nat, @Bool> = Tuple(pick(LIT, 5), true);\n"
                    "  nat_to_int(@Nat.0)"),
        "nat", reads_value=True),
    "literal pattern over @Int": _Context(
        _fn("@Int -> @Int", "match @Int.0 {\n    LIT -> 1,\n    _ -> 0\n  }"),
        "pattern", run=lambda v: int(v == 0)),
    "literal pattern over @Nat": _Context(
        _fn("@Nat -> @Int", "match @Nat.0 {\n    LIT -> 1,\n    _ -> 0\n  }"),
        "pattern", run=lambda v: int(v == 0)),
    "literal pattern over @Byte": _Context(
        _fn("@Int -> @Int",
            "match int_to_byte(@Int.0) {\n    Some(@Byte) -> match @Byte.0 {\n"
            "      LIT -> 1,\n      _ -> 0\n    },\n    None -> 9\n  }"),
        "byte pattern", run=lambda v: int(v == 0)),
    "refinement predicate": _Context(
        "type R = { @Int | @Int.0 != LIT };\n\n" + _fn("@R -> @Int", "@R.0"),
        "predicate", run=lambda v: "!contract_violation" if v == 0 else 0),
    "refined binding": _Context(
        "type Pos = { @Int | @Int.0 >= 0 };\n\n"
        + _fn("@Int -> @Int", "let @Pos = LIT;\n  @Pos.0"), "refined"),
    "requires and ensures": _Context(
        _fn("@Int -> @Int", "@Int.0", requires="@Int.0 == LIT",
            ensures="@Int.result == LIT"),
        "contract", occurrences=2,
        run=lambda v: 0 if v == 0 else "!contract_violation"),
    "decreases": _Context(
        _fn("@Nat -> @Nat",
            "if @Nat.0 == 0 then { 0 } else { f(@Nat.0 - 1) }",
            decreases="LIT"), "measure", run=lambda v: 0),
    "let @Byte": _Context(
        _fn("@Int -> @Int", "let @Byte = LIT;\n  byte_to_int(@Byte.0)"), "byte"),
}


@dataclass(frozen=True)
class _Verdict:
    """What one program does at each stage."""

    check: tuple[str, ...] = ()
    verify: tuple[str, ...] = ()
    obligations: tuple[tuple[str, str], ...] = ()
    checks: frozenset[str] = frozenset()
    run: object = None


#: The obligations and checks the `decreases` program's own body carries,
#: whatever its measure: the narrowing of `@Nat.0 - 1` into `f`'s `@Nat`
#: parameter and that subtraction's overflow, both proved, and the measure,
#: which the verifier does not prove of a constant.
_MEASURE_BODY = _Verdict(
    obligations=(("int_overflow", "verified"), ("nat_bind", "verified"),
                 ("decreases", "tier3")),
    checks=frozenset({"contract_violation", "nat_guard", "overflow"}),
)


def _literal_rule(context: _Context, v: int) -> _Verdict:
    """The rule stated above, for the literal *v* in *context*."""
    if context.target in ("pattern", "byte pattern") and v < 0:
        return _Verdict(check=("E005",))
    if context.target == "byte pattern" and v > 255:
        return _Verdict(check=("E149",))
    if context.target == "byte":
        codes = (("E149",) if v > 255 or v < I64_MIN else ()) + (
            ("E170",) if v < 0 else ())
        if codes:
            return _Verdict(check=codes)
        return _Verdict(run=v)
    if not I64_MIN <= v <= I64_MAX:
        return _Verdict(check=("E149",) * context.occurrences)
    run = context.run(v)
    if context.target == "nat":
        if v < 0:
            return _Verdict(verify=("E503",),
                            obligations=(("nat_bind", "violated"),),
                            checks=frozenset({"nat_guard"}),
                            run="!nat_guard")
        return _Verdict(checks=frozenset({"nat_guard"} if context.reads_value
                                         else ()), run=run)
    if context.target == "refined":
        checks = frozenset({"contract_violation"})
        if v < 0:
            return _Verdict(verify=("E505",),
                            obligations=(("refine_bind", "violated"),),
                            checks=checks, run="!contract_violation")
        return _Verdict(obligations=(("refine_bind", "verified"),),
                        checks=checks, run=run)
    if context.target in ("predicate", "contract"):
        return _Verdict(checks=frozenset({"contract_violation"}), run=run)
    if context.target == "measure":
        return _Verdict(obligations=_MEASURE_BODY.obligations,
                        checks=_MEASURE_BODY.checks, run=run)
    return _Verdict(run=run)


def _measure(source: str) -> _Verdict:
    """What the toolchain does with *source*: the check's codes, or the
    verifier's codes and obligations, the module's checks and `f(0)`."""
    checked = pipeline.check(source)
    if not checked.ok:
        return _Verdict(check=tuple(_codes(checked)))
    verified = pipeline.verify(source)
    compiled = pipeline.compile(source)
    ran = pipeline.run(compiled, fn="f", raw_args=["0"])
    return _Verdict(
        verify=tuple(_codes(verified)),
        obligations=tuple(_kinds(verified)),
        checks=frozenset(c.kind for c in compiled.checks()),
        run=f"!{ran.trap.kind}" if ran.trap is not None else ran.value,
    )


@pytest.mark.parametrize("literal", list(_LITERALS))
@pytest.mark.parametrize("context", list(_CONTEXTS))
def test_a_literal_in_every_context(context: str, literal: str) -> None:
    lit = _LITERALS[literal]
    ctx = _CONTEXTS[context]
    source = ctx.source.replace("LIT", lit.text)
    assert _measure(source) == _literal_rule(ctx, lit.value), source


# =====================================================================
# A generic call instantiated at `Nat`
# =====================================================================
#
# A type argument that only literals would fix takes the type the call's
# result is expected at (spec §4.2), so `pick(-3, 5)` returned into a `@Nat`
# is `pick` at `Nat`, and its `-3` narrows into the instantiated `@Nat`
# formal.  Every argument a generic call passes at a `Nat` formal is that
# binding site, whatever the callee (a user generic, a prelude one, a
# built-in) and wherever the call's result goes.  A generic body computes no
# `T` of its own (no ability gives a type variable arithmetic), so what a
# call at `Nat` returns came in through such an argument, and the argument is
# where it is checked.  The rule, for an argument whose value at `f(0)` is v:
#
# 1. A non-negative literal is no narrowing: nothing is recorded or checked.
# 2. Any other argument narrows.  The verifier records `nat_bind` at it:
#    `violated` (E503) where a counterexample makes it negative, `verified`
#    where none can, `tier3` where it cannot decide.  The module checks it
#    there (`nat_guard`).
# 3. The run traps `nat_guard` where v < 0, and otherwise returns what the
#    program computes from v.
# 4. The record and the check agree: the reconciliation join (`vera verify
#    --reconcile`) finds no claim without its check, and no check without
#    its claim.

_REPRO_GENERIC_RETURN = _PICK + _fn("@Int -> @Nat", "pick(-3, 5)") + "\n" + _fn(
    "@Int -> @Int",
    "let @Nat = apply_fn(fn(@Int -> @Nat) effects(pure) { pick(-3, 5) }, 0);"
    "\n  nat_to_int(@Nat.0)", name="g")


def test_repro_a_negative_literal_through_a_generic_at_a_nat_return_traps(
) -> None:
    """`pick(-3, 5)` returned from a `@Nat` function, and from a closure's
    `@Nat` return, is `pick` at `Nat`: the verifier refutes the `-3` at the
    argument, and the run traps there, where it printed -3 (PR #1700
    review)."""
    verified = pipeline.verify(_REPRO_GENERIC_RETURN)
    assert [(d.error_code, d.location.line, d.location.column)
            for d in verified.errors] == [("E503", 14, 8), ("E503", 22, 61)]
    assert _trap_kind(_REPRO_GENERIC_RETURN, "f", 0) == "nat_guard"
    assert _trap_kind(_REPRO_GENERIC_RETURN, "g", 0) == "nat_guard"


def test_repro_id_of_a_literal_subtraction_at_a_nat_return_traps() -> None:
    """`id(0 - 3)` returned from a `@Nat` function returned -3 on `main` too:
    the argument narrows into `id`'s `@Nat` formal, and is guarded there."""
    source = _ID + _fn("@Int -> @Nat", "id(0 - 3)")
    assert _codes(pipeline.verify(source)) == ["E503"]
    assert _trap_kind(source, "f", 0) == "nat_guard"


def test_repro_a_generic_stores_no_negative_in_a_nat_collection() -> None:
    """`wrap(-3)` bound at `@Array<Nat>` is `wrap` at `Nat`, which stores its
    argument in the array: the argument is checked before it is stored, so
    the element read back at `@Int` is never -3."""
    source = _WRAP + _fn(
        "@Int -> @Int",
        "let @Array<Nat> = wrap(-3);\n  let @Int = @Array<Nat>.0[0];\n"
        "  @Int.0")
    assert _codes(pipeline.verify(source)) == ["E503"]
    assert _trap_kind(source, "f", 0) == "nat_guard"


#: A condition the verifier cannot translate, false at `f(0)`.
_UNDECIDED = "array_length(array_range(0, @Int.0)) > 3"


@dataclass(frozen=True)
class _Argument:
    text: str
    #: Its value at `f(0)`.
    value: int
    #: Whether the verifier decides its sign.
    decided: bool = True
    #: Whether binding it into a `@Nat` is a narrowing.
    narrows: bool = True


_INSTANTIATED_ARGUMENTS: dict[str, _Argument] = {
    "a negative literal": _Argument("-3", -3),
    "a literal subtraction below zero": _Argument("0 - 3", -3),
    "a literal subtraction above zero": _Argument("3 - 1", 2),
    "an undecided join with a negative arm": _Argument(
        f"if {_UNDECIDED} then {{ 1 }} else {{ 0 - 1 }}", -1, decided=False),
    "an undecided join of non-negative arms": _Argument(
        f"if {_UNDECIDED} then {{ 1 }} else {{ 3 - 1 }}", 2, decided=False),
    "a non-negative literal": _Argument("5", 5, narrows=False),
}


@dataclass(frozen=True)
class _Instantiation:
    """A program passing `ARG` to a generic at a `Nat` instantiation."""

    source: str
    #: What `f(0)` returns for an argument of value v >= 0.
    run: Callable[[int], object] = lambda v: v
    #: The records the verifier keeps at the argument when it narrows.
    records: int = 1


_MAP_NAT_KEY = 'let @Map<Nat, String> = map_insert(map_new(), 2, "v");\n  '
_SET_NAT = "let @Set<Nat> = set_add(set_new(), 2);\n  "

#: The built-in generics' type-variable formals, `(name, index)`, each in a
#: program instantiating it at `Nat`.  The prelude's `option_unwrap_or` and
#: `result_unwrap_or` compile as user generics do; the rest are lowered by
#: their own translators.
_BUILTIN_AT_NAT: dict[tuple[str, int], _Instantiation] = {
    ("array_append", 1): _Instantiation(_fn(
        "@Int -> @Int",
        "let @Array<Nat> = array_append([5], ARG);\n"
        "  let @Int = @Array<Nat>.0[1];\n  @Int.0")),
    ("array_fold", 1): _Instantiation(_fn(
        "@Int -> @Nat",
        "array_fold([1, 2], ARG, fn(@Nat, @Int -> @Nat) effects(pure) "
        "{ @Nat.0 })")),
    ("async", 0): _Instantiation(_fn(
        "@Int -> @Int",
        "let @Future<Nat> = async(ARG);\n"
        "  let @Int = await(@Future<Nat>.0);\n  @Int.0", effects="<Async>")),
    ("map_insert", 1): _Instantiation(_fn(
        "@Int -> @Int",
        'let @Map<Nat, String> = map_insert(map_new(), ARG, "v");\n'
        "  let @Array<Nat> = map_keys(@Map<Nat, String>.0);\n"
        "  let @Int = @Array<Nat>.0[0];\n  @Int.0")),
    # A map value is recorded twice, as the call's argument and as the value
    # the map stores (#1440), and checked once.
    ("map_insert", 2): _Instantiation(_fn(
        "@Int -> @Int",
        'let @Map<String, Nat> = map_insert(map_new(), "k", ARG);\n'
        '  match map_get(@Map<String, Nat>.0, "k") {\n'
        "    Some(@Int) -> @Int.0,\n    None -> 7\n  }"), records=2),
    ("map_get", 1): _Instantiation(_fn(
        "@Int -> @Int",
        _MAP_NAT_KEY + "match map_get(@Map<Nat, String>.0, ARG) {\n"
        "    Some(@String) -> 1,\n    None -> 0\n  }"),
        run=lambda v: int(v == 2)),
    ("map_contains", 1): _Instantiation(_fn(
        "@Int -> @Bool",
        _MAP_NAT_KEY + "map_contains(@Map<Nat, String>.0, ARG)"),
        run=lambda v: int(v == 2)),
    ("map_remove", 1): _Instantiation(_fn(
        "@Int -> @Int",
        _MAP_NAT_KEY + "map_size(map_remove(@Map<Nat, String>.0, ARG))"),
        run=lambda v: int(v != 2)),
    ("set_add", 1): _Instantiation(_fn(
        "@Int -> @Int",
        "let @Set<Nat> = set_add(set_new(), ARG);\n"
        "  let @Array<Nat> = set_to_array(@Set<Nat>.0);\n"
        "  let @Int = @Array<Nat>.0[0];\n  @Int.0")),
    ("set_contains", 1): _Instantiation(_fn(
        "@Int -> @Bool", _SET_NAT + "set_contains(@Set<Nat>.0, ARG)"),
        run=lambda v: int(v == 2)),
    ("set_remove", 1): _Instantiation(_fn(
        "@Int -> @Int", _SET_NAT + "set_size(set_remove(@Set<Nat>.0, ARG))"),
        run=lambda v: int(v != 2)),
    ("option_unwrap_or", 1): _Instantiation(_fn(
        "@Int -> @Nat", "option_unwrap_or(None, ARG)")),
    ("result_unwrap_or", 1): _Instantiation(_fn(
        "@Int -> @Nat", 'result_unwrap_or(Err("e"), ARG)')),
}

_INSTANTIATIONS: dict[str, _Instantiation] = {
    **{f"a user generic at {site}": _Instantiation(source)
       for site, source in _GENERIC_AT_NAT.items()},
    "a user generic storing it in an Array<T>": _Instantiation(_WRAP + _fn(
        "@Int -> @Int",
        "let @Array<Nat> = wrap(ARG);\n  let @Int = @Array<Nat>.0[0];\n"
        "  @Int.0")),
    **{f"{name}'s argument {index}": inst
       for (name, index), inst in _BUILTIN_AT_NAT.items()},
}


#: A sub-pattern's bind of a type-parameter field, by the scrutinee's
#: checked type: a field the type instantiates at `Nat`, through an alias
#: or a refinement of it alike, takes no sign guard (the field's value was
#: checked where it was stored, #1679), and an `Int` field keeps it.  The
#: name is the checked type's (#1525), so an alias is its target and a
#: refinement its base.  (declarations, scrutinee type, guarded)
_FIELD_SPELLINGS: dict[str, tuple[str, str, bool]] = {
    "exactly Nat": ("", "Option<Nat>", False),
    "an alias of Nat": ("type Age = Nat;\n\n", "Option<Age>", False),
    "a refinement of Nat": (
        "type Small = { @Nat | @Nat.0 < 10 };\n\n", "Option<Small>", False),
    "Int": ("", "Option<Int>", True),
}


@pytest.mark.parametrize("spelling", list(_FIELD_SPELLINGS))
def test_a_field_bind_is_guarded_unless_its_type_is_nat(
        spelling: str) -> None:
    decls, scrutinee, guarded = _FIELD_SPELLINGS[spelling]
    source = decls + _fn(
        f"@{scrutinee} -> @Int",
        f"match @{scrutinee}.0 {{\n    Some(@Nat) -> nat_to_int(@Nat.0),\n"
        "    None -> 0\n  }")
    checks = [c for c in pipeline.compile(source).checks()
              if c.kind == "nat_guard"]
    assert bool(checks) == guarded, checks


def test_every_builtin_type_variable_formal_is_instantiated_at_nat() -> None:
    """The built-ins above are every built-in generic with a formal that IS
    a type variable, read from the registry: a new one joins the matrix or
    fails here."""
    from vera.environment import TypeEnv
    from vera.types import TypeVar

    formals = {
        (name, index)
        for name, info in TypeEnv().functions.items() if info.forall_vars
        for index, formal in enumerate(info.param_types)
        if isinstance(formal, TypeVar)
    }
    assert formals == set(_BUILTIN_AT_NAT)


@functools.lru_cache(maxsize=None)
def _instantiated(site: str, argument: str, root: str) -> ReconcileRun:
    """The program at *site* with *argument*, through check, verify, compile
    and the join, as `vera verify --reconcile` runs it."""
    source = _INSTANTIATIONS[site].source.replace(
        "ARG", _INSTANTIATED_ARGUMENTS[argument].text)
    path = Path(root) / (re.sub(r"\W+", "_", f"{site} {argument}") + ".vera")
    path.write_text(source, encoding="utf-8")
    run = reconcile_file(path)
    assert not run.check_errors and not run.compile_errors, (
        run.check_errors, run.compile_errors, source)
    return run


@pytest.fixture(scope="module")
def _instantiation_root(tmp_path_factory: pytest.TempPathFactory) -> str:
    return str(tmp_path_factory.mktemp("instantiated"))


@pytest.mark.parametrize("argument", list(_INSTANTIATED_ARGUMENTS))
@pytest.mark.parametrize("site", list(_INSTANTIATIONS))
def test_an_argument_at_a_nat_instantiation_is_a_narrowing(
        site: str, argument: str, _instantiation_root: str) -> None:
    inst = _INSTANTIATIONS[site]
    arg = _INSTANTIATED_ARGUMENTS[argument]
    run = _instantiated(site, argument, _instantiation_root)
    assert run.verify_result is not None and run.compile_result is not None
    statuses = [o.status for o in run.verify_result.obligations
                if o.kind == "nat_bind"]
    codes = [d.error_code for d in run.verify_result.diagnostics
             if d.severity == "error"]
    guards = [c for c in run.compile_result.emitted_checks
              if c.kind == "nat_guard"]
    ran = pipeline.run(run.compile_result, fn="f", raw_args=["0"])
    got = f"!{ran.trap.kind}" if ran.trap is not None else ran.value
    if not arg.narrows:
        assert (statuses, codes, guards) == ([], [], [])
    else:
        status = ("tier3" if not arg.decided
                  else "violated" if arg.value < 0 else "verified")
        assert statuses == [status] * inst.records
        assert codes == (["E503"] * inst.records
                         if status == "violated" else [])
        assert guards
    assert got == ("!nat_guard" if arg.value < 0 else inst.run(arg.value))


def _agreement_cells() -> list[object]:
    """Every (site, argument) cell; the map value's undecided ones are the
    #1695 instance it carries: two `tier3` records, one check."""
    cells: list[object] = []
    for site in _INSTANTIATIONS:
        for argument, arg in _INSTANTIATED_ARGUMENTS.items():
            marks = ()
            if (_INSTANTIATIONS[site].records > 1 and arg.narrows
                    and not arg.decided):
                marks = (pytest.mark.xfail(
                    strict=True, reason="#1695: the verifier records a map "
                    "value twice, as the call's argument and as the value "
                    "the map stores, and code generation checks it once"),)
            cells.append(pytest.param(site, argument, marks=marks,
                                      id=f"{site}-{argument}"))
    return cells


@pytest.mark.parametrize(("site", "argument"), _agreement_cells())
def test_the_record_and_the_check_of_an_instantiated_argument_agree(
        site: str, argument: str, _instantiation_root: str) -> None:
    run = _instantiated(site, argument, _instantiation_root)
    assert [m.to_dict() for m in run.mismatches] == []


#: The nearest shapes the argument check must leave alone, each with what
#: it is at base (`main` at a5b5de8f), the deleted `nat_to_int_coerce` aside:
#: (source, the verifier's warnings, the obligations, the module's checks,
#: what `f(0)` returns).
_INSTANTIATION_NEIGHBOURS: dict[str, tuple[str, list[str],
                                           list[tuple[str, str]],
                                           list[str], object]] = {
    "the same call at an Int instantiation": (
        _PICK + _fn("@Int -> @Int", "pick(-3, 5)"), [], [], [], -3),
    "an argument already a @Nat": (
        _PICK + _fn("@Nat -> @Nat", "pick(@Nat.0, 5)"), [], [], [], 0),
    "a refined instantiation over Nat": (
        "type PosNat = { @Nat | @Nat.0 > 0 };\n\n" + _PICK
        + _fn("@Int -> @PosNat", "pick(7, 5)"),
        ["E506"], [("refine_bind", "tier3")], ["contract_violation"], 7),
}


@pytest.mark.parametrize("neighbour", list(_INSTANTIATION_NEIGHBOURS))
def test_an_instantiation_s_neighbours_take_no_argument_check(
        neighbour: str, tmp_path: Path) -> None:
    """No `@Nat` instantiation, an argument that is already a `@Nat`, and a
    refined instantiation, whose predicate is the refinement's own check:
    none takes the sign check, and each verifies, compiles and runs as at
    base."""
    source, warnings, obligations, checks, value = (
        _INSTANTIATION_NEIGHBOURS[neighbour])
    path = tmp_path / "neighbour.vera"
    path.write_text(source, encoding="utf-8")
    run = reconcile_file(path)
    assert run.verify_result is not None and run.compile_result is not None
    diagnostics = run.verify_result.diagnostics
    assert [d.error_code for d in diagnostics if d.severity == "error"] == []
    assert [d.error_code for d in diagnostics
            if d.severity == "warning"] == warnings
    assert [(o.kind, o.status) for o in run.verify_result.obligations
            if o.kind not in ("requires", "ensures")] == obligations
    assert sorted(c.kind for c in run.compile_result.emitted_checks) == checks
    assert run.mismatches == []
    assert pipeline.run(run.compile_result, fn="f",
                        raw_args=["0"]).value == value


_REFINED_AT_NAT = ("type PosNat = { @Nat | @Nat.0 > 0 };\n\n" + _PICK
                   + _fn("@Int -> @PosNat", "pick(-3, 5)"))


def test_a_negative_argument_at_a_refined_instantiation_over_nat_traps(
        tmp_path: Path) -> None:
    """`pick(-3, 5)` at `@PosNat`: the argument narrows into the
    refinement's `Nat` base, so the verifier refutes it there (`nat_bind`,
    E503) and the module checks its sign where the call passes it
    (`nat_guard`), while the refined binding of the result keeps its own
    record and predicate check (`refine_bind`, `contract_violation`).  The
    join pairs each record with its check, and the run traps at the
    argument (PR #1700 review)."""
    path = tmp_path / "refined.vera"
    path.write_text(_REFINED_AT_NAT, encoding="utf-8")
    run = reconcile_file(path)
    assert run.verify_result is not None and run.compile_result is not None
    assert [(d.error_code, d.location.line, d.location.column)
            for d in run.verify_result.diagnostics] == [
        ("E503", 16, 8), ("E506", 16, 3)]
    assert [(o.kind, o.status) for o in run.verify_result.obligations
            if o.kind not in ("requires", "ensures")] == [
        ("nat_bind", "violated"), ("refine_bind", "tier3")]
    assert sorted(c.kind for c in run.compile_result.emitted_checks) == [
        "contract_violation", "nat_guard"]
    assert run.mismatches == []
    assert _trap_kind(_REFINED_AT_NAT, "f", 0) == "nat_guard"


# =====================================================================
# The operations matrix
# =====================================================================
#
# `@Nat` values at both ends of the range, passed through a parameter as
# `vera run --fn f -- n` passes them, under every operation a `@Nat` meets
# an `@Int` in.  The rule: each operation computes over the integers, and
# the result is the true one, or the trap of the type it leaves: `overflow`
# past the i64 range, `nat_underflow` for a `@Nat` subtraction below zero,
# `nat_guard` for a narrowing into a `@Nat` below zero.  No cell wraps,
# reinterprets a bit pattern, or reads a `@Nat` as a negative number.

_NAT_VALUES = (0, 1, I64_MAX - 1, I64_MAX)


def _int(v: int) -> object:
    """*v*, or the overflow trap when it is past the i64 range."""
    return v if I64_MIN <= v <= I64_MAX else "!overflow"


@dataclass(frozen=True)
class _Operation:
    #: The function `f`'s signature and body; `f` takes the `@Nat` first.
    sig: str
    body: str
    #: What `f` returns for the `@Nat` value (a trap kind as `!kind`).
    rule: Callable[[int], object]
    #: The arguments after the `@Nat`.
    extra: tuple[int, ...] = ()
    #: Declarations the body needs.
    decls: str = ""


_IDI = _fn("@Int -> @Int", "@Int.0", name="idi", vis="private") + "\n"

_OPERATIONS: dict[str, _Operation] = {
    "+ 1": _Operation("@Nat -> @Int", "@Nat.0 + 1", lambda n: _int(n + 1)),
    "- 1": _Operation("@Nat -> @Int", "@Nat.0 - 1", lambda n: n - 1),
    "* 2": _Operation("@Nat -> @Int", "@Nat.0 * 2", lambda n: _int(n * 2)),
    "/ 2": _Operation("@Nat -> @Int", "@Nat.0 / 2", lambda n: n // 2),
    "% 2": _Operation("@Nat -> @Int", "@Nat.0 % 2", lambda n: n % 2),
    "negation": _Operation("@Nat -> @Int", "-@Nat.0", lambda n: -n),
    "nat_to_int": _Operation("@Nat -> @Int", "nat_to_int(@Nat.0)",
                             lambda n: n),
    "nat_to_string": _Operation("@Nat -> @String", "nat_to_string(@Nat.0)",
                                str),
    "string interpolation": _Operation("@Nat -> @String", '"\\(@Nat.0)"',
                                       str),
    "int_to_float": _Operation("@Nat -> @Float64", "int_to_float(@Nat.0)",
                               float),
    "into an @Int slot": _Operation(
        "@Nat -> @Int", "let @Int = @Nat.0;\n  @Int.0", lambda n: n),
    "into a built-in's @Int argument": _Operation(
        "@Nat -> @Int", "max(@Nat.0, -1)", lambda n: n),
    "abs": _Operation("@Nat -> @Nat", "abs(@Nat.0)", lambda n: n),
    "bound into @Nat out of a tuple": _Operation(
        "@Nat -> @Int",
        "let Tuple<@Nat, @Int> = Tuple(@Nat.0, -1);\n  nat_to_int(@Nat.0)",
        lambda n: n),
    "bound into @Nat out of a constructor pattern": _Operation(
        "@Nat -> @Int",
        "match NB(@Nat.0) {\n    NB(@Nat) -> nat_to_int(@Nat.0)\n  }",
        lambda n: n, decls=_NB),
    "a match arm's @Int binder": _Operation(
        "@Nat -> @Int",
        "match Some(@Nat.0) {\n    Some(@Int) -> @Int.0,\n    None -> -1\n  }",
        lambda n: n),
    "an if join with an @Int arm": _Operation(
        "@Nat -> @Int", "if @Nat.0 >= 1 then { @Nat.0 } else { -5 }",
        lambda n: n if n >= 1 else -5),
    "a match join with an @Int arm": _Operation(
        "@Nat -> @Int",
        "match Some(@Nat.0) {\n    Some(@Nat) -> @Nat.0,\n    None -> -5\n  }",
        lambda n: n),
    "a handle join": _Operation(
        "@Nat -> @Int",
        "handle[Exn<Int>] {\n    throw(@Int) -> { @Int.0 }\n  } in {\n"
        "    if @Nat.0 == 0 then { throw(-7) } else { @Nat.0 }\n  }",
        lambda n: -7 if n == 0 else n),
    "a pipe into an @Int parameter": _Operation(
        "@Nat -> @Int", "@Nat.0 |> idi()", lambda n: n, decls=_IDI),
    "- 1 into a @Nat slot": _Operation(
        "@Nat -> @Int", "let @Nat = @Nat.0 - 1;\n  nat_to_int(@Nat.0)",
        lambda n: "!nat_guard" if n == 0 else n - 1),
    "@Nat - @Nat": _Operation(
        "@Nat, @Nat -> @Nat", "@Nat.1 - @Nat.0",
        lambda n: "!nat_underflow" if n < 1 else n - 1, extra=(1,)),
    "@Nat + @Nat": _Operation(
        "@Nat, @Nat -> @Nat", "@Nat.1 + @Nat.0", lambda n: _int(n + 1),
        extra=(1,)),
    "@Nat * @Nat": _Operation(
        "@Nat, @Nat -> @Nat", "@Nat.1 * @Nat.0", lambda n: _int(n * 2),
        extra=(2,)),
    "@Nat / @Nat": _Operation(
        "@Nat, @Nat -> @Nat", "@Nat.1 / @Nat.0", lambda n: n // 2,
        extra=(2,)),
    "@Nat % @Nat": _Operation(
        "@Nat, @Nat -> @Nat", "@Nat.1 % @Nat.0", lambda n: n % 2,
        extra=(2,)),
}

# A comparison against an `@Int`: -1 tells a signed comparison from an
# unsigned one (whose -1 is u64.MAX), and i64.MAX the top of the range.
_COMPARISONS: dict[str, Callable[[int, int], bool]] = {
    "==": lambda a, b: a == b, "<": lambda a, b: a < b,
    "<=": lambda a, b: a <= b, ">": lambda a, b: a > b,
    ">=": lambda a, b: a >= b,
}
for _op, _holds_for in _COMPARISONS.items():
    for _m in (-1, I64_MAX):
        _OPERATIONS[f"{_op} {_m}"] = _Operation(
            "@Nat, @Int -> @Bool", f"@Nat.0 {_op} @Int.0",
            lambda n, m=_m, holds=_holds_for: int(holds(n, m)), extra=(_m,))


@functools.lru_cache(maxsize=None)
def _compiled_operation(name: str) -> pipeline.Compiled:
    op = _OPERATIONS[name]
    compiled = pipeline.compile(op.decls + _fn(op.sig, op.body))
    assert compiled.ok, compiled.errors
    return compiled


@pytest.mark.parametrize("n", _NAT_VALUES)
@pytest.mark.parametrize("operation", list(_OPERATIONS))
def test_a_nat_operation_at_both_ends_of_the_range(
        operation: str, n: int) -> None:
    op = _OPERATIONS[operation]
    ran = pipeline.run(_compiled_operation(operation), fn="f",
                       raw_args=[str(a) for a in (n, *op.extra)])
    got = f"!{ran.trap.kind}" if ran.trap is not None else ran.value
    assert got == op.rule(n), f"{operation} at {n}"


# =====================================================================
# The negative space of every refusal
# =====================================================================


def _neighbour(context: str, text: str) -> str:
    return _CONTEXTS[context].source.replace("LIT", text)


@pytest.mark.parametrize("context", [
    "no context", "let @Nat", "@Nat argument", "@Int return",
    "literal pattern over @Int", "literal pattern over @Nat",
])
def test_the_top_of_the_i64_range_is_accepted_beside_the_value_past_it(
        context: str) -> None:
    """E149 at 2^63 has, beside it, 2^63 - 1 checked clean, verified with
    nothing refuted, and run: the bound is the range's, not one short."""
    assert _codes(pipeline.check(_neighbour(context, str(I64_MAX + 1)))) == [
        "E149"]
    accepted = _neighbour(context, str(I64_MAX))
    checked = pipeline.check(accepted)
    assert checked.ok and not checked.warnings
    verified = pipeline.verify(accepted)
    assert verified.ok
    assert all(status == "verified" for _, status in _kinds(verified))
    assert pipeline.run(accepted, fn="f", raw_args=["0"]).trap is None


def test_the_bottom_of_the_i64_range_is_accepted_beside_the_value_past_it(
) -> None:
    """Under the negation the magnitude reaches 2^63 and no further."""
    refused = _neighbour("let @Int", f"-{-I64_MIN + 1}")
    assert _codes(pipeline.check(refused)) == ["E149"]
    accepted = _neighbour("let @Int", f"-{-I64_MIN}")
    assert pipeline.verify(accepted).ok
    assert _value(accepted, "f", 0) == I64_MIN


def test_a_byte_pattern_at_255_is_accepted_beside_256() -> None:
    """The `Byte` scrutinee's pattern bound is the `Byte` range: 256 is
    E149, 255 checks clean and matches the byte 255."""
    context = "literal pattern over @Byte"
    assert _codes(pipeline.check(_neighbour(context, "256"))) == ["E149"]
    accepted = _neighbour(context, "255")
    assert pipeline.verify(accepted).ok
    assert _value(accepted, "f", 255) == 1
    assert _value(accepted, "f", 254) == 0


@pytest.mark.parametrize("context", [
    "let @Nat", "@Nat argument", "@Nat return", "@Nat array element",
    "@Nat tuple component", "@Nat constructor field",
    "generic argument at an expected @Nat",
])
def test_zero_into_a_nat_is_accepted_beside_minus_one(context: str) -> None:
    """A negative literal narrowed into `@Nat` is refuted (E503); zero, the
    nearest value the narrowing holds, verifies with nothing refuted."""
    assert _codes(pipeline.verify(_neighbour(context, "-1"))) == ["E503"]
    accepted = _neighbour(context, "0")
    verified = pipeline.verify(accepted)
    assert verified.ok and _kinds(verified) == []
    assert pipeline.run(accepted, fn="f", raw_args=["0"]).trap is None


def test_the_fix_of_a_pattern_literal_past_the_range_checks_clean() -> None:
    """The E149 fix, applied: the pattern literal at the top of the range
    (or the `Byte` range) checks with no E149."""
    for context, past, top in (
            ("literal pattern over @Int", I64_MAX + 1, I64_MAX),
            ("literal pattern over @Byte", 256, 255)):
        refused = pipeline.check(_neighbour(context, str(past)))
        assert [d.error_code for d in refused.errors] == ["E149"]
        assert str(top) in refused.errors[0].fix
        assert pipeline.check(_neighbour(context, str(top))).ok


_ARGUMENTS = _fn("@Nat, @Int -> @Nat", "@Nat.0")


@pytest.mark.parametrize(("args", "refused"), [
    ((I64_MAX, 0), None),
    ((I64_MAX + 1, 0), "@Nat"),
    ((0, 0), None),
    ((-1, 0), "@Nat"),
    ((0, I64_MAX), None),
    ((0, I64_MAX + 1), "@Int"),
    ((0, I64_MIN), None),
    ((0, I64_MIN - 1), "@Int"),
])
def test_an_argument_is_held_to_its_parameter_type_s_range(
        args: tuple[int, int], refused: str | None) -> None:
    """`vera run` and `execute` refuse an integer argument outside its
    parameter type's range rather than wrap it; the edge of each range is
    accepted.  `check_int_args=False` models a host that does not check,
    whose wrapped value then reaches the function's own guards."""
    module = pipeline.compile(_ARGUMENTS).result
    if refused is None:
        assert pipeline.run(module, fn="f",
                            raw_args=[str(a) for a in args]).value == args[0]
        assert execute(module, fn_name="f", args=list(args)).value == args[0]
        return
    message = f"out of range for parameter type {refused}"
    with pytest.raises(RuntimeError, match=message):
        pipeline.run(module, fn="f", raw_args=[str(a) for a in args])
    with pytest.raises(RuntimeError, match=message):
        execute(module, fn_name="f", args=list(args))


_BYTE_ARGUMENT = _fn("@Byte -> @Int", "byte_to_int(@Byte.0)")


@pytest.mark.parametrize(("arg", "refused"), [
    (0, False), (255, False), (256, True), (-1, True),
])
def test_a_byte_argument_is_held_to_the_byte_range(
        arg: int, refused: bool) -> None:
    """A `@Byte` parameter is held to `0 .. 255` as an `@Int` or a `@Nat`
    one is to its range, a raw argument and a programmatic one alike:
    `vera run` handed 256 to a `@Byte` function as the i32 256, and -1 as
    4294967295.  The edges of the range are accepted."""
    module = pipeline.compile(_BYTE_ARGUMENT).result
    if not refused:
        assert pipeline.run(module, fn="f",
                            raw_args=[str(arg)]).value == arg
        assert execute(module, fn_name="f", args=[arg]).value == arg
        return
    message = "out of range for parameter type @Byte"
    with pytest.raises(RuntimeError, match=message):
        pipeline.run(module, fn="f", raw_args=[str(arg)])
    with pytest.raises(RuntimeError, match=message):
        execute(module, fn_name="f", args=[arg])


def test_the_argument_range_check_is_the_host_s() -> None:
    """The refusal is the host's: with it off, `-1` reaches a `@Nat`
    parameter as the i64 it is, and nothing in the function converts it."""
    module = pipeline.compile(_ARGUMENTS).result
    assert execute(module, fn_name="f", args=[-1, 0],
                   check_int_args=False).value == -1


#: Signatures whose integer parameters sit among two-slot ones.  A `@String`
#: or an `@Array` lowers to an `i32_pair`, two WASM arguments, so the
#: arguments `execute` takes do not line up one to one with the parameters
#: they belong to.  Each: (the parameters, the result, the body); no body
#: reads a pair, which a call passes as a zero pointer and length.
_PAIRED: dict[str, tuple[tuple[str, ...], str, str]] = {
    "a @Nat after a @String": (("@String", "@Nat"), "@Nat", "@Nat.0"),
    "a @Nat after two pairs": (
        ("@String", "@Array<Int>", "@Nat"), "@Nat", "@Nat.0"),
    "a @Nat before a @String": (("@Nat", "@String"), "@Nat", "@Nat.0"),
    "an @Int and a @Nat after a @String": (
        ("@String", "@Int", "@Nat"), "@Int", "@Int.0"),
    "a @Byte after a @String": (
        ("@String", "@Byte"), "@Int", "byte_to_int(@Byte.0)"),
    "an @Int after a @String": (("@String", "@Int"), "@Int", "@Int.0"),
}


@functools.lru_cache(maxsize=None)
def _paired_module(shape: str) -> CompileResult:
    params, result, body = _PAIRED[shape]
    return pipeline.compile(
        _fn(f"{', '.join(params)} -> {result}", body)).result


def _paired_args(shape: str,
                 ints: tuple[int, ...]) -> tuple[list[int | float], list[str]]:
    """A call's programmatic and raw arguments: *ints* to the integer
    parameters in order, and each pair a zero pointer and length (the empty
    string, raw)."""
    values = iter(ints)
    programmatic: list[int | float] = []
    raw: list[str] = []
    for param in _PAIRED[shape][0]:
        if param in ("@String", "@Array<Int>"):
            programmatic += [0, 0]
            raw.append("")
        else:
            value = next(values)
            programmatic.append(value)
            raw.append(str(value))
    return programmatic, raw


@pytest.mark.parametrize(("shape", "ints", "outcome"), [
    ("a @Nat after a @String", (-1,), "@Nat"),
    ("a @Nat after a @String", (I64_MAX,), I64_MAX),
    ("a @Nat after two pairs", (-1,), "@Nat"),
    ("a @Nat after two pairs", (I64_MAX,), I64_MAX),
    ("a @Nat before a @String", (-1,), "@Nat"),
    ("a @Nat before a @String", (I64_MAX,), I64_MAX),
    ("an @Int and a @Nat after a @String", (7, -1), "@Nat"),
    ("an @Int and a @Nat after a @String", (-1, 7), -1),
    ("a @Byte after a @String", (256,), "@Byte"),
    ("a @Byte after a @String", (255,), 255),
    ("an @Int after a @String", (I64_MAX + 1,), "@Int"),
    ("an @Int after a @String", (I64_MAX,), I64_MAX),
])
def test_an_argument_beside_a_pair_is_held_to_its_parameter_s_range(
        shape: str, ints: tuple[int, ...], outcome: int | str) -> None:
    """A `@String` or an `@Array` parameter is two WASM arguments, and the
    programmatic check reads each integer's range from the parameter it
    belongs to, wherever the pairs sit: it skipped every function with a
    pair, so `execute` passed -1 into a `@Nat` after a `@String` (PR #1700
    review).  The raw path holds the same ranges; the edge of each range is
    accepted, and so is an `@Int` -1 beside the `@Nat`."""
    module = _paired_module(shape)
    programmatic, raw = _paired_args(shape, ints)
    if isinstance(outcome, int):
        assert execute(module, fn_name="f",
                       args=programmatic).value == outcome
        assert pipeline.run(module, fn="f", raw_args=raw).value == outcome
        return
    message = f"out of range for parameter type {outcome}"
    with pytest.raises(RuntimeError, match=message):
        execute(module, fn_name="f", args=programmatic)
    with pytest.raises(RuntimeError, match=message):
        pipeline.run(module, fn="f", raw_args=raw)


def test_the_range_check_beside_a_pair_is_the_host_s() -> None:
    """With the host's check off, -1 reaches the `@Nat` after a `@String` as
    the i64 it is: the refusal above is the host's."""
    programmatic, _ = _paired_args("a @Nat after a @String", (-1,))
    assert execute(_paired_module("a @Nat after a @String"), fn_name="f",
                   args=programmatic, check_int_args=False).value == -1


_ABS = _fn("@Int -> @Nat", "abs(@Int.0)")


def test_repro_abs_of_the_i64_minimum_traps_rather_than_wrap() -> None:
    """`abs(-2^63)` is 2^63, which no `@Nat` holds: the call carries the
    i64 overflow obligation (Tier 3 over an unconstrained `@Int`) and traps
    with the overflow kind; one above the minimum returns i64.MAX."""
    assert _kinds(pipeline.verify(_ABS)) == [("int_overflow", "tier3")]
    assert [c.kind for c in pipeline.compile(_ABS).checks()] == ["overflow"]
    assert _trap_kind(_ABS, "f", I64_MIN) == "overflow"
    assert _value(_ABS, "f", I64_MIN + 1) == I64_MAX
    assert _value(_ABS, "f", -5) == 5


_PARSE_NAT = _fn(
    "@String -> @String",
    "match parse_nat(@String.0) {\n    Ok(@Nat) -> nat_to_string(@Nat.0),\n"
    "    Err(@String) -> @String.0\n  }")


@pytest.mark.parametrize(("numeral", "result"), [
    (str(I64_MAX), str(I64_MAX)),
    (str(I64_MAX + 1), "out of range"),
    (str(U64_MAX), "out of range"),
    (str(U64_MAX + 1), "out of range"),
    ("99999999999999999999", "out of range"),
    ("12", "12"),
])
def test_repro_parse_nat_refuses_a_numeral_past_the_range(
        numeral: str, result: str) -> None:
    """`parse_nat` returns `Err("out of range")` for a numeral above
    i64.MAX, where it trapped or wrapped (2^64 parsed as 0)."""
    assert _value(_PARSE_NAT, "f", numeral) == result


# `parse_int` accumulates its digits as `parse_nat` does, and the two are
# held to their ranges by one rule: a numeral past the type's range is
# `Err("out of range")`, never a wrapped value.  `parse_int`'s range is the
# i64's, so `-9223372036854775808` parses and its magnitude unsigned does not.
_PARSE_INT = _fn(
    "@String -> @String",
    "match parse_int(@String.0) {\n    Ok(@Int) -> int_to_string(@Int.0),\n"
    "    Err(@String) -> @String.0\n  }")


@pytest.mark.parametrize(("numeral", "result"), [
    (str(I64_MAX), str(I64_MAX)),
    (f"+{I64_MAX}", str(I64_MAX)),
    (f"-{I64_MAX}", str(-I64_MAX)),
    (f"-{-I64_MIN}", str(I64_MIN)),
    (str(I64_MAX + 1), "out of range"),
    (f"+{I64_MAX + 1}", "out of range"),
    (f"-{-I64_MIN + 1}", "out of range"),
    ("99999999999999999999", "out of range"),
    ("-99999999999999999999", "out of range"),
    ("-12", "-12"),
    ("12", "12"),
])
def test_repro_parse_int_refuses_a_numeral_past_the_range(
        numeral: str, result: str) -> None:
    """`parse_int` returns `Err("out of range")` for a numeral outside the
    i64 range, where it wrapped (`9223372036854775808` parsed as -2^63),
    and still reads `-9223372036854775808`, whose magnitude no `Int`
    holds."""
    assert _value(_PARSE_INT, "f", numeral) == result
