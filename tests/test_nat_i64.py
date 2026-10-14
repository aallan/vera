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

import pytest

from tests import pipeline

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
