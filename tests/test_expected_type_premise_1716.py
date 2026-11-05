"""An established fact comes from a value's own leaves (#1716).

THE MECHANISM.  The checker types a join (an `if`, a `match`, a block, a
`handle`) as the side its branches share the most of: `if c then
{ @Option<Int>.0 } else { None }` checked at `Option<PosInt>` is recorded
at `Option<PosInt>`, since its `None` was checked there, and
`if c then { @Int.0 } else { @PosInt.0 }` is recorded at `PosInt` with no
expected type at all.  That type states facts a branch never had.  Two
readers took it as a fact of the value:

* carrier 1, the payload obligation of a value handed to a nested refinement
  (`ContractVerifier._check_nested_refinement_obligation`, #1410), which
  took the source type's nested facts as premises: the goal was its own
  premise, so a call argument, a return, a `let` or a construction's field
  read `verified` while the run broke the payload; since #1833 a `State`
  handler in a `match` arm translates, and its arm reaches this too;
* carrier 2, the stand-in of a join the verifier cannot translate
  (`SmtContext._stand_in`, #1696 R2), which stated the recorded type's
  refinement over its constant: an `Exn` handler whose body is such a join
  proved `ensures(@Int.result > 0)` at Tier 1 and the run broke it.

THE RULE (`narrowing.established_type`).  A value is established at the
type its leaves (`narrowing.value_leaves`) share where every leaf that
yields a value has one type, and at none otherwise; a leaf's recorded type
is its own (a slot's binder, a call's declared return, a construction's
fields, a literal).  Carrier 1 takes its premises from that type, none where
there is none; carrier 2's stand-in carries its type's facts only where that
type is the one it was recorded at, and its base alone otherwise.  The
obligation is then discharged from the leaves' own facts under each
branch's path condition, which the solver context holds already.

THE INSTRUMENT.  For each carrier, the form of the join × the arm the
breaking leaf takes × the position the value is coerced at × the leaf's
kind, each cell a program and its run at an input that takes that arm: a
breaking leaf's run traps, and no record the cell is about reads
`verified`; the neighbour (the same shape with a leaf that holds) runs to
completion and stays `verified`, so the rule loses no proof the leaves
give.  A `verified` record whose run traps is the defect.
"""

from __future__ import annotations

from dataclasses import dataclass

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(
    decides=["vera/narrowing.py", "vera/smt.py", "vera/verifier.py"])

FILE = "expected_type_premise.vera"

#: The input every cell runs at: it takes the arm that holds the leaf under
#: test, and that leaf breaks the refinement there.
X = -5


def _verify(source: str) -> pipeline.Verified:
    verified = pipeline.verify(source, file=FILE)
    errors = verified.checked.errors
    assert not errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:90]) for d in errors]}\n{source}")
    return verified


def _run(source: str) -> pipeline.Ran:
    ran = pipeline.run(source, "t", [X], file=FILE)
    assert ran.compiled is not None and ran.compiled.ok, (
        "fixture must compile, got: "
        f"{[(d.error_code, d.description[:90]) for d in ran.compiled.errors]}"
        if ran.compiled is not None else "no compile")
    return ran


# =====================================================================
# The joins: a form over its leaves, the leaf under test at arm `k`
# =====================================================================

@dataclass(frozen=True)
class Form:
    """A join of *arms* leaves; ``build(leaves, k)`` writes it with the
    leaf at index *k* taken at `X` (``@Int.0`` is `X` wherever a form is
    written)."""

    id: str
    arms: int


def _match(leaves: list[str], k: int) -> str:
    patterns = [str(i) for i in range(len(leaves) - 1)] + ["_"]
    body = ",\n".join(f"    {p} -> {leaf}" for p, leaf in zip(patterns, leaves))
    return f"match @Int.0 + {-X + k} {{\n{body}\n  }}"


def _if(leaves: list[str], k: int) -> str:
    cond = "==" if k == 0 else "!="
    return (f"if @Int.0 + {-X} {cond} 0 then {{ {leaves[0]} }} "
            f"else {{ {leaves[1]} }}")


def build(form: Form, leaves: list[str], k: int, *, ty: str,
          filler_handle: str) -> str:
    """*form* over *leaves* (the leaf under test already at *k*); *ty* is
    the type the join is a value of, *filler_handle* an `Exn` clause's
    value for the forms that put the leaf under a handler."""
    if form.id == "if":
        return _if(leaves, k)
    if form.id in ("match2", "match3"):
        return _match(leaves, k)
    if form.id == "block":
        # `@Int.0` is `X` again after the `let`.
        return f"{{\n    let @Int = @Int.0 + 0;\n    {_if(leaves, k)}\n  }}"
    if form.id == "state_arm":
        wrapped = list(leaves)
        wrapped[k] = (
            "handle[State<Int>](@Int = 0) {\n"
            "      get(@Unit) -> { resume(@Int.0) },\n"
            "      put(@Int) -> { resume(()) }\n"
            f"    }} in {{\n      {leaves[k]}\n    }}")
        return _match(wrapped, k)
    if form.id == "exn_arm":
        wrapped = list(leaves)
        wrapped[k] = (
            "handle[Exn<Int>] {\n"
            f"      throw(@Int) -> {{ {filler_handle} }}\n"
            f"    }} in {{\n      {leaves[k]}\n    }}")
        return _match(wrapped, k)
    if form.id == "closure":
        # The closure's parameter is `X`, so `@Int.0` reads the same.
        return (f"apply_fn(fn(@Int -> @{ty}) effects(pure) {{\n"
                f"    {_if(leaves, k)}\n  }}, @Int.0)")
    raise AssertionError(form.id)  # pragma: no cover


FORMS_1 = (Form("if", 2), Form("match2", 2), Form("match3", 3),
           Form("block", 2), Form("state_arm", 2), Form("exn_arm", 2),
           Form("closure", 2))
FORMS_2 = (Form("if", 2), Form("match2", 2), Form("match3", 3),
           Form("block", 2))


# =====================================================================
# Carrier 1: a payload refinement, `Option<PosInt>`
# =====================================================================

_DECLS_1 = """\
type PosInt = { @Int | @Int.0 > 0 };

private fn mk(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

private fn mkp(@Int -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then { Some(@Int.0) } else { None }
}

private fn consume(@Option<PosInt> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<PosInt>.0 {
    Some(@PosInt) -> @PosInt.0,
    None -> 1
  }
}

private fn consume2(@Tuple<Option<PosInt>, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Tuple<Option<PosInt>, Int>.0 {
    Tuple(@Option<PosInt>, @Int) -> consume(@Option<PosInt>.0)
  }
}
"""

#: The leaf under test, by kind: one whose payload breaks `PosInt` at `X`
#: (the `Some(X)` the caller passes, `mk`'s, one built here), and its
#: neighbour, whose payload holds.
LEAVES_1 = {
    "slot": ("@Option<Int>.0", "@Option<PosInt>.0"),
    "call": ("mk(@Int.0)", "mkp(@Int.0)"),
    "construction": ("Some(@Int.0)", "Some(7)"),
}

#: Where the join is coerced to `Option<PosInt>`: (f's return type, f's
#: body around the join, t's body around the call of f).
POSITIONS_1 = {
    "argument": ("Int", "consume({v})", "{call}"),
    "return": ("Option<PosInt>", "{v}", "consume({call})"),
    "let": ("Int", "let @Option<PosInt> = {v};\n  consume(@Option<PosInt>.0)",
            "{call}"),
    "field": ("Int", "consume2(Tuple({v}, 1))", "{call}"),
}


def program_1(form: Form, k: int, position: str, leaf: str, *,
              breaks: bool) -> str:
    under_test = LEAVES_1[leaf][0 if breaks else 1]
    leaves = ["None"] * form.arms
    leaves[k] = under_test
    value = build(form, leaves, k, ty="Option<PosInt>", filler_handle="None")
    ret, body, outer = POSITIONS_1[position]
    call = "f(@Int.0, Some(@Int.0), Some(7))"
    return (
        f"{_DECLS_1}\n"
        f"public fn f(@Int, @Option<Int>, @Option<PosInt> -> @{ret})\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  {body.format(v=value)}\n}}\n\n"
        "public fn t(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  {outer.format(call=call)}\n}}\n")


CELLS_1 = [
    pytest.param(form, k, position, leaf,
                 id=f"{form.id}-arm{k}-{position}-{leaf}")
    for form in FORMS_1 for k in range(form.arms)
    for position in POSITIONS_1 for leaf in LEAVES_1
]


def _f_refine_binds(verified: pipeline.Verified) -> list[str]:
    return [o.status for o in verified.obligations
            if o.fn_name == "f" and o.kind == "refine_bind"]


@pytest.mark.parametrize("form,k,position,leaf", CELLS_1)
def test_a_payload_no_leaf_establishes_is_not_proved(
        form: Form, k: int, position: str, leaf: str) -> None:
    """Carrier 1: the join holds a leaf whose payload breaks `PosInt` at
    `X`; the run traps, and no record of the coercion reads `verified`."""
    source = program_1(form, k, position, leaf, breaks=True)
    ran = _run(source)
    assert ran.trap is not None, f"the breaking leaf must trap\n{source}"
    statuses = _f_refine_binds(_verify(source))
    assert statuses and "verified" not in statuses, (statuses, source)


@pytest.mark.parametrize("form,k,position,leaf", CELLS_1)
def test_a_payload_every_leaf_establishes_stays_proved(
        form: Form, k: int, position: str, leaf: str) -> None:
    """Carrier 1's neighbour: every leaf's payload holds; the run
    completes, nothing is refuted, and every record is what it was at the
    base (`_neighbour_records`)."""
    source = program_1(form, k, position, leaf, breaks=False)
    assert _run(source).ok, source
    verified = _verify(source)
    statuses = _f_refine_binds(verified)
    assert statuses == _neighbour_records(form, position, leaf), (
        statuses, source)
    assert not verified.errors, source


def _neighbour_records(form: Form, position: str, leaf: str) -> list[str]:
    """The neighbour's coercion records, as at da406983.  A slot or a call
    of `Option<PosInt>` beside `None` leaves is no row (every leaf carries
    the refinement already).  `Some(7)` is its field's row, proved; under an
    `Exn` handler the construction has no record and the value's row is
    disclosed (#1695's construction-in-a-handler line); as a tuple field
    through a join it is the field's guarded row."""
    if leaf != "construction":
        return []
    if form.id == "exn_arm":
        return ["tier3_unguarded"]
    if position == "field" and form.id in ("if", "match2", "match3", "block"):
        return ["tier3"]
    return ["verified"]


# =====================================================================
# Carrier 2: a head refinement through a stand-in, `PosInt`
# =====================================================================

_DECLS_2 = """\
type PosInt = { @Int | @Int.0 > 0 };

private fn same(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

private fn pos(@PosInt -> @PosInt)
  requires(true)
  ensures(true)
  effects(pure)
{
  @PosInt.0
}

private fn id(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}
"""

#: The leaf under test, by kind, breaking `> 0` at `X` and its neighbour.
#: `@PosInt.0` is the caller's 7.
LEAVES_2 = {
    "slot": ("@Int.0", "@PosInt.0"),
    "call": ("same(@Int.0)", "pos(@PosInt.0)"),
    "arithmetic": ("@Int.0 + 0", "@PosInt.0 + 0"),
}

#: Where the handler's value reaches f's `ensures(@Int.result > 0)`.
POSITIONS_2 = {
    "return": "{h}",
    "let": "let @Int = {h};\n  @Int.0",
    "argument": "id({h})",
    "field": "let Tuple<@Int, @Int> = Tuple({h}, 1);\n  @Int.1",
}


def program_2(form: Form, k: int, position: str, leaf: str, *,
              breaks: bool) -> str:
    under_test = LEAVES_2[leaf][0 if breaks else 1]
    leaves = ["@PosInt.0"] * form.arms
    leaves[k] = under_test
    join = build(form, leaves, k, ty="Int", filler_handle="@PosInt.0")
    handler = ("handle[Exn<Int>] {\n    throw(@Int) -> { @PosInt.0 }\n"
               f"  }} in {{\n    {join}\n  }}")
    return (
        f"{_DECLS_2}\n"
        "public fn f(@Int, @PosInt -> @Int)\n"
        "  requires(true)\n  ensures(@Int.result > 0)\n  effects(pure)\n"
        f"{{\n  {POSITIONS_2[position].format(h=handler)}\n}}\n\n"
        "public fn t(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  f(@Int.0, 7)\n}\n")


CELLS_2 = [
    pytest.param(form, k, position, leaf,
                 id=f"{form.id}-arm{k}-{position}-{leaf}")
    for form in FORMS_2 for k in range(form.arms)
    for position in POSITIONS_2 for leaf in LEAVES_2
]
#: The neighbours whose every leaf is a `PosInt`: a slot and a call.  The
#: arithmetic one is an `Int` leaf, the rule's cost
#: (`test_a_join_of_two_types_is_established_at_neither`).
NEIGHBOURS_2 = [c for c in CELLS_2 if c.values[3] != "arithmetic"]


def _f_ensures(verified: pipeline.Verified) -> str:
    (status,) = [o.status for o in verified.obligations
                 if o.fn_name == "f" and o.kind == "ensures"]
    return status


@pytest.mark.parametrize("form,k,position,leaf", CELLS_2)
def test_a_stand_in_carries_no_refinement_a_leaf_lacks(
        form: Form, k: int, position: str, leaf: str) -> None:
    """Carrier 2: the handler's body is a join with a leaf that breaks
    `> 0` at `X`; the run fails f's postcondition, which is not proved."""
    source = program_2(form, k, position, leaf, breaks=True)
    ran = _run(source)
    assert ran.trap is not None, f"the breaking leaf must trap\n{source}"
    assert _f_ensures(_verify(source)) != "verified", source


@pytest.mark.parametrize("form,k,position,leaf", NEIGHBOURS_2)
def test_a_stand_in_whose_leaves_share_its_refinement_keeps_it(
        form: Form, k: int, position: str, leaf: str) -> None:
    """Carrier 2's neighbour: every leaf is a `PosInt` (a slot, a call's
    return); the run completes, and the postcondition stays proved."""
    source = program_2(form, k, position, leaf, breaks=False)
    assert _run(source).ok, source
    assert _f_ensures(_verify(source)) == "verified", source


# =====================================================================
# The reported instances, unparametrised
# =====================================================================

_JOIN_PAYLOAD_PREMISE = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn f(@Int, @Option<Int> -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(if @Int.0 > 0 then { @Option<Int>.0 } else { None })
}

private fn g(@Option<PosInt> -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Option<PosInt>.0
}

public fn t(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match f(1, Some(@Int.0)) {
    Some(@PosInt) -> @PosInt.0,
    None -> 0
  }
}
"""


def test_repro_1716_a_join_argument_assumes_no_payload_its_branch_lacks() -> None:
    """The issue as filed: the argument's payload row reads `verified` on
    the join's recorded `Option<PosInt>`; `t(-5)` traps in `t`'s binder."""
    verified = _verify(_JOIN_PAYLOAD_PREMISE)
    assert [(o.status, o.error_code) for o in verified.obligations
            if o.fn_name == "f" and o.kind == "refine_bind"] == [
                ("violated", "E505")]
    assert _run(_JOIN_PAYLOAD_PREMISE).trap is not None


_HANDLE_IN_AN_ARM = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn hb(@Int -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    0 -> None,
    _ -> handle[State<Int>](@Int = 0) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      Some(@Int.0)
    }
  }
}

public fn t(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match hb(@Int.0) {
    None -> 0 - 99,
    Some(@PosInt) -> @PosInt.0
  }
}
"""


def test_repro_1716_a_state_handler_in_a_match_arm_is_refuted() -> None:
    """The second instance (R111's `h13`, since #1833 translates the
    handler): the return's payload is refuted, and `t(-5)` traps."""
    verified = _verify(_HANDLE_IN_AN_ARM)
    assert [(o.status, o.error_code) for o in verified.obligations
            if o.fn_name == "hb" and o.kind == "refine_bind"] == [
                ("violated", "E505")]
    assert _run(_HANDLE_IN_AN_ARM).trap is not None


_EXN_HANDLER_OVER_A_JOIN = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn f(@Bool, @Int, @PosInt -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Int = handle[Exn<Int>] {
    throw(@Int) -> { 1 }
  } in {
    if @Bool.0 then { @Int.0 } else { @PosInt.0 }
  };
  @Int.0
}

public fn t(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true, @Int.0, 3)
}
"""


def test_repro_1716_a_stand_in_states_no_refinement_of_its_recorded_join() -> None:
    """Carrier 2 as found: the `Exn` handler's stand-in took the join's
    recorded `PosInt`, so f's postcondition proved and `t(-5)` broke it;
    it is a runtime check (E522), as before #1833."""
    verified = _verify(_EXN_HANDLER_OVER_A_JOIN)
    assert _f_ensures(verified) == "tier3"
    assert "E522" in [d.error_code for d in verified.warnings]
    ran = _run(_EXN_HANDLER_OVER_A_JOIN)
    assert ran.trap is not None


def test_a_join_of_two_types_is_established_at_neither() -> None:
    """The rule's cost, pinned: a handler whose body joins a `PosInt` slot
    and an `Int` that happens to be positive (`@PosInt.0 + 0`) proves
    nothing of `> 0`, since no leaf's type states it of the second."""
    source = program_2(Form("if", 2), 0, "return", "arithmetic", breaks=False)
    assert "@PosInt.0 + 0" in source
    assert _run(source).ok
    assert _f_ensures(_verify(source)) == "tier3"


_CLOSURE_RETURN = """\
type PosInt = { @Int | @Int.0 > 0 };
type ToPos = fn(Int -> PosInt) effects(pure);

public fn f(@ToPos, @Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  apply_fn(@ToPos.0, @Int.0)
}
"""


def test_a_call_stand_in_keeps_its_declared_refined_return() -> None:
    """A leaf is not a join: the stand-in of a call the verifier cannot
    translate (a closure applied through `apply_fn`) carries its declared
    return's refinement, the callee's own contract, so the postcondition
    resting on it stays proved."""
    verified = _verify(_CLOSURE_RETURN)
    assert _f_ensures(verified) == "verified"


def _exn_let(clause: str, body: str) -> str:
    """f binds an `Exn` handler's value and returns it under
    `ensures(@Int.result > 0)`; the handler's stand-in decides the proof."""
    return (
        "type PosInt = { @Int | @Int.0 > 0 };\n\n"
        "private fn pos(@PosInt -> @PosInt)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @PosInt.0\n}\n\n"
        "public fn f(@Bool, @PosInt -> @Int)\n"
        "  requires(true)\n  ensures(@Int.result > 0)\n  effects(pure)\n"
        "{\n"
        "  let @Int = handle[Exn<Int>] {\n"
        f"    throw(@Int) -> {{ {clause} }}\n"
        f"  }} in {{\n    {body}\n  }};\n"
        "  @Int.0\n}\n")


#: Handler bodies whose every value-yielding leaf is a `PosInt`, beside an
#: `Exn` clause whose value is the literal `1`.
LITERAL_CLAUSE_BODIES = {
    "if_of_slots": "if @Bool.0 then { @PosInt.0 } else { @PosInt.0 }",
    "block_tail": "{\n      let @Int = 2;\n      @PosInt.0\n    }",
    "slot_beside_call": "if @Bool.0 then { @PosInt.0 } else { pos(@PosInt.0) }",
    "throw_arm": "if @Bool.0 then { throw(1) } else { @PosInt.0 }",
}


@pytest.mark.parametrize("body", list(LITERAL_CLAUSE_BODIES.values()),
                         ids=list(LITERAL_CLAUSE_BODIES))
def test_a_literal_leaf_that_satisfies_the_refinement_shares_it(body: str) -> None:
    """A literal's value is known: the clause value `1` satisfies `> 0`, so
    the handler is established at `PosInt` with its `PosInt` leaves and the
    postcondition stays proved; both arms run clean."""
    source = _exn_let("1", body)
    assert _f_ensures(_verify(source)) == "verified", source
    for flag in (0, 1):
        ran = pipeline.run(source, "f", [flag, 3], file=FILE)
        assert ran.ok, source


def test_a_literal_leaf_that_breaks_the_refinement_shares_nothing() -> None:
    """The clause value `0` does not satisfy `> 0`: the postcondition is not
    proved, and the run that throws breaks it."""
    source = _exn_let("0", LITERAL_CLAUSE_BODIES["throw_arm"])
    assert _f_ensures(_verify(source)) == "tier3"
    assert pipeline.run(source, "f", [1, 3], file=FILE).trap is not None


def test_a_never_leaf_takes_no_part_in_the_shared_type() -> None:
    """A `throw` arm yields no value: beside a `PosInt` arm and a `PosInt`
    clause value, the handler is established at `PosInt`."""
    source = _exn_let("@PosInt.0", LITERAL_CLAUSE_BODIES["throw_arm"])
    assert _f_ensures(_verify(source)) == "verified"
    assert pipeline.run(source, "f", [1, 3], file=FILE).ok


# =====================================================================
# Two leaves share a type only where they state the same facts
# =====================================================================

_REFINEMENTS = """\
type PosInt = { @Int | @Int.0 > 0 };
type NegInt = { @Int | @Int.0 < 0 };
type AlsoPos = PosInt;
type SamePos = { @Int | @Int.0 > 0 };
"""

#: The second leaf's type beside a `PosInt` leaf, the run's value for it,
#: and whether the two state the same facts (so the proof stands).
PAIRS = {
    "the_same_name": ("PosInt", "3", True),
    "another_name_for_it": ("AlsoPos", "3", True),
    "the_predicate_written_again": ("SamePos", "3", True),
    "another_predicate": ("NegInt", "0 - 4", False),
}


def _pair_carrier_1(other: str, value: str) -> str:
    return (
        f"{_REFINEMENTS}\n"
        "private fn consume(@Option<PosInt> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  match @Option<PosInt>.0 {\n    Some(@PosInt) -> @PosInt.0,\n"
        "    None -> 1\n  }\n}\n\n"
        f"public fn f(@Bool, @Option<PosInt>, @Option<{other}> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  consume(if @Bool.0 then {{ @Option<PosInt>.0 }} "
        f"else {{ @Option<{other}>.0 }})\n}}\n\n"
        "public fn t(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  f(@Int.0 > 0, Some(3), Some({value}))\n}}\n")


def _pair_carrier_2(other: str, value: str) -> str:
    return (
        f"{_REFINEMENTS}\n"
        f"public fn f(@Bool, @PosInt, @{other} -> @Int)\n"
        "  requires(true)\n  ensures(@Int.result > 0)\n  effects(pure)\n"
        "{\n  let @Int = handle[Exn<Int>] {\n"
        "    throw(@Int) -> { @PosInt.0 }\n"
        f"  }} in {{\n    if @Bool.0 then {{ @PosInt.0 }} else {{ @{other}.0 }}\n"
        "  };\n  @Int.0\n}\n\n"
        "public fn t(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  f(@Int.0 > 0, 3, {value})\n}}\n")


@pytest.mark.parametrize("pair", list(PAIRS))
def test_two_refinements_share_a_type_only_by_their_predicate(pair: str) -> None:
    """A join of a `PosInt` leaf and a second refined leaf over one base, on
    both carriers, run at the second leaf's arm (`t(-5)`): a second name
    for the predicate, or the predicate written again, shares it and the
    proof stands with a clean run; another predicate (`NegInt`) shares
    nothing, and the run breaks what a shared type would have proved."""
    other, value, shared = PAIRS[pair]
    for build, statuses in (
            (_pair_carrier_1, lambda v: _f_refine_binds(v)),
            (_pair_carrier_2, lambda v: [_f_ensures(v)])):
        source = build(other, value)
        got = statuses(_verify(source))
        ran = _run(source)
        if shared:
            # Carrier 1 lists no row where the leaves carry the refinement
            # already (the table's own rule); carrier 2's `ensures` is one.
            assert all(s == "verified" for s in got), (got, source)
            assert ran.ok, source
        else:
            assert got and "verified" not in got, (got, source)
            assert ran.trap is not None, source


def test_an_unknown_leaf_shares_no_type() -> None:
    """A leaf whose type is unknown (or holds an unknown part) establishes
    nothing, where `types_equal` would call it equal to any type, `Never`
    included."""
    from vera import ast, narrowing
    from vera.types import INT, NEVER, AdtType, RefinedType, UnknownType

    pos = RefinedType(INT, ast.BinaryExpr(
        op=ast.BinOp.GT, left=ast.SlotRef(type_name="Int", type_args=None,
                                          index=0),
        right=ast.IntLit(value=0)))
    for unknown in (UnknownType(), AdtType("Option", (UnknownType(),))):
        for other in (pos, AdtType("Option", (pos,)), NEVER):
            left, right = ast.BoolLit(value=True), ast.BoolLit(value=False)
            join = ast.IfExpr(condition=ast.BoolLit(value=True),
                              then_branch=left, else_branch=right)
            types = {id(left): other, id(right): unknown}
            assert narrowing.established_type(
                join, lambda e: types.get(id(e))) is None, (unknown, other)
        assert not narrowing.same_established(unknown, unknown)


# =====================================================================
# The comparison and the literal rule, one branch per cell
# =====================================================================

def _pred(op: "object", bound: int) -> "object":
    from vera import ast
    return ast.BinaryExpr(
        op=op, left=ast.SlotRef(type_name="Int", type_args=None, index=0),
        right=ast.IntLit(value=bound))


def _types() -> dict[str, "object"]:
    from vera import ast
    from vera.types import (
        INT, NAT, AdtType, ConcreteEffectRow, EffectInstance, FunctionType,
        PureEffectRow, RefinedType, TypeVar)
    pos = RefinedType(INT, _pred(ast.BinOp.GT, 0))
    io = ConcreteEffectRow(frozenset({EffectInstance("IO", ())}))
    return {
        "pos": pos, "pos_again": RefinedType(INT, _pred(ast.BinOp.GT, 0)),
        "neg": RefinedType(INT, _pred(ast.BinOp.LT, 0)),
        "pos_over_nat": RefinedType(NAT, _pred(ast.BinOp.GT, 0)),
        "int": INT, "nat": NAT,
        "opt_pos": AdtType("Option", (pos,)),
        "opt_neg": AdtType("Option", (RefinedType(INT, _pred(ast.BinOp.LT, 0)),)),
        "res_pos": AdtType("Result", (pos,)),
        "pair": AdtType("Tuple", (pos, INT)),
        "fn": FunctionType((pos,), INT, PureEffectRow()),
        "fn_two": FunctionType((pos, INT), INT, PureEffectRow()),
        "fn_param": FunctionType((INT,), INT, PureEffectRow()),
        "fn_ret": FunctionType((pos,), pos, PureEffectRow()),
        "fn_io": FunctionType((pos,), INT, io),
        "t": TypeVar("T"), "u": TypeVar("U"),
    }


def test_same_established_compares_a_refinement_by_its_predicate_and_base() -> None:
    from vera.narrowing import same_established
    ty = _types()
    assert same_established(ty["pos"], ty["pos_again"])
    assert not same_established(ty["pos"], ty["neg"])
    assert not same_established(ty["pos"], ty["int"])
    assert not same_established(ty["int"], ty["pos"])
    assert not same_established(ty["pos"], ty["pos_over_nat"])


def test_same_established_compares_a_data_type_by_name_arity_and_arguments() -> None:
    from vera.narrowing import same_established
    ty = _types()
    assert same_established(ty["opt_pos"], ty["opt_pos"])
    assert not same_established(ty["opt_pos"], ty["opt_neg"])
    assert not same_established(ty["opt_pos"], ty["res_pos"])
    assert not same_established(ty["opt_pos"], ty["pair"])
    assert not same_established(ty["opt_pos"], ty["int"])


def test_same_established_compares_a_function_type_part_by_part() -> None:
    from vera.narrowing import same_established
    ty = _types()
    assert same_established(ty["fn"], ty["fn"])
    for other in ("fn_two", "fn_param", "fn_ret", "fn_io", "int"):
        assert not same_established(ty["fn"], ty[other]), other


def test_same_established_compares_a_primitive_and_a_variable_by_name() -> None:
    from vera.narrowing import same_established
    from vera.types import NEVER, UnknownType
    ty = _types()
    assert same_established(ty["int"], ty["int"])
    assert same_established(NEVER, NEVER)
    assert not same_established(ty["int"], ty["nat"])
    assert not same_established(ty["int"], ty["t"])
    assert same_established(ty["t"], ty["t"])
    assert not same_established(ty["t"], ty["u"])
    assert not same_established(ty["t"], ty["int"])
    assert not same_established(UnknownType(), UnknownType())
    assert not same_established(None, ty["int"])
    assert not same_established(ty["int"], None)


def test_a_negated_number_is_a_literal_and_a_negated_bool_is_not() -> None:
    from vera import ast
    from vera.narrowing import is_literal
    three = ast.IntLit(value=3)
    assert is_literal(ast.UnaryExpr(op=ast.UnaryOp.NEG, operand=three))
    assert not is_literal(ast.UnaryExpr(
        op=ast.UnaryOp.NOT, operand=ast.BoolLit(value=True)))
    assert not is_literal(ast.UnaryExpr(
        op=ast.UnaryOp.NEG, operand=ast.SlotRef(
            type_name="Int", type_args=None, index=0)))
    assert not is_literal(ast.UnaryExpr(
        op=ast.UnaryOp.NEG, operand=ast.StringLit(value="a")))
    assert is_literal(ast.UnaryExpr(
        op=ast.UnaryOp.NEG, operand=ast.FloatLit(value=1.5)))


def test_a_literal_satisfies_a_type_only_by_every_fact_it_states() -> None:
    """True where the solver proves each fact of the literal, false where
    one fails, where the literal is of another sort, and where a predicate
    of the type has no term."""
    from vera import ast
    from vera.smt import SmtContext
    from vera.types import INT, NAT, RefinedType
    smt, ty = SmtContext(), _types()
    three, zero = ast.IntLit(value=3), ast.IntLit(value=0)
    assert smt._literal_satisfies(three, ty["pos"])
    assert not smt._literal_satisfies(zero, ty["pos"])
    assert smt._literal_satisfies(three, INT)
    assert smt._literal_satisfies(zero, NAT)
    assert not smt._literal_satisfies(
        ast.UnaryExpr(op=ast.UnaryOp.NEG, operand=three), NAT)
    assert not smt._literal_satisfies(ast.BoolLit(value=True), ty["pos"])
    assert not smt._literal_satisfies(ast.BoolLit(value=True), INT)
    assert not smt._literal_satisfies(ast.FloatLit(value=3.0), ty["pos"])
    no_term = RefinedType(INT, ast.SlotRef(
        type_name="Bool", type_args=None, index=0))
    assert not smt._literal_satisfies(three, no_term)
