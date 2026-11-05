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
    completes, nothing is refuted, and what the base proved stays proved."""
    source = program_1(form, k, position, leaf, breaks=False)
    assert _run(source).ok, source
    verified = _verify(source)
    statuses = _f_refine_binds(verified)
    assert "violated" not in statuses, (statuses, source)
    assert not verified.errors, source


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
