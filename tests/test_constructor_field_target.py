"""A constructor argument's instantiated field type is on the record.

The generic FUNCTION call has recorded each argument's instantiated formal as
its target since #747, because the verifier's narrowing walk consults that
table whenever the DECLARED formal is a TypeVar.  The constructor door never
did, so a field type the checker knows only after inference — and, separately,
any CONCRETE field type of a monomorphic constructor — was invisible to the
walk.  Both shapes were measured silent at `main` 6dc41d40 and at
`release/v0.2.0` 8eca11c0, each with the guard emitted and nothing on the
record:

* `match Some(0 - 5) { Some(@Nat) -> … }`.  The checker inferred `T = Nat` from
  the argument — before #1541 `0 - 5` was two non-negative literals, so
  `Nat - Nat` — typed the construction `Option<Nat>`, and the narrowing into
  that `@Nat` field had no target to be read from.  The artifact DID refuse the value, so it was an
  under-count of the Tier-3 checks rather than a false Tier 1; the common
  spellings (a parameter scrutinee, a `let` scrutinee, a call-produced one) all
  recorded correctly, which is what says the target was the gap.
* `MkBox([0 - 5])` into an `Array<Pos>` field.  Here nothing refused it
  either: the `-5` went into the `Array<Pos>`.  The same array literal against
  an `@Array<Pos>` PARAMETER does report `violated`, which is the control that
  separates the target threading from the lowering.

Found by the binder-position generator (`tests/test_binder_position_generator.py`),
which pinned both as what the compiler did until this fix; the cells here range
over the POSITION rather than over those two examples.
"""
from __future__ import annotations

import pytest

from tests.verifier_helpers import _verify


_POS = "type Pos = { @Int | @Int.0 > 0 };\n\n"


def _binds(source: str) -> list[tuple[str, str]]:
    return sorted(
        (o.kind, o.status) for o in _verify(source).obligations
        if o.kind in ("refine_bind", "nat_bind", "int_widen")
    )


# =====================================================================
# The position, not the two examples
# =====================================================================
#
# The dimension the class turns on is WHERE the field type comes from, since
# that is what decides whether a target was recorded: inferred from the
# argument (a generic constructor with no expected), declared concretely (a
# monomorphic constructor), or forced by the context (an expected type the
# enclosing position supplies).  Crossed with the shape of the narrowing:
# on the field itself, inside a container the field names, and one
# constructor deep.

_GENERIC_INFERRED = """public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(0 - 5) {
    Some(@Nat) -> @Nat.0,
    None -> 0 - 5
  }
}
"""

_CONCRETE_ARRAY_FIELD = _POS + """private data Box {
  MkBox(Array<Pos>)
}

private fn build(@Unit -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{
  MkBox([0 - 5])
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match build(()) {
    MkBox(@Array<Pos>) -> 1
  }
}
"""

_CONCRETE_MAP_FIELD = _POS + """private data Box {
  MkBox(Map<String, Pos>)
}

private fn build(@Unit -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{
  MkBox(map_insert(map_new(), "a", 0 - 5))
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match build(()) {
    MkBox(@Map<String, Pos>) -> 1
  }
}
"""

_CONCRETE_SCALAR_FIELD = _POS + """private data Box {
  MkBox(Pos)
}

private fn build(@Unit -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{
  MkBox(0 - 5)
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match build(()) {
    MkBox(@Pos) -> 1
  }
}
"""

_NESTED_CONSTRUCTOR = _POS + """private data Box {
  MkBox(Option<Pos>)
}

private fn build(@Unit -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{
  MkBox(Some(0 - 5))
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match build(()) {
    MkBox(@Option<Pos>) -> 1
  }
}
"""

#: label -> the program.  Every cell routes a value its field's type forbids
#: into a constructor argument.  Measured against this tree without the
#: target recording, three of the five are SILENT — no record at all,
#: `ok: true`: the generic field inferred from the argument, the
#: array-valued field, and the one a constructor deep.  The other two are
#: the controls, and they are what say the gap is the TARGET rather than the
#: constructor door as a whole: a concrete scalar field and a map-valued one
#: were already recorded without it.
_FIELD_SOURCES = {
    "generic, inferred from the argument": _GENERIC_INFERRED,
    "concrete, array-valued field": _CONCRETE_ARRAY_FIELD,
    "concrete, map-valued field": _CONCRETE_MAP_FIELD,
    "concrete, one constructor deep": _NESTED_CONSTRUCTOR,
    "concrete, scalar field (control)": _CONCRETE_SCALAR_FIELD,
}


@pytest.mark.parametrize("label", sorted(_FIELD_SOURCES))
def test_a_constructor_argument_the_field_forbids_is_on_the_record(
    label: str,
) -> None:
    """Whatever the field type's source, the narrowing is recorded and not
    proved.

    Two readings, neither of them a literal status.  A record EXISTS, which
    is what four of these five lacked; and none of the records is
    `verified`, which is the claim that matters about a value the field's
    type forbids.  Pinning `violated` instead would go green for a compiler
    that had stopped verifying and started refusing, and pinning the KIND
    would over-specify: which of the sign direction and the §2.6.5 predicate
    the verifier reaches first is a property of how the literal is typed
    rather than of the position under test.  The generic cell, whose field
    is a `@Nat`, reports `nat_bind`; the refined cells report `refine_bind`.
    """
    binds = _binds(_FIELD_SOURCES[label])
    assert binds, (
        f"{label}: a value the field's type forbids reaches it with nothing "
        f"in the obligation stream"
    )
    assert all(status != "verified" for _k, status in binds), (
        f"{label}: a value the field's type forbids is PROVED to satisfy it: "
        f"{binds}"
    )


@pytest.mark.parametrize(
    "label",
    ["concrete, scalar field (control)", "concrete, map-valued field"],
)
def test_the_controls_were_already_recorded_before_this_fix(
    label: str,
) -> None:
    """The premise for calling the other three a gap.

    A concrete SCALAR field and a map-valued one were both on the record
    without this fix, which is what separates "the constructor door records
    nothing" from "the door records only what an expected type reached".  If
    either ever needed the fix too, the three silent cells would be evidence
    of something wider than the target table and the account in this file
    would be wrong.
    """
    assert _binds(_FIELD_SOURCES[label]), label


def test_the_expected_type_still_wins_over_the_inferred_one() -> None:
    """A gap is filled, never displaced.

    `wrap_opt` returns `@Option<Nat>` and builds `Some(@Int.0)`.  The
    argument-driven inference reads `T = Int` off the argument and never
    consults the return, so recording unconditionally REPLACED the `Nat` the
    context had already supplied and lost the obligation — the single corpus
    mover on the first shape of this change, and `ch04_nat_binding.vera` is
    the conformance program that pins it.
    """
    source = """public fn wrap_opt(@Int -> @Option<Nat>)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}
"""
    assert _binds(source) == [("nat_bind", "verified")], _binds(source)
