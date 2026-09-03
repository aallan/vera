"""#1285: which cell ``new(State<T>)`` reads under a multi-``State`` row.

``old(State<T>)`` has been family-keyed since #1205/#1209 — the snapshot map
and the read both go through ``_state_effect_family``, so
``old(State<Bool>)`` reaches the Bool cell whatever else the row declares.
``new(State<T>)`` instead read the name-keyed ``_effect_ops["get"]``, which
holds whichever family the row registered FIRST.  Under a single-``State``
row the two keyings coincide, which is why every existing program agreed;
under a multi-``State`` row they do not, and the two sides of one ``ensures``
clause were reading different cells.

The failure was not quiet.  ``effects(<State<Int>, State<Bool>>)`` with
``ensures(new(State<Bool>) == true)`` is check-green and verify-green, emits
``state_get_Int``'s i64 into the Bool comparison's ``i32.eq``, and dies at
load with wasmtime's raw ``type mismatch``.  But the type mismatch is the
symptom of a wrong cell, not the defect: where both cells share a width the
module loads and silently answers about the other one, which is what the
``Int``/``Nat`` case below pins.

Each case seeds its target cell with a value the OTHER cell in the row
cannot be holding, so a read of the wrong cell cannot coincide with the
right answer.  The postconditions are Tier 3 (E523 — ``new()`` is outside the
decidable fragment), so they are compiled to runtime checks: the program
trapping on its own ``ensures`` is what a wrong-cell read looks like here,
which makes each case an ensures-and-run soundness differential rather than
a value comparison alone.
"""

from __future__ import annotations

import pytest

from tests.checker_helpers import _check_err, _check_ok
from tests.codegen_helpers import _compile, _run, wat_calls
from tests.verifier_helpers import _verify_ok


# --- the issue's shape: Bool named second, read at the Bool cell -------

# The Bool cell is left at its default (false) and the Int cell is seeded
# with 42 by the caller's handler.  Reading the Int cell for
# `new(State<Bool>)` cannot produce `false`: 42 is neither 0 nor a valid
# i32 the `i32.eq` would accept, which is why this shape failed at load.
_BOOL_SECOND = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(new(State<Bool>) == false)
  effects(<State<Int>, State<Bool>>)
{
  7
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Bool>>)
{
  handle[State<Int>](@Int = 42) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    probe(())
  }
}
"""


def test_new_reads_the_family_the_contract_names_not_the_rows_first() -> None:
    """pre_fix: `call $vera.state_get_Int` (i64) into the Bool `i32.eq`,
    and `vera run` died at load with `type mismatch: expected i32, found
    i64` — from source both `vera check` and `vera verify` accept."""
    _check_ok(_BOOL_SECOND)
    _verify_ok(_BOOL_SECOND)
    assert _run(_BOOL_SECOND) == 7


def test_new_emits_the_named_familys_getter() -> None:
    """The dispatch target itself, so a case that happened to agree on
    values still fails when the wrong import is called."""
    result = _compile(_BOOL_SECOND)
    assert wat_calls(result.wat, "vera.state_get_Bool")


# --- the same defect where BOTH cells are i64 (loads, wrong answer) ----

# `Int` and `Nat` are both i64, so nothing about the widths refuses this
# module: pre-fix it loaded, read the FIRST-registered family's cell, and
# either answered about the wrong cell or trapped on its own postcondition.
# The two cells hold 42 and 9 — neither is the other, and neither is a
# default — so the read cannot be right by coincidence.
_NAT_SECOND = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(new(State<Nat>) == 9)
  effects(<State<Int>, State<Nat>>)
{
  7
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    handle[State<Nat>](@Nat = 9) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      probe(())
    }
  }
}
"""


def test_new_same_width_cells_read_the_named_one() -> None:
    """The width-blind case: pre-fix this loaded and trapped on probe's own
    ensures, having read the Int cell's 42 where the contract named the Nat
    cell's 9.  A postcondition the verifier discharged and the runtime
    refutes is the soundness shape, not a codegen inconvenience."""
    _check_ok(_NAT_SECOND)
    _verify_ok(_NAT_SECOND)
    assert _run(_NAT_SECOND) == 7
    result = _compile(_NAT_SECOND)
    assert wat_calls(result.wat, "vera.state_get_Nat")


# --- old() and new() on the two sides of one clause -------------------

_OLD_AND_NEW = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(new(State<Nat>) == old(State<Nat>))
  effects(<State<Int>, State<Nat>>)
{
  7
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    handle[State<Nat>](@Nat = 9) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      probe(())
    }
  }
}
"""


def test_old_and_new_of_one_family_read_one_cell() -> None:
    """The clause that names the SAME family twice: `old` was already
    family-keyed, so pre-fix the two sides read different cells and the
    unchanged-cell claim was refuted at runtime (9 vs 42)."""
    _check_ok(_OLD_AND_NEW)
    _verify_ok(_OLD_AND_NEW)
    assert _run(_OLD_AND_NEW) == 7


# --- controls: the single-State row is unmoved ------------------------

_SINGLE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(new(State<Int>) == 42)
  effects(<State<Int>>)
{
  7
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    probe(())
  }
}
"""


def test_single_state_new_is_unchanged() -> None:
    """Under one State the name-keyed and family-keyed lookups coincide;
    this is the shape the whole existing corpus exercises."""
    _check_ok(_SINGLE)
    _verify_ok(_SINGLE)
    assert _run(_SINGLE) == 7
    result = _compile(_SINGLE)
    assert wat_calls(result.wat, "vera.state_get_Int")


_SINGLE_ALIAS = """
type Count = Nat;

private fn probe(@Unit -> @Int)
  requires(true)
  ensures(new(State<Count>) == 9)
  effects(<State<Count>>)
{
  7
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Count>](@Count = 9) {
    get(@Unit) -> { resume(@Count.0) },
    put(@Count) -> { resume(()) }
  } in {
    probe(())
  }
}
"""


def test_new_through_an_alias_resolves_the_same_family_old_does() -> None:
    """`_state_effect_family` resolves `State<Count>` to the `Nat` family
    (#1205), which is the key both the import registry and the snapshot map
    use — so routing `new()` through it must not lose the alias hop."""
    _check_ok(_SINGLE_ALIAS)
    _verify_ok(_SINGLE_ALIAS)
    assert _run(_SINGLE_ALIAS) == 7


# --- the runtime check is real, not vacuous ---------------------------

_REFUTED = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(new(State<Nat>) == 8)
  effects(<State<Int>, State<Nat>>)
{
  7
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    handle[State<Nat>](@Nat = 9) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      probe(())
    }
  }
}
"""


_UNDECLARED_FAMILY = """
public fn probe(@Unit -> @Int)
  requires(true)
  ensures({form}(State<Bool>) == false)
  effects(<State<Int>>)
{{
  7
}}
"""


@pytest.mark.parametrize("form", ["new", "old"])
def test_a_family_the_row_does_not_declare_is_loud_on_both_sides(
    form: str,
) -> None:
    """`new()` and `old()` fail the SAME way on a family with no cell.

    The CHECKER now refuses both (#1298): a contract may only name a
    `State<T>` the enclosing function's effect row declares, so the program
    never reaches codegen.  It used to be check-green and land on codegen's
    E699 — the internal-compiler-error diagnostic whose own text says the
    type checker should have rejected the input, which was exactly the
    situation, with a bug-report request the user should not act on.

    Pinning both forms together is what keeps the family keying honest: a
    `new()` that fell back to any getter would pass this file's other cases
    and fail only here.  They are rejected by ONE rule, since both read the
    same cell.
    """
    source = _UNDECLARED_FAMILY.format(form=form)
    diags = _check_err(source, "State<Bool>")
    codes = [d.error_code for d in diags]
    assert "E177" in codes, [(d.error_code, d.description) for d in diags]
    named = next(d for d in diags if d.error_code == "E177")
    # The diagnostic names the UNDECLARED family and the row that was
    # declared instead; without both a reader cannot tell which of the two
    # to change.
    assert "State<Bool>" in named.description, named.description
    assert "State<Int>" in named.description, named.description


def test_an_open_row_tail_may_supply_the_family() -> None:
    """The carve-out, pinned: an OPEN row is not refused.

    A row entry naming a `forall` type parameter is a row VARIABLE, and its
    tail may be instantiated at a call site that supplies the family — so
    refusing here would reject a program legal under some instantiation. The
    rule E177 enforces is membership in a CLOSED row.

    Worth stating how this cell arrived: a first pass concluded open rows were
    not expressible and asserted that instead. A tripwire over the compiler's
    own `row_var` assignments refuted it — `resolution.py` sets one whenever a
    row entry names a type parameter — which is the shape below.
    """
    source = """
public forall<E> fn probe(@Unit -> @Int)
  requires(true)
  ensures(new(State<Bool>) == false)
  effects(<State<Int>, E>)
{
  7
}
"""
    _check_ok(source)


def test_the_declared_family_is_still_accepted() -> None:
    """The over-rejection control: a contract naming the row's OWN family
    checks clean, so the new rule refuses only what the row omits."""
    source = """
public fn probe(@Unit -> @Int)
  requires(true)
  ensures(new(State<Int>) == 0)
  effects(<State<Int>>)
{
  7
}
"""
    _check_ok(source)


@pytest.mark.parametrize("form", ["new", "old"])
def test_a_second_declared_family_is_accepted(form: str) -> None:
    """A row declaring TWO families accepts either — the rule is membership,
    not "the first one"."""
    source = f"""
public fn probe(@Unit -> @Int)
  requires(true)
  ensures({form}(State<Bool>) == false)
  effects(<State<Int>, State<Bool>>)
{{
  7
}}
"""
    _check_ok(source)


def test_a_false_postcondition_still_traps() -> None:
    """The instrument check.  Every case above asserts a program RUNS, which
    proves nothing unless a wrong `new()` would have been caught — so the
    same shape with the cell's value off by one must trap on its Tier 3
    postcondition.  Without this, a `new()` that read nothing at all would
    pass the whole file.
    """
    from vera.codegen.api import WasmTrapError

    _check_ok(_REFUTED)
    with pytest.raises(WasmTrapError) as excinfo:
        _run(_REFUTED)
    # The KIND, not merely that something trapped: an `unreachable` from a
    # GC guard or a narrowing check would satisfy a bare `raises` and prove
    # nothing about the postcondition, which is the one thing this test
    # exists to establish.
    assert excinfo.value.kind == "contract_violation", excinfo.value.kind
