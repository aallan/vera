"""#1207: mono discovery and the WASM call-rewrite name ONE clone.

An effect operation in a value position — ``get(())`` as the first element
of an array literal, or as a direct argument — is what fixes a generic
call's type variable.  Two independent consultors read that position: the
monomorphizer's instantiation DISCOVERY decides which clone to emit, and
the WASM call-rewrite decides which clone to CALL.  Discovery had no
effect-operation registry at all, so it fell through to the literal-driven
default (``Int``) and emitted ``pick$Int`` where the rewrite asked for
``pick$Nat`` — a dangling call target, so the caller is skipped with E602
and `main` disappears from a check-green, verify-clean program.

The fix single-sources the table: :func:`vera.slots.effect_op_result_names`
derives ``op name -> Vera result type name`` from an effect reference, and
all three consumers read it — codegen's per-function registry (the declared
``effects(<State<T>>)`` row), the handler-expression registry inside
``_translate_handle_state``, and mono discovery's scoped walk.

The proving check is a DIFFERENTIAL, not a unit test on either side: the
two consultors are separate code paths, and a unit test on discovery alone
would have stayed green through the whole desync.  Each case asserts

* the compiler reports NO E602/E620 — that diagnostic *is* the two sides
  disagreeing, reported by the compiler itself;
* the emitted clone carries the CHECKER's type name (``pick$Nat``,
  ``pick$Count``), pinning which side moved — an alignment that had both
  sides agree on ``Int`` would satisfy the first assertion alone; and
* the program runs to the checker's value.

Both scoping routes are covered, because codegen has two injection sites
for the registry and they are scoped differently: the enclosing
``handle[State<T>]`` expression (the op wins over a same-named user
function, matching ``_translate_handle_state``) and the function's own
declared effect row (a same-named user function wins, matching the
``_fn_sigs`` guard in ``codegen/functions.py``).
"""

from __future__ import annotations

import pytest

from tests.checker_helpers import _check_ok
from tests.codegen_helpers import _compile, _run
from tests.verifier_helpers import _verify_ok

_PICK = """
public forall<T> fn pick(@Array<T>, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
"""

# --- the reported shape: `get(())` as the FIRST array-literal element ---
# `pick`'s @T binds from the array's element type, which is the State cell's.
# `@T.0` is the SECOND parameter (De Bruijn: most recent), so the value is 9
# whichever clone runs — the discriminator is the clone NAME, asserted below.
_HANDLER_PLAIN = _PICK + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 2) {
    put(@Nat) -> { resume(()) }
  } in {
    put(6);
    nat_to_int(pick([get(()), 4], 9))
  }
}
"""

# The same shape through a scalar ALIAS cell.  `_effect_op_result_vera`
# records the alias-OPAQUE source spelling, so the clone is `pick$Count` —
# an alignment that resolved the alias on one side only would still dangle.
_HANDLER_ALIAS = """
type Count = Nat;
""" + _PICK + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Count>](@Count = 2) {
    put(@Count) -> { resume(()) }
  } in {
    put(6);
    nat_to_int(pick([get(()), 4], 9))
  }
}
"""

# The second injection site: no `handle` in this function at all — the op
# comes from the DECLARED effect row, and the handler is a caller away.
_EFFECT_ROW = _PICK + """
private fn inner(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(<State<Nat>>)
{
  pick([get(()), 4], 9)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 2) {
    put(@Nat) -> { resume(()) }
  } in {
    put(6);
    nat_to_int(inner(()))
  }
}
"""

# `get(())` in DIRECT argument position rather than inside an array — the
# same registry, reached through the plain parameter/argument unification.
_DIRECT_ARG = """
public forall<T> fn second(@T, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 2) {
    put(@Nat) -> { resume(()) }
  } in {
    put(6);
    nat_to_int(second(get(()), 9))
  }
}
"""

# --- the nesting shapes: what a handler's registry does to the enclosing one
# The registry is MERGED over the enclosing one for the handler's BODY, not
# swapped for it, on BOTH sides — discovery here and
# `_translate_handle_state` in codegen.  These three pin why, because the
# suite otherwise passes with discovery flipped to replace-semantics
# (measured), which would put the two consultors back out of step.

# An `Exn` handler contributes NO operation result type, so it is the case
# that separates merge from replace: the enclosing `State<Nat>` cell must
# still answer `get` inside the inner body.  Codegen agrees by construction
# — `_translate_handle_exn` never touches the registry at all — so replacing
# here would name `pick$Int` against the rewrite's `pick$Nat`: #1207 again.
_EXN_IN_STATE = _PICK + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 2) {
    put(@Nat) -> { resume(()) }
  } in {
    put(6);
    nat_to_int(handle[Exn<Int>] {
      throw(@Int) -> { 0 }
    } in {
      pick([get(()), 4], 9)
    })
  }
}
"""

# Two State cells of DIFFERENT types: the inner one owns `get` for its own
# body (the merge is ordered so the inner entry wins), and the outer answers
# outside it.  6 from the outer cell + 9 from `pick`'s second parameter.
_NESTED_DISTINCT_STATE = _PICK + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 2) {
    put(@Nat) -> { resume(()) }
  } in {
    put(6);
    nat_to_int(get(())) + handle[State<Int>](@Int = 5) {
      put(@Int) -> { resume(()) }
    } in {
      pick([get(()), 4], 9)
    }
  }
}
"""

# A user function named `get` INSIDE a handler body: the FUNCTION wins, as
# it does at the declared-row site — the checker resolves a bare name to a
# declaration of it wherever one is in scope, handler body included, and
# both discovery and the rewrite now ask that one question at the call site
# (#1284).  Its `@Int` return is what makes the case discriminate: resolving
# to the cell would name `pick$Nat`, the function names `pick$Int`.
#
# This case previously expected `pick$Nat`, pinning codegen's unconditional
# `_effect_ops` overwrite in `_translate_handle_state` as the oracle — a
# value the checker never agreed with, and the disagreement #1284 is.
_USER_GET_UNDER_HANDLER = """
private fn get(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  77
}
""" + _PICK + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 2) {
    put(@Nat) -> { resume(()) }
  } in {
    put(6);
    nat_to_int(pick([get(()), 4], 9))
  }
}
"""

# (case id, source, expected clone name, expected run value)
_CASES = [
    ("handler_plain", _HANDLER_PLAIN, "pick$Nat", 9),
    # #1511: the cell's alias is resolved where it is written before it
    # names the clone, so `Count` (an alias of `Nat`) names `pick$Nat`.
    ("handler_alias", _HANDLER_ALIAS, "pick$Nat", 9),
    ("effect_row", _EFFECT_ROW, "pick$Nat", 9),
    ("direct_arg", _DIRECT_ARG, "second$Nat", 9),
    ("exn_nested_in_state", _EXN_IN_STATE, "pick$Nat", 9),
    ("nested_distinct_state", _NESTED_DISTINCT_STATE, "pick$Int", 15),
    ("user_get_under_handler", _USER_GET_UNDER_HANDLER, "pick$Int", 9),
]

# The BUILTIN sibling of the same value position: `get(())` as an
# `array_append` argument under an alias cell.  No clone is named here — the
# builtin's argument typing is #1006's own path — so it is asserted on the
# value alone, as the control that the registry rework left it alone.
_BUILTIN_ARG = """
type Count = Nat;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Count>](@Count = 5) {
    put(@Count) -> { resume(()) }
  } in {
    let @Array<Nat> = array_append([1, 2], get(()));
    nat_to_int(@Array<Nat>.0[2])
  }
}
"""


@pytest.mark.parametrize(
    ("source", "clone", "expected"),
    [pytest.param(s, c, e, id=i) for i, s, c, e in _CASES],
)
def test_discovery_and_rewrite_name_one_clone(
    source: str, clone: str, expected: int,
) -> None:
    """No E602/E620, the checker's clone name, and the checker's value."""
    _check_ok(source)
    _verify_ok(source)
    result = _compile(source)
    codes = [d.error_code for d in result.diagnostics]
    assert "E602" not in codes, (
        "discovery and the call-rewrite named different clones: "
        f"{[d.description for d in result.diagnostics]}"
    )
    assert "E620" not in codes, (
        f"caller dropped: {[d.description for d in result.diagnostics]}"
    )
    assert f"(func ${clone} " in result.wat, (
        f"expected the clone {clone!r} in the emitted WAT; "
        f"got {sorted(_clone_names(result.wat))}"
    )
    assert _run(source) == expected


def test_builtin_argument_position_still_reads_the_cell() -> None:
    """`array_append(…, get(()))` under an alias cell keeps the cell's value."""
    _check_ok(_BUILTIN_ARG)
    _verify_ok(_BUILTIN_ARG)
    assert _run(_BUILTIN_ARG) == 5


def _clone_names(wat: str) -> set[str]:
    """Every ``$name$Type`` clone symbol defined in *wat*."""
    return {
        line.split("(func $", 1)[1].split(" ", 1)[0]
        for line in wat.splitlines()
        if "(func $" in line and "$" in line.split("(func $", 1)[1]
    }


def test_user_fn_named_get_still_wins_in_the_effect_row() -> None:
    """A same-named user function is NOT an effect op in the declared row.

    ``codegen/functions.py`` keeps an op out of ``_effect_ops`` when
    ``_fn_sigs`` already owns the name, so the rewrite resolves such a call
    through the ordinary function path.  Discovery has to make the same
    call, or the alignment this module pins would move the desync rather
    than close it.  ``get`` here returns ``@Bool``, which no State cell in
    the program carries — so a discovery that consulted the op registry
    anyway would emit ``pick$Int`` (the cell) instead of ``pick$Bool``.
    """
    source = """
private fn get(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  true
}
""" + _PICK + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  if pick([get(()), false], true) then { 1 } else { 2 }
}
"""
    _check_ok(source)
    result = _compile(source)
    assert "E602" not in [d.error_code for d in result.diagnostics], (
        f"{[d.description for d in result.diagnostics]}"
    )
    assert "(func $pick$Bool " in result.wat, sorted(_clone_names(result.wat))
