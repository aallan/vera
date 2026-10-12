"""Regression: same-ADT self-nested constructor sort selection (#918).

Before #918 the verifier's ``_find_sort_for_ctor`` resolved a constructor to
its ADT and returned the FIRST cached Z3 sort whose *base* name (before ``<``)
matched — with no discrimination by type arguments.  For a same-ADT
self-nesting like ``Some(Some(x))`` the outer ``Some`` resolved to whichever
``Option<...>`` instantiation happened to be cached (e.g. ``Option<Int>``)
rather than the needed ``Option<Option<Int>>``, so ``sort.constructor(idx)``
was fed a wrongly-sorted ``DatatypeRef`` and Z3 crashed with an **uncaught
Python traceback** on a ``vera check``-green program:

* a nested-``Option``-returning body ``Some(Some(@Int.0))`` →
  ``z3.z3types.Z3Exception: Sort mismatch``;
* a nested same-ADT ctor literal in a CONTRACT (``ensures(Some(Some(x)) == ...)``)
  once an ``Option<Int>`` sort was seeded →
  ``AttributeError: 'DatatypeSortRef' object has no attribute 'is_int'``;
* ``vera test`` on such a function routed through the verifier and crashed the
  same way.

The fix translates a constructor call's arguments first, recovers each
argument's Vera type from its Z3 sort, and unifies those against the
constructor's declared (``TypeVar``-bearing) field types to pin the owning
ADT's FULL instantiation — so ``Some`` in an ``Option<Option<Int>>`` context
selects the ``Option<Option<Int>>`` sort (whose argument slot expects
``Option<Int>``, matching the inner ``Some(x)``).

Two soundness/regression invariants are pinned alongside the crash fix:

* **No false PROVE.** A genuinely-false postcondition over a nested-ADT value
  must still be disproved (E500).  The fix enables *real* Tier-1 reasoning over
  the nested structure — it must reject a false claim, not blanket-demote.
* **No false E500 on unrelated calls.** Pinning is gated to ADTs that already
  have a cached instantiation, so a top-level ``Some(42)`` argument in a caller
  whose context never materialised ``Option`` stays opaque/demoted exactly as
  before (#882).  Materialising it on demand would flip such a call from
  opaque-demote to a fresh unconstrained return value and regress an unrelated
  ``ensures``-over-a-helper-result to a false counterexample (the #887 trap).
"""
from __future__ import annotations

from tests.verifier_helpers import _verify, _verify_ok, _verify_err
from tests.codegen_helpers import _compile, _run


# A nested-`Option`-returning function whose body is `Some(Some(@Int.0))`.
# RED on base: the verifier crashes with `z3.z3types.Z3Exception: Sort mismatch`
# while translating the outer `Some` against the cached `Option<Int>` sort.
_NESTED_BODY = """
private fn f(@Int -> @Option<Option<Int>>)
  requires(true)
  ensures(true)
  effects(pure)
{ Some(Some(@Int.0)) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match f(1) {
    Some(@Option<Int>) -> match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> 0 },
    None -> 0
  }
}
"""


# A nested same-ADT ctor literal inside a CONTRACT.  The `@Option<Int>`
# parameter seeds an `Option<Int>` sort into the cache, so the outer `Some` in
# the ensures literal resolves (base-name-wins) to `Option<Int>` — its arg is
# `Option<Int>`-sorted while the ctor expects `Int`.  RED on base:
# `AttributeError: 'DatatypeSortRef' object has no attribute 'is_int'`.
_NESTED_CONTRACT = """
private fn g(@Option<Int>, @Int -> @Int)
  requires(true)
  ensures(Some(Some(@Int.0)) == Some(Some(@Int.0)))
  effects(pure)
{ @Int.0 }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ g(Some(1), 2) }
"""


# A TRUE postcondition over the nested value — the fix must reason about the
# nested `Option<Option<Int>>` structure and PROVE it at Tier 1 (not merely
# stop crashing by demoting).
_NESTED_TRUE = """
private fn f(@Int -> @Option<Option<Int>>)
  requires(true)
  ensures(@Option<Option<Int>>.result == Some(Some(@Int.0)))
  effects(pure)
{ Some(Some(@Int.0)) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match f(1) { Some(@Option<Int>) -> 1, None -> 0 } }
"""


# A FALSE postcondition over the nested value: the body returns `Some(Some(x))`
# but the ensures claims `Some(Some(x + 1))`.  Genuinely false — must be
# disproved (E500).  The soundness probe: the fix must not introduce a false
# PROVE by pinning a wrong sort or over-eagerly demoting.
_NESTED_FALSE = """
private fn f(@Int -> @Option<Option<Int>>)
  requires(true)
  ensures(@Option<Option<Int>>.result == Some(Some(@Int.0 + 1)))
  effects(pure)
{ Some(Some(@Int.0)) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match f(1) { Some(@Option<Int>) -> 1, None -> 0 } }
"""


# Regression guard for the #887 trap: a single-level `Some(42)` argument to a
# helper call, in a caller (`main`) whose context never materialises `Option`.
# The helper has a trivial `ensures(true)`, so on base the call is opaque and
# `main`'s `== 42` postcondition is discharged another way (Tier-1 clean with a
# Tier-3 runtime check).  A too-broad on-demand sort materialisation flips the
# call to a fresh unconstrained return value and produces a FALSE E500
# counterexample (`_call_unwrap_or_1 = <garbage>`).  This must stay clean.
_SINGLE_LEVEL_CALL_ARG = """
private fn unwrap_or(@Option<Int>, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> @Int.0 } }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 42)
  effects(pure)
{ unwrap_or(Some(42), 0) }
"""


# A DIFFERENT-ADT nesting (`Cons(Some(x), Nil)`) — the outer ctor's base name
# is unambiguous, so it never triggered the bug.  Pins that the fix leaves this
# non-nested-same-ADT case verifying cleanly.
_DIFFERENT_ADT_NESTING = """
private data MyList<T> {
  Nil,
  Cons(T, MyList<T>)
}

private fn f(@Int -> @MyList<Option<Int>>)
  requires(true)
  ensures(true)
  effects(pure)
{ Cons(Some(@Int.0), Nil) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match f(1) { Cons(@Option<Int>, @MyList<Option<Int>>) -> 1, Nil -> 0 } }
"""


def test_nested_option_body_verifies_without_crash() -> None:
    """`Some(Some(x))` body verifies — no Z3 `Sort mismatch` traceback.

    RED on base: `z3.z3types.Z3Exception: Sort mismatch` (uncaught).
    Mutation oracle: dropping the type-args argument to `_find_sort_for_ctor`
    (reverting to the base-name-only scan) re-crashes this.
    """
    _verify_ok(_NESTED_BODY)


def test_nested_ctor_in_contract_verifies_without_crash() -> None:
    """A nested same-ADT ctor literal in an `ensures` verifies — no
    `AttributeError: 'DatatypeSortRef' object has no attribute 'is_int'`.

    RED on base: the outer `Some` resolves to the seeded `Option<Int>` sort and
    Z3's numeric-cast path raises the AttributeError.
    """
    _verify_ok(_NESTED_CONTRACT)


def test_true_nested_postcondition_proved_tier1() -> None:
    """A TRUE postcondition over the nested value is PROVED, not just
    non-crashing — the fix enables real Tier-1 reasoning over the structure."""
    _verify_ok(_NESTED_TRUE)


def test_false_nested_postcondition_disproved() -> None:
    """Soundness: a FALSE postcondition over the nested value is rejected
    (E500), not falsely proved.

    Mutation oracle: were the fix to pin a wrong sort or blanket-demote to
    Tier 3, this claim would go unchecked and slip through — this test flips.
    """
    _verify_err(_NESTED_FALSE, "does not hold")


def test_single_level_call_arg_stays_clean() -> None:
    """Regression guard (#887 trap): a single-level `Some(42)` argument to a
    trivial-`ensures` helper stays opaque/demoted — no false E500.

    Mutation oracle: dropping the `_has_cached_instantiation` gate makes the fix
    materialise `Option<Int>` on demand for this call arg, flipping the call to
    a fresh unconstrained return value and rejecting `main` with a false
    counterexample.  This test flips RED.
    """
    _verify_ok(_SINGLE_LEVEL_CALL_ARG)


def test_different_adt_nesting_stays_clean() -> None:
    """A different-ADT nesting (`Cons(Some(x), Nil)`) — never triggered the bug,
    must stay verifying cleanly after the fix."""
    _verify_ok(_DIFFERENT_ADT_NESTING)


def test_no_sort_mismatch_traceback_in_diagnostics() -> None:
    """Pin the mechanism: the nested-body program produces no error diagnostic
    at all (it verifies), so no Z3-internal exception text leaks as a
    diagnostic.  On base the run raised an uncaught traceback instead of a
    clean result."""
    result = _verify(_NESTED_BODY)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors == [], (
        f"Expected clean verify, got errors: {[e.description for e in errors]}"
    )


# =====================================================================
# Nat-instantiated parity (regression addendum, same PR as the Int fix).
#
# The first cut of the #918 fix recovered a constructor argument's Vera type
# from its Z3 sort via `_z3_sort_to_vera_type`, which unconditionally mapped
# Z3's shared `IntSort` back to `Int` — collapsing `Nat`.  Post-#884 the
# datatype-sort mangling is INJECTIVE: `Option<Nat>` materialises as
# `Option_LNat_R` and `Option<Int>` as `Option_LInt_R` — DISTINCT Z3 datatype
# sorts.  So for a `Some(@Nat.0)` in an `Option<Nat>` context the pin computed
# the `Int`-keyed instantiation, `_find_sort_for_ctor` MATERIALISED a fresh
# `Option<Int>` sort that never existed in the context, and comparing it
# against the context's `Option<Nat>` value in `_datatype_value_eq` raised an
# uncaught `z3.z3types.Z3Exception: sort mismatch` — RE-OPENING the exact #918
# crash mode for the (extremely common) `Nat` instantiation, on a
# `vera check`-green program.
#
# The single-level `Some(@Nat.0)` case (`_NAT_SINGLE`) is a genuine NEW
# regression: CLEAN on base (pre-#918), crashes on the first-cut #918 HEAD.
# The nested `Option<Option<Nat>>` / `Box<Box<Nat>>` cases crashed on base too
# (the pre-existing #918 gap), so bringing them to Int/Nat parity closes both
# in one move.
#
# CRITICAL: these MUST instantiate over `Nat`, not `Int` — `Int` is the
# collapse target, so an `Int`-typed program cannot see this bug (the recovered
# type coincides with the fallback).
# =====================================================================


import pytest  # noqa: E402

from vera.codegen import execute  # noqa: E402
from vera.codegen.api import WasmTrapError  # noqa: E402


# Single-level `Some(@Nat.0)` returning `Option<Nat>` with a TRUE
# `ensures(result == Some(@Nat.0))`.  This is the genuine NEW regression:
# CLEAN on base (4 verified, Tier 1), crashes on the first-cut #918 HEAD with
# `z3.z3types.Z3Exception: sort mismatch` while comparing the freshly
# materialised `Option<Int>` sort against the context's `Option<Nat>`.
_NAT_SINGLE = """
private fn f(@Nat -> @Option<Nat>)
  requires(true)
  ensures(@Option<Nat>.result == Some(@Nat.0))
  effects(pure)
{ Some(@Nat.0) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match f(7) { Some(@Nat) -> 1, None -> 0 } }
"""


# Nested `Option<Option<Nat>>` with a TRUE nested postcondition — Int/Nat
# parity with `_NESTED_TRUE`.
_NAT_NESTED_TRUE = """
private fn f(@Nat -> @Option<Option<Nat>>)
  requires(true)
  ensures(@Option<Option<Nat>>.result == Some(Some(@Nat.0)))
  effects(pure)
{ Some(Some(@Nat.0)) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match f(7) { Some(@Option<Nat>) -> 1, None -> 0 } }
"""


# Nested user ADT `Box<Box<Nat>>` — parity for a user-declared generic.
_NAT_BOX_NESTED_TRUE = """
private data Box<T> { MkBox(T) }

private fn f(@Nat -> @Box<Box<Nat>>)
  requires(true)
  ensures(@Box<Box<Nat>>.result == MkBox(MkBox(@Nat.0)))
  effects(pure)
{ MkBox(MkBox(@Nat.0)) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match f(7) { MkBox(@Box<Nat>) -> 1 } }
"""


# A FALSE single-level `Nat` postcondition: body returns `Some(@Nat.0)` but the
# ensures claims `Some(@Nat.0 + 1)`.  Genuinely false — the soundness probe for
# the Nat path (the input coincides with no fallback, unlike an `Int` probe).
_NAT_SINGLE_FALSE = """
private fn f(@Nat -> @Option<Nat>)
  requires(true)
  ensures(@Option<Nat>.result == Some(@Nat.0 + 1))
  effects(pure)
{ Some(@Nat.0) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match f(7) { Some(@Nat) -> 1, None -> 0 } }
"""


def test_nat_single_level_postcondition_no_crash() -> None:
    """NON-NEGOTIABLE floor: single-level `Some(@Nat.0)` verifies clean — no
    `z3.z3types.Z3Exception: sort mismatch`.

    RED on the first-cut #918 HEAD: the `Nat`->`Int` collapse in
    `_z3_sort_to_vera_type` pins `Option<Int>`, `_find_sort_for_ctor`
    materialises a fresh `Option<Int>` sort, and `_datatype_value_eq` crashes
    comparing it against the context's `Option<Nat>`.  CLEAN on base (pre-#918).
    Mutation oracle: reverting the `_find_sort_for_ctor` select-cached change
    re-crashes this.
    """
    _verify_ok(_NAT_SINGLE)


def test_nat_nested_option_parity_no_crash() -> None:
    """Int/Nat parity: `Option<Option<Nat>>` verifies clean like its `Int`
    sibling (`_NESTED_TRUE`).  Crashed on base too (pre-existing #918 gap)."""
    _verify_ok(_NAT_NESTED_TRUE)


def test_nat_nested_user_adt_parity_no_crash() -> None:
    """Int/Nat parity: `Box<Box<Nat>>` (user generic) verifies clean.  Crashed
    on base too (pre-existing #918 gap)."""
    _verify_ok(_NAT_BOX_NESTED_TRUE)


def test_nat_true_postcondition_proved_tier1() -> None:
    """The TRUE single-level `Nat` postcondition is genuinely PROVED at Tier 1
    (0 Tier-3 demotions), not merely non-crashing — the recovered `Nat`
    instantiation feeds real SMT reasoning."""
    result = _verify(_NAT_SINGLE)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors == [], f"Unexpected verify errors: {errors}"
    assert result.summary.tier1_verified >= 1
    assert result.summary.tier3_runtime == 0, (
        "The Nat postcondition must prove at Tier 1, not demote to Tier 3: "
        f"{result.summary.tier3_runtime} tier-3 obligation(s)"
    )


def test_nat_true_postcondition_runs_correctly() -> None:
    """Verify<->run differential (TRUE side): the proved `Nat` program also runs
    without trapping and returns the expected value."""
    assert _run(_NAT_SINGLE, fn="main") == 1


def test_nat_false_postcondition_rejected_e500() -> None:
    """Soundness (Nat path): a FALSE single-level `Nat` postcondition
    (`Some(@Nat.0 + 1)` over a `Some(@Nat.0)` body) is rejected at Tier-1 E500
    with a counterexample — NOT falsely proved and NOT blanket-demoted.

    This proves the Nat fix opened neither a false Tier-1 nor a crash.  An
    `Int`-typed version of this probe cannot distinguish the fix from the bug
    (Int is the collapse target).
    """
    result = _verify(_NAT_SINGLE_FALSE)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert any(d.error_code == "E500" for d in errors), (
        f"Expected E500 for the false Nat postcondition, got {errors}"
    )


def test_nat_false_postcondition_traps_at_runtime() -> None:
    """Verify<->run differential (FALSE side): the false `Nat` postcondition is
    ENFORCED at runtime — `Some(7) == Some(8)` is structurally false, so the
    runtime postcondition check traps.  The soundness half of the differential:
    a codegen path that let the false claim through would make this pass."""
    result = _compile(_NAT_SINGLE_FALSE)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected compile errors: {errors}"
    with pytest.raises(WasmTrapError, match="Postcondition violation") as excinfo:
        execute(result, fn_name="main")
    assert excinfo.value.kind == "contract_violation"
