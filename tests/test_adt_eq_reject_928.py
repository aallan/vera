"""Regression tests for #928 — ``==`` / ``!=`` / ``eq`` on a non-``Eq``-derivable
type is a *silent wrong result*, the severest failure class (the equality
sibling of #921).

Before the fix, the checker accepted ``a == b`` (and the ``eq`` ability op)
whenever the two operands shared a type — it never asked whether that type was
actually ``Eq``.  A non-``Eq`` ``==`` then reached codegen where, unlike the
direct-ADT path (which routes through ``_translate_adt_eq`` and raises a clean
E613), it fell to a raw ``i32`` / pointer comparison that never consulted the
structural-``Eq`` derivability dispatch:

* **Function-typed ``==``** — two structurally-identical closures compared
  ``false`` by pointer identity.  check-green, compile-green, wrong at runtime.
* **``State<Rec>`` / composite ``==``** where ``Rec`` has a ``Map`` field —
  ``old(State<Rec>) == new(State<Rec>)`` in a postcondition lowered the
  composite at raw ``i32``: silent pointer identity, zero diagnostics.

Root fix (spec-faithful): ``==`` / ``!=`` / ``eq`` is the surface spelling of
the ``Eq`` ability (§9.8.1), which derives **structurally** (§9.8.2, #773) for
the ``Eq`` primitives, simple enums, and ADTs whose fields are (recursively)
all ``Eq`` — but NOT for function types, ``Array`` / ``Map`` / ``Set`` /
``Tuple``, or a composite carrying such a field.  The checker now rejects a
non-derivable operand at *check* time with **E243**, mirroring #921's E242 for
``Ord``.  The checker's verdict is kept in exact lockstep with codegen's
structural-``Eq`` dispatch by ``test_eq_gate_matches_codegen`` — the
cross-component differential is what proves the soundness invariant (#732); a
green unit suite alone could hide a checker↔codegen desync.

Written test-first: each RED case is green (compiles, wrong run value) on the
pre-fix compiler and now rejects with E243; each POSITIVE control still
type-checks, compiles, and RUNS to the correct structural-equality result.
"""

from __future__ import annotations

import pytest

from vera.checker.core import TypeChecker
from vera.checker.eq_ability import is_eq_derivable
from vera.codegen.core import CodeGenerator
from vera.types import PrimitiveType, Type, pretty_type
from tests.checker_helpers import _error_codes as _errors
from tests.codegen_helpers import _run
from tests import pipeline


# ---------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------


# =====================================================================
# 1. The checker rejects `==` / `!=` / `eq` on a non-Eq type (E243)
# =====================================================================

class TestEqNonDerivableRejected928:
    def test_function_typed_eq_binop_rejected(self) -> None:
        # RED on base: this check-passes and compiles; two structurally-equal
        # closures then compare `false` by POINTER identity — a silent wrong
        # result.  Now rejected at check with E243.
        src = """
type IntToInt = fn(Int -> Int) effects(pure);

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 };
  let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 };
  @IntToInt.0 == @IntToInt.1
}
"""
        assert "E243" in _errors(src)

    def test_function_typed_neq_binop_rejected(self) -> None:
        # `!=` shares the Eq gate — the same silent pointer compare, negated.
        src = """
type IntToInt = fn(Int -> Int) effects(pure);

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 };
  let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 };
  @IntToInt.0 != @IntToInt.1
}
"""
        assert "E243" in _errors(src)

    def test_function_typed_eq_ability_op_rejected(self) -> None:
        # The `eq(...)` ability-op surface reaches the same silent lowering; it
        # must reject identically to the `==` binop (single shared predicate).
        src = """
type IntToInt = fn(Int -> Int) effects(pure);

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 };
  let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 };
  eq(@IntToInt.0, @IntToInt.1)
}
"""
        assert "E243" in _errors(src)

    def test_state_over_map_composite_eq_rejected(self) -> None:
        # RED on base: `Rec` has a Map field (non-Eq).  The State postcondition
        # `new(State<Rec>) == old(State<Rec>)` lowered the composite `==` at
        # raw i32 — silent pointer identity, zero diagnostics.  Now E243.
        src = """
private data Rec { MkRec(Map<String, Int>) }

public fn keep(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Rec>) == old(State<Rec>))
  effects(<State<Rec>>)
{
  let @Rec = get(());
  put(@Rec.0);
  ()
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""
        assert "E243" in _errors(src)

    def test_direct_map_composite_eq_rejected_at_check(self) -> None:
        # The direct-ADT form was already caught LATE (an E613 at codegen via
        # `_translate_adt_eq`).  The check-time gate upgrades it to the earliest
        # stage — E243 before codegen runs at all.
        src = """
private data Rec { MkRec(Map<String, Int>) }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Rec = MkRec(map_new());
  let @Rec = MkRec(map_new());
  @Rec.0 == @Rec.1
}
"""
        assert "E243" in _errors(src)

    def test_array_field_composite_eq_rejected(self) -> None:
        # An Array-field composite is non-Eq by the same rule as Map.
        src = """
private data Buf { MkBuf(Array<Int>) }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Buf = MkBuf(array_new());
  let @Buf = MkBuf(array_new());
  @Buf.0 == @Buf.1
}
"""
        assert "E243" in _errors(src)


# =====================================================================
# 2. POSITIVE controls — Eq-derivable `==` still checks, compiles, RUNS
#    to the correct structural-equality result (no over-rejection).
# =====================================================================

# Every helper returns 1 for its EXPECTED structural-equality verdict, so a
# regression that pointer-compares (or over-rejects) shifts the total off 10.
# String operands are built with `string_concat` so the "equal" case exercises
# CONTENT comparison on fresh, distinct-pointer heap strings — a pointer-identity
# lowering would return the WRONG answer here (mutation-validated).
_POSITIVE_CONTROLS = """
private data Box { MkBox(Int) }
private data List<T> { Nil, Cons(T, List<T>) }

public fn c_int(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ if 3 == 3 then { 1 } else { 0 } }

public fn c_str(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ if string_concat("a", "b") == string_concat("a", "b") then { 1 } else { 0 } }

public fn c_bool(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ if (true == true) then { 1 } else { 0 } }

public fn c_box(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ if MkBox(5) == MkBox(5) then { 1 } else { 0 } }

public fn c_box_ne(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ if MkBox(5) == MkBox(6) then { 0 } else { 1 } }

public fn c_list(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ if Cons(1, Nil) == Cons(1, Nil) then { 1 } else { 0 } }

public fn c_opt(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ if Some(7) == Some(7) then { 1 } else { 0 } }

public fn c_res(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{
  let @Result<Int, String> = Ok(7);
  let @Result<Int, String> = Ok(7);
  if @Result<Int, String>.0 == @Result<Int, String>.1 then { 1 } else { 0 }
}

public fn c_nested(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ if Cons(Cons(1, Nil), Nil) == Cons(Cons(1, Nil), Nil) then { 1 } else { 0 } }

public fn c_nested_ne(@Unit -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ if Cons(Cons(1, Nil), Nil) == Cons(Cons(2, Nil), Nil) then { 0 } else { 1 } }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 10)
  effects(pure)
{
  c_int(()) + c_str(()) + c_bool(()) + c_box(()) + c_box_ne(()) + c_list(())
    + c_opt(()) + c_res(()) + c_nested(()) + c_nested_ne(())
}
"""


class TestEqDerivablePositiveControls928:
    def test_positive_controls_type_check(self) -> None:
        # No over-rejection: none of the Eq-derivable `==` sites emits E243.
        assert "E243" not in _errors(_POSITIVE_CONTROLS)

    def test_positive_controls_run_correctly(self) -> None:
        # And they compile + RUN to the correct structural-equality total —
        # 10 (each of ten checks returns its expected verdict = 1).  A
        # pointer-identity regression on the fresh-heap String or the two
        # distinct-allocation ADT cases would shift this off 10.
        assert _run(_POSITIVE_CONTROLS) == 10


# =====================================================================
# 3. CROSS-COMPONENT DIFFERENTIAL (#732 soundness core)
#
# The checker's Eq-gate must reject EXACTLY what codegen's structural-Eq
# dispatch cannot derive, and accept exactly what it can.  A green unit suite
# can hide a checker↔codegen desync (a type one side derives and the other
# rejects → either a false reject or the silent pointer-compare #928 closes).
# This runs BOTH real predicates on a shared corpus and asserts equality.
# =====================================================================

# Programs declaring the corpus ADTs.  Each corpus entry is (probe_ctor_field,
# type_string): the checker verdict is read off the RESOLVED field type of a
# `Probe` constructor; the codegen verdict is `_type_eq_derivable(type_string)`.
# Covers: Eq primitives, simple enum, one-field record, recursive ADT, nested
# generic (#923), Option/Result, the non-Eq containers (Array/Map/Set/Tuple),
# composites carrying a non-Eq field (WithMap/WithArr) vs an all-Eq composite
# (Rec), and the built-in `Json` (Map + Array fields → non-derivable).
_DIFF_DECLS = """
private data Box { MkBox(Int) }
private data Color { Red, Green, Blue }
private data List<T> { Nil, Cons(T, List<T>) }
private data WithMap { MkWM(Map<String, Int>) }
private data WithArr { MkWA(Array<Int>) }
private data Rec { MkR(Box, List<Int>) }
private data Probe {
  PBox(Box),
  PColor(Color),
  PList(List<Int>),
  PNest(List<List<Int>>),
  POpt(Option<Int>),
  PRes(Result<Int, String>),
  PArr(Array<Int>),
  PMap(Map<String, Int>),
  PSet(Set<Int>),
  PTup(Tuple<Int, Int>),
  PWM(WithMap),
  PWA(WithArr),
  PRec(Rec),
  PJson(Json)
}
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure) { 0 }
"""

# probe constructor name -> the codegen type-name string for the SAME field.
_DIFF_ADT_CORPUS: dict[str, str] = {
    "PBox": "Box",
    "PColor": "Color",
    "PList": "List<Int>",
    "PNest": "List<List<Int>>",
    "POpt": "Option<Int>",
    "PRes": "Result<Int, String>",
    "PArr": "Array<Int>",
    "PMap": "Map<String, Int>",
    "PSet": "Set<Int>",
    "PTup": "Tuple<Int, Int>",
    "PWM": "WithMap",
    "PWA": "WithArr",
    "PRec": "Rec",
    "PJson": "Json",
}

# The Eq primitives — checked directly (they never appear as a probe ctor field
# needing resolution, and both predicates key them the same way).
_DIFF_PRIMITIVES: tuple[str, ...] = (
    "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit",
)


def _codegen_gen() -> CodeGenerator:
    compiled = pipeline.compile(_DIFF_DECLS, file="fixture.vera")
    _ = compiled.result  # raises the parse or transform error, if any
    assert compiled.generator is not None
    return compiled.generator


def _checker_env() -> TypeChecker:
    prog = pipeline.parse(_DIFF_DECLS).program
    tc = TypeChecker(source=_DIFF_DECLS)
    tc.check_program(prog)
    return tc


def test_eq_gate_matches_codegen() -> None:
    """Differential: checker Eq-gate verdict == codegen structural-Eq verdict.

    Runs BOTH real predicates over the corpus and asserts they agree on EVERY
    type.  Includes a sentinel assertion that the corpus is non-trivial (both
    True and False verdicts occur) so a bug making one side vacuously constant
    can't pass by coincidence.
    """
    gen = _codegen_gen()
    tc = _checker_env()
    env = tc.env
    probe_fields = {
        cname: ci.field_types[0]
        for cname, ci in env.data_types["Probe"].constructors.items()
        if ci.field_types is not None
    }

    verdicts: list[bool] = []
    # Primitives.
    for name in _DIFF_PRIMITIVES:
        checker_v = is_eq_derivable(PrimitiveType(name), env)
        codegen_v = gen._type_eq_derivable(name, frozenset())
        assert checker_v == codegen_v, (
            f"Eq-derivability desync on primitive {name!r}: "
            f"checker={checker_v} codegen={codegen_v}"
        )
        verdicts.append(checker_v)
    # ADTs / containers / composites, read off the resolved probe field type.
    for ctor, type_str in _DIFF_ADT_CORPUS.items():
        field_ty: Type = probe_fields[ctor]
        checker_v = is_eq_derivable(field_ty, env)
        codegen_v = gen._type_eq_derivable(type_str, frozenset())
        assert checker_v == codegen_v, (
            f"Eq-derivability desync on {type_str!r} "
            f"(checker sees {pretty_type(field_ty)!r}): "
            f"checker={checker_v} codegen={codegen_v}"
        )
        verdicts.append(checker_v)

    # Sentinel: the corpus exercises BOTH answers (guards against a predicate
    # collapsing to a constant on either side — a vacuous pass).
    assert any(verdicts) and not all(verdicts), (
        "corpus must contain both Eq-derivable and non-derivable types"
    )


@pytest.mark.parametrize(
    "type_str,expected",
    [
        ("Box", True),
        ("Color", True),
        ("List<Int>", True),
        ("List<List<Int>>", True),
        ("Option<Int>", True),
        ("Result<Int, String>", True),
        ("Rec", True),
        ("Array<Int>", False),
        ("Map<String, Int>", False),
        ("Set<Int>", False),
        ("Tuple<Int, Int>", False),
        ("WithMap", False),
        ("WithArr", False),
        ("Json", False),
    ],
)
def test_codegen_derivability_ground_truth(type_str: str, expected: bool) -> None:
    """Pin codegen's structural-Eq verdict per corpus type (the ground truth
    the checker gate must match).  If codegen's behaviour ever changes, this
    fails FIRST and forces the checker gate + the differential to be revisited
    in lockstep rather than silently drifting apart."""
    gen = _codegen_gen()
    assert gen._type_eq_derivable(type_str, frozenset()) is expected
