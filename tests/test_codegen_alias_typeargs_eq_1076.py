"""Tests for #1076 / #1077 / #1078 — the Eq-dispatch ground-spelling cluster.

Three same-family holes in the ``==`` / show / hash machinery, all reducing to
"a type name reached a dispatch spelled other than as its ground type":

**#1076 — silent wrong `==` over NON-Unit alias type arguments.**  ``Box<MyInt>``
(``type MyInt = Int;``), ``Box<MyStr>``, ``Box<MyBool>``, ``Box<Future<Int>>``,
and alias chains: the dispatch's free-type-variable heuristic
(``_type_arg_is_free_var``) and concreteness gate (``_eq_type_name_fully_concrete``)
classified the alias spelling as an unresolved type variable, so the comparison
silently fell back to the scalar POINTER compare — two structurally equal
values compared unequal (0) on a check-green program.  This is the non-Unit
half of the heuristic #1070 patched for erases-to-Unit spellings.  The fix
GROUNDS the spelling (alias chains resolved, transparent ``Future<...>``
peeled — ``_canonical_field_type`` / the generator-side
``_ground_field_type_name``) at the classifier, the concreteness gate, the
E613 derivability gate (kept in lockstep with the ``$eq`` generator per the
#732 differential), the field-type resolution (``_resolve_field_type_for_eq``,
so ``$eq``/show/hash field dispatch sees ``"Int"``/``"String"`` and compares
content, not pointer halves), and the width function (``_eq_field_wasm_type``,
so the #1060 wildcard walks size ``MyInt``/``Future<Int>`` fields as i64, not
the 4-byte ADT-pointer default).

**#1077 — loud show/hash misses for aliased-Unit spellings.**  ``show``/``hash``
of a ``Tuple<U, Int>`` (``type U = Unit;``) loud-skipped the function: the
Tuple-variadic plan branch (``_composite_ctor_plans``) passed RAW type args to
the per-field dispatch, unlike the registered-ADT branch #1070 fixed.  A bare
value of an erases-to-Unit alias type missed the top-level show/hash ``Unit``
arms, which compared the literal name.  Both now ground/erasure-key.

**#1078 — silent wrong `==` over array ELEMENTS of parameterized ADTs.**
``Array<Box<Int>>`` (literal spelling included): an ``IndexExpr`` operand's
element type reached the dispatch as the bare head (``"Box"`` —
``_infer_index_element_type`` drops the element ``NamedType``'s type args), was
classified as a lost-type-argument clone, and pointer-compared.  The recovery
chain (``_eq_operand_full_name``) now re-derives the full element spelling from
the indexed collection, which carries its complete type arguments.
"""
from __future__ import annotations

from tests.codegen_helpers import (
    _compile,
    _run,
)


def _warnings(source: str) -> list[str]:
    """Warning codes emitted compiling *source* (severity == 'warning')."""
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "warning"]


# =====================================================================
# #1076 — structural Eq over non-Unit alias type arguments.  Equal pairs
# were silently 0 (pointer compare); distinct pairs must STAY 0 through
# the structural path (soundness, not always-true).
# =====================================================================

def _eq_box(alias_decl: str, arg: str, pay_a: str, pay_b: str) -> str:
    eff = "<Async>" if "async(" in pay_a + pay_b else "pure"
    return f"""\
{alias_decl}
private data Box<T> {{ MkB(Int, T, Int) }}

private fn a(-> @Box<{arg}>)
  requires(true) ensures(true) effects({eff})
{{ MkB(11, {pay_a}, 22) }}

private fn b(-> @Box<{arg}>)
  requires(true) ensures(true) effects({eff})
{{ MkB(11, {pay_b}, 22) }}

public fn f(-> @Bool)
  requires(true) ensures(true) effects({eff})
{{
  let @Box<{arg}> = a();
  let @Box<{arg}> = b();
  @Box<{arg}>.0 == @Box<{arg}>.1
}}
"""


def test_eq_myint_equal() -> None:
    """Box<MyInt> (`type MyInt = Int;`): equal structs compare EQUAL."""
    assert _run(_eq_box("type MyInt = Int;", "MyInt", "7", "7"), fn="f") == 1


def test_eq_myint_distinct() -> None:
    assert _run(_eq_box("type MyInt = Int;", "MyInt", "7", "9"), fn="f") == 0


def test_eq_myint_equal_above_2_32() -> None:
    """Payloads above 2^32 compare equal — the field is compared at i64
    width (an i32-width mistake would still pass this one, hence the
    distinct pin below)."""
    assert _run(
        _eq_box("type MyInt = Int;", "MyInt", "4294967303", "4294967303"),
        fn="f",
    ) == 1


def test_eq_myint_distinct_above_2_32_low_bits_collide() -> None:
    """4294967303 (2^32 + 7) vs 7: distinct at i64 width but identical in the
    low 32 bits — an i32-width compare would wrongly report equal."""
    assert _run(
        _eq_box("type MyInt = Int;", "MyInt", "4294967303", "7"), fn="f",
    ) == 0


def test_eq_mystr_equal_content() -> None:
    """Box<MyStr> (`type MyStr = String;`): two separately-allocated equal
    strings compare EQUAL — the field dispatches to the String CONTENT
    comparison, not a pointer(-half) compare."""
    assert _run(
        _eq_box("type MyStr = String;", "MyStr", '"hello"', '"hello"'),
        fn="f",
    ) == 1


def test_eq_mystr_distinct() -> None:
    assert _run(
        _eq_box("type MyStr = String;", "MyStr", '"hello"', '"world"'),
        fn="f",
    ) == 0


def test_eq_mybool_equal() -> None:
    assert _run(
        _eq_box("type MyBool = Bool;", "MyBool", "true", "true"), fn="f",
    ) == 1


def test_eq_mybool_distinct() -> None:
    assert _run(
        _eq_box("type MyBool = Bool;", "MyBool", "true", "false"), fn="f",
    ) == 0


def test_eq_future_int_equal() -> None:
    """Box<Future<Int>>: the transparent wrapper's payload is compared."""
    assert _run(_eq_box("", "Future<Int>", "async(5)", "async(5)"), fn="f") == 1


def test_eq_future_int_distinct() -> None:
    assert _run(_eq_box("", "Future<Int>", "async(5)", "async(9)"), fn="f") == 0


def test_eq_alias_to_future_int_equal() -> None:
    """Box<FI> (`type FI = Future<Int>;`): alias-to-transparent-compound."""
    assert _run(
        _eq_box("type FI = Future<Int>;", "FI", "async(5)", "async(5)"),
        fn="f",
    ) == 1


# -- #1076 wildcard width: the #1060 walks size the type-param field from the
# -- GROUND spelling.  A Bool follows the field so an i64-vs-i32 (or
# -- i32_pair-vs-i32) width mistake shifts the read and manifests.

def _wild_bool(alias_decl: str, arg: str, pay: str) -> str:
    eff = "<Async>" if "async(" in pay else "pure"
    return f"""\
{alias_decl}
private data Bx<T> {{ MkBx(Int, T, Bool) }}

private fn mk(-> @Bx<{arg}>)
  requires(true) ensures(true) effects({eff})
{{ MkBx(11, {pay}, true) }}

public fn f(-> @Bool)
  requires(true) ensures(true) effects({eff})
{{
  let @Bx<{arg}> = mk();
  match @Bx<{arg}>.0 {{
    MkBx(@Int, _, @Bool) -> @Bool.0
  }}
}}
"""


def test_wildcard_myint_width_i64() -> None:
    """Bx<MyInt> wildcard: the erased-over field is 8 bytes (Int), not the
    4-byte ADT-pointer default — the following Bool reads true."""
    assert _run(_wild_bool("type MyInt = Int;", "MyInt", "7"), fn="f") == 1


def test_wildcard_mystr_width_i32_pair() -> None:
    """Bx<MyStr> wildcard: the field is an 8-byte i32_pair (String)."""
    assert _run(
        _wild_bool("type MyStr = String;", "MyStr", '"hello"'), fn="f",
    ) == 1


def test_wildcard_future_int_width_i64() -> None:
    """Bx<Future<Int>> wildcard: the transparent payload's width (i64)."""
    assert _run(_wild_bool("", "Future<Int>", "async(5)"), fn="f") == 1


# -- #1076 controls: literal spellings and a genuine free type variable.

def test_control_eq_literal_int() -> None:
    assert _run(_eq_box("", "Int", "7", "7"), fn="f") == 1


def test_control_eq_literal_string() -> None:
    assert _run(_eq_box("", "String", '"hello"', '"hello"'), fn="f") == 1


def test_control_eq_literal_bool() -> None:
    assert _run(_eq_box("", "Bool", "true", "true"), fn="f") == 1


def test_control_wildcard_literal_int() -> None:
    assert _run(_wild_bool("", "Int", "7"), fn="f") == 1


_FREE_VAR_CONTROL = """\
private data Box<T> { MkB(T) }

private forall<T where Eq<T>>
fn same(@Box<T>, @Box<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Box<T>.1 == @Box<T>.0 }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ same(MkB(4), MkB(4)) }
"""


def test_control_genuine_free_var_dead_clone_still_compiles() -> None:
    """A genuine free `T` (`@Box<T>` in the dead base generic clone, #912)
    must STILL classify as a free variable — the grounding walk returns an
    unregistered name unchanged — so the dead clone compiles via the scalar
    fallback and the reachable mono clone compares structurally (1)."""
    assert _run(_FREE_VAR_CONTROL, fn="f") == 1


# =====================================================================
# #1077 — show/hash: Tuple with an aliased-Unit type argument, and a bare
# value of an erases-to-Unit alias type.  All four loud-skipped (E602).
# =====================================================================

_TUPLE_SHOW = """\
type U = Unit;

private fn mkt(-> @Tuple<U, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple((), 42) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Tuple<U, Int> = mkt();
  eq(show(@Tuple<U, Int>.0), "(unit, 42)")
}
"""


def test_show_tuple_aliased_unit_component() -> None:
    """show(Tuple<U, Int>) renders "(unit, 42)" — the aliased component is
    grounded to Unit (zero width) and the Int is read at the right offset."""
    assert _run(_TUPLE_SHOW, fn="f") == 1
    assert "E602" not in _warnings(_TUPLE_SHOW)


_TUPLE_HASH = """\
type U = Unit;

private fn mkt(@Int -> @Tuple<U, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple((), @Int.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ hash(mkt(42)) == hash(mkt(43)) }
"""


def test_hash_tuple_aliased_unit_payload_sensitive() -> None:
    """hash(Tuple<U, Int>) folds the REAL Int (distinct payloads hash
    distinctly), reading it at the erasure-aware offset."""
    assert _run(_TUPLE_HASH, fn="f") == 0


_BARE_SHOW = """\
type U = Unit;

private fn mku(-> @U)
  requires(true) ensures(true) effects(pure)
{ () }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(mku()), "unit") }
"""


def test_show_bare_aliased_unit_value() -> None:
    """show of a bare `@U`-typed value renders "unit" — the top-level Unit
    arm keys on erasure, not the literal name."""
    assert _run(_BARE_SHOW, fn="f") == 1
    assert "E602" not in _warnings(_BARE_SHOW)


_BARE_HASH = """\
type U = Unit;

private fn mku(-> @U)
  requires(true) ensures(true) effects(pure)
{ () }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ hash(mku()) == hash(mku()) }
"""


def test_hash_bare_aliased_unit_value() -> None:
    assert _run(_BARE_HASH, fn="f") == 1


_TUPLE_SHOW_LITERAL = """\
private fn mkt(-> @Tuple<Unit, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple((), 42) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Tuple<Unit, Int> = mkt();
  eq(show(@Tuple<Unit, Int>.0), "(unit, 42)")
}
"""


def test_control_show_tuple_literal_unit() -> None:
    assert _run(_TUPLE_SHOW_LITERAL, fn="f") == 1


_BARE_SHOW_LITERAL = """\
public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(()), "unit") }
"""


def test_control_show_bare_literal_unit() -> None:
    assert _run(_BARE_SHOW_LITERAL, fn="f") == 1


# =====================================================================
# #1078 — element-wise `==` on arrays of parameterized ADTs.  The literal
# spelling failed too (argument DROP, not alias resolution): equal elements
# silently compared unequal via the pointer fallback.
# =====================================================================

def _arr_eq(alias_decl: str, arg: str, pay: str) -> str:
    return f"""\
{alias_decl}
private data Box<T> {{ MkB(Int, T, Int) }}

private fn mkbox(-> @Box<{arg}>)
  requires(true) ensures(true) effects(pure)
{{ MkB(11, {pay}, 22) }}

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{{
  let @Array<Box<{arg}>> = [mkbox(), mkbox()];
  @Array<Box<{arg}>>.0[0] == @Array<Box<{arg}>>.0[1]
}}
"""


def test_array_element_eq_box_int_literal() -> None:
    """Array<Box<Int>>: equal elements compare EQUAL (structural, not the
    pointer compare of two distinct allocations)."""
    assert _run(_arr_eq("", "Int", "7"), fn="f") == 1


def test_array_element_eq_box_unit_literal() -> None:
    assert _run(_arr_eq("", "Unit", "()"), fn="f") == 1


def test_array_element_eq_box_aliased_unit() -> None:
    """Array<Box<U>>: the recovered element spelling rides the #1070/#1076
    grounding, so the aliased-Unit instantiation compares structurally too."""
    assert _run(_arr_eq("type U = Unit;", "U", "()"), fn="f") == 1


def test_array_element_eq_box_myint_alias() -> None:
    assert _run(_arr_eq("type MyInt = Int;", "MyInt", "7"), fn="f") == 1


_ARR_DISTINCT = """\
private data Box<T> { MkB(Int, T, Int) }

private fn mk(@Int -> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, @Int.0, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Box<Int>> = [mk(7), mk(9)];
  @Array<Box<Int>>.0[0] == @Array<Box<Int>>.0[1]
}
"""


def test_array_element_eq_distinct_stays_false() -> None:
    """Distinct element payloads compare UNEQUAL through the structural path
    (soundness: the fix must not make element compares always-true)."""
    assert _run(_ARR_DISTINCT, fn="f") == 0


_ARR_ABOVE_2_32 = """\
private data Box<T> { MkB(Int, T, Int) }

private fn mk(@Int -> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, @Int.0, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Box<Int>> = [mk(4294967303), mk(4294967303)];
  @Array<Box<Int>>.0[0] == @Array<Box<Int>>.0[1]
}
"""


def test_array_element_eq_equal_above_2_32() -> None:
    assert _run(_ARR_ABOVE_2_32, fn="f") == 1


_ARR_ABOVE_2_32_DISTINCT = """\
private data Box<T> { MkB(Int, T, Int) }

private fn mk(@Int -> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, @Int.0, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Box<Int>> = [mk(4294967303), mk(7)];
  @Array<Box<Int>>.0[0] == @Array<Box<Int>>.0[1]
}
"""


def test_array_element_eq_distinct_above_2_32_low_bits_collide() -> None:
    """2^32+7 vs 7: identical low 32 bits — the element field compare must be
    i64-wide."""
    assert _run(_ARR_ABOVE_2_32_DISTINCT, fn="f") == 0


_ARR_NON_GENERIC_CONTROL = """\
private data P { MkP(Int, Int) }

private fn mk(-> @P)
  requires(true) ensures(true) effects(pure)
{ MkP(11, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Array<P> = [mk(), mk()];
  @Array<P>.0[0] == @Array<P>.0[1]
}
"""


def test_control_array_element_eq_non_generic() -> None:
    """Array<P> (non-generic ADT): was already structural and correct."""
    assert _run(_ARR_NON_GENERIC_CONTROL, fn="f") == 1


_DIRECT_COMPARE_CONTROL = """\
private data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, 7, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Int> = mk();
  let @Box<Int> = mk();
  @Box<Int>.0 == @Box<Int>.1
}
"""


def test_control_direct_compare_same_values() -> None:
    """The same values compared DIRECTLY (no array) were already structural —
    pins that the element path now agrees with the direct path."""
    assert _run(_DIRECT_COMPARE_CONTROL, fn="f") == 1
