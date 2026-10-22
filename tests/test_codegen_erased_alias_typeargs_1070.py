"""Tests for #1070 — non-literal erases-to-Unit type ARGUMENTS.

The #1060 wildcard width recomputation resolves a type-parameter field's
concrete type from the scrutinee's type arguments and asks
``_eq_field_wasm_type`` for its width — but that function's zero-size test was
the LITERAL ``base == "Unit"``.  Registration canonicalises a DECLARED erased
field to "Unit" (#1043), but a type ARGUMENT arrives spelled as at the use
site: ``Box<U>`` (``type U = Unit;``), ``Box<Future<Unit>>``, ``Box<FU>``
(``type FU = Future<Unit>;``), and alias chains all got 4 bytes, so every
field after the erased one was read at a shifted offset — silently, on a
check-green program: the trailing Int read 0 instead of 22, and the
nested-constructor variant matched off garbage (0 instead of 314).

The same literal-test disease affected structural Eq over the same spellings
— PRE-EXISTING, not introduced by #1060 (the #1060 claim that eq/show/hash
"already recompute correctly" was true only for the literal ``Box<Unit>``
spelling): ``Box<U>`` failed the `==` dispatch's concreteness gate
(``_eq_type_name_fully_concrete``) and free-type-variable heuristic
(``_type_arg_is_free_var``) — "U" looked like an unresolved type var — so the
comparison fell back to the scalar POINTER compare and equal structs compared
unequal (0), silently.  ``show``/``hash`` over the same shapes loud-skipped
(E602), since their field dispatch keys on the resolved type NAME.

The fix keys every site on ERASURE (`_slot_name_erases_to_unit` / its
generator-side mirror) instead of the literal name:

* ``_eq_field_wasm_type`` — width: an erases-to-Unit field is ``"unit"``;
* ``_resolve_field_type_for_eq`` — canonicalises an erases-to-Unit resolution
  to "Unit" (mirroring registration), so show/hash/`$eq` field dispatch works;
* ``_eq_type_name_fully_concrete`` / ``_type_arg_is_free_var`` — an
  erases-to-Unit spelling is concrete, not a free type variable;
* ``_type_eq_derivable`` — derivable (equal by definition), keeping the E613
  gate in lockstep with the `$eq` generator (#732 differential);
* ``_later_sub_pattern_reads`` (rider) — a zero-size BINDING after an
  unrecoverable wildcard is not a read, so the trailing-``@Unit`` shape
  compiles instead of over-conservatively loud-skipping.
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
# Wildcard width — the #1060 shapes, respelled through every non-literal
# erases-to-Unit form.  RED before the fix: 0 instead of 22 / 314.
# =====================================================================

_WILD = """\
type U = Unit;
private data Box<T> {{ MkB(Int, T, Int) }}

private fn mk(-> @Box<{arg}>)
  requires(true) ensures(true) effects(pure)
{{ MkB(11, (), 22) }}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{{
  let @Box<{arg}> = mk();
  match @Box<{arg}>.0 {{
    MkB(@Int, _, @Int) -> @Int.0
  }}
}}
"""


def test_wildcard_alias_to_unit() -> None:
    """Box<U> with `type U = Unit;`: the wildcard advances 0 bytes → 22."""
    assert _run(_WILD.format(arg="U"), fn="f") == 22


def test_wildcard_future_unit_arg() -> None:
    """Box<Future<Unit>>: the transparent compound erases → 22.  The field is
    a `Future`, so its value is `async(())`, under the `Async` row."""
    source = (_WILD.format(arg="Future<Unit>")
              .replace("MkB(11, (), 22)", "MkB(11, async(()), 22)")
              .replace("effects(pure)", "effects(<Async>)"))
    assert _run(source, fn="f") == 22


_WILD_FU = """\
type FU = Future<Unit>;
private data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<FU>)
  requires(true) ensures(true) effects(<Async>)
{ MkB(11, async(()), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Box<FU> = mk();
  match @Box<FU>.0 {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_wildcard_alias_to_future_unit() -> None:
    """Box<FU> with `type FU = Future<Unit>;`: alias-to-compound erases → 22."""
    assert _run(_WILD_FU, fn="f") == 22


_WILD_CHAIN = """\
type U = Unit;
type U2 = U;
private data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<U2>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<U2> = mk();
  match @Box<U2>.0 {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_wildcard_alias_chain_to_unit() -> None:
    """Box<U2> with `type U2 = U = Unit;`: the chain erases hop by hop → 22."""
    assert _run(_WILD_CHAIN, fn="f") == 22


_ENTRY_U = """\
type U = Unit;
private data BB { MkBox(Int), MkNot(Int) }
private data Entry<T> { En(T, BB) }

private fn mk(-> @Entry<U>)
  requires(true) ensures(true) effects(pure)
{ En((), MkBox(314)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Entry<U> = mk();
  match @Entry<U>.0 {
    En(_, MkBox(@Int)) -> @Int.0,
    En(_, MkNot(@Int)) -> 0 - @Int.0
  }
}
"""


def test_wildcard_alias_before_nested_ctor() -> None:
    """En(_, MkBox(@Int)) on Entry<U>: the nested tag is read @4 → 314 (both
    the condition tag-walk and the extraction walk erase the alias arg)."""
    assert _run(_ENTRY_U, fn="f") == 314


# =====================================================================
# Structural Eq — PRE-EXISTING silent-wrong over the same spellings: the
# dispatch treated "U" as a free type variable and fell back to the scalar
# pointer compare, so two structurally equal values compared unequal.
# =====================================================================

_EQ_U = """\
type U = Unit;
private data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<U>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<U> = a();
  let @Box<U> = a();
  @Box<U>.0 == @Box<U>.1
}
"""


def test_eq_alias_to_unit_equal_structs() -> None:
    """Two equal MkB(11, (), 22) as Box<U> compare EQUAL (structural, not a
    pointer compare of two distinct allocations)."""
    assert _run(_EQ_U, fn="f") == 1


_EQ_U_DISTINCT = """\
type U = Unit;
private data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<U>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

private fn b(-> @Box<U>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 99) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<U> = a();
  let @Box<U> = b();
  @Box<U>.1 == @Box<U>.0
}
"""


def test_eq_alias_to_unit_distinct_stays_false() -> None:
    """Distinct trailing payloads still compare unequal (Eq is sound, not
    always-true) — and the compared Int is at the erasure-aware offset."""
    assert _run(_EQ_U_DISTINCT, fn="f") == 0


_EQ_FUTURE = """\
private data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<Future<Unit>>)
  requires(true) ensures(true) effects(<Async>)
{ MkB(11, async(()), 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(<Async>)
{
  let @Box<Future<Unit>> = a();
  let @Box<Future<Unit>> = a();
  @Box<Future<Unit>>.0 == @Box<Future<Unit>>.1
}
"""


def test_eq_future_unit_arg_equal_structs() -> None:
    """Box<Future<Unit>>: the compound spelling routes structurally too."""
    assert _run(_EQ_FUTURE, fn="f") == 1


# =====================================================================
# show / hash — loud-skipped (E602) over these spellings before the fix;
# with the field resolution canonicalised to "Unit" they now compute.
# =====================================================================

_SHOW_U = """\
type U = Unit;
private data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<U>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<U> = a();
  eq(show(@Box<U>.0), "MkB(11, unit, 22)")
}
"""


def test_show_alias_to_unit_renders() -> None:
    """show over Box<U> renders the erased field as "unit" and the trailing
    Int from the right offset — no E602 loud-skip."""
    assert _run(_SHOW_U, fn="f") == 1
    assert "E602" not in _warnings(_SHOW_U)


_HASH_U_DISTINCT = """\
type U = Unit;
private data Box<T> { MkB(Int, T, Int) }

private fn a(@Int -> @Box<U>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), @Int.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ hash(a(22)) == hash(a(99)) }
"""


def test_hash_alias_to_unit_payload_sensitive() -> None:
    """hash over Box<U> folds the REAL trailing Int (distinct payloads hash
    distinctly) — wrong offsets would fold identical garbage."""
    assert _run(_HASH_U_DISTINCT, fn="f") == 0


_HASH_U_EQUAL = """\
type U = Unit;
private data Box<T> { MkB(Int, T, Int) }

private fn a(@Int -> @Box<U>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), @Int.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ hash(a(22)) == hash(a(22)) }
"""


def test_hash_alias_to_unit_deterministic() -> None:
    assert _run(_HASH_U_EQUAL, fn="f") == 1


# =====================================================================
# Controls — the literal spelling stays green through the erasure keying.
# =====================================================================


def test_control_wildcard_literal_unit() -> None:
    assert _run(_WILD.format(arg="Unit"), fn="f") == 22


_EQ_LITERAL = """\
private data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Unit> = a();
  let @Box<Unit> = a();
  @Box<Unit>.0 == @Box<Unit>.1
}
"""


def test_control_eq_literal_unit() -> None:
    assert _run(_EQ_LITERAL, fn="f") == 1


# =====================================================================
# Rider — a zero-size BINDING after an UNRECOVERABLE wildcard is not a
# "later read": it binds nothing and loads nothing, so the shape compiles
# (it over-conservatively loud-skipped when #1060 landed).
# =====================================================================

_TRAILING_UNIT_BINDING = """\
private data B3<T> { MkB3(Int, T, Unit) }

private fn mk(-> @B3<Bool>)
  requires(true) ensures(true) effects(pure)
{ MkB3(5, true, ()) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match mk() {
    MkB3(@Int, _, @Unit) -> @Int.0
  }
}
"""


def test_trailing_unit_binding_after_unrecoverable_wildcard() -> None:
    """`match mk() { MkB3(@Int, _, @Unit) }` — the direct-call scrutinee makes
    the type-parameter wildcard's width unrecoverable, but the only later
    sub-pattern is a zero-size `@Unit` binding (no read), so the function
    compiles and reads field 0 (extracted before the wildcard) correctly."""
    assert "E602" not in _warnings(_TRAILING_UNIT_BINDING)
    assert _run(_TRAILING_UNIT_BINDING, fn="f") == 5


_DIRECT_CALL_READ_AFTER_UNIT_BINDING = """\
private data B4<T> { MkB4(Int, T, Unit, Int) }

private fn mk(-> @B4<Bool>)
  requires(true) ensures(true) effects(pure)
{ MkB4(5, true, (), 7) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match mk() {
    MkB4(@Int, _, @Unit, @Int) -> @Int.0
  }
}
"""


def test_read_beyond_unit_binding_now_resolves() -> None:
    """A REAL read (`@Int` field 3) after the erased binding: on the
    #1060/#1070 interim this direct-call scrutinee was unrecoverable
    (the inferred type dropped its arguments) and the shape correctly
    LOUD-skipped rather than reading a wrong offset.  The #1065
    declared-return recovery resolves `B4<Bool>` from the callee's
    signature, so the shape now compiles and reads the constructed
    trailing `Int` — the loud-skip boundary itself is still pinned by
    the unresolved-variable shapes in
    test_codegen_typeparam_unit_wildcard_1060.py."""
    assert _run(_DIRECT_CALL_READ_AFTER_UNIT_BINDING, fn="f") == 7
