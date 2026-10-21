"""Tests for #1043 — registered constructor layouts erase zero-size fields.

The registered ``ConstructorLayout.field_offsets`` (computed by
``RegistrationMixin._compute_constructor_layout`` via
``_resolve_field_wasm_type``) used to give a declared ``Unit`` (or transparent
``Future<Unit>``) field a 4-byte ``i32`` slot — the ``wt is None`` fallback
returned ``"i32"``.  But CONSTRUCTION (``_translate_constructor_call``) lays a
zero-size field out erasure-aware: wt ``"unit"``, size 0, align 1, nothing
stored.  Every consumer that trusts the registered offsets for such a
constructor therefore read the wrong offset — silently, on check-green programs:

* a WILDCARD over the erased field plus a nested constructor pattern read the
  nested tag/fields at a shifted offset (garbage), matching the wrong arm;
* structural ``Eq`` / ``show`` / ``hash`` walked the registered offsets and
  compared / rendered / folded a field at the wrong address.

The fix makes the registered layout agree with construction's canonical
convention (``_resolve_field_wasm_type`` returns ``"unit"`` for an
erases-to-Unit field; ``_wasm_type_size`` / ``_wasm_type_align`` learn
``"unit"`` → 0 / 1).  These tests pin the layout differential and the
end-to-end behaviour of every consumer.
"""
from __future__ import annotations

from vera.naming import display_adt_name

from tests.codegen_helpers import (
    _compile,
    _compile_with_generator,
    _run,
)


def _errors(source: str) -> list[str]:
    """Error codes emitted compiling *source* (severity == 'error')."""
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "error"]


def _warnings(source: str) -> list[str]:
    """Warning codes emitted compiling *source* (severity == 'warning')."""
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "warning"]


# =====================================================================
# Layout differential — registered field_offsets must equal construction's
# canonical convention (tag@0; a zero-size field is wt "unit", size 0,
# align 1, and does not advance the offset).  These pin the erased-field
# positions directly at the layout level, including erased-LAST (whose
# spurious extra slot would land past the alloc, so an end-to-end run reads
# coincidental garbage) and the Future<Unit> / alias spellings that
# registration canonicalises to "unit".  The Future<Unit> case also runs
# end-to-end (construct via `async(())` + wildcard-match + Eq + show) in the
# dedicated section further below — it is NOT blocked by any skip.
# =====================================================================

_LAYOUT_SRC = """\
type U = Unit;
type FU = Future<Unit>;
type U2 = U;
private data BB { MkBox(Int), MkNot(Int) }
private data P1 { MkP1(Unit, BB) }
private data P2 { MkP2(BB, Unit) }
private data P3 { MkP3(Unit, BB, Unit) }
private data PF { MkPF(Future<Unit>, BB) }
private data PA { MkPA(U, BB) }
private data PFA { MkPFA(FU, BB) }
private data PA2 { MkPA2(U2, BB) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
"""


def _layout(ctor: str) -> tuple:
    _result, gen = _compile_with_generator(_LAYOUT_SRC)
    # A user constructor is keyed by its link name, `<Type>$<Ctor>` (#1694).
    for adt in gen._adt_layouts.values():
        for key, lay in adt.items():
            if display_adt_name(key) == ctor:
                return (lay.field_offsets, lay.field_types, lay.total_size)
    raise AssertionError(f"constructor {ctor!r} not registered")


def test_layout_bare_unit_first() -> None:
    """MkP1(Unit, BB): Unit is wt 'unit' @4 (0 bytes); BB @4 (not @8)."""
    offsets, types, total = _layout("MkP1")
    assert offsets == ((4, "unit"), (4, "i32"))
    assert types == ("Unit", "BB")
    assert total == 8


def test_layout_bare_unit_last() -> None:
    """MkP2(BB, Unit): BB @4; the trailing Unit is wt 'unit' @8, 0 bytes."""
    offsets, types, total = _layout("MkP2")
    assert offsets == ((4, "i32"), (8, "unit"))
    assert types == ("BB", "Unit")
    assert total == 8


def test_layout_multi_erased() -> None:
    """MkP3(Unit, BB, Unit): both Units are 'unit'; BB stays @4."""
    offsets, types, total = _layout("MkP3")
    assert offsets == ((4, "unit"), (4, "i32"), (8, "unit"))
    assert types == ("Unit", "BB", "Unit")
    assert total == 8


def test_layout_future_unit() -> None:
    """MkPF(Future<Unit>, BB): Future<Unit> erases to 'unit' @4; BB @4.

    The Vera field-type name canonicalises Future<Unit> to 'Unit' so
    structural Eq/show/hash treat it as the zero-size value it represents.
    """
    offsets, types, total = _layout("MkPF")
    assert offsets == ((4, "unit"), (4, "i32"))
    assert types == ("Unit", "BB")
    assert total == 8


def test_layout_alias_to_unit() -> None:
    """MkPA(U, BB) where `type U = Unit`: alias erases to 'unit'."""
    offsets, types, _ = _layout("MkPA")
    assert offsets == ((4, "unit"), (4, "i32"))
    assert types == ("Unit", "BB")


def test_layout_alias_to_future_unit() -> None:
    """MkPFA(FU, BB) where `type FU = Future<Unit>`: erases to 'unit'."""
    offsets, types, _ = _layout("MkPFA")
    assert offsets == ((4, "unit"), (4, "i32"))
    assert types == ("Unit", "BB")


def test_layout_alias_chain_to_unit() -> None:
    """MkPA2(U2, BB) where `type U2 = U = Unit`: chain erases to 'unit'."""
    offsets, types, _ = _layout("MkPA2")
    assert offsets == ((4, "unit"), (4, "i32"))
    assert types == ("Unit", "BB")


# =====================================================================
# End-to-end — the p6 shape: a WILDCARD over an erased field plus a nested
# two-constructor pattern.  With a wrong offset the nested tag check reads
# zeroed fresh-alloc memory, coincidentally matches tag 0, and the wrong
# arm extracts zeros.
# =====================================================================

_P6_WILDCARD = """\
private data BB { MkBox(Int), MkNot(Int) }
private data P { MkP(Unit, BB) }

private fn mkp(@Int -> @P)
  requires(true) ensures(true) effects(pure)
{ MkP((), MkBox(@Int.0)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @P = mkp(4242);
  match @P.0 {
    MkP(_, MkBox(@Int)) -> @Int.0,
    MkP(_, MkNot(@Int)) -> 0 - @Int.0
  }
}
"""


def test_wildcard_over_erased_field_nested_match() -> None:
    """MkP(_, MkBox(@Int)) over MkP(Unit, BB) extracts the real 4242."""
    assert _run(_P6_WILDCARD, fn="f") == 4242


# =====================================================================
# End-to-end — the p7 shape: structural Eq with the erased field FIRST.
# The derived $eq walks the field types; a mis-placed Unit field shifts the
# BB comparison onto the wrong bytes and two equal values compare unequal.
# =====================================================================

_P7_EQ_FIRST = """\
private data BB { MkBox(Int), MkNot(Int) }
private data P { MkP(Unit, BB) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @P = MkP((), MkBox(7));
  let @P = MkP((), MkBox(7));
  @P.0 == @P.1
}
"""


def test_eq_erased_field_first_equal() -> None:
    """Two equal MkP((), MkBox(7)) compare equal (structural Eq)."""
    assert _run(_P7_EQ_FIRST, fn="f") == 1


_P7_EQ_MULTI = """\
private data BB { MkBox(Int), MkNot(Int) }
private data P { MkP(Unit, BB, Unit) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @P = MkP((), MkBox(7), ());
  let @P = MkP((), MkBox(7), ());
  @P.0 == @P.1
}
"""


def test_eq_multi_erased_equal() -> None:
    """MkP(Unit, BB, Unit): the leading Unit must not shift BB's compare."""
    assert _run(_P7_EQ_MULTI, fn="f") == 1


_P7_EQ_UNEQUAL = """\
private data BB { MkBox(Int), MkNot(Int) }
private data P { MkP(Unit, BB) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @P = MkP((), MkBox(7));
  let @P = MkP((), MkBox(9));
  @P.0 == @P.1
}
"""


def test_eq_erased_field_distinct_stays_false() -> None:
    """Distinct payloads still compare unequal (Eq stays sound, not just true)."""
    assert _run(_P7_EQ_UNEQUAL, fn="f") == 0


# =====================================================================
# End-to-end — show / hash over an erased-field ADT.  A Unit field renders
# as "unit" (consistent with a bare Unit value) and folds a constant into
# the hash; both must read the *real* subsequent field, not garbage.
# =====================================================================

_SHOW_ERASED = """\
private data BB { MkBox(Int), MkNot(Int) }
private data P { MkP(Unit, BB) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(MkP((), MkBox(7))), "MkP(unit, MkBox(7))") }
"""


def test_show_erased_field_renders_real_field() -> None:
    """show(MkP((), MkBox(7))) == "MkP(unit, MkBox(7))" (reads BB @4)."""
    assert _run(_SHOW_ERASED, fn="f") == 1


_HASH_DISTINCT = """\
private data BB { MkBox(Int), MkNot(Int) }
private data P { MkP(Unit, BB) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ hash(MkP((), MkBox(7))) == hash(MkP((), MkBox(99))) }
"""


def test_hash_erased_field_is_payload_sensitive() -> None:
    """Distinct payloads hash distinctly — hash reads BB @4, not garbage @8."""
    assert _run(_HASH_DISTINCT, fn="f") == 0


_HASH_EQUAL = """\
private data BB { MkBox(Int), MkNot(Int) }
private data P { MkP(Unit, BB) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ hash(MkP((), MkBox(7))) == hash(MkP((), MkBox(7))) }
"""


def test_hash_erased_field_equal_structures() -> None:
    """Equal structures hash equal (determinism pin)."""
    assert _run(_HASH_EQUAL, fn="f") == 1


# =====================================================================
# End-to-end — a Future<Unit> field.  `async(())` constructs a Future<Unit>
# that registration canonicalises to the zero-size "unit" (#1031), so the
# whole erased-field machinery must run for it exactly as for a bare Unit.
# These upgrade the layout-only `test_layout_future_unit` pin: `async(())`
# construction compiles and runs (it is NOT blocked by any skip).
# =====================================================================

_FUTURE_WILDCARD = """\
private data BB { MkBox(Int), MkNot(Int) }
private data PF { MkPF(Future<Unit>, BB) }

private fn mk(@Int -> @PF)
  requires(true) ensures(true) effects(pure)
{ MkPF(async(()), MkBox(@Int.0)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @PF = mk(4242);
  match @PF.0 {
    MkPF(_, MkBox(@Int)) -> @Int.0,
    MkPF(_, MkNot(@Int)) -> 0 - @Int.0
  }
}
"""


def test_future_unit_wildcard_over_erased_field() -> None:
    """MkPF(_, MkBox(@Int)) over MkPF(Future<Unit>, BB) reads BB @4 → 4242."""
    assert _run(_FUTURE_WILDCARD, fn="f") == 4242


_FUTURE_EQ = """\
private data BB { MkBox(Int), MkNot(Int) }
private data PF { MkPF(Future<Unit>, BB) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @PF = MkPF(async(()), MkBox(7));
  let @PF = MkPF(async(()), MkBox(7));
  @PF.0 == @PF.1
}
"""


def test_future_unit_eq_equal() -> None:
    """Two MkPF(async(()), MkBox(7)) compare equal (the Future<Unit> field is
    equal by definition; BB @4 is compared on the right bytes)."""
    assert _run(_FUTURE_EQ, fn="f") == 1


_FUTURE_EQ_DISTINCT = """\
private data BB { MkBox(Int), MkNot(Int) }
private data PF { MkPF(Future<Unit>, BB) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @PF = MkPF(async(()), MkBox(7));
  let @PF = MkPF(async(()), MkBox(9));
  @PF.0 == @PF.1
}
"""


def test_future_unit_eq_distinct_stays_false() -> None:
    """Distinct BB payloads still compare unequal (Eq reads the real field)."""
    assert _run(_FUTURE_EQ_DISTINCT, fn="f") == 0


_FUTURE_SHOW = """\
private data BB { MkBox(Int), MkNot(Int) }
private data PF { MkPF(Future<Unit>, BB) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(MkPF(async(()), MkBox(7))), "MkPF(unit, MkBox(7))") }
"""


def test_future_unit_show_renders_real_field() -> None:
    """show(MkPF(async(()), MkBox(7))) renders the Future<Unit> as "unit" and
    reads BB @4 → "MkPF(unit, MkBox(7))"."""
    assert _run(_FUTURE_SHOW, fn="f") == 1


# =====================================================================
# Controls — the SAME shapes WITHOUT an erased field must stay green.
# =====================================================================

_C_EQ_NO_UNIT = """\
private data BB { MkBox(Int), MkNot(Int) }
private data P { MkP(BB) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @P = MkP(MkBox(7));
  let @P = MkP(MkBox(7));
  @P.0 == @P.1
}
"""


def test_control_eq_no_erased_field() -> None:
    assert _run(_C_EQ_NO_UNIT, fn="f") == 1


_C_WILD_NO_UNIT = """\
private data CC { MkC(Int) }
private data BB { MkBox(Int), MkNot(Int) }
private data P { MkP(CC, BB) }

private fn mkp(@Int -> @P)
  requires(true) ensures(true) effects(pure)
{ MkP(MkC(1), MkBox(@Int.0)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @P = mkp(4242);
  match @P.0 {
    MkP(_, MkBox(@Int)) -> @Int.0,
    MkP(_, MkNot(@Int)) -> 0 - @Int.0
  }
}
"""


def test_control_wildcard_no_erased_field() -> None:
    assert _run(_C_WILD_NO_UNIT, fn="f") == 4242


_C_SHOW_NO_UNIT = """\
private data BB { MkBox(Int), MkNot(Int) }
private data P { MkP(BB) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(MkP(MkBox(7))), "MkP(MkBox(7))") }
"""


def test_control_show_no_erased_field() -> None:
    assert _run(_C_SHOW_NO_UNIT, fn="f") == 1


# =====================================================================
# Builtin variadic Tuple — its registered layout is EMPTY (recomputed per
# call), so a WILDCARD over an erased Tuple component has no metadata and
# LOUD-skips (E602).  That is acceptable and unchanged; pin the loud skip
# (a diagnostic, not silence).
# =====================================================================

_TUPLE_WILD_ERASED = """\
private data BB { MkBox(Int), MkNot(Int) }

private fn mkt(@Int -> @Tuple<Unit, BB>)
  requires(true) ensures(true) effects(pure)
{ Tuple((), MkBox(@Int.0)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Tuple<Unit, BB> = mkt(4242);
  match @Tuple<Unit, BB>.0 {
    Tuple(_, MkBox(@Int)) -> @Int.0
  }
}
"""


def test_tuple_wildcard_over_erased_loud_skip() -> None:
    """Builtin Tuple wildcard-over-erased LOUD-skips with E602 (not silent)."""
    assert "E602" in _warnings(_TUPLE_WILD_ERASED)
