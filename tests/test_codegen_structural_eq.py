"""Tests for #773 — structural (not scalar-rep-based) Eq auto-derivation.

Before the fix, ``Eq`` auto-derivation was scalar-WASM-rep-based:

* a ``String`` field (an ``i32_pair``) made an ADT non-derivable (E613) even
  though ``String`` satisfies ``Eq`` — a **false reject**;
* a nested concrete-ADT field (an ``i32`` pointer) passed the scalar check and
  was compared with ``i32.eq`` — **pointer identity, not value** — a **false
  accept** (structurally-equal values with distinct allocations compared
  unequal);
* a ``Map`` field (also an ``i32`` pointer) likewise passed and compared by
  pointer identity — a false accept for a type with no ``Eq`` semantics.

The fix makes derivation structural: ``String`` fields compare by content,
nested-ADT fields recurse into that ADT's own equality, and field types with no
``Eq`` semantics (``Array`` / ``Map`` / host handles) are rejected loudly with
E613 at compile time.
"""

from __future__ import annotations

import tempfile

import pytest

from vera.codegen import CompileResult, compile, execute
from vera.parser import parse_file
from vera.transform import transform


def _compile(source: str) -> CompileResult:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    tree = parse_file(path)
    ast = transform(tree)
    return compile(ast, source=source, file=path)


def _compile_ok(source: str) -> CompileResult:
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected errors: {errors}"
    return result


def _run(source: str, fn: str | None = None) -> int:
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn)
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _errors(source: str) -> list[str]:
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "error"]


# ---------------------------------------------------------------------------
# False-reject direction: a String-field ADT under an Eq-constrained generic
# ---------------------------------------------------------------------------

# `string_concat` produces FRESH heap strings (distinct pointers), so the
# "equal" case exercises content comparison rather than coinciding pointer
# identity — a String literal is interned to one pointer and would make a
# pointer-identity comparison accidentally right (mutation-validated).
_BOX_STRING_EQ = """\
public data Box<T> { MkBox(T) }
private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure) { @T.1 == @T.0 }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Box<String> = MkBox(string_concat("ab", "cd"));
  let @Box<String> = MkBox(string_concat("ab", "cd"));
  eq2(@Box<String>.1, @Box<String>.0)
}
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Box<String> = MkBox(string_concat("ab", "cd"));
  let @Box<String> = MkBox(string_concat("ab", "xy"));
  eq2(@Box<String>.1, @Box<String>.0)
}
"""


def test_box_string_eq_accepts_and_compares_by_content_equal() -> None:
    """Box<String> IS Eq (String is Eq); equal contents compare true."""
    assert _run(_BOX_STRING_EQ, fn="same") == 1


def test_box_string_eq_compares_by_content_unequal() -> None:
    """Different String contents (distinct allocations) compare false."""
    assert _run(_BOX_STRING_EQ, fn="diff") == 0


def test_string_field_direct_eq() -> None:
    """A concrete String-field ADT compared directly with `==` by content."""
    source = """\
public data Named { MkNamed(String) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Named = MkNamed("hi");
  let @Named = MkNamed("hi");
  @Named.1 == @Named.0
}
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Named = MkNamed("hi");
  let @Named = MkNamed("bye");
  @Named.1 == @Named.0
}
"""
    assert _run(source, fn="same") == 1
    assert _run(source, fn="diff") == 0


def test_string_field_distinct_allocations_by_content() -> None:
    """String fields with EQUAL content at DISTINCT allocations compare equal.

    String *literals* are interned to one pointer, which would make a pointer-
    identity comparison accidentally right; `string_concat` builds fresh heap
    strings with distinct pointers, so this test genuinely distinguishes
    content comparison from pointer identity (mutation-validated).
    """
    source = """\
public data Named { MkNamed(String) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @String = string_concat("ab", "cd");
  let @String = string_concat("ab", "cd");
  let @Named = MkNamed(@String.1);
  let @Named = MkNamed(@String.0);
  @Named.1 == @Named.0
}
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @String = string_concat("ab", "cd");
  let @String = string_concat("ab", "xy");
  let @Named = MkNamed(@String.1);
  let @Named = MkNamed(@String.0);
  @Named.1 == @Named.0
}
"""
    assert _run(source, fn="same") == 1
    assert _run(source, fn="diff") == 0


# ---------------------------------------------------------------------------
# False-accept direction: nested-ADT field compared by value, not pointer
# ---------------------------------------------------------------------------

_NESTED_ADT = """\
public data Inner { MkInner(Int) }
public data Outer { MkOuter(Inner) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Outer = MkOuter(MkInner(5));
  let @Outer = MkOuter(MkInner(5));
  @Outer.1 == @Outer.0
}
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Outer = MkOuter(MkInner(5));
  let @Outer = MkOuter(MkInner(6));
  @Outer.1 == @Outer.0
}
"""


def test_nested_adt_equal_distinct_allocations() -> None:
    """Two structurally-equal Outer values with DISTINCT Inner allocations.

    Pre-fix this returned 0 (pointer identity); it must be 1 (structural).
    """
    assert _run(_NESTED_ADT, fn="same") == 1


def test_nested_adt_unequal_stays_false() -> None:
    """Structurally-UNequal nested values stay false."""
    assert _run(_NESTED_ADT, fn="diff") == 0


# ---------------------------------------------------------------------------
# Recursion depth: a 2-level nested ADT
# ---------------------------------------------------------------------------

# Names avoid single uppercase letters (`A`/`B`/`C`), which collide with a
# prelude generic type parameter and pull in a broken `option_map` — an
# unrelated pre-existing codegen bug (reported separately).
_TWO_LEVEL = """\
public data Leaf { MkLeaf(Int) }
public data Mid { MkMid(Leaf) }
public data Top { MkTop(Mid) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Top = MkTop(MkMid(MkLeaf(7)));
  let @Top = MkTop(MkMid(MkLeaf(7)));
  @Top.1 == @Top.0
}
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Top = MkTop(MkMid(MkLeaf(7)));
  let @Top = MkTop(MkMid(MkLeaf(8)));
  @Top.1 == @Top.0
}
"""


def test_two_level_nested_equal() -> None:
    """Top wraps Mid wraps Leaf — deep structural equality across allocations."""
    assert _run(_TWO_LEVEL, fn="same") == 1


def test_two_level_nested_unequal() -> None:
    """Deep structural inequality at the leaf propagates to false."""
    assert _run(_TWO_LEVEL, fn="diff") == 0


# ---------------------------------------------------------------------------
# Recursive generic ADT: List<T> — the case that forces real $eq_ functions
# (inline expansion cannot terminate on a self-referential type), and deep
# type-param substitution (the Cons tail is declared `List<T>`, not a bare
# param, so `T` must substitute inside the parameterized field type).
# ---------------------------------------------------------------------------

_REC_LIST = """\
public data List<T> { Nil, Cons(T, List<T>) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @List<Int> = Cons(1, Cons(2, Nil));
  let @List<Int> = Cons(1, Cons(2, Nil));
  @List<Int>.1 == @List<Int>.0
}
public fn diff_head(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @List<Int> = Cons(1, Cons(2, Nil));
  let @List<Int> = Cons(9, Cons(2, Nil));
  @List<Int>.1 == @List<Int>.0
}
public fn diff_tail(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @List<Int> = Cons(1, Cons(2, Nil));
  let @List<Int> = Cons(1, Cons(9, Nil));
  @List<Int>.1 == @List<Int>.0
}
public fn diff_len(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @List<Int> = Cons(1, Cons(2, Nil));
  let @List<Int> = Cons(1, Nil);
  @List<Int>.1 == @List<Int>.0
}
"""


def test_recursive_list_equal() -> None:
    """Structurally-equal Cons chains at distinct allocations compare true."""
    assert _run(_REC_LIST, fn="same") == 1


def test_recursive_list_unequal() -> None:
    """Head, tail-element, and length differences all compare false."""
    assert _run(_REC_LIST, fn="diff_head") == 0
    assert _run(_REC_LIST, fn="diff_tail") == 0
    assert _run(_REC_LIST, fn="diff_len") == 0


def test_generic_wrapping_generic_string() -> None:
    """Deep substitution through a nested generic: P<String> wraps Box<T>.

    The field of `MkP` is declared `Box<T>` — substituting `T -> String`
    must recurse into `$eq_Box<String>` (String content comparison), not a
    pointer compare.
    """
    source = """\
public data Box<T> { MkBox(T) }
public data P<T> { MkP(Box<T>) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @P<String> = MkP(MkBox(string_concat("ab", "cd")));
  let @P<String> = MkP(MkBox(string_concat("ab", "cd")));
  @P<String>.1 == @P<String>.0
}
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @P<String> = MkP(MkBox(string_concat("ab", "cd")));
  let @P<String> = MkP(MkBox(string_concat("ab", "xy")));
  @P<String>.1 == @P<String>.0
}
"""
    assert _run(source, fn="same") == 1
    assert _run(source, fn="diff") == 0


# ---------------------------------------------------------------------------
# Field-type coverage pins: NaN Float64 (derived eq must agree with the
# primitive `==` — both false), Byte fields, and a mutually-recursive ADT
# pair.  (A Unit field is skipped: Unit construction in field position is
# separately unsupported.)
# ---------------------------------------------------------------------------


def test_nan_field_consistent_with_primitive_eq() -> None:
    """A NaN Float64 field compares like primitive NaN: unequal to itself.

    Pins runtime consistency between the derived per-field `f64.eq` and the
    primitive `==` (both 0).  The VERIFIER-side counterpart — Z3's datatype
    equality wrongly proving NaN self-equality — is #871.
    """
    source = """\
public data FW { MkFW(Float64) }
public fn derived(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @FW = MkFW(nan());
  let @FW = MkFW(nan());
  @FW.1 == @FW.0
}
public fn primitive(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ nan() == nan() }
"""
    result = _compile_ok(source)
    assert execute(result, fn_name="derived").value == 0
    assert execute(result, fn_name="primitive").value == 0


def test_byte_field_eq() -> None:
    """A Byte field compares by value (i32 scalar).

    Byte values arrive through ``@Byte`` parameters — an integer literal in
    constructor argument position types as Nat and does not coerce to a Byte
    field (E213), and ``int_to_byte`` returns ``Option<Byte>``.
    """
    source = """\
public data BW { MkBW(Byte) }
public fn mk(@Byte -> @BW) requires(true) ensures(true) effects(pure)
{ MkBW(@Byte.0) }
public fn cmp(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure)
{ let @BW = mk(@Byte.1); let @BW = mk(@Byte.0); @BW.1 == @BW.0 }
"""
    result = _compile_ok(source)
    assert execute(result, fn_name="cmp", args=[65, 65]).value == 1
    assert execute(result, fn_name="cmp", args=[65, 66]).value == 0


def test_mutually_recursive_adt_pair() -> None:
    """Mutually-recursive ADTs (Even/Odd) derive Eq through each other."""
    source = """\
public data Even { ZeroE, SuccE(Odd) }
public data Odd { SuccO(Even) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Even = SuccE(SuccO(ZeroE));
  let @Even = SuccE(SuccO(ZeroE));
  @Even.1 == @Even.0
}
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Even = SuccE(SuccO(ZeroE));
  let @Even = ZeroE;
  @Even.1 == @Even.0
}
"""
    assert _run(source, fn="same") == 1
    assert _run(source, fn="diff") == 0


# ---------------------------------------------------------------------------
# Type-alias fields: the declared field type must resolve through aliases
# (including chains and alias-to-refinement) before Eq dispatch — the same
# alias resolution `_resolve_field_wasm_type` / `_type_resolves_to_nat` apply.
# Alias-to-Int, alias-to-nested-ADT, alias-to-refinement, and the 2-hop chain
# all compiled and ran on main (scalar basis); pinned so they can't regress.
# ---------------------------------------------------------------------------


def test_alias_to_int_field() -> None:
    """`type IntA = Int; MkW(IntA)` — Eq-derivable, compares by value."""
    source = """\
type IntA = Int;
public data W { MkW(IntA) }
private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure) { @T.1 == @T.0 }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ let @W = MkW(1); let @W = MkW(1); eq2(@W.1, @W.0) }
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ let @W = MkW(1); let @W = MkW(2); @W.1 == @W.0 }
"""
    assert _run(source, fn="same") == 1
    assert _run(source, fn="diff") == 0


def test_alias_to_string_field_by_content() -> None:
    """`type StrA = String` field compares by content, like a plain String."""
    source = """\
type StrA = String;
public data W { MkW(StrA) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @W = MkW(string_concat("ab", "cd"));
  let @W = MkW(string_concat("ab", "cd"));
  @W.1 == @W.0
}
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @W = MkW(string_concat("ab", "cd"));
  let @W = MkW(string_concat("ab", "xy"));
  @W.1 == @W.0
}
"""
    assert _run(source, fn="same") == 1
    assert _run(source, fn="diff") == 0


def test_alias_to_nested_adt_field() -> None:
    """`type InnerA = Inner` field recurses into Inner's structural equality."""
    source = """\
public data Inner { MkInner(Int) }
type InnerA = Inner;
public data W { MkW(InnerA) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ let @W = MkW(MkInner(5)); let @W = MkW(MkInner(5)); @W.1 == @W.0 }
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ let @W = MkW(MkInner(5)); let @W = MkW(MkInner(6)); @W.1 == @W.0 }
"""
    assert _run(source, fn="same") == 1
    assert _run(source, fn="diff") == 0


def test_alias_chain_two_hops() -> None:
    """A 2-hop alias chain (`A2 = A1 = Int`) resolves to the ground type."""
    source = """\
type A1 = Int;
type A2 = A1;
public data W { MkW(A2) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ let @W = MkW(1); let @W = MkW(1); @W.1 == @W.0 }
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ let @W = MkW(1); let @W = MkW(2); @W.1 == @W.0 }
"""
    assert _run(source, fn="same") == 1
    assert _run(source, fn="diff") == 0


def test_alias_to_refinement_field() -> None:
    """`type PosInt = { @Int | ... }` field unwraps to Int and compares."""
    source = """\
type PosInt = { @Int | @Int.0 > 0 };
public data W { MkW(PosInt) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ let @W = MkW(1); let @W = MkW(1); @W.1 == @W.0 }
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ let @W = MkW(1); let @W = MkW(2); @W.1 == @W.0 }
"""
    assert _run(source, fn="same") == 1
    assert _run(source, fn="diff") == 0


# ---------------------------------------------------------------------------
# Reject path: a field type with no Eq semantics must E613 loudly
# ---------------------------------------------------------------------------


def test_map_field_adt_rejected_loudly() -> None:
    """A Map-field ADT has no Eq semantics — must E613 at compile time.

    Pre-fix this compiled and compared the Map field by pointer identity
    (a silent false accept).  It must be a loud E613 instead.
    """
    source = """\
public data HasMap { MkHasMap(Map<String, Int>) }
private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure) { @T.1 == @T.0 }
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ let @HasMap = MkHasMap(map_new()); eq2(@HasMap.0, @HasMap.0) }
"""
    assert "E613" in _errors(source)


def test_array_field_adt_rejected_loudly() -> None:
    """An Array-field ADT has no auto-derived Eq — must E613."""
    source = """\
public data HasArr { MkHasArr(Array<Int>) }
private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure) { @T.1 == @T.0 }
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ let @HasArr = MkHasArr([1, 2, 3]); eq2(@HasArr.0, @HasArr.0) }
"""
    assert "E613" in _errors(source)


# ---------------------------------------------------------------------------
# Mixed fields: scalar + String + nested ADT in one constructor
# ---------------------------------------------------------------------------


def test_mixed_scalar_string_nested_fields() -> None:
    """A constructor mixing Int, String, and a nested ADT field.

    The String field uses `string_concat` so the equal case has distinct
    allocations (content comparison, not pointer identity).
    """
    source = """\
public data Inner { MkInner(Int) }
public data Rec { MkRec(Int, String, Inner) }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Rec = MkRec(1, string_concat("x", "y"), MkInner(9));
  let @Rec = MkRec(1, string_concat("x", "y"), MkInner(9));
  @Rec.1 == @Rec.0
}
public fn diff_str(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Rec = MkRec(1, string_concat("x", "y"), MkInner(9));
  let @Rec = MkRec(1, string_concat("x", "z"), MkInner(9));
  @Rec.1 == @Rec.0
}
public fn diff_nested(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Rec = MkRec(1, string_concat("x", "y"), MkInner(9));
  let @Rec = MkRec(1, string_concat("x", "y"), MkInner(8));
  @Rec.1 == @Rec.0
}
"""
    assert _run(source, fn="same") == 1
    assert _run(source, fn="diff_str") == 0
    assert _run(source, fn="diff_nested") == 0


# ---------------------------------------------------------------------------
# Checker <-> codegen lockstep (differential)
#
# The E613 gate (`_adt_satisfies_eq`, on the monomorphizer) and the codegen
# structural-Eq generator (`_generate_adt_eq_fn`) must agree exactly: a program
# the gate ACCEPTS must compile cleanly (never hit codegen's loud "no Eq
# comparison" invariant / E699), and one it REJECTS must E613.  A green unit
# suite can hide a desync between the two, so this is a differential — run both
# sides on the same programs and compare — not a single-sided assertion.
# ---------------------------------------------------------------------------

# (data-decls, field-type-of-the-wrapped-value, expected-derivable) triples.
# Each wraps the value in `MkW(...)` of `data W { MkW(<field>) }` and compares
# two `@W` slots under an Eq-constrained generic.
_DIFFERENTIAL_CASES = [
    ("public data W { MkW(Int) }", "MkW(1)", True),
    ("public data W { MkW(String) }", 'MkW(string_concat("x", "y"))', True),
    ("public data W { MkW(Bool) }", "MkW(true)", True),
    ("public data W { MkW(Int, String) }",
     'MkW(1, string_concat("x", "y"))', True),
    ("public data Inner { MkInner(Int) }\npublic data W { MkW(Inner) }",
     "MkW(MkInner(1))", True),
    ("public data W { MkW(Map<String, Int>) }", "MkW(map_new())", False),
    ("public data W { MkW(Array<Int>) }", "MkW([1])", False),
    ("public data Bad { MkBad(Map<String, Int>) }\n"
     "public data W { MkW(Bad) }", "MkW(MkBad(map_new()))", False),
]


@pytest.mark.parametrize("decls,ctor,derivable", _DIFFERENTIAL_CASES)
def test_structural_eq_gate_matches_codegen(
    decls: str, ctor: str, derivable: bool
) -> None:
    """The E613 gate's verdict matches the actual compile outcome.

    Derivable  → compiles with no error (gate accepted AND codegen generated).
    Non-derivable → E613 (gate rejected) and NO E699 (codegen never reached its
    invariant — the two agree on the rejection).
    """
    source = f"""\
{decls}
private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure) {{ @T.1 == @T.0 }}
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{{
  let @W = {ctor};
  let @W = {ctor};
  eq2(@W.1, @W.0)
}}
"""
    codes = _errors(source)
    if derivable:
        assert codes == [], (
            f"gate accepted but compile errored: {codes}"
        )
    else:
        assert "E613" in codes, f"expected E613 rejection, got {codes}"
        # The gate must reject BEFORE codegen — never a raw invariant/E699.
        assert "E699" not in codes, (
            f"codegen invariant hit despite gate rejection (desync): {codes}"
        )


# ---------------------------------------------------------------------------
# #772 interaction probe (report-only; behaviour asserted, not a fix here)
#
# The exact #772 constructor-path repro: `eq2(MkBox("a"), MkBox("a"))` where the
# type argument is inferred from a `ConstructorCall`.  Under #773's structural
# rewrite the outcome is a clean E613 rather than the pre-existing silent
# false-accept OR a codegen invariant crash: the monomorphizer still resolves
# the `ConstructorCall` to the BARE `Box` (dropping `<String>`), so the gate has
# no type argument and — in lockstep with codegen, which likewise can't resolve
# the field — rejects.  Recovering the lost type argument (so this DERIVES) is
# #772's job.  This test pins the current, lockstep-correct behaviour so a
# future #772 fix flips it deliberately.
# ---------------------------------------------------------------------------


def test_772_constructor_path_rejects_in_lockstep() -> None:
    """#772 ctor-path: bare-name resolution → clean E613, no E699 crash."""
    source = """\
public data Box<T> { MkBox(T) }
private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure) { @T.1 == @T.0 }
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ eq2(MkBox("a"), MkBox("a")) }
"""
    codes = _errors(source)
    assert "E613" in codes, f"expected E613, got {codes}"
    assert "E699" not in codes, (
        f"#772 ctor-path must not hit a codegen invariant: {codes}"
    )
