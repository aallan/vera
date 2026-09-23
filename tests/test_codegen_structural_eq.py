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
# Recursive generic ADT: List<T> — the case that forces real $rt.eq_ functions
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
    must recurse into `$rt.eq_Box<String>` (String content comparison), not a
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
# Direct == gate (PR #870 review): a direct comparison has no generic-
# constraint gate in front of it, so `_translate_adt_eq` itself must check
# derivability and reject with a clean E613 — never an E699 invariant, and
# never a wrong-answer helper.
# ---------------------------------------------------------------------------


def test_direct_eq_map_field_rejected_e613() -> None:
    """Direct `==` on a Map-field ADT is a clean E613, not an E699."""
    source = """\
public data HasMap { MkHasMap(Map<String, Int>) }
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @HasMap = MkHasMap(map_new());
  let @HasMap = MkHasMap(map_new());
  @HasMap.1 == @HasMap.0
}
"""
    codes = _errors(source)
    assert "E613" in codes, f"expected E613, got {codes}"
    assert "E699" not in codes, f"invariant leak on the direct path: {codes}"


def test_direct_eq_md_builtin_rejected_e613() -> None:
    """Direct `==` on an Md builtin (empty field_types) is E613, not E699.

    The #872 shape: `MdText("a") == MdText("a")` passed check and crashed
    codegen with an invariant; the direct-path gate rejects it cleanly.
    """
    source = """\
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ MdText("a") == MdText("a") }
"""
    codes = _errors(source)
    assert "E613" in codes, f"expected E613, got {codes}"
    assert "E699" not in codes, f"invariant leak on the direct path: {codes}"


def test_tuple_eq_rejected_both_paths() -> None:
    """Tuple equality rejects on BOTH paths until tuple structural Eq exists.

    `Tuple`'s registered layout is a variadic zero-field placeholder (real
    layouts are recomputed per construction), so treating it as a fieldless
    enum generated an ALWAYS-TRUE `$rt.eq_Tuple` — `Tuple(1, 2) == Tuple(3, 4)`
    returned true through both the Eq-constrained generic and the direct
    `==` (PR #870 review, Critical).  Both must be a loud E613 instead.
    """
    generic = """\
private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure) { @T.1 == @T.0 }
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Tuple<Int, Int> = Tuple(1, 2);
  let @Tuple<Int, Int> = Tuple(3, 4);
  eq2(@Tuple<Int, Int>.1, @Tuple<Int, Int>.0)
}
"""
    direct = """\
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{
  let @Tuple<Int, Int> = Tuple(1, 2);
  let @Tuple<Int, Int> = Tuple(3, 4);
  @Tuple<Int, Int>.1 == @Tuple<Int, Int>.0
}
"""
    for name, source in (("generic", generic), ("direct", direct)):
        codes = _errors(source)
        assert "E613" in codes, f"{name}: expected E613, got {codes}"
        assert "E699" not in codes, f"{name}: invariant leak: {codes}"


def test_direct_eq_ctor_inferred_option_accepts_and_runs() -> None:
    """#772 direct path: `Some(1) == Some(1)` recovers `Option<Int>` and runs.

    The `==` operand type is inferred from the `ConstructorCall` `Some(1)`;
    pre-#772 that resolved to the BARE `Option` (type-argument loss) and the
    direct-path gate spuriously E613'd.  The fix recovers `<Int>`, so the
    comparison derives and compares by value.
    """
    same = """\
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ Some(1) == Some(1) }
"""
    diff = """\
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ Some(1) == Some(2) }
"""
    assert _errors(same) == [], f"Some(1)==Some(1) must derive: {_errors(same)}"
    assert _run(same) == 1
    assert _run(diff) == 0


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
    # A second opaque host handle (Set), pinning the full rejected-type set.
    ("public data W { MkW(Set<Int>) }", "MkW(set_new())", False),
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
# #772 — Eq auto-derivation on the CONSTRUCTOR-inferred path is type-arg-aware
#
# When an Eq-constrained generic's type var is inferred from a `ConstructorCall`
# (`eq2(MkBox("a"), …)`), the monomorphizer resolves the argument to the BARE
# ADT name `Box` for clone mangling.  Pre-#772 that bare name also reached the
# Eq gate, which — having no `<String>` type argument — rejected `Box<String>`
# with a spurious E613 (an over-reject; post-#773 it no longer mis-compiles, it
# refuses a program the slot-ref form accepts).  #772 recovers the type argument
# for the Eq check specifically (leaving clone mangling on the bare name), so the
# constructor path derives `Eq` exactly when the slot-ref path does.
#
# These assert the POST-FIX behaviour and must run correctly (content
# comparison, not pointer identity), while a genuinely non-Eq type argument
# (Array) is still rejected.
# ---------------------------------------------------------------------------

_BOX_STRING_CTOR_EQ = """\
public data Box<T> { MkBox(T) }
private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure) { @T.1 == @T.0 }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ eq2(MkBox("a"), MkBox("a")) }
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ eq2(MkBox("a"), MkBox("b")) }
"""

# Nested-ADT field: two `MkInner(1)` are DISTINCT heap allocations with equal
# content, so an equal result on `same` proves the derived Eq compares by VALUE
# (recurses into `$rt.eq_Inner`), not by the wrapper pointer — the run differential
# that a pointer-identity mis-compile would fail (`same` would be 0).  This
# exercises the constructor path in isolation from builtin-return inference
# (the pre-#769 String-returning-builtin gap that `string_concat` args once
# hit — since fixed by the registry-complete builtin tables).
_BOX_NESTED_CTOR_EQ = """\
public data Inner { MkInner(Int) }
public data Box<T> { MkBox(T) }
private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure) { @T.1 == @T.0 }
public fn same(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ eq2(MkBox(MkInner(1)), MkBox(MkInner(1))) }
public fn diff(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ eq2(MkBox(MkInner(1)), MkBox(MkInner(2))) }
"""


def test_772_ctor_path_box_string_accepts() -> None:
    """#772: `eq2(MkBox("a"), ...)` (ctor-inferred Box<String>) compiles.

    The type argument `String` is recovered — for the Eq gate AND the clone
    body's slot type AND the call-site mangled name — so the constructor path
    now derives `Eq` just as the slot-ref form does, with no spurious E613.
    """
    codes = _errors(_BOX_STRING_CTOR_EQ)
    assert codes == [], f"ctor-path Box<String> must derive Eq, got {codes}"


def test_772_ctor_path_box_string_run_differential() -> None:
    """#772: the ctor-path Box<String> derivation compares by String content."""
    assert _run(_BOX_STRING_CTOR_EQ, fn="same") == 1
    assert _run(_BOX_STRING_CTOR_EQ, fn="diff") == 0


def test_772_ctor_path_nested_adt_compares_by_value() -> None:
    """#772: the recovered derivation recurses into the field's Eq, not pointer.

    `MkInner(1)` on each side is a fresh allocation; an equal `same` result
    proves value comparison — a pointer-identity mis-compile returns 0 here.
    """
    assert _run(_BOX_NESTED_CTOR_EQ, fn="same") == 1
    assert _run(_BOX_NESTED_CTOR_EQ, fn="diff") == 0


def test_772_ctor_path_box_array_still_rejected_e613() -> None:
    """#772 soundness gate: a non-Eq type argument (Array) is STILL rejected.

    The fix recovers the type argument; it must not over-accept.  `Box<Array>`
    (Array has no Eq semantics) is E613 on the constructor path, with no E699
    codegen-invariant leak.
    """
    source = """\
public data Box<T> { MkBox(T) }
private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure) { @T.1 == @T.0 }
public fn main(@Unit -> @Bool) requires(true) ensures(true) effects(pure)
{ eq2(MkBox([1, 2]), MkBox([1, 2])) }
"""
    codes = _errors(source)
    assert "E613" in codes, f"non-Eq Box<Array> must reject, got {codes}"
    assert "E699" not in codes, f"invariant leak on rejection: {codes}"


# ---------------------------------------------------------------------------
# #898 — sparse multi-type-parameter ADT on the constructor-inferred Eq path.
#
#   data Res<A, B> { MkOk(A), MkErr(B) }
#
# `MkErr(5)` recovers only `B = Int`; the `MkOk(A)` constructor is ABSENT from
# the argument, so `A` is genuinely undetermined at the call site.  Structural
# Eq derivation checks ALL constructors' fields — `MkOk(A)` included — so
# `Res<A, Int>` is Eq-derivable iff `A` is Eq, which cannot be decided from
# `MkErr(5)` alone.  Rejecting is therefore CORRECT (never unsound), but the
# old diagnostic (E613 "Res does not satisfy Eq") is misleading: the real
# problem is an under-determined type argument.  The fix reports the clearer
# E619 ("cannot infer type argument") for exactly this shape, while leaving the
# fully-determined and non-Eq cases unchanged (accept / E613 respectively).
#
# See tests/conformance/ch09_multiparam_ctor_eq.vera for the accept-side
# end-to-end program (annotated `Res<Int, Int>` derives + compares by value).
# ---------------------------------------------------------------------------

_RES_ADT = "public data Res<A, B> { MkOk(A), MkErr(B) }\n"
_ID1 = (
    "private forall<T where Eq<T>> fn id1(@T -> @Bool)\n"
    "  requires(true) ensures(true) effects(pure) { @T.0 == @T.0 }\n"
)


def test_898_sparse_multiparam_ctor_underdetermined_is_e619_not_e613() -> None:
    """#898: `id1(MkErr(5))` on `Res<A, B>` leaves `A` undetermined.

    Rejection is correct (derivability depends on the free `A`), but the
    diagnostic must be the clearer E619 (under-determined type argument),
    NOT the misleading E613 ("Res does not satisfy Eq").
    """
    source = (
        _RES_ADT + _ID1
        + "public fn main(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure) { id1(MkErr(5)) }\n"
    )
    codes = _errors(source)
    assert "E619" in codes, (
        f"under-determined type arg must be E619, got {codes}"
    )
    assert "E613" not in codes, (
        f"misleading E613 must be replaced by E619, got {codes}"
    )
    assert "E699" not in codes, f"invariant leak on rejection: {codes}"


def test_898_fully_determined_multiparam_ctor_accepts_and_runs() -> None:
    """#898 accept side: a fully-annotated `Res<Int, Int>` derives Eq.

    Both type parameters are supplied (via the `let` slot annotation), so the
    constructor path derives structural Eq exactly as the slot-ref form does
    and compares by value — `MkErr(5) == MkErr(6)` is `false` (0).
    """
    source = (
        _RES_ADT + _ID1
        + "public fn same(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure) {\n"
        "  let @Res<Int, Int> = MkErr(5);\n"
        "  id1(@Res<Int, Int>.0)\n"
        "}\n"
    )
    assert _errors(source) == [], "fully-determined Res<Int,Int> must derive Eq"
    assert _run(source, fn="same") == 1


def test_898_fully_determined_multiparam_direct_eq_compares_by_value() -> None:
    """#898: direct `==` on two `Res<Int,Int>` MkErr values compares by value."""
    source = (
        _RES_ADT
        + "public fn diff(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure) {\n"
        "  let @Res<Int, Int> = MkErr(5);\n"
        "  let @Res<Int, Int> = MkErr(6);\n"
        "  @Res<Int, Int>.0 == @Res<Int, Int>.1\n"
        "}\n"
    )
    assert _errors(source) == [], "direct == on Res<Int,Int> must derive"
    assert _run(source, fn="diff") == 0


def test_898_soundness_gate_nonEq_multiparam_stays_e613() -> None:
    """#898 soundness gate: a non-Eq type argument still rejects with E613.

    `Res<Array<Int>, Int>` is fully determined (both params supplied) but `A`
    is `Array`, which has no Eq semantics — this must STAY a clean E613, not an
    E619 (the parameter is not under-determined, it is determined-and-non-Eq)
    and not an over-accept.
    """
    source = (
        _RES_ADT + _ID1
        + "public fn main(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure) {\n"
        "  let @Res<Array<Int>, Int> = MkErr(5);\n"
        "  id1(@Res<Array<Int>, Int>.0)\n"
        "}\n"
    )
    codes = _errors(source)
    assert "E613" in codes, f"non-Eq Res<Array,Int> must reject E613, got {codes}"
    assert "E619" not in codes, (
        f"determined-but-non-Eq is E613, not E619, got {codes}"
    )
    assert "E699" not in codes, f"invariant leak on rejection: {codes}"


# ---------------------------------------------------------------------------
# #898 round 2 — the FULL over-reject fix (cross-argument type-arg merge) and
# the E619 diagnostic-accuracy correction.
#
# Round 2, Task 1: `eq2(MkErr(5), MkOk("x"))` is a fully-determined
# `Res<String, Int>` — arg 0 fixes `B`, arg 1 fixes `A` — and now type-checks
# (checker cross-argument merge), monomorphizes to the `Res<String, Int>` clone
# on both the codegen and verifier sides, and runs by VALUE.  A genuine
# per-parameter conflict stays a clear E205; a fully-determined NON-Eq type
# stays E613.
#
# Round 2, Task 2: E619 fires only when the under-determined type WOULD derive
# once its free parameter is annotated (all KNOWN components are Eq).  A known
# non-Eq component — recovered (`Res<A, Array<Int>>`) or structural
# (`W<A,B>{ K(Array<A>, B) }`) — is the accurate E613 instead, since no
# annotation of the free parameter can make it Eq.
# ---------------------------------------------------------------------------

_EQ2 = (
    "private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)\n"
    "  requires(true) ensures(true) effects(pure) { eq(@T.1, @T.0) }\n"
)


def test_898r2_cross_arg_merge_compiles_and_runs() -> None:
    """Task 1: `eq2(MkErr(5), MkOk("x"))` cross-determines `Res<String, Int>`.

    Arg 0 (`MkErr`) fixes `B = Int`, arg 1 (`MkOk`) fixes `A = String`, so the
    monomorphizer's cross-argument merge recovers the full `Res<String, Int>`
    clone on BOTH the discovery and call-rewrite sides — the call compiles with
    no Eq rejection (a pre-fix bare-`Res` recovery was an E619) and runs by
    structural comparison to 0 (the two arguments use different constructors,
    so they are unequal).  A determined-both-params call in ONE 2-arg `eq2`
    necessarily compares two DIFFERENT constructors; the same-constructor
    value-equality proof lives in the conformance program
    ``ch09_multiparam_ctor_eq`` (annotated `Res<Int, Int>`).
    """
    source = (
        _RES_ADT + _EQ2
        + "public fn diff(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ eq2(MkErr(5), MkOk(\"x\")) }\n"
    )
    assert _errors(source) == [], (
        f"cross-arg-determined Res<String,Int> must derive Eq, "
        f"got {_errors(source)}"
    )
    assert _run(source, fn="diff") == 0  # MkErr vs MkOk — different constructors


def test_898r2_cross_arg_determined_noneq_is_e613() -> None:
    """Task 1 soundness: a cross-arg-determined NON-Eq type stays E613.

    `eq2(MkErr([1]), MkOk(2))` is a fully-determined `Res<Int, Array<Int>>`
    (arg 0 fixes `B = Array<Int>`, arg 1 fixes `A = Int`).  It type-checks (both
    parameters determined) but `Array` has no Eq semantics, so it must be a
    clean E613 — not an over-accept, not E619 (nothing is under-determined).
    """
    source = (
        _RES_ADT + _EQ2
        + "public fn main(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ eq2(MkErr([1]), MkOk(2)) }\n"
    )
    codes = _errors(source)
    assert "E613" in codes, f"determined non-Eq must be E613, got {codes}"
    assert "E619" not in codes, f"determined non-Eq is not E619, got {codes}"
    assert "E699" not in codes, f"invariant leak: {codes}"


def test_898r2_e619_accuracy_known_noneq_recovered_is_e613() -> None:
    """Task 2: a recovered non-Eq component is E613, not E619.

    `id1(MkErr([1]))` recovers `B = Array<Int>` (non-Eq) and leaves `A` free.
    No value of `A` makes `Res<A, Array<Int>>` derive Eq, so "annotate to fix"
    (E619) is false advice — it must be the accurate E613.
    """
    source = (
        _RES_ADT + _ID1
        + "public fn main(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ id1(MkErr([1])) }\n"
    )
    codes = _errors(source)
    assert "E613" in codes, f"recovered non-Eq component must be E613, got {codes}"
    assert "E619" not in codes, (
        f"a known non-Eq component is E613, not E619, got {codes}"
    )
    assert "E699" not in codes, f"invariant leak: {codes}"


def test_898r2_e619_accuracy_structural_noneq_field_is_e613() -> None:
    """Task 2: a structurally non-Eq field is E613 even with a free parameter.

    `data W<A, B> { K(Array<A>, B) }`, `id1(K([1], 7))` collapses to bare `W`
    with `B = Int` recovered.  The `Array<A>` field has no Eq semantics for ANY
    `A`, so annotating the free parameter cannot help — the accurate diagnostic
    is E613, not E619.
    """
    source = (
        "private data W<A, B> { K(Array<A>, B) }\n" + _ID1
        + "public fn main(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ id1(K([1], 7)) }\n"
    )
    codes = _errors(source)
    assert "E613" in codes, f"structural non-Eq field must be E613, got {codes}"
    assert "E619" not in codes, (
        f"a structural non-Eq field is E613, not E619, got {codes}"
    )
    assert "E699" not in codes, f"invariant leak: {codes}"


def test_898r2_e619_accuracy_all_known_eq_free_param_stays_e619() -> None:
    """Task 2: genuinely under-determined with all-Eq known components → E619.

    `id1(MkErr(5))` recovers `B = Int` (Eq) and leaves `A` free.  Annotating
    `A` to an Eq type makes `Res<A, Int>` derive, so the clearer E619 is
    correct — this must NOT regress to E613 under the accuracy fix.
    """
    source = (
        _RES_ADT + _ID1
        + "public fn main(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ id1(MkErr(5)) }\n"
    )
    codes = _errors(source)
    assert "E619" in codes, f"all-known-Eq under-determined must be E619, got {codes}"
    assert "E613" not in codes, f"must stay E619 not E613, got {codes}"
    assert "E699" not in codes, f"invariant leak: {codes}"


def test_898r2_e619_message_has_no_sentinel_and_valid_fix() -> None:
    """The E619 message and fix must not leak the internal `?` sentinel, and the
    fix must be a syntactically valid Vera annotation (#898 round-3 review).

    For `id1(MkErr(5))` the free parameter `A` used to render as the reserved
    `_FREE_TYPE_PARAM = "?"` sentinel — `Res<?, Int>` — and the fix suggested
    `let @Res<?, Int><...> = ...;`, which is not valid Vera (double type-args,
    `?`, `<...>` placeholder).  The free slot now renders as its declared
    parameter name (`Res<A, Int>`) and the fix is a concrete, compilable
    annotation binding the free parameter to an Eq type (`let @Res<Int, Int>
    = ...;`).
    """
    source = (
        _RES_ADT + _ID1
        + "public fn main(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ id1(MkErr(5)) }\n"
    )
    result = _compile(source)
    e619 = [d for d in result.diagnostics if d.error_code == "E619"]
    assert e619, "expected an E619 diagnostic"
    d = e619[0]
    # No sentinel leak anywhere in the user-facing text.
    for field in (d.description, d.fix):
        assert "?" not in field, f"sentinel leaked in E619 text: {field!r}"
        assert "<...>" not in field, f"placeholder syntax in E619 text: {field!r}"
    # The description names the ADT with its declared parameter names, not `?`.
    assert "Res<A, Int>" in d.description, (
        f"free slot must render as its parameter name, got: {d.description!r}"
    )
    # The fix's suggested annotation must actually compile: extract the
    # `let @<Type> = ...;` type and check the whole program with that binding
    # derives (a valid, actionable fix — not `Res<?, Int><...>`).
    import re
    m = re.search(r"let @(Res<[^=]*?>) =", d.fix)
    assert m, f"fix must contain a concrete `let @Res<...> =` binding, got: {d.fix!r}"
    fixed_type = m.group(1).strip()
    probe = (
        _RES_ADT + _ID1
        + "public fn main(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure) {\n"
        f"  let @{fixed_type} = MkErr(5);\n"
        f"  id1(@{fixed_type}.0)\n"
        "}\n"
    )
    assert _errors(probe) == [], (
        f"the E619 fix's annotation ({fixed_type}) must compile + derive, "
        f"got {_errors(probe)}"
    )


# ---------------------------------------------------------------------------
# #923 — direct `==` on a NESTED-generic recursive ADT, type inferred from a
# constructor operand.
#
#   data List<T> { Nil, Cons(T, List<T>) }
#   Cons(Cons(1, Nil), Nil) == Cons(Cons(1, Nil), Nil)
#
# The `==` operand type is inferred from the outer `ConstructorCall`; the outer
# constructor's type argument is recovered by inferring each field's type.  Pre-
# #923 that recovery went only ONE level deep — the inner `Cons(1, Nil)` field
# resolved to the BARE `List` (dropping its own `<Int>`), so the outer name was
# reconstructed as `List<List>` instead of `List<List<Int>>`.  `List<List>`
# carries a type argument (`List`) that is a bare generic-ADT name with no
# argument of its own, which the codegen derivability path treats as a lost-type-
# arg clone → routed to the scalar (pointer) lowering's sibling rejection →
# spurious E613, even though `List<List<Int>>` is fully structurally Eq-derivable
# (the checker's `_adt_satisfies_eq` recurses fully and accepts it).
#
# The fix recovers nested type arguments FULLY, so codegen accepts the composite
# exactly as the checker does — while a genuinely non-Eq nested component
# (`List<List<Array<Int>>>`) must STILL reject with E613 (no over-accept).
# ---------------------------------------------------------------------------

_NESTED_GENERIC_LIST = "public data List<T> { Nil, Cons(T, List<T>) }\n"


def test_923_nested_generic_direct_eq_accepts_and_runs() -> None:
    """#923: `Cons(Cons(1, Nil), Nil) == ...` (List<List<Int>>) derives + runs.

    The outer operand infers `List<List<Int>>`; pre-#923 the inner field
    recovered only the bare `List`, reconstructing `List<List>` and spuriously
    E613-ing.  Full nested recovery accepts it exactly as the checker does.
    """
    same = (
        _NESTED_GENERIC_LIST
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if Cons(Cons(1, Nil), Nil) == Cons(Cons(1, Nil), Nil)\n"
        "  then { 1 } else { 0 } }\n"
    )
    diff = (
        _NESTED_GENERIC_LIST
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if Cons(Cons(1, Nil), Nil) == Cons(Cons(2, Nil), Nil)\n"
        "  then { 1 } else { 0 } }\n"
    )
    assert _errors(same) == [], f"List<List<Int>> `==` must derive: {_errors(same)}"
    assert _run(same) == 1
    assert _run(diff) == 0


def test_923_three_level_nested_generic_direct_eq() -> None:
    """#923: a 3-level nesting (List<List<List<Int>>>) also derives + runs.

    Proves the recovery is genuinely recursive (not a hardcoded two-level
    special case): the outer field recovers `List<List<Int>>`, whose own field
    recovers `List<Int>`.
    """
    same = (
        _NESTED_GENERIC_LIST
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if Cons(Cons(Cons(1, Nil), Nil), Nil)\n"
        "     == Cons(Cons(Cons(1, Nil), Nil), Nil)\n"
        "  then { 1 } else { 0 } }\n"
    )
    diff = (
        _NESTED_GENERIC_LIST
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if Cons(Cons(Cons(1, Nil), Nil), Nil)\n"
        "     == Cons(Cons(Cons(9, Nil), Nil), Nil)\n"
        "  then { 1 } else { 0 } }\n"
    )
    assert _errors(same) == [], (
        f"List<List<List<Int>>> `==` must derive: {_errors(same)}"
    )
    assert _run(same) == 1
    assert _run(diff) == 0


def test_923_nested_generic_eq_builtin_form() -> None:
    """#923: the `eq(...)` builtin form of the nested-generic `==` also derives.

    `eq(a, b)` desugars to the same structural comparison as `a == b`, so it
    must accept the nested-generic operand identically.
    """
    same = (
        _NESTED_GENERIC_LIST
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if eq(Cons(Cons(1, Nil), Nil), Cons(Cons(1, Nil), Nil))\n"
        "  then { 1 } else { 0 } }\n"
    )
    diff = (
        _NESTED_GENERIC_LIST
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if eq(Cons(Cons(1, Nil), Nil), Cons(Cons(2, Nil), Nil))\n"
        "  then { 1 } else { 0 } }\n"
    )
    assert _errors(same) == [], (
        f"eq(...) nested-generic must derive: {_errors(same)}"
    )
    assert _run(same) == 1
    assert _run(diff) == 0


def test_923_mixed_nested_generic_direct_eq() -> None:
    """#923: a mixed nested-generic (Chain<Pair<Int>>) derives + runs by value.

    A distinct outer/inner generic pairing (not the self-nested `List<List>`)
    proves the recovery reconstructs `Chain<Pair<Int>>`, not `Chain<Pair>`.
    """
    decls = (
        "public data Pair<T> { MkPair(T, T) }\n"
        "public data Chain<T> { Empty, Link(T, Chain<T>) }\n"
    )
    same = (
        decls
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if Link(MkPair(1, 2), Empty) == Link(MkPair(1, 2), Empty)\n"
        "  then { 1 } else { 0 } }\n"
    )
    diff = (
        decls
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if Link(MkPair(1, 2), Empty) == Link(MkPair(1, 9), Empty)\n"
        "  then { 1 } else { 0 } }\n"
    )
    assert _errors(same) == [], (
        f"Chain<Pair<Int>> `==` must derive: {_errors(same)}"
    )
    assert _run(same) == 1
    assert _run(diff) == 0


def test_923_nested_generic_non_eq_component_still_rejected_e613() -> None:
    """#923 soundness gate: a genuinely non-Eq nested component STILL rejects.

    `List<List<Array<Int>>>` — the innermost component is `Array<Int>`, which
    has no Eq semantics — must be a clean E613, never over-accepted by the
    fuller recovery, and never an E699 codegen-invariant leak.
    """
    source = (
        _NESTED_GENERIC_LIST
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if Cons(Cons([1], Nil), Nil) == Cons(Cons([1], Nil), Nil)\n"
        "  then { 1 } else { 0 } }\n"
    )
    codes = _errors(source)
    assert "E613" in codes, (
        f"non-Eq nested component (Array) must reject, got {codes}"
    )
    assert "E699" not in codes, f"invariant leak on rejection: {codes}"


# ---------------------------------------------------------------------------
# #932 — the GENERIC-CALL/clone sibling of #923.  A nested-generic ADT reached
# through an Eq-constrained generic function:
#
#   data List<T> { Nil, Cons(T, List<T>) }
#   forall<T where Eq<T>> fn eq2(@T, @T -> @Bool) { @T.0 == @T.1 }
#   eq2(Cons(Cons(1, Nil), Nil), Cons(Cons(1, Nil), Nil))     -- List<List<Int>>
#
# #923 fixed the DIRECT-`==` derivability path.  The generic-call path instead
# recovers the constrained-var operand's type name via the shared clone-mangler
# (`_get_arg_type_info_wasm` / `_get_arg_type_info`), which recovers only ONE
# level of nested type argument → `List<List>`.  That truncated name feeds the
# E613 derivability gate (`_check_constraints` → `_adt_satisfies_eq`), whose
# inner `List` has no type argument → treated as a lost-type-arg clone →
# spurious E613, even though `List<List<Int>>` is fully structurally Eq-derivable
# (the checker accepts it, so `vera check` is green — a check↔codegen divergence).
#
# The fix recurses the type-argument recovery FOR THE DERIVABILITY DECISION ONLY,
# WITHOUT altering the mangled clone name codegen emits and looks up (that clone
# name stays `eq2$List<List>`; test_772_ctor_path_nested_adt must remain green).
# A genuinely non-Eq nested leaf must STILL reject E613 (no over-accept).
# ---------------------------------------------------------------------------

_NESTED_GENERIC_EQ2 = (
    "private data List<T> { Nil, Cons(T, List<T>) }\n"
    "private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)\n"
    "  requires(true) ensures(true) effects(pure) { @T.0 == @T.1 }\n"
)


def test_932_generic_call_nested_generic_accepts_and_runs() -> None:
    """#932: `eq2(Cons(Cons(1,Nil),Nil), …)` (List<List<Int>>) derives + runs.

    The constrained-var operand infers the truncated `List<List>`; pre-#932 the
    lost inner `<Int>` spuriously E613'd on the generic-call path even though
    `vera check` accepts it.  Full nested recovery for the derivability decision
    accepts it exactly as the checker does — with NO change to the clone name.
    """
    same = (
        _NESTED_GENERIC_EQ2
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if eq2(Cons(Cons(1, Nil), Nil), Cons(Cons(1, Nil), Nil))\n"
        "  then { 1 } else { 0 } }\n"
    )
    diff = (
        _NESTED_GENERIC_EQ2
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if eq2(Cons(Cons(1, Nil), Nil), Cons(Cons(2, Nil), Nil))\n"
        "  then { 1 } else { 0 } }\n"
    )
    assert _errors(same) == [], (
        f"List<List<Int>> via generic call must derive: {_errors(same)}"
    )
    assert _run(same) == 1
    assert _run(diff) == 0


def test_932_generic_call_three_level_nested_generic() -> None:
    """#932: a 3-level nesting (List<List<List<Int>>>) via the generic call.

    Proves the derivability recovery is genuinely recursive on the generic-call
    path (not a hardcoded two-level special case).
    """
    same = (
        _NESTED_GENERIC_EQ2
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if eq2(Cons(Cons(Cons(1, Nil), Nil), Nil),\n"
        "         Cons(Cons(Cons(1, Nil), Nil), Nil))\n"
        "  then { 1 } else { 0 } }\n"
    )
    diff = (
        _NESTED_GENERIC_EQ2
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if eq2(Cons(Cons(Cons(1, Nil), Nil), Nil),\n"
        "         Cons(Cons(Cons(9, Nil), Nil), Nil))\n"
        "  then { 1 } else { 0 } }\n"
    )
    assert _errors(same) == [], (
        f"List<List<List<Int>>> via generic call must derive: {_errors(same)}"
    )
    assert _run(same) == 1
    assert _run(diff) == 0


def test_932_generic_call_mixed_nested_generic() -> None:
    """#932: a mixed nested-generic (Chain<Pair<Int>>) via the generic call.

    A distinct outer/inner generic pairing (not self-nested `List<List>`)
    proves the derivability recovery reconstructs `Chain<Pair<Int>>`, not the
    truncated `Chain<Pair>`, on the generic-call path.
    """
    decls = (
        "private data Pair<T> { MkPair(T, T) }\n"
        "private data Chain<T> { Empty, Link(T, Chain<T>) }\n"
        "private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure) { @T.0 == @T.1 }\n"
    )
    same = (
        decls
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if eq2(Link(MkPair(1, 2), Empty), Link(MkPair(1, 2), Empty))\n"
        "  then { 1 } else { 0 } }\n"
    )
    diff = (
        decls
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if eq2(Link(MkPair(1, 2), Empty), Link(MkPair(1, 9), Empty))\n"
        "  then { 1 } else { 0 } }\n"
    )
    assert _errors(same) == [], (
        f"Chain<Pair<Int>> via generic call must derive: {_errors(same)}"
    )
    assert _run(same) == 1
    assert _run(diff) == 0


def test_932_generic_call_nested_non_eq_leaf_still_rejected_e613() -> None:
    """#932 soundness gate: a genuinely non-Eq nested leaf STILL rejects E613.

    `List<List<Array<Int>>>` reached via the generic call — innermost component
    `Array<Int>` has no Eq semantics — must be a clean E613, never over-accepted
    by the fuller derivability recovery, and never an E699 invariant leak.
    """
    source = (
        _NESTED_GENERIC_EQ2
        + "public fn main(@Unit -> @Int) requires(true) ensures(true)\n"
        "  effects(pure)\n"
        "{ if eq2(Cons(Cons([1], Nil), Nil), Cons(Cons([1], Nil), Nil))\n"
        "  then { 1 } else { 0 } }\n"
    )
    codes = _errors(source)
    assert "E613" in codes, (
        f"non-Eq nested leaf (Array) via generic call must reject, got {codes}"
    )
    assert "E699" not in codes, f"invariant leak on rejection: {codes}"
