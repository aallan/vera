"""Tests for #1085 / #1086 / #1087 — the alias-of-ADT / forall-Eq / bare-Future
dispatch cluster (siblings of the #1076/#1077 ground-spelling family).

Three same-family holes in the ``==`` / forall-Eq-gate / ``show`` machinery, all
reducing to "a type name reached a dispatch spelled other than as its ground
type" — but at ENTRY POINTS the #1076/#1077 pass did not touch:

**#1085 — silent wrong `==` over an alias of a WHOLE ADT.**  ``type MyBox =
Box<Int>;`` then ``@MyBox.0 == @MyBox.1``: the operand reaches the ``==``
dispatch as the bare alias name ``MyBox``, absent from ``_adt_type_names``, so
the structural path was skipped and ``==`` fell to the scalar POINTER compare —
two structurally equal, distinct-pointer values compared unequal (0) on a
check-green program.  #1076 grounded type ARGUMENTS (``Box<MyInt>``); this
grounds the whole OPERAND (``_canonical_field_type`` at the dispatch site, so
``MyBox`` → ``Box<Int>`` and ``lv_base`` → ``Box``).

**#1086 — wrong-loud E613 for a forall<T where Eq<T>> at an Eq alias.**
``same(mk(), mk())`` where the argument is ``@Box<MyInt>`` (``type MyInt =
Int;``) was rejected with E613 "Type 'MyInt' does not satisfy ability 'Eq'":
the monomorphizer's top-level constraint gate (``_check_constraints``) tested
``concrete in type_set`` (primitive) then ``_adt_satisfies_eq`` (registered ADT
layout) — an alias name is NEITHER, so the legal program was rejected.  The
gate now grounds via the shared ``_type_eq_derivable`` oracle (which the ``$eq``
generator's field resolution mirrors — the #732 differential), so an Eq alias
is accepted and a genuinely non-Eq alias (``type BadArr = Array<Int>;``) still
E613s.

**#1087 — loud show/hash miss on a bare / aliased Future value.**  ``show(@FI.0)``
(``type FI = Future<Int>;``) and ``show(@Future<Int>.0)`` loud-skipped the
enclosing function (E602): the argument's inferred type reached the top-level
show/hash dispatch as ``FI`` / ``Future<Int>``, matched no primitive / Unit /
composite arm, and abandoned the render.  #1077 covered aliased-UNIT spellings;
this is the non-Unit bare-Future sibling.  ``_translate_show`` /
``_translate_hash`` now ground the inferred type (``_canonical_field_type``
peels the transparent wrapper to its payload — ``FI`` → ``Int``), so the render
dispatches exactly as the literal payload would.
"""
from __future__ import annotations

from tests.codegen_helpers import (
    _compile,
    _run,
)
from tests.codegen_helpers import _run_checked


def _warnings(source: str) -> list[str]:
    """Warning codes emitted compiling *source* (severity == 'warning')."""
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "warning"]


def _errors(source: str) -> list[str]:
    """Error codes emitted compiling *source* (severity == 'error')."""
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "error"]


# =====================================================================
# #1085 — structural Eq over an alias of a WHOLE ADT.  Equal pairs were
# silently 0 (pointer compare); distinct pairs must STAY 0 through the
# structural path (soundness, not always-true).
# =====================================================================

def _eq_alias_adt(alias_decl: str, ty: str, pay_a: str, pay_b: str) -> str:
    """Two ``@{ty}`` slots (``ty`` an alias of a whole ADT) compared by ``==``."""
    return f"""\
data Box<T> {{ MkB(Int, T, Int) }}
{alias_decl}

private fn a(-> @{ty})
  requires(true) ensures(true) effects(pure)
{{ MkB(11, {pay_a}, 22) }}

private fn b(-> @{ty})
  requires(true) ensures(true) effects(pure)
{{ MkB(11, {pay_b}, 22) }}

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{{
  let @{ty} = a();
  let @{ty} = b();
  @{ty}.0 == @{ty}.1
}}
"""


def test_eq_alias_of_generic_adt_equal() -> None:
    """`type MyBox = Box<Int>;`: two equal `@MyBox` compare EQUAL (structural,
    not the pointer compare of two distinct allocations)."""
    assert _run(
        _eq_alias_adt("type MyBox = Box<Int>;", "MyBox", "7", "7"), fn="f",
    ) == 1


def test_eq_alias_of_generic_adt_distinct() -> None:
    assert _run(
        _eq_alias_adt("type MyBox = Box<Int>;", "MyBox", "7", "9"), fn="f",
    ) == 0


def test_eq_alias_of_generic_adt_equal_above_2_32() -> None:
    """Payloads above 2^32 compare equal — the field is compared at i64 width."""
    assert _run(
        _eq_alias_adt(
            "type MyBox = Box<Int>;", "MyBox", "4294967303", "4294967303",
        ),
        fn="f",
    ) == 1


def test_eq_alias_of_generic_adt_distinct_above_2_32_low_bits_collide() -> None:
    """4294967303 (2^32 + 7) vs 7: distinct at i64 width but identical low 32
    bits — an i32-width compare would wrongly report equal."""
    assert _run(
        _eq_alias_adt("type MyBox = Box<Int>;", "MyBox", "4294967303", "7"),
        fn="f",
    ) == 0


def test_eq_alias_of_generic_adt_string_content() -> None:
    """`type MyBoxS = Box<String>;`: the string field dispatches to the CONTENT
    comparison — two separately built equal strings compare equal."""
    assert _run(
        _eq_alias_adt(
            "type MyBoxS = Box<String>;", "MyBoxS",
            'string_concat("he", "llo")', 'string_concat("hel", "lo")',
        ),
        fn="f",
    ) == 1


def test_eq_alias_of_generic_adt_string_distinct() -> None:
    assert _run(
        _eq_alias_adt(
            "type MyBoxS = Box<String>;", "MyBoxS",
            'string_concat("he", "llo")', 'string_concat("wor", "ld")',
        ),
        fn="f",
    ) == 0


def test_eq_alias_chain_of_generic_adt_equal() -> None:
    """`type MyBox = Box<Int>; type MyBox2 = MyBox;`: an alias CHAIN to a whole
    ADT grounds hop by hop and compares structurally."""
    assert _run(
        _eq_alias_adt(
            "type MyBox = Box<Int>;\ntype MyBox2 = MyBox;",
            "MyBox2", "7", "7",
        ),
        fn="f",
    ) == 1


def test_eq_alias_chain_of_generic_adt_distinct() -> None:
    assert _run(
        _eq_alias_adt(
            "type MyBox = Box<Int>;\ntype MyBox2 = MyBox;",
            "MyBox2", "7", "9",
        ),
        fn="f",
    ) == 0


_EQ_ALIAS_NON_GENERIC = """\
data P { MkP(Int, Int) }
type PA = P;

private fn a(-> @PA)
  requires(true) ensures(true) effects(pure)
{ MkP(11, 22) }

private fn b(-> @PA)
  requires(true) ensures(true) effects(pure)
{ MkP(11, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @PA = a();
  let @PA = b();
  @PA.0 == @PA.1
}
"""


def test_eq_alias_of_non_generic_adt_equal() -> None:
    """`type PA = P;` (alias of a NON-generic ADT): still routes structurally."""
    assert _run(_EQ_ALIAS_NON_GENERIC, fn="f") == 1


_EQ_ALIAS_NON_GENERIC_DISTINCT = """\
data P { MkP(Int, Int) }
type PA = P;

private fn mk(@Int -> @PA)
  requires(true) ensures(true) effects(pure)
{ MkP(@Int.0, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @PA = mk(11);
  let @PA = mk(99);
  @PA.0 == @PA.1
}
"""


def test_eq_alias_of_non_generic_adt_distinct() -> None:
    assert _run(_EQ_ALIAS_NON_GENERIC_DISTINCT, fn="f") == 0


# -- #1085 controls: the direct (un-aliased) spelling was already structural.

_EQ_DIRECT_CONTROL = """\
data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, 7, 22) }

private fn b(-> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, 7, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Int> = a();
  let @Box<Int> = b();
  @Box<Int>.0 == @Box<Int>.1
}
"""


def test_control_eq_direct_box_int() -> None:
    """The un-aliased `@Box<Int>` compare was already structural (pins that the
    alias path now agrees with the direct path)."""
    assert _run(_EQ_DIRECT_CONTROL, fn="f") == 1


# =====================================================================
# #1086 — forall<T where Eq<T>> instantiated at an Eq alias.  The
# top-level constraint gate rejected a legal program with E613.
# =====================================================================

def _forall_eq_alias(alias_decl: str, arg: str, pay_a: str, pay_b: str) -> str:
    """`same(a(), b())` with `same : forall<T where Eq<T>>`, T inferred to the
    alias `arg` from a `@Box<arg>` argument."""
    return f"""\
data Box<T> {{ MkB(T) }}
{alias_decl}

forall<T where Eq<T>>
fn same(@Box<T>, @Box<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{{ @Box<T>.1 == @Box<T>.0 }}

private fn a(-> @Box<{arg}>)
  requires(true) ensures(true) effects(pure)
{{ MkB({pay_a}) }}

private fn b(-> @Box<{arg}>)
  requires(true) ensures(true) effects(pure)
{{ MkB({pay_b}) }}

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{{ same(a(), b()) }}
"""


def test_forall_eq_alias_int_equal() -> None:
    """T := MyInt (`type MyInt = Int;`): the gate accepts and the equal values
    compare EQUAL (was a wrong-loud E613)."""
    src = _forall_eq_alias("type MyInt = Int;", "MyInt", "7", "7")
    assert "E613" not in _errors(src)
    assert _run(src, fn="f") == 1


def test_forall_eq_alias_int_distinct() -> None:
    """Distinct payloads compare UNEQUAL through the structural path (the fix
    must not make the compare always-true)."""
    assert _run(
        _forall_eq_alias("type MyInt = Int;", "MyInt", "7", "9"), fn="f",
    ) == 0


def test_forall_eq_alias_int_equal_above_2_32() -> None:
    assert _run(
        _forall_eq_alias(
            "type MyInt = Int;", "MyInt", "4294967303", "4294967303",
        ),
        fn="f",
    ) == 1


def test_forall_eq_alias_int_distinct_above_2_32_low_bits_collide() -> None:
    assert _run(
        _forall_eq_alias("type MyInt = Int;", "MyInt", "4294967303", "7"),
        fn="f",
    ) == 0


def test_forall_eq_alias_future_int_equal() -> None:
    """T := FI (`type FI = Future<Int>;`): a transparent-Future alias is Eq
    (grounds to Int); equal payloads compare equal."""
    src = _forall_eq_alias("type FI = Future<Int>;", "FI", "async(5)", "async(5)")
    assert "E613" not in _errors(src)
    assert _run(src, fn="f") == 1


def test_forall_eq_alias_future_int_distinct() -> None:
    assert _run(
        _forall_eq_alias(
            "type FI = Future<Int>;", "FI", "async(5)", "async(9)",
        ),
        fn="f",
    ) == 0


def test_forall_eq_alias_of_whole_adt_equal() -> None:
    """T := MyPair (`type MyPair = Pair;`, a whole-ADT alias): the gate grounds
    it to the registered ADT and derives Eq structurally."""
    src = """\
data Pair { MkPair(Int, Int) }
data Box<T> { MkB(T) }
type MyPair = Pair;

forall<T where Eq<T>>
fn same(@Box<T>, @Box<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Box<T>.1 == @Box<T>.0 }

private fn a(-> @Box<MyPair>)
  requires(true) ensures(true) effects(pure)
{ MkB(MkPair(1, 2)) }

private fn b(-> @Box<MyPair>)
  requires(true) ensures(true) effects(pure)
{ MkB(MkPair(1, 2)) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ same(a(), b()) }
"""
    assert "E613" not in _errors(src)
    assert _run(src, fn="f") == 1


# -- #1086 differential lockstep: the gate must ACCEPT an Eq alias (compiles
# -- cleanly) and REJECT a genuinely non-Eq alias (E613, and never the codegen
# -- E699 invariant — the two sides agree).  Keeps `_type_eq_derivable` in
# -- lockstep with the `$eq` generator (the #732 invariant) at THIS entry point.

_FORALL_EQ_NON_EQ_ALIAS = """\
data Box<T> { MkB(T) }
type BadArr = Array<Int>;

forall<T where Eq<T>>
fn same(@Box<T>, @Box<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Box<T>.1 == @Box<T>.0 }

private fn a(-> @Box<BadArr>)
  requires(true) ensures(true) effects(pure)
{ MkB([1]) }

private fn b(-> @Box<BadArr>)
  requires(true) ensures(true) effects(pure)
{ MkB([1]) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ same(a(), b()) }
"""


def test_forall_eq_non_eq_alias_still_rejected() -> None:
    """`type BadArr = Array<Int>;` grounds to a non-Eq type — the gate still
    raises E613 (never weakened) and codegen never hits its E699 invariant
    (the gate rejects first; the two sides stay in lockstep)."""
    codes = _errors(_FORALL_EQ_NON_EQ_ALIAS)
    assert "E613" in codes
    assert "E699" not in codes


# =====================================================================
# #1087 — show / hash of a bare or aliased Future value.  All loud-skipped
# (E602), never a wrong value.
# =====================================================================

def _show_future(alias_decl: str, ty: str, pay: str, expected: str) -> str:
    return f"""\
{alias_decl}
private fn mkf(-> @{ty})
  requires(true) ensures(true) effects(pure)
{{ {pay} }}

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{{
  let @{ty} = mkf();
  eq(show(@{ty}.0), "{expected}")
}}
"""


def test_show_aliased_future_int() -> None:
    """show(@FI.0) (`type FI = Future<Int>;`) renders the payload "5" — the
    alias grounds and the transparent wrapper peels to Int."""
    src = _show_future("type FI = Future<Int>;", "FI", "async(5)", "5")
    assert _run(src, fn="f") == 1
    assert "E602" not in _warnings(src)


def test_show_bare_future_int() -> None:
    """show(@Future<Int>.0) renders "5" — the transparent wrapper peels to its
    payload at the top-level show dispatch."""
    src = _show_future("", "Future<Int>", "async(5)", "5")
    assert _run(src, fn="f") == 1
    assert "E602" not in _warnings(src)


def test_show_aliased_future_bool() -> None:
    """show(@FB.0) (`type FB = Future<Bool>;`) renders the Bool payload."""
    src = _show_future("type FB = Future<Bool>;", "FB", "async(true)", "true")
    assert _run(src, fn="f") == 1
    assert "E602" not in _warnings(src)


_HASH_FUTURE_EQUAL = """\
type FI = Future<Int>;

private fn mkf(@Int -> @FI)
  requires(true) ensures(true) effects(pure)
{ async(@Int.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @FI = mkf(5);
  let @FI = mkf(5);
  hash(@FI.0) == hash(@FI.1)
}
"""


def test_hash_aliased_future_equal_payload() -> None:
    """hash(@FI.0) folds the peeled payload — equal payloads hash equal."""
    assert _run(_HASH_FUTURE_EQUAL, fn="f") == 1
    assert "E602" not in _warnings(_HASH_FUTURE_EQUAL)


_HASH_FUTURE_DISTINCT = """\
type FI = Future<Int>;

private fn mkf(@Int -> @FI)
  requires(true) ensures(true) effects(pure)
{ async(@Int.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @FI = mkf(4294967303);
  let @FI = mkf(7);
  hash(@FI.0) == hash(@FI.1)
}
"""


def test_hash_aliased_future_distinct_payload_i64() -> None:
    """Distinct payloads (2^32+7 vs 7, colliding low 32 bits) hash distinctly —
    the payload is folded at i64 width, not truncated to the pointer word."""
    assert _run(_HASH_FUTURE_DISTINCT, fn="f") == 0


_HASH_BARE_FUTURE = """\
private fn mkf(@Int -> @Future<Int>)
  requires(true) ensures(true) effects(pure)
{ async(@Int.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Future<Int> = mkf(5);
  let @Future<Int> = mkf(5);
  hash(@Future<Int>.0) == hash(@Future<Int>.1)
}
"""


def test_hash_bare_future_equal_payload() -> None:
    assert _run(_HASH_BARE_FUTURE, fn="f") == 1
    assert "E602" not in _warnings(_HASH_BARE_FUTURE)


# -- #1087 control: show of a plain Int (the ground payload) already worked.

_SHOW_INT_CONTROL = """\
private fn mki(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(mki()), "5") }
"""


def test_control_show_plain_int() -> None:
    assert _run(_SHOW_INT_CONTROL, fn="f") == 1


# =====================================================================
# Round 2 (PR #1090 review) — #1091 + the composite-Future recovery hole
# (CodeRabbit finding 1) + the #1092 Byte-field construction width.
#
# The #1087 fix grounded the show/hash dispatch's INFERRED type, but the
# composite path then recovers the PARAMETERIZED type from the DECLARED
# spelling (`_parameterized_arg_type` — `_declared_type_expr_for_show`
# returns `FOI` / `Future<Option<Int>>` / `MyBox` verbatim), UNDOING the
# grounding before `_show_value` / `_hash_value`.  Two consequences:
#
# * a COMPOSITE Future payload (`Future<Option<Int>>`, bare or aliased)
#   still loud-skipped (E602) — the scalar payloads #1087 fixed dispatch
#   BEFORE the recovery, composites AFTER it;
# * show/hash of an alias of a WHOLE ADT (`type MyBox = Box;`, #1091)
#   loud-skipped — `_show_value("MyBox")` resolves no constructor plans.
#
# The fix grounds the recovery result at both dispatch sites and the
# Array-element type at the composite render's Array arms (a `@Array<FI>`
# slot's ELEMENT reaches `_show_array` / `_hash_array` as the raw alias).
# The Tuple / registered-ADT plan branches already ground their component
# resolutions (#1076/#1077) — pinned as controls below.
# =====================================================================

_SHOW_BARE_COMPOSITE_FUTURE = """\
private fn mkf(-> @Future<Option<Int>>)
  requires(true) ensures(true) effects(pure)
{ async(Some(5)) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Future<Option<Int>> = mkf();
  eq(show(@Future<Option<Int>>.0), "Some(5)")
}
"""


def test_show_bare_composite_future() -> None:
    """show of a bare `Future<Option<Int>>` renders the composite payload —
    the transparent wrapper peels at the recovery, not only at the scalar
    dispatch (#1087's arm covered scalar payloads; this is the composite
    sibling the recovery un-grounded)."""
    assert _run(_SHOW_BARE_COMPOSITE_FUTURE, fn="f") == 1
    assert "E602" not in _warnings(_SHOW_BARE_COMPOSITE_FUTURE)


_SHOW_ALIASED_COMPOSITE_FUTURE = """\
type FOI = Future<Option<Int>>;

private fn mkf(-> @FOI)
  requires(true) ensures(true) effects(pure)
{ async(Some(5)) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @FOI = mkf();
  eq(show(@FOI.0), "Some(5)")
}
"""


def test_show_aliased_composite_future() -> None:
    assert _run(_SHOW_ALIASED_COMPOSITE_FUTURE, fn="f") == 1
    assert "E602" not in _warnings(_SHOW_ALIASED_COMPOSITE_FUTURE)


_HASH_COMPOSITE_FUTURE_DISTINCT = """\
type FOI = Future<Option<Int>>;

private fn mkf(@Int -> @FOI)
  requires(true) ensures(true) effects(pure)
{ async(Some(@Int.0)) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @FOI = mkf(5);
  let @FOI = mkf(9);
  hash(@FOI.0) == hash(@FOI.1)
}
"""


def test_hash_aliased_composite_future_payload_sensitive() -> None:
    """hash of an aliased composite Future folds the REAL payload — distinct
    Option payloads hash distinctly (was an E602 function drop)."""
    assert _run(_HASH_COMPOSITE_FUTURE_DISTINCT, fn="f") == 0


_HASH_COMPOSITE_FUTURE_EQUAL = """\
private fn mkf(@Int -> @Future<Option<Int>>)
  requires(true) ensures(true) effects(pure)
{ async(Some(@Int.0)) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Future<Option<Int>> = mkf(5);
  let @Future<Option<Int>> = mkf(5);
  hash(@Future<Option<Int>>.0) == hash(@Future<Option<Int>>.1)
}
"""


def test_hash_bare_composite_future_equal_payload() -> None:
    assert _run(_HASH_COMPOSITE_FUTURE_EQUAL, fn="f") == 1
    assert "E602" not in _warnings(_HASH_COMPOSITE_FUTURE_EQUAL)


# -- #1091: show/hash of an alias of a WHOLE ADT.

_SHOW_ALIAS_WHOLE_ADT_NONGEN = """\
data Box { MkB(Int, Int) }
type MyBox = Box;

private fn a(-> @MyBox)
  requires(true) ensures(true) effects(pure)
{ MkB(11, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @MyBox = a();
  eq(show(@MyBox.0), "MkB(11, 22)")
}
"""


def test_show_alias_of_whole_adt_non_generic() -> None:
    """`type MyBox = Box;` (#1091): show renders the structural form — the
    recovered declared spelling grounds to the registered ADT instead of
    loud-skipping (E602)."""
    assert _run(_SHOW_ALIAS_WHOLE_ADT_NONGEN, fn="f") == 1
    assert "E602" not in _warnings(_SHOW_ALIAS_WHOLE_ADT_NONGEN)


_SHOW_ALIAS_WHOLE_ADT_GENERIC = """\
data Box<T> { MkB(Int, T, Int) }
type MB = Box<Int>;

private fn a(-> @MB)
  requires(true) ensures(true) effects(pure)
{ MkB(11, 7, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @MB = a();
  eq(show(@MB.0), "MkB(11, 7, 22)")
}
"""


def test_show_alias_of_whole_adt_generic() -> None:
    """`type MB = Box<Int>;` (#1091): the generic-instantiation alias grounds
    and every field renders at its constructed offset."""
    assert _run(_SHOW_ALIAS_WHOLE_ADT_GENERIC, fn="f") == 1
    assert "E602" not in _warnings(_SHOW_ALIAS_WHOLE_ADT_GENERIC)


_HASH_ALIAS_WHOLE_ADT_DISTINCT = """\
data Box<T> { MkB(Int, T, Int) }
type MB = Box<Int>;

private fn mk(@Int -> @MB)
  requires(true) ensures(true) effects(pure)
{ MkB(11, @Int.0, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @MB = mk(4294967303);
  let @MB = mk(7);
  hash(@MB.0) == hash(@MB.1)
}
"""


def test_hash_alias_of_whole_adt_payload_sensitive() -> None:
    """hash(@MB) folds the real fields (#1091) — payloads distinct at i64
    width (2^32+7 vs 7 collide in their low 32 bits) hash distinctly."""
    assert _run(_HASH_ALIAS_WHOLE_ADT_DISTINCT, fn="f") == 0


# -- Array-element grounding: the composite render's Array arms receive the
# -- element type as spelled in the recovered compound (`Array<FI>`), which
# -- the top-level grounding does not touch (nested args are per-consumer).

_SHOW_ARRAY_OF_ALIASED_FUTURE_SLOT = """\
type FI = Future<Int>;

private fn mkf(-> @FI)
  requires(true) ensures(true) effects(pure)
{ async(5) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Array<FI> = [mkf(), mkf()];
  eq(show(@Array<FI>.0), "[5, 5]")
}
"""


def test_show_array_of_aliased_future_slot() -> None:
    """show(@Array<FI>) renders each element's peeled payload — the element
    spelling grounds at the Array arm (the recovered `Array<FI>` is already
    the full compound; the ELEMENT was the un-ground name)."""
    assert _run(_SHOW_ARRAY_OF_ALIASED_FUTURE_SLOT, fn="f") == 1
    assert "E602" not in _warnings(_SHOW_ARRAY_OF_ALIASED_FUTURE_SLOT)


_SHOW_ARRAYLIT_OF_ALIASED_FUTURE_SLOTS = """\
type FI = Future<Int>;

private fn mkf(-> @FI)
  requires(true) ensures(true) effects(pure)
{ async(5) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @FI = mkf();
  eq(show([@FI.0, @FI.0]), "[5, 5]")
}
"""


def test_show_arraylit_of_aliased_future_slots() -> None:
    """show of an inline array literal whose elements are aliased-Future
    slots — the ArrayLit element recovery feeds the same Array arm."""
    assert _run(_SHOW_ARRAYLIT_OF_ALIASED_FUTURE_SLOTS, fn="f") == 1
    assert "E602" not in _warnings(_SHOW_ARRAYLIT_OF_ALIASED_FUTURE_SLOTS)


_HASH_ARRAY_OF_ALIASED_FUTURE_DISTINCT = """\
type FI = Future<Int>;

private fn mkf(@Int -> @FI)
  requires(true) ensures(true) effects(pure)
{ async(@Int.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Array<FI> = [mkf(4294967303)];
  let @Array<FI> = [mkf(7)];
  hash(@Array<FI>.0) == hash(@Array<FI>.1)
}
"""


def test_hash_array_of_aliased_future_payload_sensitive() -> None:
    """hash(@Array<FI>) folds each element at the peeled payload's i64 width
    (2^32+7 vs 7 collide in their low 32 bits)."""
    assert _run(_HASH_ARRAY_OF_ALIASED_FUTURE_DISTINCT, fn="f") == 0


# -- Audit controls (:352 / :375 recovery callers): a Tuple component and a
# -- generic-ADT constructor argument of an aliased-Future type were ALREADY
# -- rendered correctly — the #1077 Tuple plan branch and the #1076-grounded
# -- registered-ADT field resolution ground the recovered raw spellings at
# -- consumption.  Pinned so the recovery callers stay covered downstream.

_SHOW_TUPLE_ALIASED_FUTURE_COMPONENT = """\
type FI = Future<Int>;

private fn mkf(-> @FI)
  requires(true) ensures(true) effects(pure)
{ async(5) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @FI = mkf();
  eq(show(Tuple(@FI.0, 42)), "(5, 42)")
}
"""


def test_control_show_tuple_aliased_future_component() -> None:
    assert _run(_SHOW_TUPLE_ALIASED_FUTURE_COMPONENT, fn="f") == 1


_SHOW_CTOR_ALIASED_FUTURE_ARG = """\
data Box<T> { MkB(T) }
type FI = Future<Int>;

private fn mkf(-> @FI)
  requires(true) ensures(true) effects(pure)
{ async(5) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @FI = mkf();
  eq(show(MkB(@FI.0)), "MkB(5)")
}
"""


def test_control_show_ctor_aliased_future_arg() -> None:
    assert _run(_SHOW_CTOR_ALIASED_FUTURE_ARG, fn="f") == 1


# -- PR #1090 review pins (F2): surfaces the round-1 groundings fixed beyond
# -- the filed issues' wording — pinned so the CHANGELOG claims stay true.

_SHOW_ALIASED_PRIMITIVE = """\
type MyInt = Int;

private fn mk(-> @MyInt)
  requires(true) ensures(true) effects(pure)
{ 5 }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @MyInt = mk();
  eq(show(@MyInt.0), "5")
}
"""


def test_show_aliased_primitive_int() -> None:
    """show of a bare aliased-primitive value (`type MyInt = Int;`) — the
    #1087 grounding covers plain aliases, not only Future spellings."""
    assert _run(_SHOW_ALIASED_PRIMITIVE, fn="f") == 1
    assert "E602" not in _warnings(_SHOW_ALIASED_PRIMITIVE)


_SHOW_REFINEMENT_INT = """\
type Pos = { @Int | @Int.0 > 0 };

private fn mk(-> @Pos)
  requires(true) ensures(true) effects(pure)
{ 5 }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Pos = mk();
  eq(show(@Pos.0), "5")
}
"""


def test_show_refinement_int() -> None:
    """show of a refinement-typed value (`type Pos = { @Int | ... };`) — the
    alias walk resolves the refinement to its base spelling."""
    assert _run(_SHOW_REFINEMENT_INT, fn="f") == 1
    assert "E602" not in _warnings(_SHOW_REFINEMENT_INT)


_EQ_REFINEMENT_OVER_ADT = """\
data Box<T> { MkB(Int, T, Int) }
type NB = { @Box<Int> | true };

private fn a(-> @NB)
  requires(true) ensures(true) effects(pure)
{ MkB(11, 7, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @NB = a();
  let @NB = a();
  @NB.0 == @NB.1
}
"""


def test_eq_refinement_over_whole_adt_equal() -> None:
    """`==` through a refinement of a whole ADT (`type NB = { @Box<Int> |
    true };`) compares STRUCTURALLY — on the pre-#1085 base this silently
    pointer-compared (equal values -> 0)."""
    assert _run(_EQ_REFINEMENT_OVER_ADT, fn="f") == 1


_EQ_REFINEMENT_OVER_ADT_DISTINCT = """\
data Box<T> { MkB(Int, T, Int) }
type NB = { @Box<Int> | true };

private fn mk(@Int -> @NB)
  requires(true) ensures(true) effects(pure)
{ MkB(11, @Int.0, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @NB = mk(7);
  let @NB = mk(9);
  @NB.0 == @NB.1
}
"""


def test_eq_refinement_over_whole_adt_distinct() -> None:
    assert _run(_EQ_REFINEMENT_OVER_ADT_DISTINCT, fn="f") == 0


# =====================================================================
# #1092 — construction width of an int literal coerced into a generic
# field instantiated at @Byte.
#
# `let @Box<Byte> = MkB(0);` is check-green (the checker coerces an
# in-range 0..255 literal to @Byte through the generic instantiation —
# out-of-range, negative, and non-literal @Int arguments are all loud
# E170 rejections, and a DECLARED `Byte` field rejects the literal with
# E213).  But construction sized the field from the ARGUMENT's own
# inferred WASM type (IntLit -> i64, stored at the i64 slot), while
# every READER — field extraction, the structural-`$eq` helper,
# show/hash — sizes it from the instantiated field type (Byte -> i32 at
# the i32 offset): extraction read 0 for a stored 255, and `==` compared
# equal-looking garbage — `MkB(0) == MkB(255)` returned 1, silently, on
# a check-green program.  The `@Byte`-slot passthrough (`MkB(@Byte.0)`)
# stores i32 and was always coherent (pinned below).
#
# The width fix keys on the checker-recorded TARGET type of the
# construction (`_target_codegen_type_full`, the #820 table): these
# tests therefore compile through the real pipeline — typecheck with
# artifacts, then compile with the tables threaded, exactly as the CLI
# does (`vera run`/`compile`/`serve`/`test` all thread them; a bare
# transform -> compile keeps the documented #798/#820 degraded-path
# caveat).
# =====================================================================


_BYTE_LIT_EQ_DISTINCT = """\
private data Box<T> { MkB(T) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Byte> = MkB(0);
  let @Box<Byte> = MkB(255);
  @Box<Byte>.0 == @Box<Byte>.1
}
"""


def test_byte_field_inline_literal_eq_distinct() -> None:
    """MkB(0) vs MkB(255) as `@Box<Byte>` compare UNEQUAL — construction
    stores the coerced literal at the field's i32 Byte width, where `$eq`
    reads (was: i64 store at a shifted slot, both reads saw the same bytes,
    silently equal on a check-green program)."""
    assert _run_checked(_BYTE_LIT_EQ_DISTINCT, fn="f") == 0


_BYTE_LIT_EQ_EQUAL = """\
private data Box<T> { MkB(T) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Byte> = MkB(7);
  let @Box<Byte> = MkB(7);
  @Box<Byte>.0 == @Box<Byte>.1
}
"""


def test_byte_field_inline_literal_eq_equal() -> None:
    assert _run_checked(_BYTE_LIT_EQ_EQUAL, fn="f") == 1


_BYTE_LIT_EXTRACTION = """\
private data Box<T> { MkB(T) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Byte> = MkB(255);
  match @Box<Byte>.0 {
    MkB(@Byte) -> byte_to_int(@Byte.0)
  }
}
"""


def test_byte_field_inline_literal_extraction() -> None:
    """The strongest #1092 pin: extracting the field reads back the STORED
    value (was 0 — the i64 store put 255 at a slot the i32 extraction never
    read)."""
    assert _run_checked(_BYTE_LIT_EXTRACTION, fn="f") == 255


_BYTE_LIT_ALIAS_FORALL_DISTINCT = """\
private data Box<T> { MkB(T) }
type MB = Byte;

private forall<T where Eq<T>>
fn same(@Box<T>, @Box<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Box<T>.1 == @Box<T>.0 }

private fn a(-> @Box<MB>)
  requires(true) ensures(true) effects(pure)
{ MkB(0) }

private fn b(-> @Box<MB>)
  requires(true) ensures(true) effects(pure)
{ MkB(255) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ same(a(), b()) }
"""


def test_byte_field_alias_forall_eq_inline_distinct() -> None:
    """`type MB = Byte;` under forall-Eq with inline-literal construction:
    the #1086 grounding admits the alias (was wrong-loud E613 on the base),
    so the compare must be CORRECT — 0 vs 255 unequal.  The declared-return
    target (`-> @Box<MB>`) grounds to Byte for the width coercion."""
    assert _run_checked(_BYTE_LIT_ALIAS_FORALL_DISTINCT, fn="f") == 0


_BYTE_PASSTHROUGH_CONTROL_DISTINCT = """\
private data Box<T> { MkB(T) }

private fn mk(@Byte -> @Box<Byte>)
  requires(true) ensures(true) effects(pure)
{ MkB(@Byte.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Byte> = mk(0);
  let @Box<Byte> = mk(255);
  @Box<Byte>.0 == @Box<Byte>.1
}
"""


def test_control_byte_field_passthrough_distinct() -> None:
    """A `@Byte`-slot passthrough argument always stored i32 — coherent with
    every reader before and after the fix (pins that the coercion does not
    disturb the already-correct spelling)."""
    assert _run_checked(_BYTE_PASSTHROUGH_CONTROL_DISTINCT, fn="f") == 0


_BYTE_PASSTHROUGH_CONTROL_EQUAL = """\
private data Box<T> { MkB(T) }

private fn mk(@Byte -> @Box<Byte>)
  requires(true) ensures(true) effects(pure)
{ MkB(@Byte.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Byte> = mk(7);
  let @Box<Byte> = mk(7);
  @Box<Byte>.0 == @Box<Byte>.1
}
"""


def test_control_byte_field_passthrough_equal() -> None:
    assert _run_checked(_BYTE_PASSTHROUGH_CONTROL_EQUAL, fn="f") == 1


_BYTE_INT_INSTANTIATION_CONTROL = """\
private data Box<T> { MkB(T) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Int> = MkB(0);
  let @Box<Int> = MkB(4294967296);
  @Box<Int>.0 == @Box<Int>.1
}
"""


def test_control_int_instantiation_literal_untouched() -> None:
    """`let @Box<Int> = MkB(0);` — an Int-instantiated literal field keeps
    its i64 store (the coercion keys on the TARGET arg being Byte; 0 vs
    2^32 must stay distinct at i64 width)."""
    assert _run_checked(_BYTE_INT_INSTANTIATION_CONTROL, fn="f") == 0
