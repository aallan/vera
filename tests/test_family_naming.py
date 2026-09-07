"""The State/Exn cell FAMILY is the cell the checker typed (#1209).

The checker resolves an effect instance's type arguments in full
(``_resolve_effect_ref`` -> ``_resolve_type``), so ``State<MyAlias>`` under
``type MyAlias = Option<Int>`` and ``State<Option<Int>>`` are ONE
``EffectInstance``: one handler handles both spellings, and a call across
them type-checks.  Codegen used to name the family from the SOURCE spelling
for anything that did not resolve to a scalar (the #1205 gate), so those two
spellings minted two host cells — one per checker, two per codegen, a silent
state split behind a green check.

:func:`vera.naming.family_name` is now the one family renderer for every
site (registration, per-function lowering, the ``old(State<T>)`` snapshot),
so the cell identity codegen emits is the cell identity the checker typed.

What this file pins, in order:

* the collapse is OBSERVABLE — a mixed-spelling program returns the value
  the shared cell holds, not the untouched one a split cell leaves behind;
* the import surface COLLAPSES with it — one family, one set of host
  imports, not two;
* it holds across a MODULE boundary, where each side names against its own
  alias namespace;
* distinct cells stay distinct — the collapse is resolution, not erasure;
* a resolution that cannot be MANGLED keeps the opaque spelling, because a
  family name is a WAT symbol before it is anything else;
* alias-free programs are byte-identical, which is what says the change
  reaches exactly the alias spellings and nothing else.

The whole-corpus measurement behind the last point lives in
``tests/test_slot_naming_blast_radius.py``; the unit-level rendering rules
live in ``tests/test_slot_naming.py``.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen.compilability import MAX_CELL_FAMILY_SYMBOL
from vera.codegen import CompileResult, compile as codegen_compile, execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver

_ROOT = Path(__file__).resolve().parent.parent

_STATE_GET_RE = re.compile(r'\(import "vera" "(state_get_[A-Za-z0-9_$?]*)"')
_STATE_IMPORT_RE = re.compile(r'\(import "vera" "(state_[a-z]+_[A-Za-z0-9_$?]*)"')
_EXN_TAG_RE = re.compile(r"\(tag \$(exn_[A-Za-z0-9_$?]*)")


# =====================================================================
# Helpers
# =====================================================================


def _compile_source(source: str, tmp_path: Path, name: str = "m") -> CompileResult:
    """Compile *source* through the real file-based pipeline."""
    path = tmp_path / f"{name}.vera"
    path.write_text(source, encoding="utf-8")
    return _compile_path(path)


def _compile_path(path: Path) -> CompileResult:
    """Parse + resolve + check + compile *path*, asserting a clean check."""
    source = path.read_text(encoding="utf-8")
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=path.parent)
    resolved = resolver.resolve_imports(program, path)
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(path), resolved_modules=resolved,
    )
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, (
        f"{path.name} must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:80]) for d in errors]}"
    )
    return codegen_compile(
        program, source=source, file=str(path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
    )


def _compile_ok(source: str, tmp_path: Path, name: str = "m") -> CompileResult:
    """:func:`_compile_source`, asserting codegen raised no hard error."""
    result = _compile_source(source, tmp_path, name)
    hard = [d for d in result.diagnostics if d.severity == "error"]
    assert not hard, (
        f"expected a clean compile, got: "
        f"{[(d.error_code, d.description[:90]) for d in hard]}"
    )
    return result


def _families(wat: str) -> set[str]:
    """Every State import and Exn tag family symbol emitted in *wat*."""
    return set(_STATE_IMPORT_RE.findall(wat)) | set(_EXN_TAG_RE.findall(wat))


# =====================================================================
# (1) The collapse is observable in what a program COMPUTES
# =====================================================================

# A callee declares the effect one way, the handler spells it the other.  A
# split family gives the handler's cell the initial value forever (the
# callee's `put` lands in a cell nothing reads); a collapsed one gives the
# value the callee wrote, which is what the checker's single instance means.
_MIXED_STATE_COMPOSITE = """\
type MaybeInt = Option<Int>;

private fn stash(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Option<Int>>>)
{
  put(Some(7))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<MaybeInt>](@MaybeInt = None) {
    get(@Unit) -> { resume(@MaybeInt.0) },
    put(@MaybeInt) -> { resume(()) }
  } in {
    stash(());
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""

# The same shape through a PARAMETERISED alias, which reaches the collapse by
# substitution rather than by a bare name follow.
_MIXED_STATE_PARAM_ALIAS = """\
type Boxed<T> = Option<T>;

private fn stash(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Option<Int>>>)
{
  put(Some(7))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Boxed<Int>>](@Boxed<Int> = None) {
    get(@Unit) -> { resume(@Boxed<Int>.0) },
    put(@Boxed<Int>) -> { resume(()) }
  } in {
    stash(());
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""


@pytest.mark.parametrize(
    ("source", "why"),
    [
        (_MIXED_STATE_COMPOSITE, "bare composite alias"),
        (_MIXED_STATE_PARAM_ALIAS, "parameterised composite alias"),
    ],
    ids=["bare_composite_alias", "parameterised_composite_alias"],
)
def test_mixed_spelling_state_cell_is_one_cell(
    source: str, why: str, tmp_path: Path,
) -> None:
    """The handler reads what the differently-spelled callee wrote.

    ``0 - 1`` is the value a SPLIT family produces (the handler's ``None``
    survives because the callee's ``put`` went to a second cell), so the
    assertion distinguishes the two outcomes rather than merely observing
    that the program runs.
    """
    result = _compile_ok(source, tmp_path)
    assert execute(result).value == 7, f"{why}: the two spellings share a cell"


_MIXED_EXN_STRING_ALIAS = """\
type Msg = String;

private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  throw("abcde")
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Msg>] {
    throw(@Msg) -> { string_length(@Msg.0) }
  } in {
    boom(())
  }
}
"""


def test_mixed_spelling_exn_string_payload_moves_its_pair(
    tmp_path: Path,
) -> None:
    """An ``Exn<Msg>`` handler catches an ``Exn<String>`` throw, pair intact.

    ``String`` is an ``i32_pair`` payload — the tag carries ``(ptr, len)`` —
    so this is the shape where a family split is not merely a wrong value
    but a wrong ARITY: the thrower's two-i32 tag and the catcher's tag have
    to be the same tag.  ``string_length`` reads the ``len`` half, so a
    payload that arrived through the wrong tag cannot answer 5 by accident.
    """
    result = _compile_ok(_MIXED_EXN_STRING_ALIAS, tmp_path)
    assert _families(result.wat) == {"exn_String"}, result.wat[:400]
    assert execute(result).value == 5


# =====================================================================
# (2) One collapsed family, one set of host imports
# =====================================================================


def test_one_import_per_collapsed_family(tmp_path: Path) -> None:
    """The mixed-spelling program declares the ``Option<Int>`` family ONCE.

    Every host binding is synthesised per registered family (wasmtime in
    ``vera/runtime/state.py``, the browser bundle by regex over the import
    names), so a family that splits fans the import surface out too — the
    #808 hazard.  Counting the ``state_get_`` imports, not just checking the
    set, catches a duplicate registration under one name as well.
    """
    result = _compile_ok(_MIXED_STATE_COMPOSITE, tmp_path)
    gets = _STATE_GET_RE.findall(result.wat)
    assert gets == ["state_get_Option_LInt_R"], result.wat[:600]
    assert _families(result.wat) == {
        "state_get_Option_LInt_R", "state_put_Option_LInt_R",
        "state_push_Option_LInt_R", "state_pop_Option_LInt_R",
    }


# =====================================================================
# (3) The collapse crosses a module boundary
# =====================================================================

_XMOD_LIB = """\
module paylib;

type Payload = Option<Int>;

public fn stash(@Int -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Payload>>)
{
  put(Some(@Int.0))
}
"""

_XMOD_MAIN = """\
import paylib;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = None) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    stash(7);
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""


def test_cross_module_composite_alias_collapses(tmp_path: Path) -> None:
    """A module-private composite alias joins the importer's cell.

    Each side renders against its OWN alias namespace — ``Payload`` exists
    only in ``paylib`` — and they still have to land on one family, because
    the checker types one instance across the import.  The value oracle is
    the same distinguishing 7-vs--1 as the single-module case.
    """
    (tmp_path / "paylib.vera").write_text(_XMOD_LIB, encoding="utf-8")
    (tmp_path / "main.vera").write_text(_XMOD_MAIN, encoding="utf-8")
    result = _compile_path(tmp_path / "main.vera")
    hard = [d for d in result.diagnostics if d.severity == "error"]
    assert not hard, [(d.error_code, d.description[:90]) for d in hard]
    assert _STATE_GET_RE.findall(result.wat) == ["state_get_Option_LInt_R"]
    assert execute(result).value == 7


# =====================================================================
# (4) Distinct cells stay distinct — the negative
# =====================================================================

_TWO_DISTINCT_CELLS = """\
type MaybeInt = Option<Int>;
type MaybeBool = Option<Bool>;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<MaybeInt>](@MaybeInt = Some(4)) {
    put(@MaybeInt) -> { resume(()) }
  } in {
    handle[State<MaybeBool>](@MaybeBool = None) {
      put(@MaybeBool) -> { resume(()) }
    } in {
      put(Some(true))
    };
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""


def test_two_aliases_of_different_types_keep_two_families(
    tmp_path: Path,
) -> None:
    """Collapsing is RESOLUTION, not erasure of the type argument.

    ``Option<Int>`` and ``Option<Bool>`` are two checker instances, so they
    must stay two cells: two import families, and the outer cell still
    holding 4 after the inner handler wrote to its own.  A family renderer
    that dropped type arguments (the pre-#914 one-level bug) would pass the
    positive tests above and fail here.
    """
    result = _compile_ok(_TWO_DISTINCT_CELLS, tmp_path)
    assert set(_STATE_GET_RE.findall(result.wat)) == {
        "state_get_Option_LInt_R", "state_get_Option_LBool_R",
    }, result.wat[:600]
    assert execute(result).value == 4


# =====================================================================
# (5) A family name is a WAT symbol before it is anything else
# =====================================================================

_NESTED_FN_CELL = """\
type Handler = Option<fn(Int -> Int) effects(pure)>;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Handler>](@Handler = None) {
    put(@Handler) -> { resume(()) }
  } in {
    0
  }
}
"""

# The #1219 flip made observable: a callee declares the cell by its RESOLVED
# spelling, the handler by the alias.  Pre-flip those were two families, so
# the callee's `put` landed in a cell nothing read and `main` returned the
# handler's initial `0 - 1`; post-flip they are one cell and it returns 5.
_MIXED_FN_CELL = """\
type Handler = Option<fn(Int -> Int) effects(pure)>;

private fn stash(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Option<fn(Int -> Int) effects(pure)>>>)
{
  put(Some(fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Handler>](@Handler = None) {
    get(@Unit) -> { resume(@Handler.0) },
    put(@Handler) -> { resume(()) }
  } in {
    stash(());
    match get(()) {
      Some(@Fn) -> 5,
      None -> 0 - 1
    }
  }
}
"""

# The elision the spellability gate had been masking.  `Option<Pos>` and
# `Option<Neg>` are two checker instances, and both render
# `Option<{@Int | ...}>` through `pretty_type` — so dropping the gate
# WITHOUT moving to the structural key would have merged them.
_TWO_REFINED_ARG_CELLS = """\
type Pos = { @Int | @Int.0 > 0 };
type Neg = { @Int | @Int.0 < 0 };

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Pos>>](@Option<Pos> = None) {
    put(@Option<Pos>) -> { resume(()) }
  } in {
    handle[State<Option<Neg>>](@Option<Neg> = None) {
      put(@Option<Neg>) -> { resume(()) }
    } in {
      0
    };
    0
  }
}
"""


def test_fn_type_composite_cell_takes_its_resolved_family(
    tmp_path: Path,
) -> None:
    """A cell whose resolution carries a function type DOES take it (#1219).

    ``Option<fn(Int -> Int) effects(pure)>`` renders with parentheses and an
    arrow, which the pre-#1219 escape did not cover — emitting it produced
    an import name the WAT parser rejects, so ``family_name`` gated on the
    spellable ``Head<arg, arg>`` grammar and kept the alias-opaque
    ``Handler``.  With the mangler total, the resolved rendering IS the
    family and the symbol is its mangling: the ``_U28_``/``_U29_`` are the
    parentheses, ``_U2d__R`` the arrow.
    """
    result = _compile_ok(_NESTED_FN_CELL, tmp_path)
    assert _STATE_GET_RE.findall(result.wat) == [
        "state_get_Option_Lfn_U28_Int_S_U2d__R_SInt_U29__Seffects"
        "_U28_pure_U29__R"
    ]
    assert execute(result).value == 0


def test_mixed_spelling_fn_type_cell_is_one_cell(tmp_path: Path) -> None:
    """The alias and its resolution name ONE cell, proved by the value.

    ``0 - 1`` is what a split family produces — the handler's ``None``
    survives because ``stash``'s ``put`` went to a second cell — and ``5``
    is reachable only when the handler's ``get`` observes the ``Some`` the
    differently-spelled callee wrote.  This is the run-level half of #1219:
    the symbol assertion above says the two names agree, this says the two
    SITES do.  Neither outcome is a zero default.
    """
    result = _compile_ok(_MIXED_FN_CELL, tmp_path)
    assert len(set(_STATE_GET_RE.findall(result.wat))) == 1, result.wat[:600]
    assert execute(result).value == 5


_BARE_FN_CELL = """\
type F = fn(Int -> Int) effects(pure);

public fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<F>](@F = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }) {
    get(@Unit) -> { resume(@F.0) },
    put(@F) -> { resume(()) }
  } in {
    apply_fn(get(()), 41)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(())
}
"""


def test_bare_fn_type_cell_still_takes_the_fallback_and_is_refused(
    tmp_path: Path,
) -> None:
    """What is LEFT for ``family_fallback_name`` after #1219, pinned.

    #1219 removed the mangle-safety gate, not the fallback: a type
    expression whose resolution IS a bare function type has no cell type to
    name at all, so ``family_name`` returns the fallback and the cell keeps
    its alias-opaque spelling — ``F``, never ``fn(Int -> Int)
    effects(pure)``.  The other survivor is an unresolvable type expression
    (a removed alias, an alias applied at the wrong arity), which renders
    ``?``; keeping the spelling there stops two unrelated broken cells from
    merging onto one ``?`` family.

    Inert either way, and this pins that too: the shape is refused
    downstream, the enclosing function dropped loudly (E616 for the closure
    read, then E602/E620), so the fallback name reaches an import
    declaration and nothing that calls it.  Splitting it is therefore free,
    and merging it would be the only thing with a cost.

    Promoted from ``tests/probes/state_handlers/alias_families/
    p7_fn_alias_state_arg.vera``, which asked this question and was deleted
    with the #1219 disposition.
    """
    result = _compile_source(_BARE_FN_CELL, tmp_path)
    assert _families(result.wat) == {
        "state_get_F", "state_put_F", "state_push_F", "state_pop_F",
    }, result.wat[:400]
    codes = {d.error_code for d in result.diagnostics}
    assert {"E602", "E620"} <= codes, codes
    assert "(func $probe" not in result.wat
    assert "(func $main" not in result.wat


def test_two_refinements_of_one_base_in_argument_position_stay_apart(
    tmp_path: Path,
) -> None:
    """Dropping the gate must not merge what ``pretty_type`` elides (#1219).

    ``Option<Pos>`` and ``Option<Neg>`` are two checker instances that
    ``pretty_type`` renders identically (``Option<{@Int | ...}>``), because
    a refinement in argument position prints its predicate as ``...``.  The
    spellability gate refused that rendering and both cells fell back to
    their alias spellings, so the elision never reached a symbol; removing
    the gate without moving to the structural key would have merged them.
    Two families here is the assertion that the move happened.
    """
    result = _compile_ok(_TWO_REFINED_ARG_CELLS, tmp_path)
    families = set(_STATE_GET_RE.findall(result.wat))
    assert len(families) == 2, families


# =====================================================================
# (6) Alias-free programs are byte-identical
# =====================================================================

# Every corpus program that emits a family symbol and contains no alias in
# the cell position: the exact symbol set, pinned.  The #1209 flip moved
# NONE of these — that is what says it reaches alias spellings only.
_STABLE_SYMBOLS: tuple[tuple[str, frozenset[str]], ...] = (
    ("examples/increment.vera", frozenset({
        "state_get_Int", "state_put_Int", "state_push_Int", "state_pop_Int"})),
    ("examples/effect_handler.vera", frozenset({
        "state_get_Int", "state_put_Int", "state_push_Int", "state_pop_Int",
        "exn_Int"})),
    ("tests/conformance/ch07_state_composite.vera", frozenset({
        "state_get_Option_LInt_R", "state_put_Option_LInt_R",
        "state_push_Option_LInt_R", "state_pop_Option_LInt_R",
        "state_get_Tuple_LInt_CInt_R", "state_put_Tuple_LInt_CInt_R",
        "state_push_Tuple_LInt_CInt_R", "state_pop_Tuple_LInt_CInt_R"})),
    ("tests/conformance/ch07_exn_composite.vera", frozenset({
        "exn_Option_LInt_R", "exn_Tuple_LInt_CInt_R"})),
    ("tests/conformance/ch07_exn_string.vera", frozenset({"exn_String"})),
    ("tests/conformance/ch07_state_old_composite.vera", frozenset({
        "state_get_Option_LInt_R", "state_put_Option_LInt_R",
        "state_push_Option_LInt_R", "state_pop_Option_LInt_R"})),
    # The #1205 scalar-alias collapse, unchanged by the composite one.
    ("tests/conformance/ch07_state_alias.vera", frozenset({
        "state_get_Nat", "state_put_Nat", "state_push_Nat", "state_pop_Nat"})),
)


@pytest.mark.parametrize(
    ("rel", "expected"), _STABLE_SYMBOLS, ids=[s[0] for s in _STABLE_SYMBOLS],
)
def test_family_symbols_are_stable(rel: str, expected: frozenset[str]) -> None:
    """The emitted family symbols of a corpus program, pinned exactly.

    These are the ABI: a host binds ``state_get_<family>`` by name, so a
    renderer change that renames a family silently breaks every host that
    already provides it.  Asserting the exact set (not a subset) catches a
    rename, an extra family, and a dropped one alike.
    """
    result = _compile_path(_ROOT / rel)
    hard = [d for d in result.diagnostics if d.severity == "error"]
    assert not hard, [(d.error_code, d.description[:90]) for d in hard]
    assert _families(result.wat) == set(expected)


# =====================================================================
# (7) The measured radius: every corpus file the flip moved
# =====================================================================

# The whole `.vera` corpus (examples, conformance, the PR #1202 probe corpus)
# was captured before and after: `vera check --json` for every program,
# `vera run` for every probe, and the emitted `state_*` / `exn_*` symbols for
# everything that compiles.  SIX shapes differ, in two classes:
#
#   (a) two spellings of one cell now SHARE it, so the program computes a
#       different — and correct — value;
#   (b) the family symbol RENAMES from the source spelling to the resolved
#       cell (and, where both spellings appear, two families become one).
#
# No `check` diagnostic moved anywhere.  Pinning the whole set (not a sample)
# is what makes "something else also moved" a finding rather than noise.
#
# Each shape was measured on a probe program and now lives in the conformance
# suite, which is where the promotion put it; the entry point named here is
# the one whose value the probe pinned, so the assertions are the measured
# ones and not a re-baseline.
_C8_DIVERGENT: tuple[
    tuple[str, str | None, int | str, frozenset[str], str], ...
] = (
    (
        "ch07_state_composite_alias_cross_spelling.vera", None, 7, frozenset({
            "state_get_Option_LInt_R", "state_put_Option_LInt_R",
            "state_push_Option_LInt_R", "state_pop_Option_LInt_R"}),
        "(a)+(b) `State<MaybeInt>` handler around a `State<Option<Int>>` "
        "callee: EIGHT symbols (two families) collapse to four, and the "
        "program goes -1 -> 7 — the callee's write is now visible",
    ),
    (
        "ch07_state_composite_alias.vera", "roundtrip", 3, frozenset({
            "state_get_Option_LInt_R", "state_put_Option_LInt_R",
            "state_push_Option_LInt_R", "state_pop_Option_LInt_R"}),
        "(b) `state_*_MaybeInt` -> `state_*_Option_LInt_R`; single spelling, "
        "so the value is unchanged",
    ),
    (
        "ch07_state_composite_alias.vera", "put_then_read", 42, frozenset({
            "state_get_Option_LInt_R", "state_put_Option_LInt_R",
            "state_push_Option_LInt_R", "state_pop_Option_LInt_R"}),
        "(b) the same rename with a `match get(())` scrutinee",
    ),
    (
        "ch08_state_alias_per_module.vera", None, 16, frozenset({
            "state_get_Nat", "state_put_Nat",
            "state_push_Nat", "state_pop_Nat",
            "state_get_Option_LInt_R", "state_put_Option_LInt_R",
            "state_push_Option_LInt_R", "state_pop_Option_LInt_R"}),
        "(b) two modules declare `Hid<T>` differently — the module's `= T` "
        "stays the `Nat` family, the importer's `= Option<T>` renames from "
        "`Hid<Int>` to `Option<Int>`: each resolved in ITS OWN namespace",
    ),
    (
        "ch07_exn_string_alias.vera", "catch_text", "caught: negative",
        frozenset({"exn_String"}),
        "(b) `exn_Name` -> `exn_String` for `type Name = String`; the "
        "two-i32 payload still arrives intact",
    ),
    (
        "ch07_exn_string_alias.vera", "catch_length", 3,
        frozenset({"exn_String"}),
        "(b) `exn_Msg` -> `exn_String`, same pair payload through "
        "`string_length`",
    ),
)

_CONFORMANCE = _ROOT / "tests" / "conformance"


@pytest.mark.parametrize(
    ("rel", "fn", "expected", "families", "why"),
    _C8_DIVERGENT,
    ids=[f"{d[0]}::{d[1] or 'main'}" for d in _C8_DIVERGENT],
)
def test_moved_corpus_file_lands_where_it_was_measured(
    rel: str, fn: str | None, expected: int | str, families: frozenset[str],
    why: str,
) -> None:
    """Each shape the flip moved, at the symbols AND the value it moved to.

    Asserting the value as well as the symbol set is what separates "the
    families collapsed" from "the families collapsed onto the right cell":
    a merge into the WRONG family also produces one symbol set.
    """
    result = _compile_path(_CONFORMANCE / rel)
    hard = [d for d in result.diagnostics if d.severity == "error"]
    assert not hard, (
        f"{rel} should compile clean — {why}\n"
        f"got: {[(d.error_code, d.description[:90]) for d in hard]}"
    )
    assert _families(result.wat) == set(families), why
    ran = execute(result) if fn is None else execute(result, fn_name=fn)
    assert ran.value == expected, why


def test_moved_set_is_exactly_this_size() -> None:
    """Every pinned entry is distinct, and each names a file that exists.

    A count alone would pass on a table that repeated one entry six times, or
    that named a program since renamed away; this pins the shape of the table
    itself.  That the table is the WHOLE measured radius rather than a sample
    is the corpus sweep's claim, not this test's (PR #1224 review).
    """
    assert len(_C8_DIVERGENT) == 6
    assert len({(d[0], d[1]) for d in _C8_DIVERGENT}) == 6
    for rel, *_ in _C8_DIVERGENT:
        assert (_CONFORMANCE / rel).is_file(), rel


# =====================================================================
# (8) A REFINED cell is its own cell (#1218)
# =====================================================================

# The checker keeps `State<Pos>`, `State<Neg>` and `State<Int>` apart over
# one base — `EffectInstance` holds the `RefinedType`, and E125 refuses to
# pass one where another is required.  Codegen collapsed all three to the
# `Int` family, so three checker cells shared one host cell and a callee
# bound to the OUTER one wrote whichever was innermost.  Each program below
# has a value oracle whose wrong answer is the collapsed one.
_REFINED_ALIASES = """\
type Pos = { @Int | @Int.0 > 0 };
type Neg = { @Int | @Int.0 < 0 };
"""

_POS_OUTSIDE_NEG_INSIDE = _REFINED_ALIASES + """
private fn touch_outer(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Pos>>)
{
  put(111)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Pos>](@Pos = 1) {
    put(@Pos) -> { resume(()) }
  } in {
    handle[State<Neg>](@Neg = 0 - 1) {
      put(@Neg) -> { resume(()) }
    } in {
      touch_outer(())
    };
    get(())
  }
}
"""

_NEG_OUTSIDE_POS_INSIDE = _REFINED_ALIASES + """
private fn touch_outer(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Neg>>)
{
  put(0 - 222)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Neg>](@Neg = 0 - 1) {
    put(@Neg) -> { resume(()) }
  } in {
    handle[State<Pos>](@Pos = 1) {
      put(@Pos) -> { resume(()) }
    } in {
      touch_outer(())
    };
    get(())
  }
}
"""

_REFINED_INSIDE_BARE = _REFINED_ALIASES + """
private fn touch_outer(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  put(7)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 0) {
    put(@Int) -> { resume(()) }
  } in {
    handle[State<Pos>](@Pos = 33) {
      put(@Pos) -> { resume(()) }
    } in {
      touch_outer(())
    };
    get(())
  }
}
"""

_THREE_DEEP_CLAUSE_BODY = _REFINED_ALIASES + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Pos>](@Pos = 1) {
    get(@Unit) -> { resume(@Pos.0) }
  } in {
    handle[State<Neg>](@Neg = 0 - 1) {
      put(@Neg) -> { put(42); resume(()) }
    } in {
      handle[State<Pos>](@Pos = 2) {
        get(@Unit) -> { resume(@Pos.0) }
      } in {
        0
      };
      put(0 - 5)
    };
    get(())
  }
}
"""


@pytest.mark.parametrize(
    ("source", "expected", "collapsed", "why"),
    [
        (_POS_OUTSIDE_NEG_INSIDE, 111, 1,
         "a State<Pos> callee inside a State<Neg> handler writes the Pos cell"),
        (_NEG_OUTSIDE_POS_INSIDE, -222, -1,
         "and the mirror: a State<Neg> callee inside a State<Pos> handler"),
        (_REFINED_INSIDE_BARE, 7, 0,
         "same base, refined vs bare: State<Pos> inside State<Int> is two "
         "cells, both addressable"),
    ],
    ids=["pos_outside_neg_inside", "neg_outside_pos_inside",
         "refined_inside_bare"],
)
def test_nested_refinements_of_one_base_route_to_their_own_cells(
    source: str, expected: int, collapsed: int, why: str, tmp_path: Path,
) -> None:
    """Each nesting writes the cell the CHECKER says it writes (#1218).

    *collapsed* is the value the pre-fix single-`Int`-family lowering
    produced — the inner cell's, or the outer's untouched initial — so the
    assertion distinguishes right from wrong rather than merely observing
    that the program runs.  None of the six values is a zero default.
    """
    result = _compile_ok(source, tmp_path)
    assert len(_families(result.wat)) == 8, (
        f"{why}: two cells means two four-import families, got "
        f"{sorted(_families(result.wat))}"
    )
    ran = execute(result)
    assert ran.value != collapsed, f"{why}: still the collapsed answer"
    assert ran.value == expected, why


def test_three_deep_refined_nest_routes_a_clause_body_op_outward(
    tmp_path: Path,
) -> None:
    """The enclosing-context rule, through a Pos/Neg/Pos nest (#1218/#1233).

    The MIDDLE (Neg) handler's clause body runs a bare `put(42)`, which
    §7.5.2 routes to the ENCLOSING context — the outermost Pos handler.  The
    innermost Pos handler has been popped by then, so the Pos family's
    innermost cell IS the outer one and the write is addressable: 42.

    Pre-fix all three cells were the `Int` family, so the #1233
    addressability gate saw a same-family nest and refused the program
    outright (E602).  Distinct refined families make the shape legal again
    AND route it correctly, which is why this asserts a value rather than
    the absence of a diagnostic.
    """
    result = _compile_ok(_THREE_DEEP_CLAUSE_BODY, tmp_path)
    assert execute(result).value == 42


# The #1203 write guards are keyed on the cell's REPRESENTATION, so a
# refined cell keeps every guard its base gets.  Sharing one name for
# identity and representation is what made this a hazard: a family that
# discriminates the predicate matches no entry in the `"Nat"`/`"Int"`/
# `"Byte"` tables, and the guards would stop being emitted while the
# verifier went on recording them as `tier3_runtime`.
_BARE_NAT_CELL = """\
public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 0) {
    put(@Nat) -> { resume(()) }
  } in {
    put(get(()) - 1);
    get(())
  }
}
"""

_REFINED_NAT_CELL = """\
type Small = { @Nat | @Nat.0 < 100 };

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Small>](@Small = 0) {
    put(@Small) -> { resume(()) }
  } in {
    put(get(()) - 1);
    get(())
  }
}
"""


def test_refined_nat_cell_emits_the_same_write_guards_as_its_base(
    tmp_path: Path,
) -> None:
    """A refined `@Nat` cell keeps every #1203 guard the bare cell gets.

    A DIFFERENTIAL rather than a unit assertion, because the property is a
    cross-component one: the verifier records these obligations as
    `tier3_runtime` on the promise that codegen emits them, and a guard that
    silently stops being emitted leaves the obligation stream claiming a
    runtime check that does not exist.  Comparing the two programs' guard
    counts is what catches that; asserting "the refined program has some
    guards" would not.

    Mutation-validated: routing the clause-path guard back onto the cell's
    IDENTITY (`entry.family`) instead of its representation drops the
    refined program from two guard sites to one while the bare program keeps
    both.
    """
    bare = _compile_ok(_BARE_NAT_CELL, tmp_path, name="bare")
    refined = _compile_ok(_REFINED_NAT_CELL, tmp_path, name="refined")
    assert bare.wat.count("i64.lt_s") > 0
    # `>=`, not `==`, since #1439: a refined cell takes the §2.6.5
    # PREDICATE guard at each write boundary as well as the #1203 sign
    # guard, and both lower through the same comparison.  The property
    # this cell was written for is unchanged and is what `>=` states —
    # the refined cell must not LOSE a guard its base gets.
    # Counted by SIGNAL, not by shared tokens: the sign guard calls
    # `$vera.nat_guard_trap` and the predicate guard `$vera.contract_fail`,
    # and both lower through `i64.lt_s` — `refinement_binder_parts` conjoins
    # the implicit `@Nat >= 0` — so a `>=` on the shared token could not see
    # a removed sign guard (CR PR-review).
    assert (refined.wat.count("$vera.nat_guard_trap")
            == bare.wat.count("$vera.nat_guard_trap")), (
        "the refined cell lost a #1203 narrowing guard its base still gets"
    )
    assert "$vera.contract_fail" in refined.wat, (
        "the refined cell emits no §2.6.5 predicate guard, so the extra "
        "comparisons counted here are not the ones this cell is about"
    )
    # `unreachable` is shared by both guards, so it stays a `>=`; the exact
    # comparison that matters is the per-signal one above.
    assert refined.wat.count("unreachable") >= bare.wat.count("unreachable")


_REFINED_STRING_EXN = """\
type Short = { @String | string_length(@String.0) < 10 };

private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Short>>)
{
  throw("abcde")
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Short>] {
    throw(@Short) -> { string_length(@Short.0) }
  } in {
    boom(())
  }
}
"""


def test_refined_string_exn_payload_is_still_a_pair(tmp_path: Path) -> None:
    """A refined `String` tag keeps its (ptr, len) payload (#1218).

    Pair-ness is a REPRESENTATION question, and the identity name a refined
    cell now carries matches nothing in the pair table — so asking it would
    declare a one-i32 tag and bind a single local against a two-i32 throw.
    The length coming back proves both halves moved.
    """
    result = _compile_ok(_REFINED_STRING_EXN, tmp_path)
    tags = {t for t in _families(result.wat) if t.startswith("exn_")}
    assert len(tags) == 1, tags
    assert "(param i32 i32)" in result.wat, "refined String tag lost its pair"
    assert execute(result).value == 5


# =====================================================================
# (9) Symbol length is LINEAR in the predicate (PR #1238 review, F1)
# =====================================================================

# `structural_type_key` rendered the predicate with `ast.Node.pretty`, a
# newline-indented tree whose size is quadratic in nesting depth: a
# left-nested `&&` chain of 44 conjuncts produced a 112,626-character
# mangled symbol, past wasmparser's 100,000-byte name-string cap.  Check,
# verify and compile were all green; `vera run` failed to PARSE the module
# it had just emitted, while the same module ran under the browser host —
# a runtime divergence on a check-green program.  The predicate now renders
# through `vera fmt`'s own canonical expression form, so growth is linear
# in the source the user wrote.


def _conjunct_program(n: int) -> str:
    """A refined cell whose predicate is a left-nested `&&` chain."""
    conj = " && ".join(f"@Int.0 > {i}" for i in range(n))
    return (
        f"type Deep = {{ @Int | {conj} }};\n"
        "\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  handle[State<Deep>](@Deep = 100) {\n"
        "    put(@Deep) -> { resume(()) }\n"
        "  } in {\n"
        "    put(101);\n"
        "    get(())\n"
        "  }\n"
        "}\n"
    )


@pytest.mark.parametrize("n", [20, 44])
def test_deeply_conjoined_predicate_compiles_and_runs(
    n: int, tmp_path: Path,
) -> None:
    """The reviewer's shape compiles AND runs, at 20 and at 44 conjuncts.

    44 is the depth that crossed the name-string cap before the renderer
    changed; 20 is the depth the reviewer measured at 26,178 characters,
    under the cap but already growing quadratically.  Both must reach a
    module wasmtime can parse, and both must produce 101 — the value only a
    correctly-addressed cell can give.
    """
    result = _compile_ok(_conjunct_program(n), tmp_path)
    assert execute(result).value == 101


def test_predicate_symbol_length_is_linear_in_the_predicate() -> None:
    """Doubling the conjunct count roughly doubles the symbol (not squares).

    Measured on the rendering rather than on a compiled module, so the
    property is pinned independently of whatever the current cap is: a
    quadratic renderer fails this at any cap, it just fails LOUDLY at a
    different depth.
    """
    from vera.monomorphize import mangle_type_name
    from vera.types import INT, RefinedType, structural_type_key

    def mangled_len(n: int) -> int:
        conj = " && ".join(f"@Int.0 > {i}" for i in range(n))
        program = parse_to_ast(f"type T = {{ @Int | {conj} }};\n")
        te = program.declarations[0].decl.type_expr
        key = structural_type_key(RefinedType(INT, te.predicate))
        return len(mangle_type_name(key))

    at20, at40, at80 = mangled_len(20), mangled_len(40), mangled_len(80)
    # Linear: each doubling multiplies by ~2.  Quadratic would be ~4, and
    # the pre-fix renderer measured 3.9x and 3.95x across these two steps.
    assert 1.8 < at40 / at20 < 2.6, (at20, at40)
    assert 1.8 < at80 / at40 < 2.6, (at40, at80)
    # And the absolute size at the depth that used to break wasmtime.
    assert mangled_len(44) < 2_000, mangled_len(44)


def test_a_predicate_past_the_cap_is_refused_loudly(tmp_path: Path) -> None:
    """Past the backstop cap the cell is REFUSED, never silently emitted.

    The renderer makes the symbol linear, so reaching the cap now needs a
    predicate of roughly the cap's own size — but "roughly" is not "never",
    and an unloadable module is the one outcome that must be impossible.
    `_register_state_cell` refuses the cell exactly as it refuses one with
    no WASM representation (E607), and the enclosing function is dropped
    loudly rather than compiled against an import that cannot be named.

    200 conjuncts is chosen over something larger because the PARSER
    recursion-errors on a left-nested chain around 500, so the band where
    this cap is what refuses runs from ~110 conjuncts to ~400 — this sits
    inside it (7,294 mangled characters against the 4,096 cap) and stays
    inside it if either bound moves a little.
    """
    result = _compile_source(_conjunct_program(200), tmp_path)
    codes = {d.error_code for d in result.diagnostics}
    assert "E607" in codes, codes
    assert _families(result.wat) == set(), sorted(_families(result.wat))
    note = next(d for d in result.diagnostics if d.error_code == "E607")
    assert "cell family symbol" in note.description, note.description
    assert f"{MAX_CELL_FAMILY_SYMBOL:,}" in note.rationale, note.rationale


def test_the_cap_refusal_reaches_the_browser_target_too(
    tmp_path: Path,
) -> None:
    """The refusal happens at COMPILE, so every host sees it (F1 part 2).

    The bug this backstops was a DIVERGENCE — wasmtime could not parse the
    module the browser host ran happily — so a cap enforced anywhere but at
    emission would reproduce it one cap later.  Refusing at family
    registration means the oversized import is never written, and the
    browser bundle's own import synthesis has nothing to bind.

    So this actually emits the bundle and reads it (PR #1238 review): a test
    named for the second host that only re-read the first host's artefact
    would record coverage that does not exist.  The module the browser is
    handed carries no `state_*` import at all, which is what makes the two
    hosts agree by construction rather than by a second cap.
    """
    from vera.browser.emit import emit_browser_bundle

    result = _compile_source(_conjunct_program(200), tmp_path)
    assert "E607" in {d.error_code for d in result.diagnostics}
    assert "(func $main" not in result.wat, "the enclosing function is dropped"

    out_dir = tmp_path / "bundle"
    emit_browser_bundle(result.wasm_bytes, out_dir)
    module = (out_dir / "module.wasm").read_bytes()
    # The runtime binds `state_*` by splitting import NAMES out of the
    # module's own import section, so an absent import is an absent binding.
    assert b"state_get_" not in module, "an oversized cell reached the bundle"
    assert b"state_push_" not in module
    runtime = (out_dir / "runtime.mjs").read_text(encoding="utf-8")
    assert "state_get_" in runtime, (
        "the runtime's import synthesis should still be present — this test "
        "is about the module carrying nothing for it to bind, not about the "
        "runtime losing the feature"
    )


def test_every_expression_kind_has_a_formatter_arm() -> None:
    """`format_expr_canonical` is TOTAL over expressions, which its two users need.

    `Formatter._fmt_expr` ends in a `return "<expr>"` catch-all.  For
    `vera fmt` that would be a broken emission caught by the formatter's own
    re-parse postcondition; for `vera.types.structural_type_key` it would be
    worse and quieter — two structurally distinct predicates both rendering
    `<expr>` share a cell FAMILY, which is a shared State cell behind a
    check that typed them apart (#1218's failure mode, reintroduced through
    the renderer that fixed it).

    Checked STRUCTURALLY, the way `scripts/check_walker_coverage.py` checks
    its walkers: the classes `_fmt_expr` actually branches on, read off its
    `isinstance` calls.  A raw substring search over the same source would
    discharge an arm from a comment or a docstring that merely names the
    class (PR #1238 review), which is a false green on the property that
    two predicates never share a family name.

    `_EXPR_BASES` is excluded, and the exclusion is an explicit LIST rather
    than a predicate, because no predicate is true (PR #1238 review).
    `ast.Expr` is a plain frozen dataclass with a documentation convention,
    not an ABC — `inspect.isabstract` is False for every class in the
    module, so filtering on it excluded nothing at all.  Nor does "declares
    no dataclass fields of its own" work: `UnitLit` and `HoleExpr` declare
    none either, and both are concrete nodes that need an arm.

    The list is cross-checked in both directions so it cannot rot silently.
    A class listed here must HAVE subclasses, which no concrete leaf does,
    so a concrete node can never be quietly excluded; and a class that has
    subclasses and is NOT listed fails loudly, naming itself, which is what
    a future convention-only intermediate would do.  A red gate demanding a
    human decision is the right failure for a base-class question that
    Python cannot answer here.

    Name presence is only half the gate — a class can be dispatched and
    still render indistinguishably.  `test_format_expr_renders_every_kind
    _distinctly` is the behavioural half.

    SCOPE, stated rather than gated: `_fmt_type_bare`, `_fmt_pattern` and
    `_fmt_effect_row` have catch-alls of their own (`"?"`, `"_"`), reached
    through this dispatch from binding patterns and lambda signatures.
    Every current subclass of each has an arm, and each catch-all is marked
    `# pragma: no cover`; they are not enumerated here because their class
    sets are closed by the grammar rather than open like `Expr`.
    """
    import ast as py_ast
    import inspect

    from vera import ast as ast_mod

    # The convention-only base classes.  A new intermediate between `Expr`
    # and the concrete nodes must be ADDED here; until it is, the
    # cross-check below fails and names it.
    expr_bases = (ast_mod.Expr,)

    every = [
        c for c in vars(ast_mod).values()
        if inspect.isclass(c) and issubclass(c, ast_mod.Expr)
    ]
    has_subclasses = {
        c.__name__ for c in every
        if any(o is not c and issubclass(o, c) for o in every)
    }
    excluded = {c.__name__ for c in expr_bases}
    assert excluded <= has_subclasses, (
        f"listed as a base but has no subclasses, so it is a concrete node "
        f"whose arm this gate would stop requiring: "
        f"{sorted(excluded - has_subclasses)}"
    )
    assert has_subclasses <= excluded, (
        f"new intermediate class(es) between ast.Expr and the concrete "
        f"nodes: {sorted(has_subclasses - excluded)}.  Add to `expr_bases` "
        f"if they are convention-only bases with no `_fmt_expr` arm; "
        f"otherwise give each one an arm."
    )

    subclasses = sorted({
        c.__name__ for c in every if c.__name__ not in excluded
    })
    source = (_ROOT / "vera" / "formatter.py").read_text(encoding="utf-8")
    dispatched: set[str] = set()
    for node in py_ast.walk(py_ast.parse(source)):
        if not isinstance(node, py_ast.FunctionDef) or node.name != "_fmt_expr":
            continue
        for call in py_ast.walk(node):
            if not isinstance(call, py_ast.Call):
                continue
            if getattr(call.func, "id", None) != "isinstance":
                continue
            target = call.args[1]
            names = target.elts if isinstance(target, py_ast.Tuple) else [target]
            dispatched.update(
                n.id for n in names if isinstance(n, py_ast.Name))
    missing = [name for name in subclasses if name not in dispatched]
    assert not missing, (
        f"ast.Expr subclasses with no _fmt_expr arm, so they would render "
        f"as the lossy '<expr>' catch-all: {missing}"
    )
    assert len(subclasses) >= 25, subclasses


# One representative source expression per `ast.Expr` kind the grammar lets
# a refinement predicate hold, plus the three shapes canonical form merges.
# Every one must render to its own string: dispatching a class is not the
# same as DISCRIMINATING it, and only the latter keeps two cells apart.
_KIND_SAMPLES: tuple[str, ...] = (
    "1 > @Int.0",                       # IntLit
    "2 > @Int.0",                       # IntLit, another value
    "1.5 > 0.0 && @Int.0 > 0",          # FloatLit
    "true && @Int.0 > 0",               # BoolLit
    "false || @Int.0 > 0",              # BoolLit, another value
    'string_length("s") > @Int.0',      # StringLit
    'string_length("\\(1)") > @Int.0',    # InterpolatedString
    "array_length([1, 2]) > @Int.0",    # ArrayLit
    "@Int.0 > 0",                       # SlotRef
    "@Int.0 + 1 > 0",                   # BinaryExpr
    "!(@Int.0 > 0)",                    # UnaryExpr
    "[1, 2][0] > @Int.0",               # IndexExpr
    "int_abs(@Int.0) > 0",              # FnCall
    "if @Int.0 > 0 then { true } else { false }",   # IfExpr
    "{ @Int.0 } > 0",                   # Block
    "assert(@Int.0 > 0)",               # AssertExpr
    "assume(@Int.0 > 0)",               # AssumeExpr
    "?",                                # HoleExpr
)

_MERGE_SAMPLES: tuple[tuple[str, str], ...] = (
    ("private data Col { Red, Green }\n\n",
     "match Red { Red -> { true }, Green -> false }"),
    ("private data Col { Red, Green }\n\n",
     "match Red { Red -> true, Green -> false }"),
    ("private data Col { Red, Green }\n\n",
     "match Red { Red -> { { true } }, Green -> false }"),
    ("private data Col { Red, Green }\n\n",
     "match Red { Red -> { true }, Green -> { false } }"),
)


def test_format_expr_renders_every_kind_distinctly() -> None:
    """The BEHAVIOURAL half of the coverage gate (PR #1238 review, G2).

    The static gate above proves each class is dispatched.  It cannot
    prove the dispatch DISCRIMINATES, and three mutants survive it: a class
    named only in a comment, a catch-all that returns a constant, and two
    arms collapsed onto one rendering.  All three are wrong in the same
    direction — two predicates that render alike name one cell family.

    So: format a representative of every kind, plus the arm-block shapes
    canonical form deliberately merges, and require the renderings to be
    pairwise distinct and free of the `<expr>` marker.  Structural mode,
    because that is the mode `structural_type_key` uses and the one whose
    injectivity is load-bearing.
    """
    from vera.formatter import format_expr_canonical

    def predicate(text: str, prelude: str = ""):
        program = parse_to_ast(f"{prelude}type Probe = {{ @Int | {text} }};\n")
        for decl in program.declarations:
            inner = getattr(decl, "decl", decl)
            if getattr(inner, "name", None) == "Probe":
                return inner.type_expr.predicate
        raise AssertionError(f"no Probe in {text!r}")

    samples = [("", text) for text in _KIND_SAMPLES] + list(_MERGE_SAMPLES)
    seen: dict[str, str] = {}
    for prelude, text in samples:
        rendered = format_expr_canonical(predicate(text, prelude),
                                         structural=True)
        assert "<expr>" not in rendered, (
            f"{text!r} hit the lossy catch-all: {rendered!r}")
        assert rendered not in seen, (
            f"two predicates render alike, so they would share a cell "
            f"family: {text!r} and {seen[rendered]!r} both -> {rendered!r}")
        seen[rendered] = text
    assert len(seen) == len(samples)


def test_format_expr_canonical_round_trips_adversarial_predicates() -> None:
    """`parse(format(e)) == e` — the property injectivity rests on.

    Associativity is where a canonical renderer would lose information if it
    simply dropped parentheses: `(a + b) + c` and `a + (b + c)` are distinct
    expressions, hence distinct refinement types, hence cells the checker
    keeps apart.  `_needs_parens` re-derives the brackets from precedence
    and associativity, so the first renders bare and the second keeps its
    pair.  Each case below is checked BOTH ways — it round-trips, and no two
    of them collide.
    """
    from vera.formatter import format_expr_canonical

    def predicate(text: str) -> object:
        program = parse_to_ast(f"type T = {{ @Int | {text} }};\n")
        return program.declarations[0].decl.type_expr.predicate

    cases = [
        "@Int.0 > 0",
        "@Int.0 < 0",
        "(@Int.0 + 1) + 2 > 0",
        "@Int.0 + (1 + 2) > 0",
        "@Int.0 - 1 - 2 > 0",
        "@Int.0 - (1 - 2) > 0",
        "@Int.0 > 0 && @Int.0 < 5 && @Int.0 != 3",
        "@Int.0 > 0 && (@Int.0 < 5 && @Int.0 != 3)",
        "(@Int.0 > 0 && @Int.0 < 5) || @Int.0 == 9",
        "@Int.0 > 0 && (@Int.0 < 5 || @Int.0 == 9)",
        "!(@Int.0 > 0)",
        "!(!(@Int.0 > 0))",
        "@Int.0 * 2 + 1 > 0",
        "@Int.0 * (2 + 1) > 0",
        "if @Int.0 > 0 then { true } else { false }",
        "match @Int.0 { 0 -> true, _ -> false }",
    ]
    seen: dict[str, str] = {}
    for text in cases:
        expr = predicate(text)
        rendered = format_expr_canonical(expr)
        assert predicate(rendered) == expr, (
            f"{text!r} rendered {rendered!r}, which parses to something else"
        )
        assert rendered not in seen, (
            f"collision: {text!r} and {seen[rendered]!r} both render "
            f"{rendered!r}"
        )
        seen[rendered] = text


# =====================================================================
# (10) The KEY renders STRUCTURALLY, not canonically (PR #1238 round 2)
# =====================================================================

# `vera fmt` exists to CHOOSE between two spellings of one construct; the
# cell-family key exists to tell two constructs apart.  Two formatter sites
# make that choice over AST shapes the checker holds distinct, so the
# canonical rendering merged them — and the merged family made the #1233
# shadowing gate fire on a check-green program, dropping `main`.  The key
# now renders in STRUCTURAL mode, where both sites follow the AST.
_MERGE_PRELUDE = "private data Col { Red, Green }\n\n"
_CLAUSE_PRELUDE = "private data C { R }\n\n"

_STRUCTURE_PAIRS: tuple[tuple[str, str, str, str], ...] = (
    ("match-arm-block-wrap", _MERGE_PRELUDE,
     "match Red { Red -> { true }, Green -> false }",
     "match Red { Red -> true, Green -> false }"),
    ("match-arm-block-wrap-both", _MERGE_PRELUDE,
     "match Red { Red -> { true }, Green -> { false } }",
     "match Red { Red -> true, Green -> false }"),
    ("match-arm-double-block", _MERGE_PRELUDE,
     "match Red { Red -> { { true } }, Green -> false }",
     "match Red { Red -> { true }, Green -> false }"),
    # Found by READING every normalisation site rather than by probing: a
    # bare handler-clause body parses, and the clause wrapper supplied its
    # braces unconditionally, so `-> resume(())` and `-> { resume(()) }`
    # rendered alike.
    ("handler-clause-braces", _CLAUSE_PRELUDE,
     "match R { R -> handle[State<Int>](@Int = 0) "
     "{ put(@Int) -> resume(()) } in { true } }",
     "match R { R -> handle[State<Int>](@Int = 0) "
     "{ put(@Int) -> { resume(()) } } in { true } }"),
    # Controls: already distinct, and must stay so.
    ("if-branch-nested-block", "",
     "if @Int.0 > 0 then { true } else { false }",
     "if @Int.0 > 0 then { { true } } else { false }"),
    ("block-operand", "", "{ @Int.0 } > 0", "@Int.0 > 0"),
    ("lambda-body-block", "",
     "apply(fn(@Int -> @Bool) effects(pure) { { @Int.0 > 0 } }, @Int.0)",
     "apply(fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }, @Int.0)"),
    # The EQUALITY direction (PR #1238 review).  Every row above has two
    # different sides, so `key_eq == ast_eq` only ever asserted `False ==
    # False` — a key that separated everything, `id()` included, would pass
    # all of them.  These two sides are the SAME TEXT parsed twice, so they
    # are dataclass-equal and distinct objects with distinct spans: the
    # checker holds them EQUAL and the key must too.  Spans are
    # `compare=False` on `ast.Node`, which is exactly the property at risk
    # if a rendering ever reaches for one.
    ("same-text-simple", "", "@Int.0 > 0", "@Int.0 > 0"),
    ("same-text-arm-block", _MERGE_PRELUDE,
     "match Red { Red -> { true }, Green -> false }",
     "match Red { Red -> { true }, Green -> false }"),
    ("same-text-handler-clause", _CLAUSE_PRELUDE,
     "match R { R -> handle[State<Int>](@Int = 0) "
     "{ put(@Int) -> resume(()) } in { true } }",
     "match R { R -> handle[State<Int>](@Int = 0) "
     "{ put(@Int) -> resume(()) } in { true } }"),
)


def _probe_predicate(text: str, prelude: str = ""):
    program = parse_to_ast(f"{prelude}type Probe = {{ @Int | {text} }};\n")
    for decl in program.declarations:
        inner = getattr(decl, "decl", decl)
        if getattr(inner, "name", None) == "Probe":
            return inner.type_expr.predicate
    raise AssertionError(f"no Probe in {text!r}")


@pytest.mark.parametrize(
    ("label", "prelude", "left", "right"), _STRUCTURE_PAIRS,
    ids=[p[0] for p in _STRUCTURE_PAIRS],
)
def test_cell_key_discriminates_every_shape_the_checker_does(
    label: str, prelude: str, left: str, right: str,
) -> None:
    """The key agrees with `RefinedType` equality, shape for shape.

    `RefinedType` equality is dataclass equality over the predicate AST, and
    E125 enforces it across functions — so any pair the AST separates is a
    pair the checker separates, and a key that merges them gives two cells
    one host cell.  Asserting `key_eq == ast_eq` rather than `key_eq is
    False` is what makes this a differential: it fails equally if the key
    ever over-separates.

    Both directions are LIVE, which took saying: while every row had two
    different sides, the equality half was vacuous and a key returning a
    fresh `id()` per call would have passed the lot.  The `same-text-*`
    rows parse one text twice, so the two predicates are dataclass-equal
    objects with different spans and identities.
    """
    from vera.types import INT, RefinedType, structural_type_key

    left_expr = _probe_predicate(left, prelude)
    right_expr = _probe_predicate(right, prelude)
    ast_eq = left_expr == right_expr
    key_eq = (structural_type_key(RefinedType(INT, left_expr))
              == structural_type_key(RefinedType(INT, right_expr)))
    assert key_eq == ast_eq, (
        f"{label}: the checker holds these {'equal' if ast_eq else 'apart'} "
        f"and the cell key does not"
    )


@pytest.mark.parametrize(
    ("label", "prelude", "left", "right"), _STRUCTURE_PAIRS[-3:],
    ids=[p[0] for p in _STRUCTURE_PAIRS[-3:]],
)
def test_the_key_ignores_where_the_predicate_was_written(
    label: str, prelude: str, left: str, right: str,
) -> None:
    """Equality survives a change of SOURCE POSITION (PR #1238 review).

    The `same-text-*` rows above parse one text twice, which catches an
    identity or a counter leaking into the key — but not a SPAN, because
    two parses of the same source put the predicate at the same line and
    column.  Here the second parse is displaced by padding the prelude, so
    the two predicates are dataclass-equal with different spans.

    `ast.Node.span` is `compare=False`, so the checker holds them equal and
    two such refinement aliases are one cell.  A key that reached for a
    span would split that cell — and every alias-spelling collapse this
    file pins would come apart with it, silently, since a split family is
    only visible in a value.
    """
    from vera.types import INT, RefinedType, structural_type_key

    here = _probe_predicate(left, prelude)
    displaced = _probe_predicate(right, "-- padding\n\n\n" + prelude)
    assert here == displaced, f"{label}: the fixture itself is not equal"
    assert (getattr(here, "span", None) is None
            or here.span != displaced.span), (
        f"{label}: the two parses share a span, so this proves nothing"
    )
    assert (structural_type_key(RefinedType(INT, here))
            == structural_type_key(RefinedType(INT, displaced))), (
        f"{label}: the key moved with the predicate's source position"
    )


@pytest.mark.parametrize(
    ("label", "prelude", "left", "right"), _STRUCTURE_PAIRS,
    ids=[p[0] for p in _STRUCTURE_PAIRS],
)
def test_structural_rendering_still_reparses_to_its_own_ast(
    label: str, prelude: str, left: str, right: str,
) -> None:
    """Structural mode keeps the left-inverse property (PR #1238 round 2).

    The whole injectivity argument is `parse(format(e)) == e`, so a
    structural spelling that did not re-parse — or re-parsed to something
    else — would buy discrimination with the very property that justifies
    it.  Both members of every pair go out and come back unchanged.
    """
    from vera.formatter import format_expr_canonical

    for text in (left, right):
        expr = _probe_predicate(text, prelude)
        rendered = format_expr_canonical(expr, structural=True)
        assert _probe_predicate(rendered, prelude) == expr, (
            f"{label}: {text!r} -> {rendered!r} -> a different AST"
        )


@pytest.mark.parametrize(
    ("label", "prelude", "left", "right"), _STRUCTURE_PAIRS[:4],
    ids=[p[0] for p in _STRUCTURE_PAIRS[:4]],
)
def test_canonical_mode_is_untouched_by_the_structural_split(
    label: str, prelude: str, left: str, right: str,
) -> None:
    """`vera fmt` still CHOOSES — the split is key-only.

    Structural mode exists because the two jobs disagree; if it leaked into
    canonical output, `vera fmt` would stop normalising a redundant arm
    block and every corpus file holding one would fall out of canonical
    form.  The four shapes above are exactly the ones canonical mode is
    supposed to merge, so this asserts that it still does.
    """
    from vera.formatter import format_expr_canonical

    left_expr = _probe_predicate(left, prelude)
    right_expr = _probe_predicate(right, prelude)
    assert (format_expr_canonical(left_expr)
            == format_expr_canonical(right_expr)), (
        f"{label}: canonical form should still pick one spelling"
    )


_MERGE_GATE = _MERGE_PRELUDE + """
type A = { @Int | match Red { Red -> { @Int.0 > 0 }, Green -> false } };

type B = { @Int | match Red { Red -> @Int.0 > 0, Green -> false } };

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<A>](@A = 4) {
    get(@Unit) -> { resume(@A.0) },
    put(@A) -> { resume(()) }
  } in {
    let @B = handle[State<B>](@B = 1) {
      get(@Unit) -> { resume(@B.0) },
      put(@B) -> { resume(()) } with @B = get(()) * 10
    } in {
      put(7);
      get(())
    };
    @B.0 * 100 + get(())
  }
}
"""


def test_arm_block_spelling_alone_makes_two_cells(tmp_path: Path) -> None:
    """The end-to-end shape: two predicates differing ONLY in an arm's
    redundant block wrapper are two cells, and the program runs.

    Under the merged key both `State<A>` and `State<B>` were the same
    family, so the #1233 gate saw a same-family nest and refused `main`
    outright — check-green, verify-green, no exports.  With them distinct
    the inner clause's `with @B = get(()) * 10` reads the OUTER `A` cell per
    §7.5.2 (4), stores 40, and `main` returns `40 * 100 + 4`.  4004 is
    therefore reachable only when the two cells are separate AND the
    outward read lands on the right one.
    """
    result = _compile_ok(_MERGE_GATE, tmp_path)
    assert len(_families(result.wat)) == 8, sorted(_families(result.wat))
    assert execute(result).value == 4004
