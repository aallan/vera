"""#1436 — a constructor name is resolved in the namespace that uses it.

Code generation projects `_adt_layouts` into by-name maps (`ctor_layouts`,
`_ctor_to_adt`) that the wasm layer consults, and that projection was built
across EVERY namespace a compilation absorbs.  So a declaration in one
namespace answered for another's: an entry-file `private data Mine { Pad(Bool),
Sq(Bool) }` took the `Sq` slot from an imported `data Shape { Sq(Int),
Circ(Int) }`, and the MODULE's own bodies were then compiled against the
entry's tag.

The shadowing declaration need never be used, and `vera check` and
`vera verify` are both clean on every program here — which is what makes it a
silent wrong value rather than a diagnostic.

#1414 gave the wasm layer a per-ADT view and routed the render, equality and
nullary-construction sites through it; that fixes collisions WITHIN one
namespace.  This is the cross-namespace half: the ADT names differ (`Shape`
vs `Mine`) and only the constructor name collides, so a per-ADT view does not
see it.  The projection is now built per namespace, applying infrastructure,
then foreign declarations, then the compiling namespace's own — so a local
declaration shadows an imported constructor (§8.5.2) without the module's own
bodies ever seeing the entry's.
"""
from __future__ import annotations

from pathlib import Path
from typing import ClassVar

import pytest

from vera.codegen.api import CompileResult

from tests.module_fixture_helpers import (
    build_multi_module,
    build_multi_module_past_check,
    module_value,
)

_LIB = """\
module s3lib;

public data Shape {
  Sq(Int),
  Circ(Int)
}

public fn mk_sq(@Int -> @Shape)
  requires(true)
  ensures(true)
  effects(pure)
{
  Sq(@Int.0)
}

public fn mk_circ(@Int -> @Shape)
  requires(true)
  ensures(true)
  effects(pure)
{
  Circ(@Int.0)
}

public fn area_tag(@Shape -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Shape.0 {
    Sq(@Int) -> 100 + @Int.0,
    Circ(@Int) -> 200 + @Int.0
  }
}
"""

#: The entry file, with the shadowing declaration spliced in or left out.
#: `Mine` is never used: its mere presence is the defect.
_MAIN = """\
import s3lib;

%(shadow)spublic fn shown(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(s3lib::mk_sq(7))
}

public fn tag_of_circ(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  s3lib::area_tag(s3lib::mk_circ(7))
}

public fn cross_eq(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if s3lib::mk_sq(7) == s3lib::mk_circ(7) then { 1 } else { 0 }
}

public fn cross_hash(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if hash(s3lib::mk_sq(7)) == hash(s3lib::mk_circ(7)) then { 1 } else { 0 }
}
"""

_SHADOW = "private data Mine {\n  Pad(Bool),\n  Sq(Bool)\n}\n\n"

#: What each function must answer.  Measured on the control at every
#: revision, and measured WRONG under the shadow before this fix:
#: `Circ(7)` / `107` / `1` / `1`.
_EXPECTED = {
    "shown": "Sq(7)",
    "tag_of_circ": 207,
    "cross_eq": 0,
    "cross_hash": 0,
}


def _build(tmp_path: Path, shadow: bool):
    files = {
        "s3lib.vera": _LIB,
        "main.vera": _MAIN % {"shadow": _SHADOW if shadow else ""},
    }
    return build_multi_module(tmp_path, files)


class TestImportedConstructorShadow:
    """The reviewer's four faces of #1436, each against its own control."""

    @pytest.mark.parametrize("fn", sorted(_EXPECTED))
    def test_the_shadow_does_not_change_the_answer(
        self, fn: str, tmp_path: Path,
    ) -> None:
        verify_errors, result, cg_errors = _build(tmp_path, shadow=True)
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        assert module_value(result, fn) == ("ok", _EXPECTED[fn])

    @pytest.mark.parametrize("fn", sorted(_EXPECTED))
    def test_the_control_answers_the_same(
        self, fn: str, tmp_path: Path,
    ) -> None:
        """Green at every revision, so the cells above cannot be satisfied by
        breaking the module for everyone."""
        verify_errors, result, cg_errors = _build(tmp_path, shadow=False)
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        assert module_value(result, fn) == ("ok", _EXPECTED[fn])

    def test_check_and_verify_are_clean_under_the_shadow(
        self, tmp_path: Path,
    ) -> None:
        """The property that made this silent: nothing refuses the program.

        `build_multi_module` raises on a check error, so reaching the
        assertion is the check half; the verify half is asserted directly.
        """
        verify_errors, _result, _cg = _build(tmp_path, shadow=True)
        assert not verify_errors, verify_errors


class TestThreeNamespaceVariant:
    """A third namespace must be neither broken nor needed.

    The collision is entry-vs-`alib`; `blib` shares no constructor name and
    is the control that the scoping did not simply disable everything.
    """

    _ALIB = _LIB.replace("s3lib", "alib")
    _BLIB = """\
module blib;

public data Box {
  Tri(Bool),
  Other(Bool)
}

public fn mk(@Bool -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tri(@Bool.0)
}

public fn which(@Box -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Box.0 {
    Tri(@Bool) -> 1,
    Other(@Bool) -> 2
  }
}
"""
    _MAIN3 = """\
import alib;
import blib;

%(shadow)spublic fn a_tag(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  alib::area_tag(alib::mk_circ(7))
}

public fn b_which(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  blib::which(blib::mk(true))
}
"""

    @pytest.mark.parametrize("shadow", [True, False])
    @pytest.mark.parametrize("fn,expected", [("a_tag", 207), ("b_which", 1)])
    def test_each_namespace_answers_for_itself(
        self, shadow: bool, fn: str, expected: int, tmp_path: Path,
    ) -> None:
        files = {
            "alib.vera": self._ALIB,
            "blib.vera": self._BLIB,
            "main.vera": self._MAIN3 % {"shadow": _SHADOW if shadow else ""},
        }
        verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        assert module_value(result, fn) == ("ok", expected)


class TestDifferingFieldTypes:
    """The same collision with incompatible field types, which degraded from
    a wrong label to a type-confused read of the string pool.

    Base rendered `Circ(Sq()Cir)` — the integer `7` read as a `String`
    (ptr, len) pair — on a check-clean, verify-clean program.
    """

    _LIB_STR = """\
module s4lib;

public data Shape {
  Sq(Int),
  Circ(String)
}

public fn mk_sq(@Int -> @Shape)
  requires(true)
  ensures(true)
  effects(pure)
{
  Sq(@Int.0)
}
"""

    @pytest.mark.parametrize("shadow", [True, False])
    def test_the_field_is_read_at_its_own_width(
        self, shadow: bool, tmp_path: Path,
    ) -> None:
        main = """\
import s4lib;

%(shadow)spublic fn shown(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(s4lib::mk_sq(7))
}
""" % {"shadow": _SHADOW if shadow else ""}
        verify_errors, result, cg_errors = build_multi_module(
            tmp_path, {"s4lib.vera": self._LIB_STR, "main.vera": main})
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        assert module_value(result, "shown") == ("ok", "Sq(7)")


class TestEntryDeclarationIsInvisibleToModules:
    """#1454 review F1 — a module's body must not see the entry's ADTs.

    Classifying an entry-file declaration as `foreign` when a module
    compiles put it in the projection one class before `own`, so it still
    shadowed the PRELUDE's constructor inside a module's body.  Measured:
    an entry `private data Mine { Pad(Bool), Some(Bool) }` — never used —
    dropped a module's `show(Some(x))` behind an `[E620]`, where the
    control renders `Some(42)`.

    A module cannot NAME the entry's declarations, so they are excluded
    outright rather than demoted.
    """

    _LIB = """\
module plib;

public fn wrap(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Some(@Int.0))
}
"""
    _MAIN = """\
import plib;

%(shadow)spublic fn go(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  plib::wrap(42)
}
"""

    @pytest.mark.parametrize("shadow", [True, False])
    def test_a_prelude_ctor_keeps_its_meaning_inside_a_module(
        self, shadow: bool, tmp_path: Path,
    ) -> None:
        sh = "private data Mine {\n  Pad(Bool),\n  Some(Bool)\n}\n\n"
        files = {
            "plib.vera": self._LIB,
            "main.vera": self._MAIN % {"shadow": sh if shadow else ""},
        }
        verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        assert module_value(result, "go") == ("ok", "Some(42)")


class TestGenericAxis:
    """#1454 review F2 — the type-parameter index table is scoped too.

    `_ctor_adt_tp_indices` is keyed by bare constructor name as well, and
    reached `WasmContext` unscoped while the layouts were already per
    namespace.  A generic entry declaration therefore isolated itself to
    that map: a module's own `Wrap(3) == Wrap(3)` came back FALSE under an
    unused entry `data Mine<T> { Pad(Bool), Wrap(T, Bool) }`, with `show`
    and `hash` dropped — check-clean and verify-clean throughout.
    """

    _GLIB = """\
module glib;

public data Box<T> {
  Wrap(T),
  Empty
}

public fn same(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if Wrap(@Int.0) == Wrap(@Int.0) then { 1 } else { 0 }
}

public fn shown(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Wrap(@Int.0))
}
"""
    _MAIN = """\
import glib;

%(shadow)spublic fn eq_(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  glib::same(3)
}

public fn sh_(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  glib::shown(3)
}
"""

    #: A USER generic shadow, and the prelude's own generic constructor.
    _SHADOWS: ClassVar[dict[str, str]] = {
        "user_generic": "private data Mine<T> {\n  Pad(Bool),\n  Wrap(T, Bool)\n}\n\n",
        "prelude_Some": "private data Mine<T> {\n  Pad(Bool),\n  Some(T, Bool)\n}\n\n",
        # The DISCRIMINATOR (#1454 review R2): a NON-generic entry shadow of
        # a generic module constructor.  It isolates the defect to the
        # type-parameter index map — the layouts scoping alone does not fix
        # it, and reverting both tp-index threadings drops the module's
        # functions with an [E620] while the generic shadows above stay
        # green.
        "nongeneric_discriminator":
            "private data Mine {\n  Pad(Bool),\n  Wrap(Bool)\n}\n\n",
        "none": "",
    }

    @pytest.mark.parametrize("shadow", sorted(_SHADOWS))
    @pytest.mark.parametrize("fn,expected", [("eq_", 1), ("sh_", "Wrap(3)")])
    def test_a_generic_module_adt_keeps_its_type_argument(
        self, shadow: str, fn: str, expected: object, tmp_path: Path,
    ) -> None:
        files = {
            "glib.vera": self._GLIB,
            "main.vera": self._MAIN % {"shadow": self._SHADOWS[shadow]},
        }
        verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        assert module_value(result, fn) == ("ok", expected)


# ---------------------------------------------------------------------------
# The CLASS instrument: the owner-collision matrix, and the scan that keeps
# the per-owner registry the only path a constructor name is resolved by.
# ---------------------------------------------------------------------------

#: One module source per CARRIER — the kind of declaration the colliding name
#: belongs to.  Each is written so that every position below names the
#: carrier's constructor inside the MODULE's own body: a position whose
#: program does not name the colliding constructor would be a cell whose
#: premise cannot fail.
#:
#: * ``plain`` — the module's own non-generic ADT, the shape #1436 was filed
#:   on;
#: * ``generic`` — the module's own generic ADT, which reaches the wasm layer
#:   through the type-parameter index table as well as through the layouts;
#: * ``prelude`` — the prelude's ``Option``, which no namespace declares, so
#:   the collision is with infrastructure rather than with another module.
_CARRIER_LIB: dict[str, str] = {
    "plain": """\
module mlib;

public data Shape {
  Sq(Int),
  Circ(Int)
}

public data Holder {
  H(Shape)
}

public fn mk_first(@Int -> @Shape)
  requires(true)
  ensures(@Shape.result == Sq(@Int.0))
  effects(pure)
{
  Sq(@Int.0)
}

public fn mk_second(@Int -> @Shape)
  requires(true)
  ensures(@Shape.result == Circ(@Int.0))
  effects(pure)
{
  Circ(@Int.0)
}

public fn arm(@Shape -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Shape.0 {
    Sq(@Int) -> 100 + @Int.0,
    Circ(@Int) -> 200 + @Int.0
  }
}

public fn nested(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(Sq(@Int.0)) {
    Some(Sq(@Int)) -> 300 + @Int.0,
    Some(Circ(@Int)) -> 400 + @Int.0,
    None -> 0
  }
}

public fn stated(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Shape>](@Shape = Sq(@Int.0)) {
    get(@Unit) -> { resume(@Shape.0) },
    put(@Shape) -> { resume(()) }
  } in {
    arm(get(()))
  }
}

public fn fielded(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match H(Sq(@Int.0)) {
    H(@Shape) -> arm(@Shape.0)
  }
}

public fn rendered(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Sq(@Int.0))
}

public fn tagged(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if Sq(@Int.0) == Circ(@Int.0) then {
    0
  } else {
    if Sq(@Int.0) == Sq(@Int.0) then { 1 } else { 2 }
  }
}
public forall<T> fn gid(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn via_generic(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  arm(gid(Sq(@Int.0)))
}

""",
    "generic": """\
module mlib;

public data Box<T> {
  Wrap(T),
  Empty
}

public data Holder {
  H(Box<Int>)
}

public fn mk_first(@Int -> @Box<Int>)
  requires(true)
  ensures(@Box<Int>.result == Wrap(@Int.0))
  effects(pure)
{
  Wrap(@Int.0)
}

public fn mk_second(@Int -> @Box<Int>)
  requires(true)
  ensures(@Box<Int>.result == Empty)
  effects(pure)
{
  Empty
}

public fn arm(@Box<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Box<Int>.0 {
    Wrap(@Int) -> 100 + @Int.0,
    Empty -> 200
  }
}

public fn nested(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(Wrap(@Int.0)) {
    Some(Wrap(@Int)) -> 300 + @Int.0,
    Some(Empty) -> 400,
    None -> 0
  }
}

public fn stated(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Box<Int>>](@Box<Int> = Wrap(@Int.0)) {
    get(@Unit) -> { resume(@Box<Int>.0) },
    put(@Box<Int>) -> { resume(()) }
  } in {
    arm(get(()))
  }
}

public fn fielded(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match H(Wrap(@Int.0)) {
    H(@Box<Int>) -> arm(@Box<Int>.0)
  }
}

public fn rendered(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Wrap(@Int.0))
}

public fn tagged(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if Wrap(@Int.0) == Empty then {
    0
  } else {
    if Wrap(@Int.0) == Wrap(@Int.0) then { 1 } else { 2 }
  }
}
public forall<T> fn gid(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn via_generic(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  arm(gid(Wrap(@Int.0)))
}

""",
    "prelude": """\
module mlib;

public data Holder {
  H(Option<Int>)
}

public fn mk_first(@Int -> @Option<Int>)
  requires(true)
  ensures(@Option<Int>.result == Some(@Int.0))
  effects(pure)
{
  Some(@Int.0)
}

public fn mk_second(@Int -> @Option<Int>)
  requires(true)
  ensures(@Option<Int>.result == None)
  effects(pure)
{
  None
}

public fn arm(@Option<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> 100 + @Int.0,
    None -> 200
  }
}

public fn nested(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(Some(@Int.0)) {
    Some(Some(@Int)) -> 300 + @Int.0,
    Some(None) -> 400,
    None -> 0
  }
}

public fn stated(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(@Int.0)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    arm(get(()))
  }
}

public fn fielded(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match H(Some(@Int.0)) {
    H(@Option<Int>) -> arm(@Option<Int>.0)
  }
}

public fn rendered(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Some(@Int.0))
}

public fn tagged(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if Some(@Int.0) == None then {
    0
  } else {
    if Some(@Int.0) == Some(@Int.0) then { 1 } else { 2 }
  }
}
public forall<T> fn gid(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn via_generic(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  arm(gid(Some(@Int.0)))
}

""",
}

#: The entry file.  Every export but ``call_result`` drives the MODULE, so the
#: cell observes what the module's own body compiled to; ``call_result`` binds
#: the module's value in the ENTRY's namespace and hands it back, so the two
#: namespaces meet on one value.
_MATRIX_MAIN = """\
import mlib;
%(imports)s
%(shadow)spublic fn construction(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  mlib::arm(mlib::mk_first(7))
}

public fn match_arm(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  mlib::arm(mlib::mk_second(7))
}

public fn nested_pattern(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  mlib::nested(7)
}

public fn call_result(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let %(ty)s = mlib::mk_first(7);
  mlib::arm(%(ty)s.0)
}

public fn state_cell(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  mlib::stated(7)
}

public fn adt_field(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  mlib::fielded(7)
}

public fn data_segment(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  mlib::rendered(7)
}

public fn tag_eq(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  mlib::tagged(7)
}

public fn generic_call(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  mlib::via_generic(7)
}
"""

#: The entry-side `match` on a value the module returned, appended to the
#: entry when the two namespaces' readings are asserted together.
_ENTRY_MATCH_FN = """
public fn entry_match(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mlib::mk_first(7) {
%(arms)s
  }
}
"""

#: Per carrier: the constructor name the collision is on, the carrier's type
#: as an entry-file slot, and the arms of the entry-side match.
_CARRIER_CTOR = {"plain": "Sq", "generic": "Wrap", "prelude": "Some"}
_CARRIER_TYPE = {
    "plain": "@Shape", "generic": "@Box<Int>", "prelude": "@Option<Int>",
}
_CARRIER_ARMS = {
    "plain": "    Sq(@Int) -> 500 + @Int.0,\n    Circ(@Int) -> 600",
    "generic": "    Wrap(@Int) -> 500 + @Int.0,\n    Empty -> 600",
    "prelude": "    Some(@Int) -> 500 + @Int.0,\n    None -> 600",
}

#: The declarations that take the carrier's constructor name away from it,
#: by the OWNER of the taking declaration — the second dimension.
#:
#: ``entry_differing`` gives the name a different arity, a different field
#: type AND a different tag position, so a projection that lets the wrong
#: declaration answer is observable in every position.  ``entry_identical``
#: gives it the module's own shape — not a coincidence-agreement cell, as
#: it turns out: identity is the ADT's and not the shape's, so at the base
#: revision the module's own `show(Sq(x))` is DROPPED naming the entry's
#: `Other` even though the two layouts are identical.  ``sibling_module``
#: and ``transitive_module`` move the taking declaration into a module the
#: compiling namespace never imports: the same mechanism, reached from the
#: other side.
#:
#: The two module-owned shadows exist for the ``prelude`` carrier only, and
#: the absence is a property of the language rather than a gap: two MODULES
#: declaring one constructor name are refused at compile before any
#: projection is built, which
#: :meth:`TestOwnerCollisionMatrix.test_two_modules_sharing_a_name_are_refused`
#: asserts.  Only a name the PRELUDE owns can be contended from a module.
_SHADOW_MODULE = """\
module xlib;

public data Mine {
  Pad(Bool),
  Some(Bool)
}

public fn xping(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""

#: A relay, so the shadowing module is reached only THROUGH another one and
#: the entry never imports it.
_RELAY_MODULE = """\
module ylib;

import xlib;

public fn yping(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  xlib::xping(@Int.0)
}
"""

#: An entry export that calls the extra module, so the shadow is part of the
#: build rather than an unreachable file.
_KEEPALIVE = """
public fn keepalive(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  %s
}
"""

_ENTRY_SHADOWS = {
    "entry_differing": "Mine",
    "entry_identical": "Other",
}
_MODULE_SHADOWS = ("sibling_module", "transitive_module")

_SHADOWS_BY_CARRIER: dict[str, tuple[str, ...]] = {
    "plain": ("none", "entry_differing", "entry_identical"),
    "generic": ("none", "entry_differing", "entry_identical"),
    "prelude": (
        "none", "entry_differing", "entry_identical",
        "sibling_module", "transitive_module",
    ),
}

#: The entry-file declaration each entry-owned shadow splices in.
_ENTRY_SHADOW_DECL: dict[str, dict[str, str]] = {
    "plain": {
        "entry_differing":
            "private data Mine {\n  Pad(Bool),\n  Sq(Bool)\n}\n\n",
        "entry_identical":
            "private data Other {\n  Sq(Int),\n  Circ(Int)\n}\n\n",
    },
    "generic": {
        "entry_differing":
            "private data Mine {\n  Pad(Bool),\n  Wrap(Bool)\n}\n\n",
        "entry_identical":
            "private data Other<T> {\n  Wrap(T),\n  Empty\n}\n\n",
    },
    "prelude": {
        "entry_differing":
            "private data Mine {\n  Pad(Bool),\n  Some(Bool)\n}\n\n",
        "entry_identical":
            "private data Other {\n  None,\n  Some(Int)\n}\n\n",
    },
}


#: Which module function each position's answer is produced by — the premise
#: assertion below reads these blocks and checks each one really names the
#: colliding constructor.
_POSITION_MODULE_FN = {
    "construction": "mk_first",
    "match_arm": "arm",
    "nested_pattern": "nested",
    "call_result": "mk_first",
    "state_cell": "stated",
    "adt_field": "fielded",
    "data_segment": "rendered",
    "tag_eq": "tagged",
    # The ninth path a constructor name is resolved through: the type
    # argument DISCOVERY infers for a generic call from a constructor
    # argument, which decides the clone's name on both sides.
    "generic_call": "via_generic",
}

#: What each position must answer — the value the SOURCE names.  The module's
#: second constructor carries a field for ``plain`` (`Circ(Int)`) and is
#: nullary for the other two (`Empty` / `None`), which is the only reason
#: ``match_arm`` differs between carriers.
_MATRIX_EXPECTED: dict[str, dict[str, object]] = {
    "plain": {
        "construction": 107,
        "match_arm": 207,
        "nested_pattern": 307,
        "call_result": 107,
        "state_cell": 107,
        "adt_field": 107,
        "data_segment": "Sq(7)",
        "tag_eq": 1,
        "generic_call": 107,
    },
    "generic": {
        "construction": 107,
        "match_arm": 200,
        "nested_pattern": 307,
        "call_result": 107,
        "state_cell": 107,
        "adt_field": 107,
        "data_segment": "Wrap(7)",
        "tag_eq": 1,
        "generic_call": 107,
    },
    "prelude": {
        "construction": 107,
        "match_arm": 200,
        "nested_pattern": 307,
        "call_result": 107,
        "state_cell": 107,
        "adt_field": 107,
        "data_segment": "Some(7)",
        "tag_eq": 1,
        "generic_call": 107,
    },
}


def _matrix_files(carrier: str, shadow: str) -> dict[str, str]:
    """The program for one (carrier, shadow) pair.

    ``mlib`` is the module under observation in every one: it declares (or,
    for the ``prelude`` carrier, uses) the contended name and never imports
    the shadowing declaration, whoever owns it.
    """
    files = {"mlib.vera": _CARRIER_LIB[carrier]}
    decl = _ENTRY_SHADOW_DECL[carrier].get(shadow, "")
    imports = ""
    keepalive = ""
    if shadow == "sibling_module":
        files["xlib.vera"] = _SHADOW_MODULE
        imports = "import xlib;\n"
        keepalive = _KEEPALIVE % "xlib::xping(1)"
    elif shadow == "transitive_module":
        files["xlib.vera"] = _SHADOW_MODULE
        files["ylib.vera"] = _RELAY_MODULE
        imports = "import ylib;\n"
        keepalive = _KEEPALIVE % "ylib::yping(1)"
    files["main.vera"] = (
        _MATRIX_MAIN % {
            "imports": imports,
            "shadow": decl,
            "ty": _CARRIER_TYPE[carrier],
        }
    ) + keepalive
    return files


@pytest.fixture(scope="module")
def owner_collision_builds(
    tmp_path_factory: pytest.TempPathFactory,
) -> dict[tuple[str, str], tuple[
    list[tuple[str, str]], CompileResult, list[tuple[str, str]],
]]:
    """One build per (carrier, shadow): every cell reads one of these."""
    built = {}
    for carrier in _CARRIER_LIB:
        for shadow in _SHADOWS_BY_CARRIER[carrier]:
            built[(carrier, shadow)] = build_multi_module(
                tmp_path_factory.mktemp(f"{carrier}_{shadow}"),
                _matrix_files(carrier, shadow),
            )
    return built


class TestOwnerCollisionMatrix:
    """The class instrument for #1436: an owner collision on every path a
    constructor name is resolved through.

    The class is *a constructor name means the declaration of the namespace
    that uses it*, and it spans three dimensions, enumerated from what the
    resolution is built out of rather than from the reported instance:

    * **carrier** — whose declaration the name belongs to: a module's own
      non-generic ADT, a module's own generic ADT (which adds the
      type-parameter index table to the two layout maps), or the prelude's
      ``Option``, which no namespace declares;
    * **shadow** — what the entry file does to the name: nothing (the
      control), declare it with a different shape and tag position, or
      declare it with the module's own shape, where a flat projection agreed
      by coincidence;
    * **position** — the path that resolves it: construction, a match arm, a
      nested constructor pattern, a value crossing the namespace boundary in
      a binder, a ``State`` cell, a field of another ADT, the data segment
      ``show`` renders the constructor name from, and the tag ``==`` compares.

    The cells of one column share a single build — nine positions read nine
    exports of one program — so each position cell asserts its own VALUE and
    the build's silence is asserted once beside them, in
    :meth:`test_the_build_itself_is_clean`.  That silence is half of what is
    under test, because the defect was silent in `vera verify`, in codegen's
    error stream, and (where it dropped a function) in both.  The shadow declarations are never used by the
    program (except in
    :class:`TestBothNamespacesReadTheirOwnDeclaration`), so a cell cannot
    pass by the shadow being unreachable.
    """

    @pytest.mark.parametrize("position", sorted(_POSITION_MODULE_FN))
    @pytest.mark.parametrize(
        "carrier,shadow",
        [(c, sh) for c in sorted(_CARRIER_LIB)
         for sh in _SHADOWS_BY_CARRIER[c]],
    )
    def test_the_module_keeps_its_own_reading(
        self,
        carrier: str,
        shadow: str,
        position: str,
        owner_collision_builds: dict[tuple[str, str], tuple[
            list[tuple[str, str]], CompileResult, list[tuple[str, str]],
        ]],
    ) -> None:
        _verify_errors, result, _cg_errors = owner_collision_builds[
            (carrier, shadow)]
        assert module_value(result, position) == (
            "ok", _MATRIX_EXPECTED[carrier][position])

    @pytest.mark.parametrize(
        "carrier,shadow",
        [(c, sh) for c in sorted(_CARRIER_LIB)
         for sh in _SHADOWS_BY_CARRIER[c]],
    )
    def test_the_build_itself_is_clean(
        self,
        carrier: str,
        shadow: str,
        owner_collision_builds: dict[tuple[str, str], tuple[
            list[tuple[str, str]], CompileResult, list[tuple[str, str]],
        ]],
    ) -> None:
        """The silence around each column, asserted once per BUILD.

        The nine position cells share one build and read their own export
        from it, so a property of the build belongs here rather than in each
        of them — otherwise one dropped function reds all nine and the
        column's failure says nothing about which position is wrong.

        A SKIP is the other face of this defect and lands in neither error
        stream: codegen drops the function and records a note, so a cell
        that asserted only values would be green for every export that
        survived and silent about the one that did not.
        """
        verify_errors, result, cg_errors = owner_collision_builds[
            (carrier, shadow)]
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        dropped = [
            (d.error_code, d.description) for d in result.diagnostics
            if d.error_code in {"E602", "E604", "E620"}
        ]
        assert not dropped, dropped

    @pytest.mark.parametrize("carrier", sorted(_CARRIER_LIB))
    def test_each_shadow_really_takes_the_name(self, carrier: str) -> None:
        """The cells' LABEL, asserted rather than asserted-about.

        A shadow that does not spell the carrier's constructor makes every
        cell in its column vacuous — green because nothing contends, not
        because the projection is scoped.  The control column is asserted to
        declare nothing, for the same reason: a control that quietly
        declared something would not be one.
        """
        ctor = _CARRIER_CTOR[carrier]
        for shadow in _SHADOWS_BY_CARRIER[carrier]:
            files = _matrix_files(carrier, shadow)
            taking = files["main.vera"].split("public fn construction")[0]
            if "xlib.vera" in files:
                taking = files["xlib.vera"]
            if shadow == "none":
                assert "data " not in taking, (
                    f"{carrier}/none is not a control: {taking!r}")
                continue
            assert f"{ctor}(" in taking, (
                f"{carrier}/{shadow} never declares {ctor}: {taking!r}")

    @pytest.mark.parametrize("carrier", sorted(_CARRIER_LIB))
    def test_the_shadowed_module_never_imports_the_shadow(
        self, carrier: str,
    ) -> None:
        """`mlib` is the namespace under observation, and it must be able to
        reach NONE of the shadowing declarations — otherwise the cell is
        about §8.5.2 shadowing, which is legal, rather than about a namespace
        answering for one that never imported it.
        """
        for shadow in _SHADOWS_BY_CARRIER[carrier]:
            assert "import" not in _matrix_files(carrier, shadow)["mlib.vera"]

    @pytest.mark.parametrize("position", sorted(_POSITION_MODULE_FN))
    @pytest.mark.parametrize("carrier", sorted(_CARRIER_LIB))
    def test_each_position_really_names_the_constructor(
        self, carrier: str, position: str,
    ) -> None:
        """The other half of the label: the module body this position's
        answer comes from must NAME the contended constructor, or the cell
        measures a program the collision cannot reach.
        """
        fn = _POSITION_MODULE_FN[position]
        blocks = _CARRIER_LIB[carrier].split("\npublic fn ")
        body = next((b for b in blocks if b.startswith(f"{fn}(")), None)
        assert body is not None, f"{carrier} declares no {fn}"
        assert _CARRIER_CTOR[carrier] in body, (
            f"{carrier}.{fn} never names {_CARRIER_CTOR[carrier]}")

    def test_two_modules_sharing_a_name_are_refused(
        self, tmp_path: Path,
    ) -> None:
        """Why the module-owned shadows exist for the prelude carrier only.

        A product that is absent from a matrix has to say why, or it reads as
        an oversight.  Two MODULES declaring one constructor name are refused
        before any projection is built, so the pair cannot reach the
        mechanism this PR repairs — which is also why a module can only
        contend for a name the PRELUDE owns.
        """
        files = _matrix_files("plain", "none")
        files["xlib.vera"] = _SHADOW_MODULE.replace(
            "Some(Bool)", "Sq(Bool)")
        files["main.vera"] = files["main.vera"].replace(
            "import mlib;", "import mlib;\nimport xlib;") + (
                _KEEPALIVE % "xlib::xping(1)")
        check_errors, _result, _cg_errors = build_multi_module_past_check(
            tmp_path, files)
        assert any(
            code == "E157" and "more than one import" in desc
            for code, desc in check_errors
        ), check_errors


class TestBothNamespacesReadTheirOwnDeclaration:
    """The three layers agree, asserted in ONE program (#1436).

    The matrix above keeps the entry's declaration unused, which is the
    reported instance.  Here the entry USES the name it took, so the
    checker's owner, the verifier's owner and codegen's tag are all
    observable at once on the same source:

    * the CHECKER resolves the entry's ``Sq`` to the ENTRY's ADT — it says so
      in E314, naming that type against a scrutinee of the module's;
    * the VERIFIER resolves the module's ``Sq`` to the MODULE's ADT — the
      module's ``ensures(@Shape.result == Sq(@Int.0))`` is discharged with no
      diagnostic, on the same program;
    * CODEGEN agrees with both — the module's exports still answer the
      module's values while the entry's declaration owns the name in the
      entry.

    The E314 is the instrument, not the complaint: the entry's own reading is
    what makes the refusal correct, and reading the ADT it names is how this
    test asks the checker whose declaration the name belongs to.
    """

    @pytest.mark.parametrize(
        "shadow", ["entry_differing", "entry_identical"])
    @pytest.mark.parametrize("carrier", sorted(_CARRIER_LIB))
    def test_the_checker_names_the_entrys_adt_while_codegen_keeps_the_modules(
        self, carrier: str, shadow: str, tmp_path: Path,
    ) -> None:
        files = _matrix_files(carrier, shadow)
        files["main.vera"] += _ENTRY_MATCH_FN % {
            "arms": _CARRIER_ARMS[carrier]}
        check_errors, result, cg_errors = build_multi_module_past_check(
            tmp_path, files)
        owner = _ENTRY_SHADOWS[shadow]
        assert any(
            code == "E314" and f"constructor of {owner}" in desc
            for code, desc in check_errors
        ), check_errors
        # ... and the module's own bodies are untouched by it.
        for position in ("construction", "data_segment", "tag_eq"):
            assert module_value(result, position) == (
                "ok", _MATRIX_EXPECTED[carrier][position]), (
                    position, cg_errors)

    @pytest.mark.parametrize("carrier", sorted(_CARRIER_LIB))
    def test_the_control_accepts_the_same_match(
        self, carrier: str, tmp_path: Path,
    ) -> None:
        """The premise for the cells above: with no shadow the entry-side
        match is accepted and answers, so the refusal they assert is the
        entry's declaration talking and not the fixture being malformed.
        """
        files = _matrix_files(carrier, "none")
        files["main.vera"] += _ENTRY_MATCH_FN % {
            "arms": _CARRIER_ARMS[carrier]}
        verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        assert module_value(result, "entry_match") == ("ok", 507)


#: Every by-name constructor lookup left in the compiler, counted per
#: (file, function, table).  Frozen deliberately: a NEW bare lookup fails
#: the scan whatever comment it carries, which a marker rail cannot do,
#: and a vanished one fails too, so a row cannot outlive the site it
#: describes.  Adding a row is the review-visible act of admitting a
#: lookup that cannot name an owner; the reasons live at the sites, in
#: their `# ctor-owner-exempt:` markers.
_BY_NAME_INVENTORY: dict[tuple[str, str, str], int] = {
    ("vera/codegen/core.py", "CodeGenerator.__init__", "_ctor_adt_tp_indices"): 1,
    ("vera/codegen/modules.py", "CrossModuleMixin._register_modules", "_ctor_adt_tp_indices"): 3,
    ("vera/codegen/registration.py", "RegistrationMixin._register_builtin_adts", "_ctor_adt_tp_indices"): 4,
    ("vera/codegen/registration.py", "RegistrationMixin._register_data", "_ctor_adt_tp_indices"): 2,
    ("vera/smt.py", "SmtContext.__init__", "_ctor_to_adt"): 1,
    ("vera/smt.py", "SmtContext._ctor_instantiation_from_args", "_ctor_to_adt"): 1,
    ("vera/smt.py", "SmtContext._find_sort_for_ctor", "_ctor_to_adt"): 1,
    ("vera/smt.py", "SmtContext._translate_ctor_call", "_ctor_to_adt"): 1,
    ("vera/smt.py", "SmtContext.register_adt", "_ctor_to_adt"): 1,
    ("vera/wasm/calls.py", "CallsMixin._translate_call", "_ctor_layouts"): 1,
    ("vera/wasm/calls_handlers.py", "CallsHandlersMixin._recover_ctor_ptype", "_ctor_adt_tp_indices"): 1,
    ("vera/wasm/context.py", "WasmContext.__init__", "_ctor_adt_tp_indices"): 1,
    ("vera/wasm/context.py", "WasmContext.__init__", "_ctor_layouts"): 1,
    ("vera/wasm/context.py", "WasmContext.__init__", "_ctor_to_adt"): 1,
    ("vera/wasm/context.py", "WasmContext._owned_ctor_layout", "_ctor_layouts"): 1,
    ("vera/wasm/data.py", "DataMixin._collect_nested_tag_checks", "_ctor_layouts"): 1,
    ("vera/wasm/data.py", "DataMixin._ctor_field_targets_byte", "_ctor_adt_tp_indices"): 1,
    ("vera/wasm/data.py", "DataMixin._ctor_field_tp_index", "_ctor_adt_tp_indices"): 1,
    ("vera/wasm/data.py", "DataMixin._extract_constructor_fields", "_ctor_layouts"): 1,
    ("vera/wasm/data.py", "DataMixin._resolve_nested_scrutinee_type", "_ctor_adt_tp_indices"): 1,
    ("vera/wasm/data.py", "DataMixin._resolve_nested_scrutinee_type", "_ctor_layouts"): 1,
    ("vera/wasm/data.py", "DataMixin._setup_match_arm_env", "_ctor_layouts"): 1,
    ("vera/wasm/data.py", "DataMixin._translate_constructor_call", "_ctor_layouts"): 1,
    ("vera/wasm/data.py", "DataMixin._translate_match_condition", "_ctor_layouts"): 1,
    ("vera/wasm/inference.py", "InferenceMixin._ctor_to_adt_name", "_ctor_to_adt"): 1,
    ("vera/wasm/inference.py", "InferenceMixin._get_arg_type_info_wasm", "_ctor_adt_tp_indices"): 1,
    ("vera/wasm/inference.py", "InferenceMixin._infer_block_result_type", "_ctor_layouts"): 2,
    ("vera/wasm/inference.py", "InferenceMixin._infer_expr_wasm_type", "_ctor_layouts"): 2,
    ("vera/wasm/operators.py", "OperatorsMixin._full_ctor_type_name", "_ctor_adt_tp_indices"): 1,
    ("vera/wasm/operators.py", "OperatorsMixin._generate_adt_eq_fn_body", "_ctor_adt_tp_indices"): 1,
}



def _emitted_and_discovered(
    tmp_path: Path, files: dict[str, str],
) -> tuple[set[object], set[object]]:
    """``(codegen emitted, verifier discovered)`` instantiations for *files*.

    The two sides of the #732 differential, driven over one program.  Read
    from the registered records each side actually consumes — codegen's
    ``_emitted_instances`` and the verifier's ``_instances`` — rather than
    recomputed, so a seam that stops threading the tables surfaces here.
    """
    from vera.checker import typecheck_with_artifacts
    from vera.codegen.core import CodeGenerator
    from vera.parser import parse_to_ast
    from vera.resolver import ModuleResolver
    from vera.verifier import ContractVerifier

    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, src in files.items():
        (tmp_path / name).write_text(src, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    source = files["main.vera"]
    program = parse_to_ast(source)
    resolved = ModuleResolver(_root=tmp_path).resolve_imports(
        program, main_path)
    # The checker's side-tables, threaded into BOTH sides exactly as the CLI
    # threads them (PR #1454 review): `MonoContext.expr_types` is the table
    # both consultors fall back to when their own walk names nothing, so a
    # differential run without it compares a configuration production never
    # uses — and a desync that only appears with the tables present would
    # pass.
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(main_path), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    assert not [d for d in diags if d.severity == "error"], diags
    gen = CodeGenerator(
        source=source, file=str(main_path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    gen.compile_program(program)
    emitted = set(getattr(gen, "_emitted_instances", set()))
    verifier = ContractVerifier(
        source=source, file=str(main_path), resolved_modules=resolved,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    verifier.register_program(program)
    discovered = {
        (name, ct)
        for name, cts in verifier._instances.items()
        for ct in cts
    }
    return emitted, discovered


class TestBothSidesDiscoverTheSameClone:
    """The #732 differential over an owner collision (#1436).

    Codegen names a clone after the ADT its scoped projection gives the
    constructor argument; the verifier names one after the ADT its own
    per-namespace table gives it.  Threading either side alone makes the two
    disagree — the shape that dropped `via_generic` with `[E602] call target
    'gid$Shape' not registered` while discovery had recorded `gid$Mine` — and
    an equality between two sets is exactly what catches it, which no
    single-sided test can.

    The premise beside the equality: both sets must actually CONTAIN the
    clone the module's body calls, under the module's own ADT.  Two empty
    sets are equal, and so are two that agree on the entry's declaration.
    """

    @pytest.mark.parametrize("shadow", ["none", "entry_differing"])
    @pytest.mark.parametrize("carrier", sorted(_CARRIER_LIB))
    def test_the_clone_named_is_the_modules_own_adt(
        self, carrier: str, shadow: str, tmp_path: Path,
    ) -> None:
        emitted, discovered = _emitted_and_discovered(
            tmp_path, _matrix_files(carrier, shadow))
        assert emitted == discovered, (emitted ^ discovered)
        owner = _CARRIER_OWNER[carrier]
        assert any(
            name == "gid" and any(owner == t.split("<")[0] for t in types)
            for name, types in emitted
        ), (owner, sorted(emitted))
        assert not any(
            name == "gid" and any(t.split("<")[0] in _SHADOW_ADTS
                                  for t in types)
            for name, types in emitted
        ), sorted(emitted)


#: The ADT the module's own constructor belongs to, per carrier — the type
#: argument discovery must infer for `gid` inside the module's body.
_CARRIER_OWNER = {"plain": "Shape", "generic": "Box", "prelude": "Option"}
#: The ADTs an entry-file shadow declares; no clone may be named after one
#: from a module's body.
_SHADOW_ADTS = frozenset({"Mine", "Other"})


#: The four prelude ADTs the prelude injects ON DEMAND, with the shape each
#: restatement has to match verbatim to be the one layout (§8.4.1).  A module
#: may also declare a DIFFERENTLY shaped type of one of these names — §8.4.1's
#: "stands alone until" — and that declaration is an ordinary ADT of its own
#: module, which is the case the projection got wrong.
_PRELUDE_RESTATEMENTS = {
    "Json": """\
public data Json {
  JNull,
  JBool(Bool),
  JNumber(Float64),
  JString(String),
  JArray(Array<Json>),
  JObject(Map<String, Json>)
}
""",
    "HtmlNode": """\
public data HtmlNode {
  HtmlElement(String, Map<String, String>, Array<HtmlNode>),
  HtmlText(String),
  HtmlComment(String)
}
""",
    "Request": """\
public data Request {
  Request(String, String, Map<String, String>, String)
}
""",
    "Response": """\
public data Response {
  Response(Int, Map<String, String>, String)
}
""",
}

#: A declaration under the same NAME whose constructors collide with
#: `Option`'s and `Result`'s at other tags and other field types — the shape
#: the review's finding 1 is written on.
_PRELUDE_NAME_DIFFERING = """\
public data %s {
  Err(String),
  Ok(Int),
  Some(Bool)
}
"""

#: The same declaration under a name nothing else claims: the control that
#: says the cells below measure the COLLISION and not the extra module.
#: The constructor names the borrowed-name declaration carries.
_PRELUDE_NAME_DIFFERING_CTORS = ("Err", "Ok", "Some")

_PRELUDE_NAME_CONTROL = """\
public data Zz {
  Zerr(String),
  Zok(Int),
  Zsome(Bool)
}
"""

_PRELUDE_LIB = """\
module tlib;

%(decl)s
public fn tping(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""

#: A module that neither declares the type nor imports the module that does,
#: reached from the entry only through `alib`.
_UNRELATED_LIB = """\
module xlib;

public fn x_show(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Some(42))
}

public fn x_result(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match parse_int("42") {
    Ok(@Int) -> @Int.0,
    Err(@String) -> 0 - 1
  }
}
"""

_RELAY_LIB = """\
module alib;

import tlib;

public fn a_ping(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  tlib::tping(@Int.0)
}
"""

_PRELUDE_MAIN = """\
%(import)s
import xlib;

public fn ent_show(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Some(42))
}

public fn ent_hash(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if hash(Some(42)) == hash(Some(43)) then { 1 } else { 0 }
}

public fn ent_match(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(42) {
    Some(@Int) -> 100 + @Int.0,
    None -> 0
  }
}

public fn ent_result(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match parse_int("42") {
    Ok(@Int) -> @Int.0,
    Err(@String) -> 0 - 1
  }
}

public fn prelude_comb(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_unwrap_or(Some(42), 7)
}

public fn x_show(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  xlib::x_show(())
}

public fn x_result(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  xlib::x_result(())
}

public forall<T> fn ent_gid(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn ent_generic(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match ent_gid(Some(42)) {
    Some(@Int) -> 100 + @Int.0,
    None -> 0
  }
}

public fn keep(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  %(keep)s
}
"""

#: What every one of these programs must answer, in every column: the
#: prelude's own reading of `Some`, `Ok` and `Err`, because no namespace here
#: declares any of them.
_PRELUDE_EXPECTED = {
    "ent_show": "Some(42)",
    "ent_hash": 0,
    "ent_match": 142,
    "ent_result": 42,
    "ent_generic": 142,
    "prelude_comb": 42,
    "x_show": "Some(42)",
    "x_result": 42,
}


def _prelude_name_files(
    name: str, shape: str, reach: str,
) -> dict[str, str]:
    """The four-namespace program for one (type, shape, reach) cell."""
    decl = {
        "differing": _PRELUDE_NAME_DIFFERING % name,
        "identical": _PRELUDE_RESTATEMENTS[name],
        "control": _PRELUDE_NAME_CONTROL,
    }[shape]
    files = {
        "tlib.vera": _PRELUDE_LIB % {"decl": decl},
        "xlib.vera": _UNRELATED_LIB,
    }
    if reach == "direct":
        files["main.vera"] = _PRELUDE_MAIN % {
            "import": "import tlib;", "keep": "tlib::tping(1)"}
    else:
        files["alib.vera"] = _RELAY_LIB
        files["main.vera"] = _PRELUDE_MAIN % {
            "import": "import alib;", "keep": "alib::a_ping(1)"}
    return files


@pytest.fixture(scope="module")
def prelude_name_builds(
    tmp_path_factory: pytest.TempPathFactory,
) -> dict[tuple[str, str, str], tuple[
    list[tuple[str, str]], CompileResult, list[tuple[str, str]],
]]:
    """One build per (type, shape, reach); every cell below reads one.

    `observation` does not change the program, so parametrizing over it
    would compile the same 24 programs seven times each (PR #1454 review).
    """
    return {
        (name, shape, reach): build_multi_module(
            tmp_path_factory.mktemp(f"{name}_{shape}_{reach}"),
            _prelude_name_files(name, shape, reach),
        )
        for name in _PRELUDE_RESTATEMENTS
        for shape in ("differing", "identical", "control")
        for reach in ("direct", "transitive")
    }


class TestAPreludeNamedDeclarationKeepsItsOwnNamespace:
    """A module's declaration under a PRELUDE type's name (#1454 review, 1).

    §8.4.1 lets a module declare a differently-shaped type of a prelude
    name that nothing demands — it "stands alone until" the prelude's is
    needed — and the first form of the scoping treated every declaration
    under a prelude NAME as infrastructure, so its constructors overwrote
    the prelude's in every namespace: `show(Some(42))` rendered
    `Some(false)`, `hash(Some(42)) == hash(Some(43))` was true, and
    `match parse_int("42")` took the `Err` arm — in the entry, inside an
    unrelated module, and in the prelude's own combinator bodies, with no
    diagnostic from any stage.

    The carve-out is keyed on SHAPE now: a declaration that restates the
    prelude's type IS the one layout and belongs everywhere; one that only
    borrows the name is an ordinary ADT of the module that wrote it.  Four
    namespaces are observed per cell — the declaring module, the entry, a
    module that can name neither, and the prelude's own bodies — across the
    four demand-injected types, both shapes, and both reaches.
    """

    @pytest.mark.parametrize("observation", sorted(_PRELUDE_EXPECTED))
    @pytest.mark.parametrize("reach", ["direct", "transitive"])
    @pytest.mark.parametrize("shape", ["differing", "identical", "control"])
    @pytest.mark.parametrize(
        "name", sorted(_PRELUDE_RESTATEMENTS))
    def test_the_prelude_keeps_its_constructors(
        self, name: str, shape: str, reach: str, observation: str,
        prelude_name_builds: dict[tuple[str, str, str], tuple[
            list[tuple[str, str]], CompileResult, list[tuple[str, str]],
        ]],
    ) -> None:
        _verify, result, _cg = prelude_name_builds[(name, shape, reach)]
        assert module_value(result, observation) == (
            "ok", _PRELUDE_EXPECTED[observation])

    @pytest.mark.parametrize("reach", ["direct", "transitive"])
    @pytest.mark.parametrize("shape", ["differing", "identical", "control"])
    @pytest.mark.parametrize("name", sorted(_PRELUDE_RESTATEMENTS))
    def test_nothing_is_reported_and_nothing_is_dropped(
        self, name: str, shape: str, reach: str,
        prelude_name_builds: dict[tuple[str, str, str], tuple[
            list[tuple[str, str]], CompileResult, list[tuple[str, str]],
        ]],
    ) -> None:
        """The silence around each program, asserted once per build.

        These programs are legal under §8.4.1 and this PR does not reach
        for a new refusal: whether a differently-shaped declaration of a
        demand-injected prelude name should be REFUSED is a language
        question, deliberately left open.  The cells above pin the VALUES;
        this one pins that nothing was reported to get them, and that no
        function was skipped on the way.
        """
        verify_errors, result, cg_errors = prelude_name_builds[
            (name, shape, reach)]
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        assert [d.error_code for d in result.diagnostics] == [], (
            result.diagnostics)

    @pytest.mark.parametrize("shape", ["differing", "identical", "control"])
    @pytest.mark.parametrize("name", sorted(_PRELUDE_RESTATEMENTS))
    def test_both_sides_agree_over_an_imported_prelude_name(
        self, name: str, shape: str, tmp_path: Path,
    ) -> None:
        """The same equality where the collision is with INFRASTRUCTURE.

        An imported ADT whose constructors are spelled `Some`, `Ok` or
        `Err` reaches each side's owner table through a different door —
        codegen's projection applies imports without displacing
        infrastructure, and the shared derivation has to say the same or
        the two name different clones and the caller is dropped (E602/E620).
        The cell the carrier matrix runs cannot see this: its collisions are
        with another namespace's ADT, never with the prelude's own.
        """
        emitted, discovered = _emitted_and_discovered(
            tmp_path, _prelude_name_files(name, shape, "direct"))
        # Premise first: two empty sets are equal, and these programs are
        # only a differential at all because the entry instantiates its own
        # `forall` over a value built with the contended constructor.
        assert any(fn == "ent_gid" for fn, _types in emitted), sorted(emitted)
        assert emitted == discovered, (emitted ^ discovered)
        # ... and the clone is named after the PRELUDE's type, not the
        # imported declaration that borrowed its constructor's spelling.
        assert all(
            not any(t.split("<")[0] == name for t in types)
            for fn, types in emitted if fn == "ent_gid"
        ), sorted(emitted)

    @pytest.mark.parametrize("name", sorted(_PRELUDE_RESTATEMENTS))
    def test_an_import_does_not_take_an_infrastructure_name(
        self, name: str,
    ) -> None:
        """The rule itself, asked of the shared owner table (#1454 review).

        Codegen's projection applies `foreign` without displacing
        infrastructure; the derivation the verifier's discovery narrows by
        has to say the same, or the two name different clones.  Asked of the
        table directly rather than through a program, because the checker's
        span-keyed type table answers a `ConstructorCall` first and would
        mask a disagreement here until some shape outran it — which is
        exactly the kind of latency a structural cell exists to remove.
        """
        from vera.monomorphize import namespace_ctor_owners
        from vera.parser import parse_to_ast

        files = _prelude_name_files(name, "differing", "direct")
        lib = parse_to_ast(files["tlib.vera"])
        entry = parse_to_ast(files["main.vera"])
        owners = namespace_ctor_owners(
            entry, [(("tlib",), lib)],
            {"Option": ("None", "Some"), "Result": ("Ok", "Err"),
             name: tuple(_PRELUDE_NAME_DIFFERING_CTORS)},
        )
        entry_owners = owners.visible(None) or {}
        for ctor, owner in (("Some", "Option"), ("Ok", "Result"),
                            ("Err", "Result")):
            assert entry_owners.get(ctor) == owner, (
                f"the entry's {ctor} resolves to {entry_owners.get(ctor)!r}, "
                f"not the prelude's {owner}")
        # The declaring module keeps its own reading of the same names.
        assert (owners.visible(("tlib",)) or {}).get("Some") == name

    @pytest.mark.parametrize("name", sorted(_PRELUDE_RESTATEMENTS))
    def test_the_declaring_module_reads_its_own(
        self, name: str, tmp_path: Path,
    ) -> None:
        """Inside the module that wrote it, the borrowed name is ITS type.

        The other half of the rule, and the one a fix that simply hid the
        declaration would break: codegen follows the checker's owner in the
        declaring namespace too, where the local declaration shadows the
        prelude's constructor (§8.5.2).
        """
        files = _prelude_name_files(name, "differing", "direct")
        files["tlib.vera"] += """
public fn t_show(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Some(true))
}
"""
        files["main.vera"] += """
public fn mod_show(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  tlib::t_show(())
}
"""
        verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        assert module_value(result, "mod_show") == ("ok", "Some(true)")
        # ... while the entry still reads the prelude's.
        assert module_value(result, "ent_show") == ("ok", "Some(42)")


class TestTheTwoOwnerDerivationsAdmitByTheSameKey:
    """Both owner tables admit a constructor by its TYPE's name (#1454
    review, finding 4).

    Codegen's `_build_adt_membership` and the shared
    `namespace_ctor_owners` answer one question — which constructors a
    namespace can name — and a selective import admits them by naming the
    PARENT type (§8.5.4).  Naming the constructor itself is not a form the
    checker accepts, so a derivation that admitted it would differ from
    both the other layer and the language, and nothing would notice until
    the shape became reachable.
    """

    _LIB = """\
module ilib;

public data Shape {
  Sq(Int),
  Circ(Int)
}

public fn mk(@Int -> @Shape)
  requires(true)
  ensures(true)
  effects(pure)
{
  Sq(@Int.0)
}
"""

    _USE = """\
import ilib(%s);

public fn go(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Sq(7) {
    Sq(@Int) -> 1,
    Circ(@Int) -> 2
  }
}
"""

    def test_the_constructor_name_in_an_import_list_admits_nothing(
        self, tmp_path: Path,
    ) -> None:
        """The checker's answer, which the tables must not contradict.

        Naming the CONSTRUCTOR in the import list does not bring it into
        scope, while naming its TYPE does.  Since #1513 a constructor of a
        type the file does not import still resolves when it denotes one
        declaration, with a warning naming the type's import (E210 for the
        construction, E320 for each pattern), so the admission shows as
        those warnings: drawn under the constructor's name, and absent under
        the type's.
        """
        from vera.checker import typecheck
        from vera.parser import parse_to_ast
        from vera.resolver import ModuleResolver

        ctor_dir = tmp_path / "ctor"
        ctor_dir.mkdir()
        (ctor_dir / "ilib.vera").write_text(self._LIB, encoding="utf-8")
        source = self._USE % "Sq"
        (ctor_dir / "main.vera").write_text(source, encoding="utf-8")
        program = parse_to_ast(source)
        resolved = ModuleResolver(_root=ctor_dir).resolve_imports(
            program, ctor_dir / "main.vera")
        diags = typecheck(program, source, resolved_modules=resolved)
        assert [(d.severity, d.error_code) for d in diags] == [
            ("warning", "E210"), ("warning", "E320"), ("warning", "E320")], (
            "naming the constructor admitted it", diags)
        assert all("'import ilib(Shape, Sq);'" in d.fix for d in diags), diags
        verify_errors, result, cg_errors = build_multi_module(
            tmp_path / "type",
            {"ilib.vera": self._LIB, "main.vera": self._USE % "Shape"})
        assert not verify_errors and not cg_errors, (verify_errors, cg_errors)
        assert module_value(result, "go") == ("ok", 1)

    @pytest.mark.parametrize(
        "names,admits", [(None, True), (("Shape",), True), (("Sq",), False)])
    def test_the_shared_derivation_admits_only_by_type_name(
        self, names: tuple[str, ...] | None, admits: bool,
    ) -> None:
        """And the shared table agrees, cell by cell.

        Driven directly rather than through a program, so the table's own
        answer is what is read.  A second module the entry can see, `jlib`,
        declares `Sq` too: the #1513 fallback fills a name only where one
        unimported type declares it, so here it cannot answer for the import
        list, and `Sq` is in the entry's table exactly when the import
        admitted it.
        """
        from vera.monomorphize import namespace_ctor_owners
        from vera.parser import parse_to_ast

        lib = parse_to_ast(self._LIB)
        jlib = parse_to_ast(
            "module jlib;\n\npublic data Tile {\n  Sq(Bool)\n}\n")
        imp = "import ilib;" if names is None else (
            f"import ilib({', '.join(names)});")
        entry = parse_to_ast(imp + """

public fn go(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
""")
        owners = namespace_ctor_owners(
            entry, [(("ilib",), lib), (("jlib",), jlib)],
            {"Shape": ("Sq", "Circ"), "Tile": ("Sq",)},
        )
        visible = owners.visible(None) or {}
        assert ("Sq" in visible) is admits, (names, sorted(visible))
        if admits:
            assert visible["Sq"] == "Shape", visible
        # The declaring module always names its own, whatever the importer
        # asked for.
        assert (owners.visible(("ilib",)) or {}).get("Sq") == "Shape"


class TestTheScopedProjectionIsTheOnlyLookupPath:
    """The structural half of the class instrument (#1436).

    The behavioural matrix can only fail for a path some program reaches.
    This one fails for a path that merely EXISTS: it walks the compiler for
    by-name constructor lookups and holds the population to an inventory, and
    it holds every ``WasmContext`` to taking all three by-name tables from
    the namespace-scoped projection.

    That second cell is the one a marker cannot satisfy.  #1454's review
    found six read sites re-labelled "resolved in the compiling namespace's
    scoped projection" while `_ctor_adt_tp_indices` was still handed to the
    context raw — the reason was false and the rail that checks markers
    cannot tell.  Here the claim is checked where it is made, at the
    construction of the context those sites read from.
    """

    #: The flat, by-name tables.  A lookup in one of them is a constructor
    #: name resolved without an owner.
    _ATTRS = frozenset({
        "_ctor_layouts", "_ctor_to_adt", "_ctor_adt_tp_indices",
    })
    #: Where a by-name lookup can live, discovered by globbing so a new
    #: module joins by existing.
    _DIRS = ("vera/wasm", "vera/codegen")
    _EXTRA_FILES = ("vera/smt.py",)
    #: The keyword arguments a `WasmContext` resolves constructor names
    #: through, every one of which must come from the scoped projection.
    _CONTEXT_KWARGS = ("ctor_layouts", "ctor_to_adt", "ctor_adt_tp_indices")

    @staticmethod
    def _sites() -> dict[tuple[str, str, str], int]:
        """Every by-name lookup, counted per (file, function, table)."""
        import ast as pyast
        from collections import Counter
        from pathlib import Path as _P

        cls_ = TestTheScopedProjectionIsTheOnlyLookupPath
        root = _P(__file__).resolve().parents[1]
        files = [
            str(f.relative_to(root))
            for d in cls_._DIRS for f in sorted((root / d).glob("*.py"))
        ] + list(cls_._EXTRA_FILES)
        found: Counter[tuple[str, str, str]] = Counter()
        for rel in files:
            tree = pyast.parse((root / rel).read_text(encoding="utf-8"))
            spans: list[tuple[int, int, str]] = []
            for owner in pyast.walk(tree):
                if not isinstance(owner, pyast.ClassDef):
                    continue
                for fn in pyast.walk(owner):
                    if isinstance(fn, (pyast.FunctionDef,
                                       pyast.AsyncFunctionDef)):
                        spans.append(
                            (fn.lineno, fn.end_lineno or fn.lineno,
                             f"{owner.name}.{fn.name}"))
            for fn in pyast.walk(tree):
                if (isinstance(fn, (pyast.FunctionDef, pyast.AsyncFunctionDef))
                        and not any(s[0] == fn.lineno for s in spans)):
                    spans.append(
                        (fn.lineno, fn.end_lineno or fn.lineno, fn.name))
            for node in pyast.walk(tree):
                if not (isinstance(node, pyast.Attribute)
                        and node.attr in cls_._ATTRS):
                    continue
                where = next(
                    (name for a, b, name in sorted(spans)
                     if a <= node.lineno <= b),
                    "<module>",
                )
                found[(rel.replace("\\", "/"), where, node.attr)] += 1
        return dict(found)

    def test_the_by_name_population_is_the_inventory(self) -> None:
        """No by-name lookup outside the inventory, and none missing from it.

        Both directions, because each catches what the other cannot: a new
        site is a lookup that escaped the registry, and a vanished one is an
        inventory row that has stopped describing the compiler and would
        otherwise keep excusing a site that no longer exists.
        """
        assert self._sites() == _BY_NAME_INVENTORY

    def test_the_mono_context_flat_tables_are_read_only_by_the_readers(
        self,
    ) -> None:
        """The third layer's flat tables are LOOKED UP in exactly two places.

        Discovery names a clone after the type it infers from a constructor
        ARGUMENT, so `MonoContext.ctor_to_adt` / `ctor_tp_indices` decide a
        constructor's owner just as codegen's projection does.  A lookup BY
        NAME is narrowed per namespace by `Monomorphizer._ctor_owner` and
        `_ctor_tp_indices`; one anywhere else is a fourth derivation of the
        same name's meaning, and the differential only catches it once a
        program reaches it.

        The table is matched both off the context and as the ``ctor_to_adt``
        argument the walk threads, because the readers are handed the
        parameter form and a bypass would be written the same way.
        Enumerations are not lookups and are left alone: `_declared_type_names`
        takes `.values()` to collect every type name that exists anywhere,
        which is a question about the PROGRAM and not about what one
        constructor denotes here — narrowing it per namespace would shrink a
        set that is deliberately namespace-wide.
        """
        import ast as pyast
        from pathlib import Path as _P

        root = _P(__file__).resolve().parents[1]
        path = root / "vera" / "monomorphize.py"
        tree = pyast.parse(path.read_text(encoding="utf-8"))
        spans: list[tuple[int, int, str]] = []
        for owner in pyast.walk(tree):
            if not isinstance(owner, pyast.ClassDef):
                continue
            for fn in pyast.walk(owner):
                if isinstance(fn, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
                    spans.append(
                        (fn.lineno, fn.end_lineno or fn.lineno, fn.name))

        def is_table(node: object) -> bool:
            """The flat map, however it reached the expression.

            Either off the context, or as the ``ctor_to_adt`` argument
            discovery threads through every walk function — the same table,
            and the parameter is the form the readers are actually handed.
            """
            if (isinstance(node, pyast.Attribute)
                    and node.attr in {"ctor_to_adt", "ctor_tp_indices"}
                    and isinstance(node.value, pyast.Attribute)
                    and node.value.attr == "ctx"):
                return True
            return (
                isinstance(node, pyast.Name)
                and node.id in {"ctor_to_adt", "ctor_tp_indices"}
            )

        def where(lineno: int) -> str:
            return next(
                (n for a, b, n in sorted(spans) if a <= lineno <= b),
                "<module>",
            )

        lookups: list[tuple[int, str]] = []
        for node in pyast.walk(tree):
            if isinstance(node, pyast.Subscript) and is_table(node.value):
                lookups.append((node.lineno, where(node.lineno)))
            elif (isinstance(node, pyast.Call)
                    and isinstance(node.func, pyast.Attribute)
                    and node.func.attr == "get"
                    and is_table(node.func.value)):
                lookups.append((node.lineno, where(node.lineno)))
        readers = {"_ctor_owner", "_ctor_tp_indices"}
        outside = [site for site in lookups if site[1] not in readers]
        assert not outside, (
            "MonoContext's flat constructor tables are looked up outside "
            f"{sorted(readers)}, which bypasses the per-namespace "
            f"narrowing: {outside}"
        )
        # Not vacuous: both readers must still be doing the lookup.
        assert {site[1] for site in lookups} == readers, lookups

    def test_every_wasm_context_takes_all_three_tables_from_the_projection(
        self,
    ) -> None:
        """Each of the three tables reaches the wasm layer scoped.

        The keyword's value must be a name the enclosing function bound by
        unpacking ``_namespace_ctor_projection()`` — not ``self.<flat map>``,
        which is how the type-parameter table stayed unscoped under six
        markers that said otherwise.
        """
        import ast as pyast
        from pathlib import Path as _P

        root = _P(__file__).resolve().parents[1]
        seen = 0
        for path in sorted((root / "vera" / "codegen").glob("*.py")):
            tree = pyast.parse(path.read_text(encoding="utf-8"))
            for fn in pyast.walk(tree):
                if not isinstance(fn, (pyast.FunctionDef,
                                       pyast.AsyncFunctionDef)):
                    continue
                bound: set[str] = set()
                for stmt in pyast.walk(fn):
                    if not isinstance(stmt, pyast.Assign):
                        continue
                    call = stmt.value
                    if (isinstance(call, pyast.Call)
                            and isinstance(call.func, pyast.Attribute)
                            and call.func.attr == "_namespace_ctor_projection"):
                        for target in stmt.targets:
                            if isinstance(target, pyast.Tuple):
                                bound |= {
                                    e.id for e in target.elts
                                    if isinstance(e, pyast.Name)
                                }
                for call in pyast.walk(fn):
                    if not (isinstance(call, pyast.Call)
                            and isinstance(call.func, pyast.Name)
                            and call.func.id == "WasmContext"):
                        continue
                    seen += 1
                    kwargs = {
                        kw.arg: kw.value for kw in call.keywords
                        if kw.arg is not None
                    }
                    for name in self._CONTEXT_KWARGS:
                        value = kwargs.get(name)
                        assert isinstance(value, pyast.Name), (
                            f"{path.name}:{call.lineno} passes {name}="
                            f"{pyast.dump(value) if value else None!r} — it "
                            "must come from `_namespace_ctor_projection()`"
                        )
                        assert value.id in bound, (
                            f"{path.name}:{call.lineno} passes {name}="
                            f"{value.id}, which is not bound from "
                            "`_namespace_ctor_projection()` in "
                            f"{fn.name}"
                        )
        assert seen == 2, (
            "expected the two context constructions (a function body and a "
            f"lifted closure body); found {seen}"
        )


#: The ENTRY-side pair that reads the verifier's answer: a claim its body
#: satisfies, and one its body refutes, both stated over the ENTRY's OWN
#: declaration of the contended name.  `%(ctor)s` is the name an imported
#: module also declares, so a verifier that had taken the module's reading
#: would type the result differently or discharge the wrong claim.
_ENTRY_VERIFIER_PAIR = """
public fn entry_true(@Bool -> @Mine)
  requires(true)
  ensures(@Mine.result == %(ctor)s(@Bool.0))
  effects(pure)
{
  %(ctor)s(@Bool.0)
}

public fn entry_false(@Bool -> @Mine)
  requires(true)
  ensures(@Mine.result == Pad(@Bool.0))
  effects(pure)
{
  %(ctor)s(@Bool.0)
}
"""


class TestTheVerifierReadsTheNameInTheNamespaceThatWroteIt:
    """The verifier's reading of the name, as a differential (#1436).

    The entry declares `Mine`, whose constructor an imported module also
    declares, and states two postconditions over it: one its body satisfies
    and one its body refutes.  Both are needed.  A DISCHARGED postcondition
    on its own says little about which declaration the name was given — a
    verifier that had stopped telling two constructors apart would discharge
    it just as happily — and a refuted one on its own is satisfied by a
    verifier that refutes everything.  Together they pin the reading: the
    true claim holds, the false one is refuted, and `vera run` returns the
    value the entry's own declaration names while the module keeps its.
    """

    @pytest.mark.parametrize("carrier", sorted(_CARRIER_LIB))
    def test_the_entrys_own_claims_are_decided_against_its_own_declaration(
        self, carrier: str, tmp_path: Path,
    ) -> None:
        files = _matrix_files(carrier, "entry_differing")
        files["main.vera"] += _ENTRY_VERIFIER_PAIR % {
            "ctor": _CARRIER_CTOR[carrier]}
        verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
        assert not cg_errors, cg_errors
        assert [code for code, _ in verify_errors] == ["E500"], verify_errors
        assert "entry_false" in verify_errors[0][1], verify_errors
        # The module's own reading is untouched by either claim.
        for position in ("construction", "data_segment", "tag_eq"):
            assert module_value(result, position) == (
                "ok", _MATRIX_EXPECTED[carrier][position])


# ---------------------------------------------------------------------------
# #1513: a constructor of a type the calling namespace does not import
# ---------------------------------------------------------------------------


_S_GBOXB = """\
module gboxb;

public data GBox<T> {
  GMk(T)
}
"""

_S_GA = """\
module ga;

import gboxb(GBox);

public forall<T> fn gcount(@GBox<T> -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  match @GBox<T>.0 {
    GMk(@T) -> 1
  }
}

public forall<T> fn gget(@GBox<T> -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @GBox<T>.0 {
    GMk(@T) -> @T.0
  }
}
"""

_S_HDR = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _s_fn(name: str, body: str) -> str:
    return f"public fn {name}(@Unit -> @Int)\n{_S_HDR}{{\n  {body}\n}}\n"


#: (the namespace that calls, its selective imports, the call) -> the clones
#: both sides must name.  `GBox` reaches the caller only through the
#: signatures of `ga`'s functions, so `GMk` resolves by the #1513 fallback.
_STRANGER_CALLS: dict[str, tuple[str, str, str, frozenset[tuple[str, ...]]]] = {
    "entry_two_instances": (
        "entry", "import ga(gcount, gget);\n",
        "gcount(GMk(9)) + gcount(GMk(true))",
        frozenset({("gcount", "Int"), ("gcount", "Bool")})),
    "entry_result_type": (
        "entry", "import ga(gcount, gget);\n", "gget(GMk(40)) + 2",
        frozenset({("gget", "Int")})),
    "entry_nested_constructor": (
        "entry", "import ga(gcount, gget);\n", "gcount(GMk(GMk(3)))",
        frozenset({("gcount", "GBox")})),
    "module_body": (
        "module", "import ga(gcount);\n",
        "gcount(GMk(1)) + gcount(GMk(false))",
        frozenset({("gcount", "Int"), ("gcount", "Bool")})),
}


def _stranger_call_files(shape: str, *, imported: bool) -> dict[str, str]:
    where, imports, call, _clones = _STRANGER_CALLS[shape]
    if imported:
        imports += "import gboxb(GBox);\n"
    files = {"gboxb.vera": _S_GBOXB, "ga.vera": _S_GA}
    if where == "entry":
        files["main.vera"] = f"{imports}\n" + _s_fn("main", call)
    else:
        files["gm.vera"] = f"module gm;\n\n{imports}\n" + _s_fn("twice", call)
        files["main.vera"] = "import gm(twice);\n\n" + _s_fn("main", "twice(())")
    return files


class TestAStrangerConstructorNamesOneClone:
    """The #732 differential over a constructor of an unimported type (#1513).

    `gcount(GMk(9))` with `GBox` reaching the caller only through `gcount`'s
    signature: code generation resolves `GMk` through the fallback class of
    `_namespace_ctor_projection` and emits `gcount<Int>` from the argument.
    The verifier's discovery reads `namespace_ctor_owners`, which had no such
    class, so `GMk` had no owner there, discovery fell back to the checker's
    `GBox<Nat>` for the literal, and it verified a `gcount<Nat>` the binary
    does not contain while the emitted `gcount<Int>` went undiscovered.  The
    same fallback, over the same modules, now fills that table.

    Each shape is run with the type imported as a control, which both sides
    answered alike before the fix; the premise asserts both sets hold the
    clones the calls name, so two empty or two equally wrong sets fail.
    """

    @pytest.mark.parametrize("imported", [False, True],
                             ids=["unimported", "imported"])
    @pytest.mark.parametrize("shape", sorted(_STRANGER_CALLS))
    def test_both_sides_name_the_same_clones(
        self, shape: str, imported: bool, tmp_path: Path,
    ) -> None:
        emitted, discovered = _emitted_and_discovered(
            tmp_path, _stranger_call_files(shape, imported=imported))
        assert emitted == discovered, (emitted ^ discovered)
        named = {
            (str(name).rsplit("$", 1)[-1], str(types[0]).split("<")[0])
            for name, types in emitted
        }
        assert named == set(_STRANGER_CALLS[shape][3]), sorted(named)

    def test_the_fallback_reads_each_namespaces_own_reach(self) -> None:
        """The table fills a name from the modules THAT namespace's checker
        sees, where one unimported type alone declares it.

        `other` declares a second public type with a `GMk`.  The entry's
        checker is handed every resolved module, `other` included, so `GMk`
        names two types there and stays unfilled; `gm`
        reaches only `ga` and `gboxb` through its imports, so there `GMk` is
        `GBox`'s.  Asked of the shared derivation directly, since the
        checker refuses the entry's ambiguous use before any program built
        from it could reach discovery.
        """
        from vera.monomorphize import namespace_ctor_owners
        from vera.parser import parse_to_ast

        modules = [
            (("gboxb",), parse_to_ast(_S_GBOXB)),
            (("ga",), parse_to_ast(_S_GA)),
            (("gm",), parse_to_ast(
                "module gm;\n\nimport ga(gcount);\n\n"
                + _s_fn("twice", "gcount(GMk(1))"))),
            (("other",), parse_to_ast(
                "module other;\n\npublic data OBox<T> {\n  GMk(T)\n}\n")),
        ]
        entry = parse_to_ast("import gm(twice);\n\n" + _s_fn("main", "0"))
        owners = namespace_ctor_owners(entry, modules, {})
        assert "GMk" not in (owners.visible(None) or {})
        assert (owners.visible(("gm",)) or {}).get("GMk") == "GBox"
        # `ga` imports the type, and `other` declares its own: neither is
        # the fallback's.
        assert (owners.visible(("ga",)) or {}).get("GMk") == "GBox"
        assert (owners.visible(("other",)) or {}).get("GMk") == "OBox"

    def test_the_fallback_fills_and_never_displaces(self) -> None:
        """A name the namespace's own declaration, an import or the
        infrastructure holds keeps that owner, though one unimported type
        in reach also declares it: the fallback only fills gaps, as
        codegen's does, which is what keeps #1436's guarantee for every
        name the three classes resolve."""
        from vera.monomorphize import namespace_ctor_owners
        from vera.parser import parse_to_ast

        modules = [
            (("gboxb",), parse_to_ast(_S_GBOXB)),
            (("ga",), parse_to_ast(_S_GA)),
            (("sib",), parse_to_ast(
                "module sib;\n\npublic data Tag {\n  Mark(Int),\n  Some(Bool)\n}"
                "\n\npublic data Pair {\n  Two(Int)\n}\n")),
        ]
        entry = parse_to_ast(
            "import ga(gcount);\nimport sib(Pair);\n\n"
            "private data Mine {\n  Mark(Int)\n}\n\n"
            + _s_fn("main", "0"))
        registry = {"Option": ("None", "Some")}
        owners = namespace_ctor_owners(entry, modules, registry)
        visible = owners.visible(None) or {}
        assert visible.get("Mark") == "Mine", visible     # own declaration
        assert visible.get("Some") == "Option", visible   # infrastructure
        assert visible.get("Two") == "Pair", visible      # an import
        assert visible.get("GMk") == "GBox", visible      # the fallback
