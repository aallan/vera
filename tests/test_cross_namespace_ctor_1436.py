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

import pytest

from tests.module_fixture_helpers import build_multi_module, module_value

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
