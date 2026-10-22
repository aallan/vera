"""#1312 / #1317 / #1694 — two namespaces' same-named data types.

Codegen's ``_adt_layouts`` held ONE layout per bare name across the whole
program, so three PAIRS could meet in one slot, and before #1312 the rails
answered all three differently: module versus prelude (E621, shape-based
since #1277), entry file versus module (nothing at all: a `vera
check`-green program compiled to a module whose ``main`` was simply absent,
#1312), and module versus module (E609/E610, keyed on PROVENANCE, #1317).
#1312 and #1317 made the last two one question about LAYOUTS (E623, and
E609/E610 relaxed for a restatement).

#1694 replaces the question.  The prelude's type names are reserved (E158,
#1469), and every other declaration is a type of its own, named by its link
name in every stage (:mod:`vera.binding`): an entry file's ``Shape`` and a
module's, or two modules', never share a slot, so their layouts no longer
decide anything.  A program is refused exactly where a value of one meets
the other, at check, by an ordinary mismatch whose message names both
owners — a restatement included, which is the breaking change (declare the
type once and import it).

:class:`TestDifferingShapesAdmittedWhenNothingMeetsThem` and
:class:`TestMeetingStillRefused` pin the two sides of that boundary;
``tests/test_per_owner_adt_identity_1317.py`` holds the full matrix.
"""
from __future__ import annotations

from pathlib import Path



from tests.module_fixture_helpers import (
    build_multi_module,
    module_value,
    refused_at_check as _refused_at_check,
    refused_multi_module,
)


# =====================================================================
# Fixtures
# =====================================================================

_BLIB_OWN_JSON = """\
module blib;

private data Jbox { JBlob(Int) }

private fn wrap(@Int -> @Jbox)
  requires(true)
  ensures(true)
  effects(pure)
{
  JBlob(@Int.0)
}

public fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match wrap(@Int.0) {
    JBlob(@Int) -> @Int.0
  }
}
"""

_ENTRY_OWN_JSON = """\
import blib(probe);

private data Jbox { JMine(Int) }

public fn consume(@Jbox -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Jbox.0 {
    JMine(@Int) -> @Int.0
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(pure)
{
  probe(7)
}
"""

# The issue's own repro, renamed off the reserved `Json` (#1469): the module
# never touches its `Jbox`, so nothing inside it drops, and the two
# declarations are two types (#1694).
_BLIB_UNUSED_JSON = """\
module blib;

private data Jbox { JBlob(Int) }

public fn probe(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}
"""

_ENTRY_UNUSED_JSON = """\
import blib(probe);

private data Jbox { JMine(Int) }

public fn consume(@Jbox -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(pure)
{
  probe(7)
}
"""

_SHARED_SHAPE_MODULE = """\
module blib;

public data Shape { Sq(Int) }

public fn probe(@Int -> @Shape)
  requires(true)
  ensures(true)
  effects(pure)
{
  Sq(@Int.0)
}
"""

_ENTRY_RESTATES_SHAPE = """\
import blib(probe);

private data Shape { Sq(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match probe(7) {
    Sq(@Int) -> @Int.0
  }
}
"""


# The two axes a single-constructor fixture cannot reach (PR #1372 review):
# constructor ORDER, because the tag is the position, and type-parameter
# ARITY.  The layout-sharing rail compared both; since #1694 neither decides
# anything, since two declarations are two types, and the cells below hold
# that a pair differing on one axis alone is refused or admitted exactly as
# a pair matching on both.

_MODULE_TWO_CTORS = """\
module blib;

public data Pair { A(Int), B(Int) }

public fn probe(@Int -> @Pair)
  requires(true)
  ensures(true)
  effects(pure)
{
  A(@Int.0)
}
"""

_ENTRY_SAME_ORDER = """\
import blib(probe);

private data Pair { A(Int), B(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match probe(7) {
    A(@Int) -> @Int.0,
    B(@Int) -> 0
  }
}
"""

# Byte-for-byte the entry above with the two constructors SWAPPED — same
# names, same field types, same arity.  Only the tag assignment moves.
_ENTRY_SWAPPED_ORDER = _ENTRY_SAME_ORDER.replace(
    "private data Pair { A(Int), B(Int) }",
    "private data Pair { B(Int), A(Int) }",
)

_MODULE_ARITY_ONE = """\
module blib;

public data Box<T> { Wrap(Int) }

public fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Wrap(@Int.0) {
    Wrap(@Int) -> @Int.0
  }
}
"""

# Same constructor, same field type; only the declaration's type-parameter
# ARITY differs.
_ENTRY_ARITY_ZERO = """\
import blib(probe);

private data Box { Wrap(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(7)
}
"""


def _codes(errors: list[tuple[str, str]]) -> list[str]:
    return [code for code, _ in errors]


# =====================================================================
# #1312 — the entry file against a module
# =====================================================================


class TestEntryVersusModule:
    """The entry file against a module: two types, refused only where they
    meet (#1312, #1694)."""

    def test_differing_private_shapes_each_keep_their_own(
        self, tmp_path: Path,
    ) -> None:
        """The issue's pair, under a name the prelude does not hold (its
        own `Json` is reserved since #1469): the entry's private `Jbox` and
        the module's private `Jbox` each keep their own layout, so nothing
        is refused and ``main`` runs."""
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "differ",
            {"blib.vera": _BLIB_OWN_JSON, "main.vera": _ENTRY_OWN_JSON},
        )
        assert cg_errors == [], cg_errors
        assert "main" in result.exports and "consume" in result.exports
        assert module_value(result) == ("ok", 7)

    def test_the_issues_own_repro(self, tmp_path: Path) -> None:
        """The issue's fixture, renamed the same way, where the module never
        touches its own type: nothing is refused either."""
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "verbatim",
            {"blib.vera": _BLIB_UNUSED_JSON, "main.vera": _ENTRY_UNUSED_JSON},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

    def test_identical_shapes_are_two_types(self, tmp_path: Path) -> None:
        """An entry file restating a module's public type declares a second
        type (#1694), so where the module's value meets the entry's
        constructors the program is refused at check, naming the module's
        type."""
        codes, text = _refused_at_check(
            tmp_path / "restate",
            {"blib.vera": _SHARED_SHAPE_MODULE,
             "main.vera": _ENTRY_RESTATES_SHAPE},
        )
        assert "E314" in codes, codes
        assert "blib.Shape" in text, text

    def test_an_entry_declaration_no_module_shares_is_untouched(
        self, tmp_path: Path,
    ) -> None:
        """Control: the rail fires on a CONTENDED name, not on any entry
        ``data`` in a program that happens to import something."""
        entry = _ENTRY_OWN_JSON.replace("Jbox", "Zbox").replace(
            "JMine", "MkZbox")
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "control",
            {"blib.vera": _BLIB_OWN_JSON, "main.vera": entry},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

    def test_constructor_ORDER_alone_is_a_different_layout(
        self, tmp_path: Path,
    ) -> None:
        """The tag is the position, so swapping two constructors made a
        different layout to the layout-sharing rail, though the names and
        field types match.  Under #1694 the pair is two types like any
        other, refused where the module's value meets the entry's
        constructors (E314)."""
        codes, text = _refused_at_check(
            tmp_path / "order",
            {"blib.vera": _MODULE_TWO_CTORS,
             "main.vera": _ENTRY_SWAPPED_ORDER},
        )
        assert "E314" in codes, codes
        assert "blib.Pair" in text, text

    def test_the_same_two_constructors_in_the_same_order_are_two_types(
        self, tmp_path: Path,
    ) -> None:
        """The same order is no exception: the layout no longer decides,
        the declaration does (#1694)."""
        codes, text = _refused_at_check(
            tmp_path / "order-ok",
            {"blib.vera": _MODULE_TWO_CTORS,
             "main.vera": _ENTRY_SAME_ORDER},
        )
        assert "E314" in codes, codes
        assert "blib.Pair" in text, text

    def test_a_signature_carrying_the_other_type_is_no_meeting_unused(
        self, tmp_path: Path,
    ) -> None:
        """Two types of one name coexist until a value crosses (#1694).

        ``boxer``'s ``@Int -> @Box<Int>`` signature carries the module's
        ``Box<T>`` to the entry, which declares a zero-arity ``Box`` of its
        own, and imports ``boxer`` without calling it.  The two are two
        types, so nothing meets, and the program runs.  The layout-sharing
        rail this replaced refused the import itself (E623, before #1694).
        """
        module = _MODULE_ARITY_ONE + """
public fn boxer(@Int -> @Box<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Wrap(@Int.0)
}
"""
        entry = _ENTRY_ARITY_ZERO.replace(
            "import blib(probe);", "import blib(probe, boxer);")
        verify_errors, result, cg_errors = build_multi_module(
            tmp_path / "arity",
            {"blib.vera": module, "main.vera": entry},
        )
        assert verify_errors == [], verify_errors
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

    def test_a_differing_arity_the_entry_cannot_reach_is_admitted(
        self, tmp_path: Path,
    ) -> None:
        """Its sibling, and the shape #1423 changed.

        The same two declarations — ``Box<T>`` in the module, ``Box`` in the
        entry — with the module taken UNCHANGED.  It exports both halves
        (``public data Box<T>`` and ``public fn probe``), so what keeps them
        apart is the ENTRY's side: ``import blib(probe);`` is selective and
        admits the function without the type, and ``probe``'s
        ``@Int -> @Int`` signature carries no ``Box`` either — so nothing
        reaches the entry, whose own declaration shadows the name in any
        case.  They cannot meet, so the module's is compiled under its own
        owner-qualified symbol and the program runs.  Before #1423 this was
        E623, and adding an unrelated second module that also declared
        ``Box`` lifted that refusal — the non-monotonicity the entry-owner
        rule ends.
        """
        verify_errors, result, cg_errors = build_multi_module(
            tmp_path / "arity-apart",
            {"blib.vera": _MODULE_ARITY_ONE, "main.vera": _ENTRY_ARITY_ZERO},
        )
        # BOTH streams, for an ADMITTED case: the two rails this change made
        # one rule report through different phases, so a regression that
        # moved the refusal into verification would leave a cg-only
        # assertion green while the program stopped compiling (PR review).
        assert verify_errors == [], verify_errors
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

# =====================================================================
# #1317 — two modules that describe one layout
# =====================================================================

_LIBA_RESTATE = """\
module liba;

public data Shape { Sq(Int) }

public fn aone(@Int -> @Shape)
  requires(true)
  ensures(true)
  effects(pure)
{
  Sq(@Int.0)
}
"""

_LIBB_RESTATE = """\
module libb;

public data Shape { Sq(Int) }

public fn bone(@Shape -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Shape.0 {
    Sq(@Int) -> @Int.0 + 1
  }
}
"""

_ENTRY_DIAMOND = """\
import liba(aone);
import libb(bone);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  bone(aone(6))
}
"""


class TestModuleRestatementDiamond:
    """Two dependencies declaring one layout are no longer a collision."""

    def test_the_restatement_diamond_is_two_types(
        self, tmp_path: Path,
    ) -> None:
        """Two dependencies restating one layout declare two types (#1694),
        so the diamond's crossing is refused at check, naming both owners;
        declaring the type once, in one module the other imports, is the
        program that compiles."""
        codes, text = _refused_at_check(
            tmp_path / "diamond",
            {"liba.vera": _LIBA_RESTATE, "libb.vera": _LIBB_RESTATE,
             "main.vera": _ENTRY_DIAMOND},
        )
        assert "E202" in codes, codes
        assert "liba.Shape" in text and "libb.Shape" in text, text

    def test_constructor_ORDER_alone_refuses_the_module_pair_too(
        self, tmp_path: Path,
    ) -> None:
        """The same axis between two modules, refused at check."""
        liba = _LIBA_RESTATE.replace(
            "public data Shape { Sq(Int) }",
            "public data Shape { Sq(Int), Cr(Int) }")
        libb = _LIBB_RESTATE.replace(
            "public data Shape { Sq(Int) }",
            "public data Shape { Cr(Int), Sq(Int) }").replace(
            "    Sq(@Int) -> @Int.0 + 1\n",
            "    Sq(@Int) -> @Int.0 + 1,\n    Cr(@Int) -> 0\n")
        codes, text = _refused_at_check(
            tmp_path / "mod-order",
            {"liba.vera": liba, "libb.vera": libb,
             "main.vera": _ENTRY_DIAMOND},
        )
        assert "E202" in codes, codes
        assert "liba.Shape" in text and "libb.Shape" in text, text

    def test_the_same_two_constructors_in_the_same_order_are_two_types(
        self, tmp_path: Path,
    ) -> None:
        """The same order between two modules is no exception either."""
        both = _LIBA_RESTATE.replace(
            "public data Shape { Sq(Int) }",
            "public data Shape { Sq(Int), Cr(Int) }")
        libb = _LIBB_RESTATE.replace(
            "public data Shape { Sq(Int) }",
            "public data Shape { Sq(Int), Cr(Int) }").replace(
            "    Sq(@Int) -> @Int.0 + 1\n",
            "    Sq(@Int) -> @Int.0 + 1,\n    Cr(@Int) -> 0\n")
        codes, text = _refused_at_check(
            tmp_path / "mod-order-ok",
            {"liba.vera": both, "libb.vera": libb,
             "main.vera": _ENTRY_DIAMOND},
        )
        assert "E202" in codes, codes
        assert "liba.Shape" in text and "libb.Shape" in text, text

    def test_both_imports_supplying_the_name_is_still_ambiguous(
        self, tmp_path: Path,
    ) -> None:
        """Two imports supplying one bare name are refused at check whatever
        the declarations are (PR #1372 review).

        §8.5.2.2's ambiguity refusal reads the import lists alone —
        `namespace_adt_names` never compares the declarations — so two
        IDENTICAL declarations are E156/E157.  The diamond cells above are
        refused for another reason: their entry imports only the functions,
        and the value crossing between the two types is the mismatch.

        Pinned so the documentation cannot drift into promising that matching
        layouts make an ambiguous import legal.
        """
        entry = (
            "import liba(aone, Shape);\n"
            "import libb(bone, Shape);\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  bone(aone(6))\n}\n"
        )
        check_errors = refused_multi_module(
            tmp_path / "ambiguous",
            {"liba.vera": _LIBA_RESTATE, "libb.vera": _LIBB_RESTATE,
             "main.vera": entry},
        )
        codes = _codes(check_errors)
        assert "E156" in codes, codes
        assert "E157" in codes, codes

    def test_a_restatement_spelled_through_the_modules_own_alias(
        self, tmp_path: Path,
    ) -> None:
        """A restatement spelled through a module's own alias (§8.4.1) is a
        type of its own like any restatement, and its meeting is refused at
        check (#1694)."""
        libb = (
            "module libb;\n\n"
            "type Count = Int;\n\n"
            "public data Shape { Sq(Count) }\n\n"
            "public fn bone(@Shape -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  match @Shape.0 {\n"
            "    Sq(@Count) -> @Count.0 + 1\n"
            "  }\n"
            "}\n"
        )
        codes, text = _refused_at_check(
            tmp_path / "aliased",
            {"liba.vera": _LIBA_RESTATE, "libb.vera": libb,
             "main.vera": _ENTRY_DIAMOND},
        )
        assert "E202" in codes, codes
        assert "liba.Shape" in text and "libb.Shape" in text, text


_LIBA_DIFFER = """\
module liba;

public data Shape { Sq(Int) }

public fn aone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Sq(@Int.0) {
    Sq(@Int) -> @Int.0
  }
}
"""

_LIBB_DIFFER = """\
module libb;

public data Shape { Cr(Bool) }

public fn bone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Cr(true) {
    Cr(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }
  }
}
"""

_ENTRY_DIFFER = """\
import liba(aone);
import libb(bone);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  aone(3) + bone(4)
}
"""


class TestDifferingShapesAdmittedWhenNothingMeetsThem:
    """What #1317 turned green here, kept in place rather than moved.

    Every cell below is a shape whose two declarations need two layouts and
    could only have one, so the refusal was the flat namespace speaking
    rather than the language.  Each was ``E609`` / ``E610`` on a
    check-green, verify-green program, and each is now compiled under
    per-owner symbols (``mod$<path>$<Name>``) and RUN, because "no longer
    refused" and "right answer" are different claims.

    They stay in this file, opposite :class:`TestMeetingStillRefused`, so
    the boundary between the two is visible in one place: what decides it
    is not the declarations but whether a value of one meets the other.
    ``tests/test_per_owner_adt_identity_1317.py`` holds the full matrix.
    """

    def test_a_selective_import_excluding_the_type_lifts_it(
        self, tmp_path: Path,
    ) -> None:
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "narrow",
            {"liba.vera": _LIBA_DIFFER, "libb.vera": _LIBB_DIFFER,
             "main.vera": _ENTRY_DIFFER},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

    def test_a_private_declaration_lifts_it(
        self, tmp_path: Path,
    ) -> None:
        libb = _LIBB_DIFFER.replace(
            "public data Shape", "private data Shape")
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "private",
            {"liba.vera": _LIBA_DIFFER, "libb.vera": libb,
             "main.vera": _ENTRY_DIFFER},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

    def test_a_local_shadow_lifts_it(
        self, tmp_path: Path,
    ) -> None:
        """The entry declares ``Shape`` too, and can name neither module's:
        the three are three types (#1694) and nothing meets, so the program
        runs.  Before #1694 both modules' declarations were qualified away
        and the entry's left alone in the slot, the one direction in which
        the two rails (E609, E623) interacted.
        """
        entry = _ENTRY_DIFFER.replace(
            "import libb(bone);\n",
            "import libb(bone);\n\nprivate data Shape { Own(Int) }\n",
        )
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "shadow",
            {"liba.vera": _LIBA_DIFFER, "libb.vera": _LIBB_DIFFER,
             "main.vera": entry},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

    def test_two_types_sharing_a_constructor_are_admitted_too(
        self, tmp_path: Path,
    ) -> None:
        """The constructor axis, relaxed in lockstep with the type axis.

        Two DIFFERENT types sharing only the name ``Sq`` contended for the
        one ctor-layout slot; each declaration now carries its owner's
        prefix, constructors included, because §8.5.4 admits a constructor
        by its type's name.
        """
        liba = _LIBA_DIFFER.replace("Shape", "Alpha")
        libb = _LIBB_DIFFER.replace("Shape", "Beta").replace(
            "Cr(Bool)", "Sq(Bool)").replace("Cr(true)", "Sq(true)").replace(
            "Cr(@Bool)", "Sq(@Bool)")
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "ctor",
            {"liba.vera": liba, "libb.vera": libb,
             "main.vera": _ENTRY_DIFFER},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)


class TestMeetingStillRefused:
    """Two owners a value can still MEET (#1694).

    Two same-named cross-module ADTs are two types, so a value crossing
    between them through the signatures a namespace imports is a mismatch
    at check, even under filters that exclude the type.  Before #1694 the
    checker unified them, and with the flow condition removed the program
    answered ``100`` where ``7`` is correct.
    """

    def test_a_value_crossing_between_two_owners_is_refused_at_check(
        self, tmp_path: Path,
    ) -> None:
        liba = _LIBA_DIFFER.replace(
            "public fn aone(@Int -> @Int)", "public fn aone(@Int -> @Shape)",
        ).replace(
            "  match Sq(@Int.0) {\n    Sq(@Int) -> @Int.0\n  }\n",
            "  Sq(@Int.0)\n")
        libb = _LIBB_DIFFER.replace(
            "public data Shape { Cr(Bool) }", "public data Shape { Sq(Bool) }",
        ).replace(
            "public fn bone(@Int -> @Int)", "public fn bone(@Shape -> @Int)",
        ).replace(
            "  match Cr(true) {\n"
            "    Cr(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }\n  }\n",
            "  match @Shape.0 {\n"
            "    Sq(@Bool) -> if @Bool.0 then { 1 } else { 0 }\n  }\n")
        entry = _ENTRY_DIFFER.replace(
            "  aone(3) + bone(4)\n", "  bone(aone(3))\n")
        codes, text = _refused_at_check(
            tmp_path / "meet",
            {"liba.vera": liba, "libb.vera": libb, "main.vera": entry},
        )
        assert "E202" in codes, codes
        assert "liba.Shape" in text and "libb.Shape" in text, text


# =====================================================================
# #1446 — one diagnostic per contended NAME, not one per declarer
# =====================================================================


_THREE_WAY_LIBA = """\
module liba;

public data Shape { Sq(Int) }

public fn aone(@Int -> @Shape)
  requires(true)
  ensures(true)
  effects(pure)
{
  Sq(@Int.0)
}
"""

_THREE_WAY_LIBB = """\
module libb;

public data Shape { Blob(Bool) }

public fn bone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Blob(true) {
    Blob(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }
  }
}
"""

_THREE_WAY_ENTRY = """\
import liba(aone);
import libb(bone);

private data Shape { Own(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match aone(6) {
    Own(@Int) -> @Int.0
  } + bone(1)
}
"""


class TestOneDiagnosticPerContendedName:
    """One conflict, one diagnostic (#1446, #1694).

    E623 walked the declarers of a contended name and emitted one
    diagnostic per module, so a name held by the entry and two modules
    arrived as a first error plus a cascade.  Since #1694 each declaration
    is a type of its own and the refusal is the meeting itself: the one
    value that crosses is the one diagnostic, and a declaration nothing
    meets is refused nothing.
    """

    def test_the_one_meeting_is_the_one_refusal(self, tmp_path: Path) -> None:
        """The entry meets ``liba`` through ``aone``'s return type, and that
        meeting is the refusal, at check (#1694); ``libb``'s own type meets
        nothing and is refused nothing."""
        codes, text = _refused_at_check(
            tmp_path / "three-way",
            {"liba.vera": _THREE_WAY_LIBA, "libb.vera": _THREE_WAY_LIBB,
             "main.vera": _THREE_WAY_ENTRY},
        )
        assert "E314" in codes, codes
        assert "liba.Shape" in text, text
        assert "libb" not in text, text

    def test_the_two_way_private_case_reports_nothing(
        self, tmp_path: Path,
    ) -> None:
        """One module's private type beside the entry's own of its name:
        two types, nothing meets, nothing is reported."""
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "two-way",
            {"blib.vera": _BLIB_OWN_JSON, "main.vera": _ENTRY_OWN_JSON},
        )
        assert [d.error_code for d in result.diagnostics] == []
        assert cg_errors == [], cg_errors
