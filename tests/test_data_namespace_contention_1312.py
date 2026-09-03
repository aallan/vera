"""#1312 / #1317 — the data-collision rails, asked about LAYOUTS.

Codegen's ``_adt_layouts`` holds ONE layout per bare name across the whole
program, so two ``data`` declarations of a name can coexist exactly when they
describe the same layout.  Three PAIRS can meet in that slot, and before this
change the rails answered all three differently:

* **module versus prelude** — E621, shape-based since #1277: a module that
  restates the prelude's type shares the slot and compiles.
* **entry file versus module** — nothing at all (#1312).  Pass 1 registers the
  entry file's ``data`` over the Pass-0.5 module harvest, which only
  ``setdefault``s, so the entry's declaration took the slot and the module's
  own constructors became ``unknown constructor`` inside the module's own
  bodies: an ``[E602]`` skip, an ``[E620]`` cascade, both WARNINGS.  A
  `vera check`-green program compiled with **exit 0** to a module whose
  ``main`` was simply absent from the exports.  The prelude rail could not be
  asked about this pair — an entry declaration SUPPRESSES the prelude's
  injection, so no prelude declaration exists to contend with.
* **module versus module** — E609/E610, keyed on PROVENANCE alone (#1317).
  Two modules whose declarations describe the SAME layout were refused
  anyway, and renaming in a dependency's source was the only remedy.

Both are now the same question, asked through the same
:func:`~vera.prelude.data_decl_shape` derivation:

* the entry-versus-module pair is **E623**, an error located at the entry
  declaration naming the module's file and line;
* the module-versus-module pair admits a restatement, with E610 relaxed in
  LOCKSTEP — two modules restating one type share its constructor names too,
  so relaxing E609 alone would close nothing.

What still refuses, and why it is not an oversight: two modules whose
declarations describe DIFFERENT layouts stay E609/E610 whatever the entry
file's import filter, local shadowing, or the declarations' visibility says.
Both modules' BODIES are compiled into the one WASM module (Passes 2.5/2.6)
and each needs its own layout for its own constructor sites; what the ENTRY
can name does not change that.  :class:`TestDifferingShapesStillRefused` pins
those measurements so the claim cannot rot into a relaxation nobody measured.
"""
from __future__ import annotations

from pathlib import Path

import pytest

from vera.errors import ERROR_CODES

from tests.module_fixture_helpers import (
    build_multi_module,
    build_multi_module_past_check,
    module_value,
)


# =====================================================================
# Fixtures
# =====================================================================

_BLIB_OWN_JSON = """\
module blib;

private data Json { JBlob(Int) }

private fn wrap(@Int -> @Json)
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

private data Json { JMine(Int) }

public fn consume(@Json -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Json.0 {
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

# The issue's own repro, verbatim: the module never touches its `Json`, so
# nothing inside it drops — but the two declarations still contend for the
# one slot, and the rail must fire on the DECLARATIONS rather than on the
# wreckage they happen to produce.
_BLIB_UNUSED_JSON = """\
module blib;

private data Json { JBlob(Int) }

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

private data Json { JMine(Int) }

public fn consume(@Json -> @Int)
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


# The two axes a single-constructor fixture cannot reach (PR #1372 review).
# `data_decl_shape` compares an ORDERED tuple of constructors, because the tag
# is the position, and compares type-parameter arity positionally — and every
# other fixture in this file differs in constructor NAMES or FIELD TYPES, or
# matches with one constructor.  A derivation that compared constructor SETS,
# or ignored arity, would pass every one of them.  These two pairs vary only
# the axis named, which is the same discipline a non-commutative operand pair
# needs to catch a slot-order bug.

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
    """E623 where the entry's declaration cannot share the module's layout."""

    def test_differing_shapes_are_refused_not_silently_dropped(
        self, tmp_path: Path,
    ) -> None:
        """Base: exit 0, ``ok: true``, warnings only, ``exports ==
        ['consume']`` — ``main`` silently gone."""
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "differ",
            {"blib.vera": _BLIB_OWN_JSON, "main.vera": _ENTRY_OWN_JSON},
        )
        assert _codes(cg_errors) == ["E623"], cg_errors
        assert not result.ok

    def test_the_issues_own_repro(self, tmp_path: Path) -> None:
        """The issue's fixture verbatim, where the module never touches its
        own ``Json``.

        Measured green at the base — nothing inside the module drops,
        because nothing inside it constructs the type — which is why the
        rail keys on the DECLARATIONS and not on the E602 wreckage.  Its
        sibling above is the shape that loses ``main``.
        """
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "verbatim",
            {"blib.vera": _BLIB_UNUSED_JSON, "main.vera": _ENTRY_UNUSED_JSON},
        )
        assert _codes(cg_errors) == ["E623"], cg_errors
        assert not result.ok

    def test_it_is_located_at_the_entry_declaration(
        self, tmp_path: Path,
    ) -> None:
        """One diagnostic, at the declaration whose registration wins the
        slot, naming the module's own file and line so the other half is
        reachable."""
        _verr, result, _cg = build_multi_module(
            tmp_path / "located",
            {"blib.vera": _BLIB_OWN_JSON, "main.vera": _ENTRY_OWN_JSON},
        )
        diag = next(d for d in result.diagnostics if d.error_code == "E623")
        assert diag.severity == "error"
        assert diag.location.file is not None
        assert diag.location.file.endswith("main.vera")
        assert diag.location.line == 3, diag.location.line
        assert "private data Json" in diag.source_line
        assert "blib" in diag.description
        assert "blib.vera:3" in diag.description
        assert diag.rationale and diag.fix and diag.spec_ref

    def test_identical_shapes_stay_legal_and_run(self, tmp_path: Path) -> None:
        """The relaxation the rail must not break: an entry file restating a
        module's public type is served by the one registered layout, and the
        program compiles and runs."""
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "restate",
            {"blib.vera": _SHARED_SHAPE_MODULE,
             "main.vera": _ENTRY_RESTATES_SHAPE},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

    def test_an_entry_declaration_no_module_shares_is_untouched(
        self, tmp_path: Path,
    ) -> None:
        """Control: the rail fires on a CONTENDED name, not on any entry
        ``data`` in a program that happens to import something."""
        entry = _ENTRY_OWN_JSON.replace("Json", "Zbox").replace(
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
        """The tag IS the position, so swapping two constructors is a
        different layout even though the names and field types match.

        The axis no other cell in this file varies: every other differing
        pair also differs in constructor names or field types, and every
        matching pair has a single constructor — so a `data_decl_shape` that
        compared constructor SETS would pass all of them and fail only here.
        """
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "order",
            {"blib.vera": _MODULE_TWO_CTORS,
             "main.vera": _ENTRY_SWAPPED_ORDER},
        )
        assert _codes(cg_errors) == ["E623"], cg_errors
        assert not result.ok

    def test_the_same_two_constructors_in_the_same_order_still_share(
        self, tmp_path: Path,
    ) -> None:
        """The control that makes the cell above mean something.

        Without it, "swapped order is refused" would also be satisfied by a
        rail that refused every two-constructor declaration.
        """
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "order-ok",
            {"blib.vera": _MODULE_TWO_CTORS,
             "main.vera": _ENTRY_SAME_ORDER},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

    def test_type_parameter_ARITY_alone_is_a_different_layout(
        self, tmp_path: Path,
    ) -> None:
        """The second axis a single-constructor fixture cannot reach: same
        constructor, same field type, different declared arity."""
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "arity",
            {"blib.vera": _MODULE_ARITY_ONE, "main.vera": _ENTRY_ARITY_ZERO},
        )
        assert _codes(cg_errors) == ["E623"], cg_errors
        assert not result.ok

    def test_the_code_is_registered(self) -> None:
        assert "E623" in ERROR_CODES
        assert ERROR_CODES["E623"]


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

    def test_the_restatement_diamond_compiles_and_runs(
        self, tmp_path: Path,
    ) -> None:
        """Base: ``[E609] Name collision: ADT type`` at compile, on a
        check-green, verify-green program, with renaming in a dependency's
        source as the only remedy."""
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "diamond",
            {"liba.vera": _LIBA_RESTATE, "libb.vera": _LIBB_RESTATE,
             "main.vera": _ENTRY_DIAMOND},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

    def test_e610_is_relaxed_in_lockstep(self, tmp_path: Path) -> None:
        """The restatement shares CONSTRUCTOR names too.

        Relaxing E609 alone would close nothing — E610 would refuse exactly
        the programs E609 just admitted — so this asserts on the code, not
        merely on the absence of E609.
        """
        _verr, _result, cg_errors = build_multi_module(
            tmp_path / "lockstep",
            {"liba.vera": _LIBA_RESTATE, "libb.vera": _LIBB_RESTATE,
             "main.vera": _ENTRY_DIAMOND},
        )
        assert "E610" not in _codes(cg_errors), cg_errors

    def test_constructor_ORDER_alone_refuses_the_module_pair_too(
        self, tmp_path: Path,
    ) -> None:
        """The same axis on the E609 rail, so the three rails cannot drift
        apart on the question they all delegate to `data_decl_shape`."""
        liba = _LIBA_RESTATE.replace(
            "public data Shape { Sq(Int) }",
            "public data Shape { Sq(Int), Cr(Int) }")
        libb = _LIBB_RESTATE.replace(
            "public data Shape { Sq(Int) }",
            "public data Shape { Cr(Int), Sq(Int) }").replace(
            "    Sq(@Int) -> @Int.0 + 1\n",
            "    Sq(@Int) -> @Int.0 + 1,\n    Cr(@Int) -> 0\n")
        _verr, _result, cg_errors = build_multi_module(
            tmp_path / "mod-order",
            {"liba.vera": liba, "libb.vera": libb,
             "main.vera": _ENTRY_DIAMOND},
        )
        assert "E609" in _codes(cg_errors), cg_errors

    def test_the_same_two_constructors_in_the_same_order_share_the_slot(
        self, tmp_path: Path,
    ) -> None:
        """Its control, for the same reason as on the entry rail."""
        both = _LIBA_RESTATE.replace(
            "public data Shape { Sq(Int) }",
            "public data Shape { Sq(Int), Cr(Int) }")
        libb = _LIBB_RESTATE.replace(
            "public data Shape { Sq(Int) }",
            "public data Shape { Sq(Int), Cr(Int) }").replace(
            "    Sq(@Int) -> @Int.0 + 1\n",
            "    Sq(@Int) -> @Int.0 + 1,\n    Cr(@Int) -> 0\n")
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "mod-order-ok",
            {"liba.vera": both, "libb.vera": libb,
             "main.vera": _ENTRY_DIAMOND},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)

    def test_both_imports_supplying_the_name_is_still_ambiguous(
        self, tmp_path: Path,
    ) -> None:
        """Sharing a layout settles COMPILATION, not SCOPE (PR #1372 review).

        The E609/E610 relaxation is a compile-phase rail.  Where both imports
        actually supply the bare name, §8.5.2.2's ambiguity refusal applies
        first and independently of the layouts — `namespace_adt_names` never
        compares them — so two IDENTICAL declarations are still E156/E157 at
        check.  The diamond cells above pass because the entry imports only
        the functions, naming the type through neither.

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
        check_errors, _result, _cg = build_multi_module_past_check(
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
        """Each declaration's field types resolve through ITS OWN module's
        aliases (§8.4.1), so a restatement spelled through a local alias is
        still a restatement.

        This is what makes the alias-map capture's POSITION load-bearing: it
        now runs before the ADT harvest, where the shape comparison reads it.
        Captured after, ``libb``'s own maps were still empty when its
        declaration was compared and the program was refused.
        """
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
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "aliased",
            {"liba.vera": _LIBA_RESTATE, "libb.vera": libb,
             "main.vera": _ENTRY_DIAMOND},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 7)


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


class TestDifferingShapesStillRefused:
    """The measurements behind #1317's residual, pinned.

    Every cell here is a shape whose two declarations need two layouts and
    can have one, so the refusal is the mechanism speaking and not a
    conservative rail.  Lifting them needs per-owner ADT layouts and
    per-owner CONSTRUCTOR symbols — the ADT analogue of the ``mod$…``
    function rerouting — which is a separate change; these cells are what
    would go green when it lands, so they are written to fail loudly rather
    than to be quietly deleted.
    """

    def test_a_selective_import_excluding_the_type_does_not_lift_it(
        self, tmp_path: Path,
    ) -> None:
        _verr, _result, cg_errors = build_multi_module(
            tmp_path / "narrow",
            {"liba.vera": _LIBA_DIFFER, "libb.vera": _LIBB_DIFFER,
             "main.vera": _ENTRY_DIFFER},
        )
        assert "E609" in _codes(cg_errors), cg_errors

    def test_a_private_declaration_does_not_lift_it(
        self, tmp_path: Path,
    ) -> None:
        libb = _LIBB_DIFFER.replace(
            "public data Shape", "private data Shape")
        _verr, _result, cg_errors = build_multi_module(
            tmp_path / "private",
            {"liba.vera": _LIBA_DIFFER, "libb.vera": libb,
             "main.vera": _ENTRY_DIFFER},
        )
        assert "E609" in _codes(cg_errors), cg_errors

    def test_a_local_shadow_does_not_lift_it(self, tmp_path: Path) -> None:
        """And the entry's own declaration meets BOTH modules', so the #1312
        rail speaks here too — the two rails coexist on one program."""
        entry = _ENTRY_DIFFER.replace(
            "import libb(bone);\n",
            "import libb(bone);\n\nprivate data Shape { Own(Int) }\n",
        )
        _verr, _result, cg_errors = build_multi_module(
            tmp_path / "shadow",
            {"liba.vera": _LIBA_DIFFER, "libb.vera": _LIBB_DIFFER,
             "main.vera": entry},
        )
        assert "E609" in _codes(cg_errors), cg_errors
        assert "E623" in _codes(cg_errors), cg_errors

    def test_two_types_sharing_a_constructor_stay_e610(
        self, tmp_path: Path,
    ) -> None:
        """The constructor axis: two DIFFERENT types sharing only the name
        ``Sq`` still contend for the one ctor-layout slot."""
        liba = _LIBA_DIFFER.replace("Shape", "Alpha")
        libb = _LIBB_DIFFER.replace("Shape", "Beta").replace(
            "Cr(Bool)", "Sq(Bool)").replace("Cr(true)", "Sq(true)").replace(
            "Cr(@Bool)", "Sq(@Bool)")
        _verr, _result, cg_errors = build_multi_module(
            tmp_path / "ctor",
            {"liba.vera": liba, "libb.vera": libb,
             "main.vera": _ENTRY_DIFFER},
        )
        assert "E610" in _codes(cg_errors), cg_errors


@pytest.mark.parametrize("builder", [build_multi_module])
def test_the_three_rails_share_one_shape_derivation(
    builder: object, tmp_path: Path,
) -> None:
    """Prelude-vs-module (E621), entry-vs-module (E623) and module-vs-module
    (E609) all decide compatibility with ``data_decl_shape``.

    Asserted structurally rather than by three separate behaviour cells: a
    second copy of "can one layout serve both" is a second thing to keep in
    step, and the three rails would then be free to disagree about which
    declarations are compatible.
    """
    import inspect

    from vera.codegen.core import CodeGenerator
    from vera.codegen.modules import CrossModuleMixin

    sources = [
        inspect.getsource(CodeGenerator._contends_with_prelude),
        inspect.getsource(CodeGenerator._check_entry_module_adt_contention),
        inspect.getsource(CrossModuleMixin._adt_decls_share_a_layout),
    ]
    for src in sources:
        assert "data_decl_shape" in src, src[:200]


def test_a_past_check_program_still_reaches_the_rail(tmp_path: Path) -> None:
    """The codegen rails must keep refusing a shape the CHECKER also refuses.

    A rail nothing exercises can rot into a relaxation nobody measures, so
    the ambiguous-import shape — which #1304 moved to the checker — is driven
    through the codegen door too.
    """
    entry = """\
import liba(Shape);
import libb(Shape);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""
    check_errors, _result, cg_errors = build_multi_module_past_check(
        tmp_path / "past",
        {"liba.vera": _LIBA_DIFFER, "libb.vera": _LIBB_DIFFER,
         "main.vera": entry},
    )
    assert check_errors, "the checker accepted an ambiguous data import"
    assert "E609" in _codes(cg_errors), cg_errors
