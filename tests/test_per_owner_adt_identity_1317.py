"""#1317 / #187 (data half) — per-owner ADT identity.

Codegen keys every ADT registry by BARE name — layouts, constructor
layouts, type-parameter metadata, the structural-``Eq`` helper namer, the
declaration index, the export table — so two modules declaring
``data Shape`` contended for one slot and E609/E610 refused the pair by
DECLARATION: no visibility gate, no import-filter gate, no shadowing
relaxation.  #1317 measured the consequence — there was no data-side escape
hatch at all, and renaming in a dependency's source was the only remedy —
and #187 named the mechanism that closes it.

The fix is one rename, in one place.  A CONTENDED module declaration and
its constructors are renamed to ``mod$<path>$<Name>`` at absorb time
(``CrossModuleMixin._register_modules``), inside every namespace that can
name them, so ADT identity is ``(owner, name)`` BY CONSTRUCTION and each of
the downstream registries is correct without knowing the rule exists.  That
is the #1029 device applied to the data namespace, and the reason the fix
is not a per-owner lookup threaded through every name-keyed consumer.

**What still refuses, and why each is not an oversight.**

* **Two suppliers.**  A name two of one namespace's imports both supply is
  ambiguous, and §8.5.2.2 refuses it rather than picking (E156 at check,
  E609/E610 as the codegen backstop).  Nothing is renamed for such a name.
* **A flow.**  Two owners' declarations can MEET in a namespace that can
  name neither, because a value crosses between them through the
  signatures it imports: with ``liba::aone(@Int -> @Shape)`` and
  ``libb::bone(@Shape -> @Int)``, an entry may write ``bone(aone(6))``
  even under filters that exclude the type, because the checker unifies
  two same-named cross-module ADTs.  Measured with the rename in place and
  the flow condition removed: a check-green, verify-green program
  returning ``100`` where ``7`` is the answer — a silent wrong answer, and
  strictly worse than the refusal it replaced.  :class:`TestMeeting` is
  that measurement, kept.
* **A prelude name.**  Maintainer ruling R7: ``Option``, ``Result``,
  ``Ordering`` and every name the prelude can provide stay E621's, exactly
  as built-in function names stay E151's, effect names E152's and built-in
  ADT names E158's.  Per-owner identity is a rule between USER modules.
* **The entry's own declaration.**  Its contention with a module's is
  E623's (#1312) and that rail is untouched — see
  :class:`TestTheEntryIsNotAParty` for the one direction in which the two
  interact.
"""
from __future__ import annotations

from pathlib import Path

import pytest

from vera.codegen.core import CodeGenerator
from vera.parser import parse_file
from vera.resolver import ModuleResolver
from vera.transform import transform

from tests.module_fixture_helpers import build_multi_module, module_value

# =====================================================================
# Fixtures
# =====================================================================

# Two modules declaring an INCOMPATIBLE `Shape`, each using only its own,
# and each exporting a function whose signature mentions neither.  That last
# property is what makes the pair provably distinct: no namespace can meet
# them, by name or by flow.
_LIBA = """\
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

_LIBB = """\
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

_ENTRY = """\
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

_LIBB_PRIVATE = _LIBB.replace("public data Shape", "private data Shape")

_ENTRY_LOCAL = _ENTRY.replace(
    "import libb(bone);\n",
    "import libb(bone);\n\nprivate data Shape { Own(Int) }\n",
)

_ENTRY_NAMES_LIBA = _ENTRY.replace(
    "import liba(aone);", "import liba(aone, Shape);")


def _codes(errors: list[tuple[str, str]]) -> list[str]:
    return sorted({code for code, _ in errors})


def _cell(
    tmp_path: Path, files: dict[str, str],
) -> tuple[list[str], list[str], tuple[str, object]]:
    """``(verify codes, codegen codes, runtime answer)`` for one program.

    All three together, deliberately: a namespace defect shows up as a
    clean verify beside a wrong value at least as often as it shows up as a
    diagnostic, and a cell that reads one stream alone cannot see it.
    """
    verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
    codes = _codes(cg_errors)
    answer: tuple[str, object] = (
        ("no-run", "compilation had errors") if codes
        else module_value(result)
    )
    return _codes(verify_errors), codes, answer


def _generator(tmp_path: Path, files: dict[str, str]) -> CodeGenerator:
    """Compile ``main.vera`` and hand back the generator itself.

    For the registry differential below, which asks the compiler's own
    tables what a name denotes rather than inferring it from the output.
    """
    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    program = transform(parse_file(str(main_path)))
    mods = ModuleResolver(tmp_path).resolve_imports(program, main_path)
    gen = CodeGenerator(
        source=main_path.read_text(encoding="utf-8"), file=str(main_path),
    )
    gen._resolved_modules = mods
    gen._result = gen.compile_program(program)  # type: ignore[attr-defined]
    return gen


# =====================================================================
# #1317's three measured remedies, verbatim from the issue
# =====================================================================


class TestTheThreeRemedies:
    """The three escape hatches #1317 measured as NOT working.

    Each was ``E609`` at ``release/v0.1.12`` and at ``release/v0.2.0``
    before this change, on a program `vera check` and `vera verify` both
    passed.  They are the issue's own RED cells, and each is asserted
    through to the runtime value — ``aone(3) + bone(4)`` is 7 — because
    "no longer refused" and "right answer" are different claims.
    """

    def test_a_selective_import_excluding_the_type(
        self, tmp_path: Path,
    ) -> None:
        """#1317 measurement 1: the filter that resolves a function clash
        did nothing for data."""
        verify, codes, answer = _cell(
            tmp_path / "narrow",
            {"liba.vera": _LIBA, "libb.vera": _LIBB, "main.vera": _ENTRY},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer

    def test_a_local_declaration_in_the_importer(
        self, tmp_path: Path,
    ) -> None:
        """#1317 measurement 2: the shadowing §8.5.4 describes for names
        did not lift the collision.

        E623 is silent here too, and correctly: the entry can name neither
        module's ``Shape``, so once both are qualified there is no pair
        left for the entry-versus-module rail to report.
        """
        verify, codes, answer = _cell(
            tmp_path / "local",
            {"liba.vera": _LIBA, "libb.vera": _LIBB,
             "main.vera": _ENTRY_LOCAL},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer

    def test_a_merely_private_namesake(self, tmp_path: Path) -> None:
        """#1317 measurement 3: a declaration invisible to every importer
        still collided."""
        verify, codes, answer = _cell(
            tmp_path / "private",
            {"liba.vera": _LIBA, "libb.vera": _LIBB_PRIVATE,
             "main.vera": _ENTRY},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer

    def test_one_module_may_keep_the_bare_name(self, tmp_path: Path) -> None:
        """The asymmetric case, and the one that shows what "keeps" means.

        The entry imports ``liba``'s ``Shape`` by name, so ``liba``'s
        declaration must keep the spelling the entry writes — the ENTRY
        program is never rewritten.  ``libb``'s is qualified away.
        """
        verify, codes, answer = _cell(
            tmp_path / "keeper",
            {"liba.vera": _LIBA, "libb.vera": _LIBB,
             "main.vera": _ENTRY_NAMES_LIBA},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer

    def test_the_keeper_is_the_declaration_the_entry_names(
        self, tmp_path: Path,
    ) -> None:
        """And it is ``liba``'s, not whichever module resolved first."""
        gen = _generator(
            tmp_path / "keeper-sym",
            {"liba.vera": _LIBA, "libb.vera": _LIBB,
             "main.vera": _ENTRY_NAMES_LIBA},
        )
        assert "Shape" in gen._adt_layouts, sorted(gen._adt_layouts)
        assert gen._adt_layout_owners.get("Shape") == ("liba",)
        assert "mod$libb$Shape" in gen._adt_layouts, sorted(gen._adt_layouts)
        assert "mod$liba$Shape" not in gen._adt_layouts


# =====================================================================
# Two user modules, one entry, both used — the issue's headline shape
# =====================================================================


class TestTwoOwnersOneEntry:
    """Two modules each declaring ``data Shape``, both imported and both
    used by an entry that names neither type."""

    def test_each_module_keeps_its_own_layout(self, tmp_path: Path) -> None:
        gen = _generator(
            tmp_path / "two",
            {"liba.vera": _LIBA, "libb.vera": _LIBB, "main.vera": _ENTRY},
        )
        assert "mod$liba$Shape" in gen._adt_layouts
        assert "mod$libb$Shape" in gen._adt_layouts
        assert list(gen._adt_layouts["mod$liba$Shape"]) == ["mod$liba$Sq"]
        assert list(gen._adt_layouts["mod$libb$Shape"]) == ["mod$libb$Cr"]

    def test_the_bare_name_is_left_to_nobody(self, tmp_path: Path) -> None:
        """No keeper, so no registry anywhere holds the bare spelling.

        The sweep is over EVERY dict the generator carries, not a list of
        the registries this change happened to think about: a consumer left
        unrewritten is exactly the failure the rename exists to make
        impossible, and enumerating the ones we remembered would measure
        the memory rather than the property.
        """
        gen = _generator(
            tmp_path / "bare",
            {"liba.vera": _LIBA, "libb.vera": _LIBB, "main.vera": _ENTRY},
        )
        stale = {"Shape", "Sq", "Cr"}
        for attr, value in vars(gen).items():
            if not isinstance(value, dict):
                continue
            hits = stale & {k for k in value if isinstance(k, str)}
            assert not hits, f"{attr} still keys the bare name(s) {hits}"

    def test_the_emitted_module_names_both_owners(
        self, tmp_path: Path,
    ) -> None:
        """The WAT carries two owner-qualified symbol families, not one.

        Asserted on the OUTPUT as well as on the registries, because the
        registries are only emission's INPUT: a rename that stopped at the
        tables would leave the two bodies sharing one emitted helper.  The
        structural-``Eq`` namer is the ADT-derived symbol a program can
        force into the WAT, so both modules compare their own value and
        both helpers must appear.
        """
        liba = _LIBA.replace(
            "  match Sq(@Int.0) {\n    Sq(@Int) -> @Int.0\n  }\n",
            "  if Sq(@Int.0) == Sq(@Int.0) then { @Int.0 } else { 0 }\n")
        libb = _LIBB.replace(
            "  match Cr(true) {\n"
            "    Cr(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }\n  }\n",
            "  if Cr(true) == Cr(true) then { @Int.0 } else { 0 }\n")
        gen = _generator(
            tmp_path / "wat",
            {"liba.vera": liba, "libb.vera": libb, "main.vera": _ENTRY},
        )
        helpers = sorted(gen._adt_eq_helpers)
        assert any("liba" in name for name in helpers), helpers
        assert any("libb" in name for name in helpers), helpers
        wat = gen._result.wat  # type: ignore[attr-defined]
        for name in helpers:
            if "liba" in name or "libb" in name:
                assert name in wat, (name, helpers)
        assert module_value(
            gen._result,  # type: ignore[attr-defined]
        ) == ("ok", 7)


# =====================================================================
# The prelude is exempt — maintainer ruling R7
# =====================================================================


_PRELUDE_A = """\
module liba;

public data Option { Nothing, Just(Int) }

public fn aone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Just(@Int.0) {
    Nothing -> 0,
    Just(@Int) -> @Int.0
  }
}
"""

_PRELUDE_B = """\
module libb;

public data Option { Zilch, Only(Bool) }

public fn bone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Only(true) {
    Zilch -> 0,
    Only(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }
  }
}
"""


class TestThePreludeIsReserved:
    """R7: a module ``data`` named after a prelude ADT stays E621's.

    Per-owner ADT identity is a rule between USER modules.  The prelude's
    names are reserved exactly as built-in function names are (E151),
    built-in effect names (E152) and built-in ADT names (E158) — so the
    rename must hold back from them, or it would dissolve the very pairs
    E621 exists to refuse.
    """

    def test_two_modules_declaring_a_prelude_name_stay_e621(
        self, tmp_path: Path,
    ) -> None:
        _verify, codes, _answer = _cell(
            tmp_path / "prelude",
            {"liba.vera": _PRELUDE_A, "libb.vera": _PRELUDE_B,
             "main.vera": _ENTRY},
        )
        assert "E621" in codes, codes

    def test_a_single_module_declaring_a_prelude_name_stays_e621(
        self, tmp_path: Path,
    ) -> None:
        """The other direction: nothing to contend with among modules, so
        the rename has no reason to fire — and E621 still does."""
        entry = _ENTRY.replace("import libb(bone);\n", "").replace(
            " + bone(4)", " + 4")
        _verify, codes, _answer = _cell(
            tmp_path / "prelude-one",
            {"liba.vera": _PRELUDE_A, "main.vera": entry},
        )
        assert "E621" in codes, codes

    def test_the_same_shape_under_a_user_name_is_admitted(
        self, tmp_path: Path,
    ) -> None:
        """The control that isolates the RESERVATION from the shapes.

        Byte-identical declarations to the E621 cell above, renamed to a
        name the prelude does not own: it compiles and runs, so what
        refuses the pair above is the prelude's ownership of ``Option``
        and nothing else about those two declarations.
        """
        files = {
            "liba.vera": _PRELUDE_A.replace("Option", "Maybe"),
            "libb.vera": _PRELUDE_B.replace("Option", "Maybe"),
            "main.vera": _ENTRY,
        }
        _verify, codes, answer = _cell(tmp_path / "user-name", files)
        assert codes == [], codes
        assert answer == ("ok", 7), answer

    def test_every_reserved_name_is_held_back(self, tmp_path: Path) -> None:
        """Structural, over the LIVE reservation rather than a list here.

        The rename reads the Pass-0.5 built-in snapshot unioned with
        ``prelude_adt_names()`` — the same two sets ``_adt_members_in_scope``
        completes its membership floor from — so a prelude ADT added later
        is reserved without this test being edited.
        """
        import inspect

        from vera.codegen.modules import CrossModuleMixin

        src = inspect.getsource(CrossModuleMixin._contended_adt_renames)
        assert "builtin_adt_names | prelude_adt_names()" in src, src[:400]


# =====================================================================
# A nested module chain
# =====================================================================


_DEEP = """\
module deep;

public data Shape { Sq(Int) }

public fn dtwo(@Shape -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Shape.0 {
    Sq(@Int) -> @Int.0
  }
}
"""

_MID = """\
module mid;

import deep(dtwo, Shape);

public fn mone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  dtwo(Sq(@Int.0))
}
"""

_OTHER = """\
module other;

public data Shape { Cr(Bool) }

public fn oone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Cr(true) {
    Cr(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }
  }
}
"""

_ENTRY_CHAIN = """\
import mid(mone);
import other(oone);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  mone(3) + oone(4)
}
"""


class TestANestedChain:
    """``entry -> mid -> deep`` beside a fourth module declaring the name.

    The case a per-DECLARING-module rewrite cannot handle: ``mid`` neither
    declares ``Shape`` nor is renamed, but it NAMES ``deep``'s — through an
    import that supplies the type and through ``dtwo``'s signature — so its
    references have to move in lockstep with ``deep``'s declaration.  The
    rename is therefore computed per NAMESPACE, from what each namespace
    resolves the bare name to, rather than per declaration.
    """

    def test_the_chain_compiles_and_runs(self, tmp_path: Path) -> None:
        verify, codes, answer = _cell(
            tmp_path / "chain",
            {"deep.vera": _DEEP, "mid.vera": _MID, "other.vera": _OTHER,
             "main.vera": _ENTRY_CHAIN},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer

    def test_the_importer_follows_the_declaring_module(
        self, tmp_path: Path,
    ) -> None:
        """``mid``'s ``Sq`` is ``deep``'s, under ``deep``'s symbol."""
        gen = _generator(
            tmp_path / "chain-sym",
            {"deep.vera": _DEEP, "mid.vera": _MID, "other.vera": _OTHER,
             "main.vera": _ENTRY_CHAIN},
        )
        assert "mod$deep$Shape" in gen._adt_layouts
        assert "mod$other$Shape" in gen._adt_layouts
        assert gen._adt_layout_owners["mod$deep$Shape"] == ("deep",)
        assert gen._adt_layout_owners["mod$other$Shape"] == ("other",)
        # `mid` was rewritten against `deep`'s rename, not given one of its
        # own — it declares nothing.
        assert not any(
            key.startswith("mod$mid$") and key.endswith(("Shape", "Sq"))
            for key in gen._adt_layouts
        )


# =====================================================================
# The constructor axis
# =====================================================================


_ALPHA = _LIBA.replace("Shape", "Alpha")
_BETA = (
    _LIBB.replace("Shape", "Beta")
    .replace("Cr(Bool)", "Sq(Bool)")
    .replace("Cr(true)", "Sq(true)")
    .replace("Cr(@Bool)", "Sq(@Bool)")
)


class TestTheConstructorAxis:
    """Two DIFFERENTLY-named types sharing one constructor spelling.

    The flat constructor registry holds one layout per constructor NAME,
    so ``Alpha { Sq(Int) }`` and ``Beta { Sq(Bool) }`` contended for it
    even though the type names never clash — E610's case, and the reason
    the two axes are asked separately.
    """

    def test_a_shared_constructor_across_two_owners_compiles(
        self, tmp_path: Path,
    ) -> None:
        verify, codes, answer = _cell(
            tmp_path / "ctor",
            {"liba.vera": _ALPHA, "libb.vera": _BETA, "main.vera": _ENTRY},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer

    def test_the_whole_declaration_moves_with_its_constructor(
        self, tmp_path: Path,
    ) -> None:
        """Not just the constructor: §8.5.4 admits a constructor by its
        type's name, so splitting them would leave ``Alpha`` holding a
        constructor it no longer names."""
        gen = _generator(
            tmp_path / "ctor-sym",
            {"liba.vera": _ALPHA, "libb.vera": _BETA, "main.vera": _ENTRY},
        )
        assert list(gen._adt_layouts["mod$liba$Alpha"]) == ["mod$liba$Sq"]
        assert list(gen._adt_layouts["mod$libb$Beta"]) == ["mod$libb$Sq"]
        assert "Alpha" not in gen._adt_layouts
        assert "Beta" not in gen._adt_layouts

    def test_a_nullary_constructor_moves_too(self, tmp_path: Path) -> None:
        """An arity-0 constructor is its own AST node in both expression
        and pattern position, so a walker covering only the applied pair
        would leave a type half-renamed."""
        liba = """\
module liba;

public data Colour { Red, Green(Int) }

public fn aone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Red {
    Red -> @Int.0,
    Green(@Int) -> 0
  }
}
"""
        libb = """\
module libb;

public data Colour { Green(Bool), Red }

public fn bone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Green(true) {
    Red -> 0,
    Green(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }
  }
}
"""
        verify, codes, answer = _cell(
            tmp_path / "nullary",
            {"liba.vera": liba, "libb.vera": libb, "main.vera": _ENTRY},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer


# =====================================================================
# What must NOT be relaxed
# =====================================================================


_FLOW_A = """\
module liba;

public data Shape { Sq(Int), Cr(Int) }

public fn aone(@Int -> @Shape)
  requires(true)
  ensures(true)
  effects(pure)
{
  Sq(@Int.0)
}
"""

_FLOW_B = """\
module libb;

public data Shape { Cr(Int), Sq(Int) }

public fn bone(@Shape -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Shape.0 {
    Sq(@Int) -> @Int.0 + 1,
    Cr(@Int) -> 100
  }
}
"""

_ENTRY_FLOW = """\
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


class TestMeeting:
    """Two owners MEET when a value can cross between them.

    Nameability is not the whole condition, and this class is the
    measurement that says so.  ``Shape`` is in neither import's filter, so
    no namespace can NAME both declarations — yet ``bone(aone(6))``
    type-checks, because the checker unifies two same-named cross-module
    ADTs, and the two declarations differ only in constructor ORDER, so
    the tags disagree.

    Measured with the rename in place and the flow condition removed: a
    check-green, verify-green program compiling to exit 0 and answering
    ``100`` where ``7`` is correct.  A silent wrong answer is worse than
    the refusal it replaced, so the pair stays E609's.
    """

    def test_a_value_flowing_between_two_owners_is_refused(
        self, tmp_path: Path,
    ) -> None:
        _verify, codes, answer = _cell(
            tmp_path / "flow",
            {"liba.vera": _FLOW_A, "libb.vera": _FLOW_B,
             "main.vera": _ENTRY_FLOW},
        )
        assert "E609" in codes, codes
        assert answer == ("no-run", "compilation had errors"), answer

    def test_the_same_two_modules_without_the_flow_are_admitted(
        self, tmp_path: Path,
    ) -> None:
        """Its control, and the one that keeps the condition honest.

        The same two incompatible declarations, with the two signatures
        narrowed to ``@Int -> @Int`` so no value can cross.  If this cell
        were also refused, the flow condition would be measuring the
        declarations rather than the reachability.
        """
        liba = _FLOW_A.replace(
            "public fn aone(@Int -> @Shape)", "public fn aone(@Int -> @Int)",
        ).replace("  Sq(@Int.0)\n", "  match Sq(@Int.0) {\n"
                  "    Sq(@Int) -> @Int.0,\n    Cr(@Int) -> 0\n  }\n")
        libb = _FLOW_B.replace(
            "public fn bone(@Shape -> @Int)", "public fn bone(@Int -> @Int)",
        ).replace("  match @Shape.0 {", "  match Sq(@Int.0) {")
        verify, codes, answer = _cell(
            tmp_path / "no-flow",
            {"liba.vera": liba, "libb.vera": libb, "main.vera": _ENTRY},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 8), answer

    def test_a_flow_spelled_through_the_exporters_own_alias_is_a_flow_too(
        self, tmp_path: Path,
    ) -> None:
        """The surface has to be read through the DECLARING module's
        aliases, not off its spelling.

        A module-local alias is not importable (§8.4.1), so the importer
        can never name ``Sh`` — but ``aone(@Int -> @Sh)`` hands it a
        ``Shape`` all the same.  Measured before the alias closure existed:
        this program compiled clean and answered ``100`` where ``7`` is
        correct, which is the same silent wrong answer as the cell above by
        a route that reads the signature and still misses it.
        """
        liba = _FLOW_A.replace(
            "module liba;\n", "module liba;\n\ntype Sh = Shape;\n",
        ).replace("public fn aone(@Int -> @Shape)",
                  "public fn aone(@Int -> @Sh)")
        libb = _FLOW_B.replace(
            "module libb;\n", "module libb;\n\ntype Sh = Shape;\n",
        ).replace("public fn bone(@Shape -> @Int)",
                  "public fn bone(@Sh -> @Int)").replace(
            "  match @Shape.0 {", "  match @Sh.0 {")
        _verify, codes, answer = _cell(
            tmp_path / "alias-flow",
            {"liba.vera": liba, "libb.vera": libb,
             "main.vera": _ENTRY_FLOW},
        )
        assert "E609" in codes, codes
        assert answer == ("no-run", "compilation had errors"), answer

    def test_a_flow_through_an_imported_adts_field_is_a_flow_too(
        self, tmp_path: Path,
    ) -> None:
        """The surface is not only function signatures.

        ``liba`` exports ``Wrapper { W(Shape) }``, so an importer naming
        ``Wrapper`` can extract a ``Shape`` from it without ever naming the
        type — the same crossing by a different route.
        """
        liba = _FLOW_A + """
public data Wrapper { W(Shape) }
"""
        entry = """\
import liba(aone, Wrapper);
import libb(bone);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match W(aone(6)) {
    W(@Shape) -> bone(@Shape.0)
  }
}
"""
        _verify, codes, _answer = _cell(
            tmp_path / "field-flow",
            {"liba.vera": liba, "libb.vera": _FLOW_B, "main.vera": entry},
        )
        assert "E609" in codes, codes


class TestTheEntryIsNotAParty:
    """E623 (#1312) is untouched, in both directions."""

    def test_one_module_against_the_entry_is_still_e623(
        self, tmp_path: Path,
    ) -> None:
        """Nothing contends among the modules — there is only one — so no
        rename fires and the entry-versus-module rail speaks as before."""
        entry = """\
import liba(aone, Shape);

private data Shape { Own(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  aone(3)
}
"""
        _verify, codes, _answer = _cell(
            tmp_path / "e623",
            {"liba.vera": _LIBA, "main.vera": entry},
        )
        assert "E623" in codes, codes

    def test_the_entrys_declaration_counts_as_an_owner(
        self, tmp_path: Path,
    ) -> None:
        """The direction that would otherwise be a hole.

        The entry declares ``Shape`` AND receives ``liba``'s through
        ``aone``'s return type, while ``libb`` declares a third.  Renaming
        the modules apart would leave E623 with no pair to refuse while the
        entry's own constructors still read ``liba``'s value — so the
        entry's declaration is counted as an owner and the name is not
        renamed at all.
        """
        libb = """\
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
        entry = """\
import liba(aone);
import libb(bone);

private data Shape { Cr(Int), Sq(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match aone(6) {
    Cr(@Int) -> @Int.0,
    Sq(@Int) -> 100
  } + bone(1)
}
"""
        _verify, codes, answer = _cell(
            tmp_path / "entry-owner",
            {"liba.vera": _FLOW_A, "libb.vera": libb, "main.vera": entry},
        )
        assert "E623" in codes, codes
        assert answer == ("no-run", "compilation had errors"), answer


class TestRestatementIsStillNotAContention:
    """The #1312 relaxation is unchanged: identical layouts share the one
    slot, which is why no corpus program's emitted WAT moves."""

    def test_two_modules_restating_one_type_are_not_renamed(
        self, tmp_path: Path,
    ) -> None:
        libb = _LIBA.replace("module liba", "module libb").replace(
            "aone", "bone")
        gen = _generator(
            tmp_path / "restate",
            {"liba.vera": _LIBA, "libb.vera": libb, "main.vera": _ENTRY},
        )
        assert "Shape" in gen._adt_layouts
        assert gen._contended_adt_display_names == {}


# =====================================================================
# The cross-derivation differential
# =====================================================================


_DIFFERENTIAL_FILES = {
    "liba.vera": _LIBA, "libb.vera": _LIBB, "main.vera": _ENTRY,
}


class TestOneSymbolPerOwnerEverywhere:
    """Every consumer asked the same ADT in the same scope answers the
    same symbol.

    The rename's whole claim is that ADT identity becomes ``(owner, name)``
    BY CONSTRUCTION — one rewrite of one AST, ahead of every registration —
    so no consumer needs to know the rule and none can be the one that was
    missed.  The claim is only worth as much as a check that would FAIL if
    one registry were left behind, so it is asserted as a differential over
    the registries rather than as a spot check on the ones this change
    thought about.

    Mutation-validated, and the mutations are recorded with what each one
    actually reached, because they do not all land in the same place:

    * leaving the ``ast.DataDecl`` itself unrenamed while its references
      move — the literal "one registry unrewritten" — turns
      :meth:`test_no_registry_keeps_a_stale_bare_name` and all three
      registry cells red, plus eleven behaviour cells;
    * dropping ``ast.ConstructorPattern`` from the walk turns ten
      BEHAVIOUR cells red and leaves the registry sweep green — a pattern
      name is not a registry key, so the two halves of this class are
      measuring different things and both are needed;
    * rewriting only the DECLARING module turns
      :meth:`TestANestedChain.test_the_chain_compiles_and_runs` red, and
      nothing else;
    * dropping the meeting condition turns :class:`TestMeeting` and
      :meth:`TestTheEntryIsNotAParty
      .test_the_entrys_declaration_counts_as_an_owner` red;
    * lifting the prelude reservation turns
      :class:`TestThePreludeIsReserved` red, along with six cells in
      ``tests/test_prelude_adt_namespace_1277.py``.
    """

    def test_no_registry_keeps_a_stale_bare_name(
        self, tmp_path: Path,
    ) -> None:
        gen = _generator(tmp_path / "diff-keys", _DIFFERENTIAL_FILES)
        renamed_bare = set(gen._contended_adt_display_names.values())
        assert renamed_bare == {"Shape", "Sq", "Cr"}, renamed_bare
        for attr, value in vars(gen).items():
            if not isinstance(value, dict):
                continue
            hits = renamed_bare & {k for k in value if isinstance(k, str)}
            assert not hits, f"{attr} still keys {sorted(hits)}"

    def test_every_registry_that_answers_agrees_on_the_owner(
        self, tmp_path: Path,
    ) -> None:
        """The positive half: for each qualified name, the registries that
        hold an entry for it hold the SAME owner's answer."""
        gen = _generator(tmp_path / "diff-owner", _DIFFERENTIAL_FILES)
        for mangled in ("mod$liba$Shape", "mod$libb$Shape"):
            owner = tuple(mangled.split("$")[1:-1])
            assert gen._adt_layout_owners[mangled] == owner, mangled
            ctors = gen._adt_layouts[mangled]
            assert ctors, mangled
            for ctor in ctors:
                assert ctor.startswith(f"mod${owner[0]}$"), (mangled, ctor)

    def test_the_two_owners_answer_differently(
        self, tmp_path: Path,
    ) -> None:
        """And the differential has two sides to compare.

        A test that only checked "every registry agrees" would pass just as
        well against a program where both owners collapsed onto one symbol
        — the pre-fix behaviour.  The layouts must be DISTINCT objects with
        distinct constructors.
        """
        gen = _generator(tmp_path / "diff-two", _DIFFERENTIAL_FILES)
        a = gen._adt_layouts["mod$liba$Shape"]
        b = gen._adt_layouts["mod$libb$Shape"]
        assert set(a) != set(b), (sorted(a), sorted(b))
        assert gen._adt_layout_owners["mod$liba$Shape"] != (
            gen._adt_layout_owners["mod$libb$Shape"]
        )

    def test_both_bodies_run_against_their_own_layout(
        self, tmp_path: Path,
    ) -> None:
        """The end of the differential: the registries feed emission, and
        emission feeds the answer.  ``aone`` reads an ``Int`` field and
        ``bone`` a ``Bool`` one; a shared layout gives at least one of them
        the wrong width."""
        _verify, codes, answer = _cell(
            tmp_path / "diff-run", _DIFFERENTIAL_FILES)
        assert codes == []
        assert answer == ("ok", 7), answer


# =====================================================================
# The mangled name never reaches the reader
# =====================================================================


class TestTheSymbolIsInternal:
    """#187's own design note, answered: the mangled name is a WASM detail
    and not a spelling the user is asked to know.

    DEFENCE IN DEPTH rather than a rail behind a reachable leak: the
    diagnostics that name an ADT today are the collision rails themselves
    (E609/E610/E621/E623), and a declaration those report on is by
    construction one the rename declined to touch.  It is kept because the
    set of diagnostics that interpolate a type name is not closed — the
    next one to be added would leak without it — and it is pinned directly
    rather than through whichever diagnostic happens to reach it.
    """

    def test_the_strip_uses_the_rename_table_not_a_pattern(
        self, tmp_path: Path,
    ) -> None:
        """So a FUNCTION mangled by #814's rerouting — a different rename
        with its own reporting — is left exactly as it was."""
        from vera.errors import Diagnostic, SourceLocation

        gen = _generator(tmp_path / "unmangle", _DIFFERENTIAL_FILES)
        diag = Diagnostic(
            description="Type 'mod$liba$Shape' and fn 'mod$liba$aone'.",
            location=SourceLocation(file="x.vera"),
            fix="Rename 'mod$libb$Cr'.",
        )
        gen._unmangle_adt_names([diag])
        assert diag.description == "Type 'Shape' and fn 'mod$liba$aone'."
        assert diag.fix == "Rename 'Cr'."

    def test_it_is_a_no_op_without_a_rename(self, tmp_path: Path) -> None:
        from vera.errors import Diagnostic, SourceLocation

        gen = _generator(
            tmp_path / "no-rename",
            {"liba.vera": _LIBA, "main.vera": _ENTRY.replace(
                "import libb(bone);\n", "").replace(" + bone(4)", " + 4")},
        )
        assert gen._contended_adt_display_names == {}
        diag = Diagnostic(
            description="mod$liba$Shape",
            location=SourceLocation(file="x.vera"),
        )
        gen._unmangle_adt_names([diag])
        assert diag.description == "mod$liba$Shape"

    @pytest.mark.parametrize(
        "files",
        [
            _DIFFERENTIAL_FILES,
            {"liba.vera": _ALPHA, "libb.vera": _BETA, "main.vera": _ENTRY},
            {"deep.vera": _DEEP, "mid.vera": _MID, "other.vera": _OTHER,
             "main.vera": _ENTRY_CHAIN},
        ],
        ids=["types", "constructors", "chain"],
    )
    def test_no_diagnostic_of_a_renamed_program_carries_the_symbol(
        self, tmp_path: Path, files: dict[str, str],
    ) -> None:
        gen = _generator(tmp_path / "sweep", files)
        for diag in gen._result.diagnostics:  # type: ignore[attr-defined]
            for attr in ("description", "rationale", "fix"):
                text = getattr(diag, attr, None) or ""
                assert "mod$" not in text, (diag.error_code, attr, text)
