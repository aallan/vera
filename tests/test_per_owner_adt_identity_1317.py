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

from tests.module_fixture_helpers import (
    build_multi_module,
    build_multi_module_past_check,
    module_value,
)

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

    Resolution failures and codegen errors are ASSERTED, not returned (PR
    review).  ``resolve_imports`` records an unresolved import in
    ``resolver.errors`` and returns whatever it did resolve, so a fixture
    with a mistyped module name quietly becomes a single-file program —
    and every cell here would then ask an empty registry a question it
    answers vacuously.  Each of this helper's callers builds a
    compile-clean fixture by construction, so either failure means the
    FIXTURE is broken rather than the compiler.
    """
    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    program = transform(parse_file(str(main_path)))
    resolver = ModuleResolver(tmp_path)
    mods = resolver.resolve_imports(program, main_path)
    resolve_errors = [d.description for d in resolver.errors]
    assert not resolve_errors, f"module resolution errors: {resolve_errors}"
    assert len(mods) == len(files) - 1, (
        f"expected {len(files) - 1} resolved modules, got "
        f"{[m.path for m in mods]}"
    )
    gen = CodeGenerator(
        source=main_path.read_text(encoding="utf-8"), file=str(main_path),
    )
    gen._resolved_modules = mods
    result = gen.compile_program(program)
    cg_errors = [
        (d.error_code, d.description)
        for d in result.diagnostics if d.severity == "error"
    ]
    assert not cg_errors, f"codegen errors: {cg_errors}"
    gen._result = result  # type: ignore[attr-defined]
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
    """R7: a prelude name bypasses the RENAME, and E621 decides it
    unchanged.

    Per-owner ADT identity is a rule between USER modules, so the rename
    holds back from every name the prelude can provide — otherwise it would
    dissolve the very pairs E621 exists to refuse.  What the exemption is
    NOT is a ban on the name: E621 is a CONTENTION check, and a module
    restating the prelude's exact shape shares the one layout and compiles.
    ``examples/vera/collections.vera`` is that shape in this repository —
    a module declaring ``public data Option<T> { None, Some(T) }`` that
    ``examples/modules.vera`` imports — so a blanket refusal would refuse a
    shipped example.  :meth:`test_a_module_restating_the_prelude_still_
    compiles` is the cell that keeps the two apart.
    """

    def test_a_module_restating_the_prelude_still_compiles(
        self, tmp_path: Path,
    ) -> None:
        """The half a blanket refusal would break.

        ``liba`` declares the prelude's ``Option`` with the prelude's own
        shape, beside a module whose unrelated ``Shape`` is not contended
        at all.  E621 is silent — the single registered layout serves both
        declarations — and the program runs.  Read against the two cells
        below, this is what shows the exemption withholds the RENAME and
        leaves E621's shape test to decide, rather than refusing the name.
        """
        liba = """\
module liba;

public data Option<T> { None, Some(T) }

public fn aone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(@Int.0) {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        verify, codes, answer = _cell(
            tmp_path / "restate-prelude",
            {"liba.vera": liba, "libb.vera": _LIBB, "main.vera": _ENTRY},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer

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
        """MEASURED over the LIVE reservation, not grepped (PR review).

        An earlier version of this cell asserted that the source of
        ``_contended_adt_renames`` contained the string
        ``builtin_adt_names | prelude_adt_names()`` — which tests the
        spelling of one line and would stay green through any change that
        computed the set and then ignored it.  This drives the rename
        itself, once per name the prelude can provide, and asserts each is
        left in the bare slot: two modules declaring it differently reach
        E621 rather than being qualified apart.

        Parameterless over the LIVE set, so a prelude ADT added later is
        covered without this cell being edited.  Mutation: replacing
        ``reserved`` with an empty frozenset reds every name here.
        """
        from vera.prelude import prelude_adt_names

        reserved = sorted(prelude_adt_names())
        assert reserved, "the prelude declares no ADTs — the set is empty"
        checked = 0
        for name in reserved:
            liba = f"""\
module liba;

public data {name} {{ ZzOnlyA(Int) }}

public fn aone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match ZzOnlyA(@Int.0) {{
    ZzOnlyA(@Int) -> @Int.0
  }}
}}
"""
            libb = f"""\
module libb;

public data {name} {{ ZzOnlyB(Bool) }}

public fn bone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match ZzOnlyB(true) {{
    ZzOnlyB(@Bool) -> if @Bool.0 then {{ @Int.0 }} else {{ 0 }}
  }}
}}
"""
            _verify, _result, cg_errors = build_multi_module(
                tmp_path / f"reserved-{name}",
                {"liba.vera": liba, "libb.vera": libb, "main.vera": _ENTRY},
            )
            codes = _codes(cg_errors)
            # Every prelude name must refuse this pair rather than qualify
            # it apart.  Which CODE depends on whether the program demands
            # the block (`Json`, `HtmlNode`, `Request`, `Response` inject
            # only on demand, so an undemanded one falls to the ordinary
            # module-versus-module rail); what is asserted is that the pair
            # is REFUSED, never renamed.
            assert codes, f"{name}: qualified apart instead of refused"
            assert set(codes) <= {"E609", "E610", "E621"}, (name, codes)
            checked += 1
        assert checked == len(reserved)

    def test_a_fresh_name_in_the_same_shape_is_admitted(
        self, tmp_path: Path,
    ) -> None:
        """The control for the cell above, so "refused" is a property of
        the RESERVATION and not of the shape those fixtures happen to
        have."""
        liba = """\
module liba;

public data ZzFreshName { ZzOnlyA(Int) }

public fn aone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match ZzOnlyA(@Int.0) {
    ZzOnlyA(@Int) -> @Int.0
  }
}
"""
        libb = """\
module libb;

public data ZzFreshName { ZzOnlyB(Bool) }

public fn bone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match ZzOnlyB(true) {
    ZzOnlyB(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }
  }
}
"""
        verify, codes, answer = _cell(
            tmp_path / "fresh",
            {"liba.vera": liba, "libb.vera": libb, "main.vera": _ENTRY},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer


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

    def test_a_restatement_spelled_through_an_alias_is_not_renamed(
        self, tmp_path: Path,
    ) -> None:
        """The rename asks the shape question with the SAME inputs the
        other three rails are given (PR review).

        §8.4.1 makes an alias module-local, so ``type Count = Int;`` beside
        ``data Shape { Sq(Count) }`` is a restatement of ``Sq(Int)`` and
        the one registered layout serves both.  The decision runs at the
        top of ``_register_modules``, BEFORE the harvest fills
        ``_module_type_aliases`` — so reading the shape from those maps
        compared the two declarations through empty ones, called an
        equivalent restatement contended, and renamed it apart while
        ``_adt_decls_share_a_layout`` (which sees the populated maps) would
        have called the same pair compatible.  Measured: two layouts,
        ``mod$liba$Shape`` and ``mod$libb$Shape``, where one belongs.

        No FLOW between the two modules, deliberately: with one
        (``aone(@Int -> @Shape)`` into ``bone(@Shape -> @Int)``, which is
        #1312's diamond) the meeting condition refuses the rename for its
        own reason and the cell would pass without the shape question ever
        being asked correctly.
        """
        libb = """\
module libb;

type Count = Int;

public data Shape { Sq(Count) }

public fn bone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Sq(@Int.0) {
    Sq(@Count) -> @Count.0
  }
}
"""
        gen = _generator(
            tmp_path / "alias-restate",
            {"liba.vera": _LIBA, "libb.vera": libb, "main.vera": _ENTRY},
        )
        assert gen._contended_adt_display_names == {}
        assert "Shape" in gen._adt_layouts
        assert not [k for k in gen._adt_layouts if k.startswith("mod$")]
        assert module_value(
            gen._result,  # type: ignore[attr-defined]
        ) == ("ok", 7)


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

    def test_every_owner_still_has_an_entry(self, tmp_path: Path) -> None:
        """The sweep's other half: nothing was DROPPED (PR review).

        Asserting only that no stale bare key survives is satisfied just as
        well by a rename that registered nothing at all — the entry would
        simply be missing, and every "is the bare name gone" assertion
        would pass.  So the qualified names are counted too: one layout per
        renamed TYPE, and one constructor entry per renamed constructor,
        with the constructor-to-owner map agreeing.
        """
        gen = _generator(tmp_path / "diff-count", _DIFFERENTIAL_FILES)
        table = gen._contended_adt_display_names
        types = {m for m in table if table[m] == "Shape"}
        ctors = {m for m in table if table[m] in {"Sq", "Cr"}}
        assert len(types) == 2, sorted(types)
        assert len(ctors) == 2, sorted(ctors)
        for mangled in types:
            assert mangled in gen._adt_layouts, (
                f"{mangled} has no registered layout — the rename dropped it"
            )
            assert mangled in gen._adt_layout_owners, mangled
        registered_ctors = {
            c for t in types for c in gen._adt_layouts[t]
        }
        assert registered_ctors == ctors, (
            sorted(registered_ctors), sorted(ctors)
        )

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



# The two-`Shape` program with a `show` in each module's body, which is the
# only surface that bakes a constructor name into the RUNTIME.  `alen`
# measures the rendered length, so a leaked prefix is a wrong number rather
# than only a wrong-looking string.
_LIBA_SHOW = """\
module liba;

public data Shape { Sq(Int) }

public fn arender(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Sq(@Int.0))
}

public fn alen(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_length(show(Sq(@Int.0)))
}
"""

_LIBB_SHOW = """\
module libb;

public data Shape { Cr(Bool) }

public fn brender(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Cr(true))
}
"""

_ENTRY_SHOW = """\
import liba(arender, alen);
import libb(brender);

public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  arender(3)
}

public fn rendered_length(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  alen(3)
}

public fn other(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  brender(0)
}
"""

_SHOW_FILES = {
    "liba.vera": _LIBA_SHOW, "libb.vera": _LIBB_SHOW,
    "main.vera": _ENTRY_SHOW,
}


class TestTheSymbolIsInternal:
    """#187's own design note, answered and then enforced: the qualified
    symbol is a WASM detail and never a spelling the reader is shown.

    This class was DEFENCE IN DEPTH and was wrong to be.  Adversarial
    review found the leak that made it load-bearing: ``show``'s constructor
    head is baked into the DATA SECTION from the registry key, so
    ``show(Sq(3))`` printed ``mod$liba$Sq(3)`` and
    ``string_length(show(Sq(3)))`` was 14 where 5 is right — a wrong string
    and a wrong number on a program with no diagnostics at all.  The three
    original cells could not see it: they read the diagnostic stream of
    programs that produce none.

    So the strip is one function — :func:`~vera.naming.display_adt_name` —
    and every surface that renders an ADT or constructor name to a PERSON
    goes through it, while no WAT symbol does.  The battery below drives
    each surface over the two-``Shape`` programs and greps its whole output
    for ``mod$``: runtime stdout, the codegen diagnostic stream, `vera
    check` / `vera verify` JSON, `vera ast --json`, `vera parse`, and the
    browser bundle.  A surface that starts rendering an ADT name without
    the strip is caught by the grep rather than by someone reading it.
    """

    def test_show_renders_the_users_spelling(self, tmp_path: Path) -> None:
        """The measurement, kept: the head is the user's name, not the key."""
        _verify, codes, answer = _cell(
            tmp_path / "show", _SHOW_FILES,
        )
        assert codes == [], codes
        assert answer == ("ok", "Sq(3)"), answer

    def test_the_rendered_length_is_the_users_spellings(
        self, tmp_path: Path,
    ) -> None:
        """And it is a NUMBER, so the cell cannot pass on a string that
        merely looks plausible: ``Sq(3)`` is 5 characters, and the leak made
        it 14."""
        _verify, _result, cg_errors = build_multi_module(
            tmp_path / "len", _SHOW_FILES,
        )
        assert cg_errors == [], cg_errors
        assert module_value(_result, fn="rendered_length") == ("ok", 5)

    def test_both_owners_render_their_own_constructor(
        self, tmp_path: Path,
    ) -> None:
        """Both sides of the contended pair, so a strip that happened to
        fix one owner is not enough."""
        _verify, result, cg_errors = build_multi_module(
            tmp_path / "both", _SHOW_FILES,
        )
        assert cg_errors == [], cg_errors
        assert module_value(result, fn="main") == ("ok", "Sq(3)")
        assert module_value(result, fn="other") == ("ok", "Cr(true)")

    def test_every_arm_of_a_renamed_adt_renders_its_own_name(
        self, tmp_path: Path,
    ) -> None:
        """EVERY constructor arm, applied and nullary, in one string.

        The show cells above each render ONE applied constructor, so a
        strip applied unevenly across the arms is invisible to them: making
        it conditional on the constructor having fields
        (``display_adt_name(cname) if fields else cname``) leaves all of
        them green and renders the nullary arm as ``mod$liba$Bz``.  This
        concatenates all three arms of one renamed type and pins the whole
        string, so a leak anywhere in the dispatch is a wrong value rather
        than a wrong-looking substring nothing reads.
        """
        liba = """\
module liba;

public data Shape { B(Int), Bx(Bool), Bz }

public fn gen3(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(string_concat(show(B(@Int.0)), show(Bx(true))), show(Bz))
}
"""
        entry = """\
import liba(gen3);
import libb(bone);

public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen3(3)
}
"""
        _verify, result, cg_errors = build_multi_module(
            tmp_path / "arms",
            {"liba.vera": liba, "libb.vera": _LIBB, "main.vera": entry},
        )
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", "B(3)Bx(true)Bz")

    def test_the_control_renders_identically_without_a_rename(
        self, tmp_path: Path,
    ) -> None:
        """The control that says the strip restores the base behaviour
        rather than inventing a new one: with ``libb``'s type renamed there
        is no contention, no rename, and the same two strings."""
        files = dict(_SHOW_FILES)
        files["libb.vera"] = _LIBB_SHOW.replace("Shape", "Widget")
        _verify, result, cg_errors = build_multi_module(
            tmp_path / "control", files,
        )
        assert cg_errors == [], cg_errors
        assert module_value(result, fn="main") == ("ok", "Sq(3)")
        assert module_value(result, fn="other") == ("ok", "Cr(true)")

    @pytest.mark.parametrize(
        "files",
        [_SHOW_FILES, _DIFFERENTIAL_FILES,
         {"liba.vera": _ALPHA, "libb.vera": _BETA, "main.vera": _ENTRY},
         {"deep.vera": _DEEP, "mid.vera": _MID, "other.vera": _OTHER,
          "main.vera": _ENTRY_CHAIN}],
        ids=["show", "types", "constructors", "chain"],
    )
    def test_no_user_facing_surface_carries_the_symbol(
        self, tmp_path: Path, files: dict[str, str],
    ) -> None:
        """The battery.  Every surface, over every renamed shape, grepped.

        The CLI surfaces are driven as subprocesses so what is inspected is
        the bytes a user actually sees — stdout included, which is where
        the leak was and which no in-process assertion on a diagnostic list
        would have reached.
        """
        import subprocess
        import sys

        tmp_path.mkdir(parents=True, exist_ok=True)
        for name, text in files.items():
            (tmp_path / name).write_text(text, encoding="utf-8")
        main_path = tmp_path / "main.vera"

        def cli(*args: str) -> str:
            proc = subprocess.run(
                [sys.executable, "-m", "vera.cli", *args, str(main_path)],
                capture_output=True, text=True, encoding="utf-8", check=False,
            )
            return proc.stdout + proc.stderr

        for surface, out in (
            ("run", cli("run")),
            ("check --json", cli("check", "--json")),
            ("verify --json", cli("verify", "--json")),
            ("ast --json", cli("ast", "--json")),
            ("parse", cli("parse")),
        ):
            assert "mod$" not in out, (surface, out[:400])

        # And the in-process diagnostic stream, which the CLI surfaces above
        # only show when something goes wrong.
        gen = _generator(tmp_path / "gen", files)
        for diag in gen._result.diagnostics:  # type: ignore[attr-defined]
            for attr in ("description", "rationale", "fix"):
                text = getattr(diag, attr, None) or ""
                assert "mod$" not in text, (diag.error_code, attr, text)

        # The BROWSER leg, which renders from the same compiled artefact.
        # Two halves: the emitted bundle's text assets, and the DATA
        # SECTION of the wasm the browser host loads — the latter is where
        # `show`'s constructor head lives, so it is the half that can leak
        # and the half a grep of the glue would miss.
        from vera.browser.emit import emit_browser_bundle

        written = emit_browser_bundle(
            gen._result.wasm_bytes,  # type: ignore[attr-defined]
            tmp_path / "bundle",
            title="probe",
        )
        for path in written:
            if path.suffix == ".wasm":
                continue  # the binary legitimately carries WAT symbols
            text = path.read_text(encoding="utf-8")
            assert "mod$" not in text, (path.name, text[:300])
        wasm = (tmp_path / "bundle" / "module.wasm").read_bytes()
        for mangled in gen._contended_adt_display_names:
            # The constructor STRINGS live in the data section; the symbol
            # may appear elsewhere in the binary as a WAT identifier, which
            # is the identity itself.  What must not be there is a rendered
            # head — `mod$liba$Sq(` — since that is what a browser viewer
            # would read.
            assert mangled.encode() + b"(" not in wasm, mangled

    def test_the_wat_keeps_the_qualified_symbol(
        self, tmp_path: Path,
    ) -> None:
        """The other side of the line, and the reason the strip is a
        DISPLAY function rather than a rename undo.

        The emitted symbol IS the per-owner identity; stripping it there
        would put the two owners back in one slot.  A program whose two
        owners each derive structural ``Eq`` forces those helpers into the
        WAT under their qualified names.
        """
        liba = _LIBA.replace(
            "  match Sq(@Int.0) {\n    Sq(@Int) -> @Int.0\n  }\n",
            "  if Sq(@Int.0) == Sq(@Int.0) then { @Int.0 } else { 0 }\n")
        libb = _LIBB.replace(
            "  match Cr(true) {\n"
            "    Cr(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }\n  }\n",
            "  if Cr(true) == Cr(true) then { @Int.0 } else { 0 }\n")
        gen = _generator(
            tmp_path / "wat-keeps",
            {"liba.vera": liba, "libb.vera": libb, "main.vera": _ENTRY},
        )
        wat = gen._result.wat  # type: ignore[attr-defined]
        # `mangle_type_name` escapes `$` for a WAT identifier, so the
        # qualified identity appears as `mod_U24_<path>_U24_<Name>` — which
        # is also why no WAT symbol can ever read as a `mod$` leak in text
        # output, and why the battery's grep and this assertion do not
        # contradict each other.
        assert "mod_U24_liba_U24_" in wat, wat[-400:]
        assert "mod_U24_libb_U24_" in wat, wat[-400:]
        assert "mod$" not in wat

    def test_the_strip_and_the_rename_table_are_one_derivation(
        self, tmp_path: Path,
    ) -> None:
        """The prose rewrite and the constructor head cannot disagree.

        The diagnostic boundary substitutes inside sentences and so needs
        the table; ``show`` strips a bare symbol and so needs the function.
        The table's VALUES are produced by the function, which is what makes
        that one answer rather than two.
        """
        from vera.naming import display_adt_name

        gen = _generator(tmp_path / "one-derivation", _DIFFERENTIAL_FILES)
        table = gen._contended_adt_display_names
        assert table, "no rename happened, so the claim is untested here"
        for mangled, bare in table.items():
            assert display_adt_name(mangled) == bare, (mangled, bare)

    def test_the_strip_leaves_an_unqualified_name_alone(self) -> None:
        """Total and idempotent, so applying it at a surface that never
        sees a qualified name costs nothing and changes nothing."""
        from vera.naming import display_adt_name

        for name in ("Sq", "Shape", "Option", "Some", "MdText"):
            assert display_adt_name(name) == name
        assert display_adt_name("mod$a$b$Shape") == "Shape"
        assert display_adt_name(display_adt_name("mod$liba$Sq")) == "Sq"

    def test_the_strip_uses_the_rename_table_not_a_pattern(
        self, tmp_path: Path,
    ) -> None:
        """The DIAGNOSTIC boundary rewrites inside prose from the table, so
        a FUNCTION mangled by #814's rerouting — a different rename with its
        own reporting — is left exactly as it was."""
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


# =====================================================================
# Alias-hidden shapes, and the E623 asymmetry — both measured
# =====================================================================


class TestShapesReadThroughTheDeclaringModulesAliases:
    """Contention is decided on RESOLVED shapes, not on spellings.

    §8.4.1 makes an alias module-local, so two modules can spell one layout
    differently and two layouts identically.  The rename is decided at the
    top of ``_register_modules``, before the harvest fills
    ``_module_type_aliases`` — so it builds each module's alias maps from
    that module's own declarations rather than reading tables that are
    still empty.  Both directions are measured, because reading unresolved
    spellings gets each one wrong in the opposite way.
    """

    def test_one_layout_spelled_two_ways_is_not_contended(
        self, tmp_path: Path,
    ) -> None:
        """Covered in full by
        :meth:`TestRestatementIsStillNotAContention
        .test_a_restatement_spelled_through_an_alias_is_not_renamed`; kept
        here as the sibling of the cell below so the pair reads together."""
        libb = _LIBA.replace("module liba", "module libb").replace(
            "aone", "bone").replace(
            "public data Shape { Sq(Int) }",
            "type Count = Int;\n\npublic data Shape { Sq(Count) }").replace(
            "Sq(@Int) -> @Int.0", "Sq(@Count) -> @Count.0")
        gen = _generator(
            tmp_path / "one-layout",
            {"liba.vera": _LIBA, "libb.vera": libb, "main.vera": _ENTRY},
        )
        assert gen._contended_adt_display_names == {}

    def test_two_layouts_spelled_one_way_are_contended(
        self, tmp_path: Path,
    ) -> None:
        """The direction an unresolved read gets wrong the other way.

        Both modules write ``data Shape { Sq(Count) }`` — the SAME
        spelling — while ``Count`` is ``Int`` in one and ``Bool`` in the
        other.  Compared as text the two look identical, so no contention
        is seen, nothing is renamed, and the pair lands back on E609 with
        both of #1317's import-side remedies failing.  Compared as resolved
        layouts they are distinct, are qualified apart, and run.
        """
        liba = """\
module liba;

type Count = Int;

public data Shape { Sq(Count) }

public fn aone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Sq(@Int.0) {
    Sq(@Count) -> @Count.0
  }
}
"""
        libb = """\
module libb;

type Count = Bool;

public data Shape { Sq(Count) }

public fn bone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Sq(true) {
    Sq(@Count) -> if @Count.0 then { @Int.0 } else { 0 }
  }
}
"""
        verify, codes, answer = _cell(
            tmp_path / "two-layouts",
            {"liba.vera": liba, "libb.vera": libb, "main.vera": _ENTRY},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer


_E623_LIBB = """\
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

_E623_ONE = """\
import liba(aone);

private data Shape { Own(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  aone(3) + 4
}
"""

_E623_TWO = """\
import liba(aone);
import libb(bone);

private data Shape { Own(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  aone(3) + bone(4)
}
"""


class TestTheEntryRailIsNotMonotonicYet:
    """A KNOWN asymmetry, pinned in both directions rather than left to be
    rediscovered (PR review).

    THE RULE a reader expects is that adding an unrelated module cannot
    lift a refusal.  This pair violates it: an entry that declares ``Shape``
    beside ONE module declaring it differently is E623, and adding a SECOND
    module with a third ``Shape`` makes the two modules contend, qualifies
    both away, leaves the entry alone in the bare slot — and E623 then has
    no pair to report, so the program compiles and runs.

    Both in-scope repairs were measured and both cost more than the
    asymmetry does:

    * qualifying a module's ``Shape`` whenever the ENTRY declares the name
      makes both cases run, and reds
      ``test_type_parameter_ARITY_alone_is_a_different_layout`` in
      ``tests/test_data_namespace_contention_1312.py`` — it relaxes E623,
      which is #1312's rail and not this change's to move;
    * declining the rename whenever the entry declares the name makes both
      cases refuse, and brings **E609** back with them — so #1317's own
      second remedy (a local declaration in the importer) stops working,
      which is the defect this change exists to close.

    The asymmetry is therefore the entry-versus-module rail's own
    over-breadth showing through, and belongs with #1312 rather than here.
    These two cells pin the CURRENT verdicts so the resolution, whichever
    way it goes, has to move them deliberately.
    """

    def test_one_contending_module_beside_the_entry_is_refused(
        self, tmp_path: Path,
    ) -> None:
        _verify, codes, answer = _cell(
            tmp_path / "e623-one",
            {"liba.vera": _LIBA, "main.vera": _E623_ONE},
        )
        assert codes == ["E623"], codes
        assert answer == ("no-run", "compilation had errors"), answer

    def test_adding_a_second_contending_module_lifts_it(
        self, tmp_path: Path,
    ) -> None:
        """The non-monotonic direction, stated as a measurement.

        Not asserted as CORRECT — asserted as what the compiler does today,
        so the #1312 resolution cannot change it silently.
        """
        verify, codes, answer = _cell(
            tmp_path / "e623-two",
            {"liba.vera": _LIBA, "libb.vera": _E623_LIBB,
             "main.vera": _E623_TWO},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer


class TestTheFlowSurfaceFailsClosed:
    """The inputs to the meeting condition, and how they fail.

    Both of these decide whether a value can cross between two owners, and
    both used to fail OPEN — reading "no crossing" from an input they did
    not understand, which is the direction that admits an unsound rename.
    """

    def test_an_unknown_declaration_kind_is_walked_whole(self) -> None:
        """A declaration kind the surface dispatch has not learned must
        over-count mentions, not report none (PR review).

        An ``else: surface = []`` reads such a kind as mentioning no types
        at all, so the flow condition stops seeing what it carries.  The
        fallback walks the whole declaration instead: an extra mention can
        only refuse a rename, never admit one.
        """
        from dataclasses import dataclass

        from vera import ast
        from vera.codegen.modules import CrossModuleMixin

        @dataclass(frozen=True)
        class _FutureDecl(ast.Decl):
            """A declaration kind the dispatch does not know."""

            name: str = "Zz"
            carried: ast.TypeExpr = ast.NamedType(name="Shape", type_args=None)

        mentions = CrossModuleMixin._exported_type_mentions(
            _FutureDecl(), {},
        )
        assert "Shape" in mentions, mentions

    def test_repeated_imports_of_one_module_union_their_filters(
        self, tmp_path: Path,
    ) -> None:
        """Two import statements naming one module contribute BOTH lists.

        Keyed by path in a dict comprehension the last statement won and
        the others were discarded, so a filter admitting neither the type
        nor the signature that carries it could hide a crossing the entry
        can actually make.  A wildcard beside a list dominates it.
        """
        from vera import ast
        from vera.codegen.modules import _merged_import_filters

        def imp(path: tuple[str, ...], names: tuple[str, ...] | None):
            return ast.ImportDecl(path=path, names=names)

        merged = _merged_import_filters([
            imp(("liba",), ("aone",)),
            imp(("liba",), ("helper",)),
            imp(("libb",), ("bone",)),
        ])
        assert merged[("liba",)] == {"aone", "helper"}
        assert merged[("libb",)] == {"bone"}

        wild = _merged_import_filters([
            imp(("liba",), ("aone",)), imp(("liba",), None),
        ])
        assert wild[("liba",)] is None

        idempotent = _merged_import_filters([
            imp(("liba",), ("aone",)), imp(("liba",), ("aone",)),
        ])
        assert idempotent[("liba",)] == {"aone"}

    def test_a_flow_behind_a_repeated_import_is_still_a_flow(
        self, tmp_path: Path,
    ) -> None:
        """And end to end: the crossing the collapse would have hidden.

        The entry imports ``liba`` twice — once for the signature that
        returns a ``Shape``, once for an unrelated helper.  With only the
        LAST list surviving, neither the type nor ``aone`` is admitted, the
        crossing goes unseen, and the two owners are qualified apart while
        ``bone(aone(6))`` still passes a value between them.
        """
        liba = _FLOW_A + """
public fn helper(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""
        entry = _ENTRY_FLOW.replace(
            "import liba(aone);", "import liba(aone);\nimport liba(helper);")
        _verify, codes, answer = _cell(
            tmp_path / "dup-import",
            {"liba.vera": liba, "libb.vera": _FLOW_B, "main.vera": entry},
        )
        assert "E609" in codes, codes
        assert answer == ("no-run", "compilation had errors"), answer


class TestADiagnosticStreamThatIsNotEmpty:
    """The display sweep, driven over a program that actually reports.

    The three original "symbol never reaches the reader" cells ran over
    programs whose diagnostic list was EMPTY, so they were green on the
    base and would have stayed green through any leak (PR review).  The
    battery above fixed that for the surfaces a clean program has; this
    class covers the diagnostic stream itself, by compiling a program that
    HAS a rename and also reports.

    What cannot be built today is a diagnostic that NAMES a renamed type:
    the codegen diagnostics that interpolate an ADT name are the collision
    rails (E609/E610/E621/E623), and a declaration those report on is by
    construction one the rename declined to touch.  That is why the strip
    at the diagnostic boundary is defence in depth and is pinned directly
    on ``_unmangle_adt_names`` as well as here.
    """

    def test_a_renamed_program_with_real_diagnostics_leaks_nothing(
        self, tmp_path: Path,
    ) -> None:
        # Two contending `Shape`s (renamed), beside a dropped function that
        # makes the stream non-empty.
        liba = _LIBA + """
public fn broken(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  zz_no_such_builtin(@Int.0)
}
"""
        entry = _ENTRY.replace(
            "  aone(3) + bone(4)\n", "  aone(3) + bone(4)\n").replace(
            "import liba(aone);", "import liba(aone, broken);")
        _verify, result, _cg = build_multi_module(
            tmp_path / "noisy",
            {"liba.vera": liba, "libb.vera": _LIBB, "main.vera": entry},
        )
        assert result.diagnostics, (
            "the stream is empty, so this cell measures nothing"
        )
        for diag in result.diagnostics:
            for attr in ("description", "rationale", "fix"):
                text = getattr(diag, attr, None) or ""
                assert "mod$" not in text, (diag.error_code, attr, text)

    def test_a_diagnostic_that_names_a_renamed_type_reads_the_users_name(
        self, tmp_path: Path,
    ) -> None:
        """The cell that makes the strip LOAD-BEARING (PR review, N1).

        Deleting the ``_unmangle_adt_names`` call from ``compile_program``
        was inert against every other cell here: the sweeps run over
        programs whose diagnostics never mention an ADT, so nothing read
        the one thing the strip exists to change.  This drives a diagnostic
        that DOES name the type — ``liba``'s ``Shape`` has an ``Array``
        field, so codegen's structural-``Eq`` rail reports E613 about it —
        on a program where ``Shape`` is contended and therefore renamed.
        Measured with the call deleted: ``Type 'mod$liba$Shape' does not
        satisfy ability 'Eq'``.

        Driven through ``build_multi_module_past_check`` because the
        CHECKER refuses the comparison first (E243).  That is the point:
        the codegen rail behind it still runs, still names the type, and
        the reader must be shown their own spelling either way.
        """
        liba = """\
module liba;

public data Shape { Sq(Array<Int>) }

public fn aone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if Sq([1]) == Sq([1]) then { @Int.0 } else { 0 }
}
"""
        check_errors, result, _cg = build_multi_module_past_check(
            tmp_path / "e613",
            {"liba.vera": liba, "libb.vera": _LIBB, "main.vera": _ENTRY},
        )
        assert check_errors, check_errors
        e613 = [d for d in result.diagnostics if d.error_code == "E613"]
        assert e613, [d.error_code for d in result.diagnostics]
        described = " ".join(
            (getattr(d, a, None) or "")
            for d in e613 for a in ("description", "rationale", "fix")
        )
        assert "Shape" in described, described[:200]
        assert "mod$" not in described, described[:200]
