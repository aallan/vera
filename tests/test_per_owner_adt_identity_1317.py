"""#1317 / #187 (data half) / #1694 — per-owner ADT identity.

Codegen keyed every ADT registry by BARE name — layouts, constructor
layouts, type-parameter metadata, the structural-``Eq`` helper namer, the
declaration index, the export table — so two modules declaring
``data Shape`` contended for one slot and E609/E610 refused the pair by
DECLARATION.  #1317 renamed a CONTENDED module declaration to
``mod$<path>$<Name>`` at absorb time.  #1694 makes that name the identity
of every module data type in every stage: the resolver pass names each
module ``data`` declaration, alias and constructor by its link name
(:mod:`vera.binding`), the checker types a module's ADT by it, and code
generation compiles the linked program, so ADT identity is
``(owner, name)`` BY CONSTRUCTION and no stage asks which owner a name
means.

**What refuses, and why each is not an oversight.**

* **Two suppliers.**  A name two of one namespace's imports both supply is
  ambiguous, and §8.5.2.2 refuses it at check rather than picking (E156,
  E157).
* **A meeting.**  Two owners' declarations are two types, so a value of
  one that reaches a place expecting the other — ``bone(aone(6))`` with
  ``liba::aone(@Int -> @Shape)`` and ``libb::bone(@Shape -> @Int)`` — is
  an ordinary mismatch at check whose message names both owners.  Before
  #1694 the checker unified two same-named cross-module ADTs, and with the
  rename in place and the flow condition removed the program returned
  ``100`` where ``7`` is the answer; :class:`TestMeeting` keeps that
  measurement.
* **A prelude name.**  ``Option``, ``Result``, ``Ordering`` and every type
  name the prelude can provide are reserved (E158, #1469), as built-in
  function names are E151's and effect names E152's.
* **The entry's own declaration** is an owner like a module's: an entry
  ``data Shape`` beside a module's is two types
  (:class:`TestTheEntryIsAnOwnerToo`).
"""
from __future__ import annotations

from pathlib import Path

import pytest

from vera.codegen.core import CodeGenerator

from tests import pipeline
from tests.module_fixture_helpers import (
    build_multi_module,
    build_multi_module_past_check,
    module_value,
    refused_at_check as _refused_at_check,
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
    main_path = pipeline.write_tree(tmp_path, files)
    checked = pipeline.check(main_path, root=tmp_path)
    _ = checked.program  # raises the parse or transform error
    resolve_errors = [d.description for d in checked.resolution_diagnostics]
    assert not resolve_errors, f"module resolution errors: {resolve_errors}"
    mods = checked.resolved or []
    assert len(mods) == len(files) - 1, (
        f"expected {len(files) - 1} resolved modules, got "
        f"{[m.path for m in mods]}"
    )
    compiled = pipeline.compile(main_path, modules=mods, checked=False)
    gen = compiled.generator
    assert gen is not None
    result = compiled.result
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

        Nothing is refused: the entry's ``Shape`` and each module's are
        three types (#1694).
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

    def test_no_declaration_keeps_the_bare_name(
        self, tmp_path: Path,
    ) -> None:
        """Whichever one the entry names, each module's declaration is under
        its own link name (#1694): there is no keeper."""
        gen = _generator(
            tmp_path / "keeper-sym",
            {"liba.vera": _LIBA, "libb.vera": _LIBB,
             "main.vera": _ENTRY_NAMES_LIBA},
        )
        assert "Shape" not in gen._adt_layouts, sorted(gen._adt_layouts)
        assert gen._adt_layout_owners.get("mod$liba$Shape") == ("liba",)
        assert "mod$libb$Shape" in gen._adt_layouts, sorted(gen._adt_layouts)


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
        assert list(gen._adt_layouts["mod$liba$Shape"]) == [
            "mod$liba$Shape$Sq"]
        assert list(gen._adt_layouts["mod$libb$Shape"]) == [
            "mod$libb$Shape$Cr"]

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


def _check_refusals(
    tmp_path: Path, files: dict[str, str],
) -> list[tuple[str | None, str]]:
    """``(code, file name)`` of each check error for the program."""
    checked = pipeline.check(pipeline.write_tree(tmp_path, files))
    return [(d.error_code, Path(d.location.file or "").name)
            for d in checked.errors]


class TestThePreludeIsReserved:
    """R7: a prelude name is never qualified apart; since #1469 it is
    reserved outright.

    Per-owner ADT identity is a rule between USER modules.  A module's
    declaration under a name the prelude provides is refused at check
    (E158), whatever its shape, a restatement of the prelude's own included,
    where code generation once decided the pair by contention (E621).
    """

    def test_a_module_restating_the_prelude_is_refused(
        self, tmp_path: Path,
    ) -> None:
        """``liba`` declares the prelude's ``Option`` with the prelude's own
        shape: refused at its declaration, where E621 once found nothing to
        contend with and let the single layout serve both."""
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
        refusals = _check_refusals(
            tmp_path / "restate-prelude",
            {"liba.vera": liba, "libb.vera": _LIBB, "main.vera": _ENTRY},
        )
        assert refusals == [("E158", "liba.vera")], refusals

    def test_two_modules_declaring_a_prelude_name_are_refused(
        self, tmp_path: Path,
    ) -> None:
        refusals = _check_refusals(
            tmp_path / "prelude",
            {"liba.vera": _PRELUDE_A, "libb.vera": _PRELUDE_B,
             "main.vera": _ENTRY},
        )
        assert ("E158", "liba.vera") in refusals, refusals
        assert ("E158", "libb.vera") in refusals, refusals

    def test_a_single_module_declaring_a_prelude_name_is_refused(
        self, tmp_path: Path,
    ) -> None:
        """Nothing to contend with among modules, and the declaration is
        refused all the same."""
        entry = _ENTRY.replace("import libb(bone);\n", "").replace(
            " + bone(4)", " + 4")
        refusals = _check_refusals(
            tmp_path / "prelude-one",
            {"liba.vera": _PRELUDE_A, "main.vera": entry},
        )
        assert refusals and refusals[0] == ("E158", "liba.vera"), refusals

    def test_the_same_shape_under_a_user_name_is_admitted(
        self, tmp_path: Path,
    ) -> None:
        """The control that isolates the RESERVATION from the shapes.

        Byte-identical declarations to the reserved-name cell above, renamed to a
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
        """MEASURED over the LIVE reservation, once per name the prelude
        provides: two modules declaring it differently are each refused at
        check (E158), never qualified apart.

        Parameterless over the LIVE set, so a prelude ADT added later is
        covered without this cell being edited.
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
            refusals = _check_refusals(
                tmp_path / f"reserved-{name}",
                {"liba.vera": liba, "libb.vera": libb, "main.vera": _ENTRY},
            )
            assert ("E158", "liba.vera") in refusals, (name, refusals)
            assert ("E158", "libb.vera") in refusals, (name, refusals)
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
        assert list(gen._adt_layouts["mod$liba$Alpha"]) == [
            "mod$liba$Alpha$Sq"]
        assert list(gen._adt_layouts["mod$libb$Beta"]) == [
            "mod$libb$Beta$Sq"]
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
    the refusal it replaced.  The two declarations are two types (#1694),
    so the meeting is refused at check, an ordinary mismatch naming both
    owners.
    """

    def test_a_value_flowing_between_two_owners_is_refused(
        self, tmp_path: Path,
    ) -> None:
        codes, text = _refused_at_check(
            tmp_path / "flow",
            {"liba.vera": _FLOW_A, "libb.vera": _FLOW_B,
             "main.vera": _ENTRY_FLOW},
        )
        assert "E202" in codes, codes
        assert "liba.Shape" in text and "libb.Shape" in text, text

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
        codes, text = _refused_at_check(
            tmp_path / "alias-flow",
            {"liba.vera": liba, "libb.vera": libb,
             "main.vera": _ENTRY_FLOW},
        )
        assert "E202" in codes, codes
        assert "liba.Shape" in text and "libb.Shape" in text, text

    def test_a_flow_through_an_imported_adts_field_is_a_flow_too(
        self, tmp_path: Path,
    ) -> None:
        """The surface is not only function signatures.

        ``liba`` exports ``Wrapper { W(Shape) }``, so an importer naming
        ``Wrapper`` can extract a ``Shape`` from its field and hand it to
        ``libb`` — the same crossing by a different route.  Binding the field
        names the type, so the entry imports ``liba``'s (an unimported name
        is E136, #1489).
        """
        liba = _FLOW_A + """
public data Wrapper { W(Shape) }
"""
        entry = """\
import liba(aone, Wrapper, Shape);
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
        codes, text = _refused_at_check(
            tmp_path / "field-flow",
            {"liba.vera": liba, "libb.vera": _FLOW_B, "main.vera": entry},
        )
        assert "E202" in codes, codes
        assert "liba.Shape" in text and "libb.Shape" in text, text


class TestTheEntryIsAnOwnerToo:
    """The entry file is an owner like any other (#1423).

    Per-owner identity applied to the modules alone left E623 deciding a
    DIFFERENT question from E609, and the two disagreed: an entry declaring
    ``Shape`` beside one contending module was refused, and adding a second
    contending module qualified both away and lifted the refusal.  The
    entry is a party to the same rule (#1694): its declaration is a type of
    its own beside each module's, keeping its bare name, which is its link
    name, and a module's value that meets the entry's type is an ordinary
    mismatch at check, located where the value meets it.
    """

    def test_a_module_the_entry_cannot_name_is_qualified_away(
        self, tmp_path: Path,
    ) -> None:
        """The entry declares ``Shape``, so §8.5.4 shadows the import of
        the same name and ``aone``'s signature carries no ``Shape``.  The
        two cannot meet, so ``liba``'s declaration takes its own symbol and
        the program runs."""
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
        verify, codes, answer = _cell(
            tmp_path / "e623",
            {"liba.vera": _LIBA, "main.vera": entry},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 3), answer

    def test_a_module_value_meeting_the_entrys_type_is_refused(
        self, tmp_path: Path,
    ) -> None:
        """And the half #1312 exists for, refused at check (#1694).

        ``aone`` RETURNS ``liba``'s ``Shape``, so a value of it reaches the
        entry, whose own declaration of the name is another type.  The
        entry's constructor cannot match it, and the pattern mismatch names
        both owners.
        """
        liba = _LIBA.replace(
            "public fn aone(@Int -> @Int)", "public fn aone(@Int -> @Shape)",
        ).replace(
            "  match Sq(@Int.0) {\n    Sq(@Int) -> @Int.0\n  }\n",
            "  Sq(@Int.0)\n")
        entry = """\
import liba(aone);

private data Shape { Own(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match aone(6) {
    Own(@Int) -> @Int.0
  }
}
"""
        codes, text = _refused_at_check(
            tmp_path / "e623-meets",
            {"liba.vera": liba, "main.vera": entry},
        )
        assert "E314" in codes, codes
        assert "liba.Shape" in text, text

    def test_the_entrys_declaration_counts_as_an_owner(
        self, tmp_path: Path,
    ) -> None:
        """The direction that would otherwise be a hole.

        The entry declares ``Shape`` AND receives ``liba``'s through
        ``aone``'s return type, while ``libb`` declares a third.  Renaming
        the modules apart would leave the entry's own constructors reading
        ``liba``'s value, so the entry's declaration is an owner like any
        other: its constructors cannot match ``liba``'s type, refused at
        check (#1694).
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
        codes, text = _refused_at_check(
            tmp_path / "entry-owner",
            {"liba.vera": _FLOW_A, "libb.vera": libb, "main.vera": entry},
        )
        assert "E314" in codes, codes
        assert "liba.Shape" in text, text


class TestARestatementIsATypeOfItsOwn:
    """Two modules declaring one layout under one name declare two types
    (#1694): each is under its own link name, as any two modules'
    same-named types are, and a program that keeps them apart runs."""

    def test_two_modules_restating_one_type_are_two_types(
        self, tmp_path: Path,
    ) -> None:
        libb = _LIBA.replace("module liba", "module libb").replace(
            "aone", "bone")
        gen = _generator(
            tmp_path / "restate",
            {"liba.vera": _LIBA, "libb.vera": libb, "main.vera": _ENTRY},
        )
        assert "Shape" not in gen._adt_layouts
        assert "mod$liba$Shape" in gen._adt_layouts
        assert "mod$libb$Shape" in gen._adt_layouts
        assert module_value(
            gen._result,  # type: ignore[attr-defined]
        ) == ("ok", 7)

    def test_a_restatement_spelled_through_an_alias_is_two_types(
        self, tmp_path: Path,
    ) -> None:
        """A restatement spelled through a module's own alias is the same
        case: two declarations, two types.  The rename this replaced asked
        the shape question with the SAME inputs the other three rails were
        given (PR review).

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
        assert "Shape" not in gen._adt_layouts
        assert {"mod$liba$Shape", "mod$libb$Shape"} <= set(gen._adt_layouts)
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
        # Every module type and user constructor is under its link name
        # (#1694), so none of the names the two modules declare is a key.
        renamed_bare = {"Shape", "Sq", "Cr"}
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
        types = {"mod$liba$Shape", "mod$libb$Shape"}
        ctors = {"mod$liba$Shape$Sq", "mod$libb$Shape$Cr"}
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
        linked_ctors = [
            ctor for ctors in gen._adt_layouts.values() for ctor in ctors
            if "$" in ctor
        ]
        assert linked_ctors, "no constructor under a link name: vacuous"
        for mangled in linked_ctors:
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
        # qualified TYPE identity appears as `mod_U24_<path>_U24_<Name>`, and
        # no symbol derived from the renamed type reads as its `mod$` spelling
        # in text output.  A FUNCTION's symbol is its link name
        # (`mod$<path>$<name>`, #1694), which is not this rename.
        assert "mod_U24_liba_U24_" in wat, wat[-400:]
        assert "mod_U24_libb_U24_" in wat, wat[-400:]
        assert "mod$liba$Shape" not in wat and "mod$libb$Shape" not in wat

    def test_the_strip_names_every_link_name_as_it_is_declared(
        self, tmp_path: Path,
    ) -> None:
        """The constructor head and the diagnostic boundary cannot
        disagree: both strip a link name to the name it was declared under
        (`display_adt_name`, #1694), for every type and constructor the
        generator holds under one."""
        from vera.naming import display_adt_name

        gen = _generator(tmp_path / "one-derivation", _DIFFERENTIAL_FILES)
        linked = {
            name: ctors for name, ctors in gen._adt_layouts.items()
            if name.startswith("mod$")
        }
        assert linked, "no type under a link name: vacuous"
        for name, ctors in linked.items():
            assert display_adt_name(name) == "Shape", name
            assert {display_adt_name(c) for c in ctors} <= {"Sq", "Cr"}, ctors

    def test_the_strip_leaves_an_unqualified_name_alone(self) -> None:
        """Total and idempotent, so applying it at a surface that never
        sees a qualified name costs nothing and changes nothing."""
        from vera.naming import display_adt_name

        for name in ("Sq", "Shape", "Option", "Some", "MdText"):
            assert display_adt_name(name) == name
        assert display_adt_name("mod$a$b$Shape") == "Shape"
        assert display_adt_name(display_adt_name("mod$liba$Sq")) == "Sq"

    def test_the_diagnostic_boundary_spells_every_link_name_as_written(
        self, tmp_path: Path,
    ) -> None:
        """The DIAGNOSTIC boundary rewrites inside prose: a type's and a
        constructor's link name to the name it is declared under, a
        function's to the name the binding's display table gives it
        (#1694)."""
        from vera.errors import Diagnostic, SourceLocation

        gen = _generator(tmp_path / "unmangle", _DIFFERENTIAL_FILES)
        diag = Diagnostic(
            description="Type 'mod$liba$Shape' and fn 'mod$liba$aone'.",
            location=SourceLocation(file="x.vera"),
            fix="Rename 'mod$libb$Shape$Cr'.",
        )
        gen._unmangle_fn_names([diag])
        assert diag.description == "Type 'Shape' and fn 'aone'."
        assert diag.fix == "Rename 'Cr'."

    def test_a_diagnostic_without_a_link_name_is_unchanged(
        self, tmp_path: Path,
    ) -> None:
        from vera.errors import Diagnostic, SourceLocation

        gen = _generator(tmp_path / "no-rename", _DIFFERENTIAL_FILES)
        diag = Diagnostic(
            description="Type 'Shape' of 'liba'.",
            location=SourceLocation(file="x.vera"),
        )
        gen._unmangle_fn_names([diag])
        assert diag.description == "Type 'Shape' of 'liba'."


# =====================================================================
# Alias-hidden shapes, and the entry's verdict with one owner or two
# =====================================================================


class TestShapesReadThroughTheDeclaringModulesAliases:
    """Two modules' declarations are two types whatever their spellings.

    §8.4.1 makes an alias module-local, so two modules can spell one layout
    differently and two layouts identically.  Each module's type is its own
    (#1694), laid out under its link name through its own module's
    aliases; both directions are measured, because reading unresolved
    spellings got each one wrong in the opposite way before.
    """

    def test_one_layout_spelled_two_ways_is_two_types(
        self, tmp_path: Path,
    ) -> None:
        """Covered in full by
        :meth:`TestARestatementIsATypeOfItsOwn
        .test_a_restatement_spelled_through_an_alias_is_two_types`; kept
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
        assert {"mod$liba$Shape", "mod$libb$Shape"} <= set(gen._adt_layouts)

    def test_two_layouts_spelled_one_way_are_contended(
        self, tmp_path: Path,
    ) -> None:
        """The direction an unresolved read gets wrong the other way.

        Both modules write ``data Shape { Sq(Count) }`` — the SAME
        spelling — while ``Count`` is ``Int`` in one and ``Bool`` in the
        other.  Compared as text the two looked identical, so before #1694
        a reading of the spelling saw no contention, renamed nothing, and
        the pair landed on E609.  Each is its own type, laid out through
        its own module's alias, and the program runs.
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


class TestTheEntryRailIsMonotonic:
    """A verdict does not change when an unrelated module is added (#1423).

    THE RULE, and it is a design principle rather than a convenience: a
    program the compiler refuses must not become one it accepts because
    something unrelated joined the build.  Per-owner identity applied to
    the modules alone broke it — an entry declaring ``Shape`` beside ONE
    contending module was E623, and adding a SECOND contending module made
    the two modules contend with each other, qualified both away, left the
    entry alone in the bare slot, and lifted the refusal.

    Typing each declaration by its own identity (#1694) settles it in both
    directions, and both cells below assert the SAME verdict: each module's
    ``Shape`` is a type of its own whether there is one of them or two.
    The refusing direction is asserted by :class:`TestTheEntryIsAnOwnerToo`:
    a module's value that reaches the entry's ``Shape`` is a mismatch at
    check with one module or with two.
    """

    def test_one_contending_module_beside_the_entry(
        self, tmp_path: Path,
    ) -> None:
        verify, codes, answer = _cell(
            tmp_path / "e623-one",
            {"liba.vera": _LIBA, "main.vera": _E623_ONE},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer

    def test_adding_a_second_contending_module_changes_nothing(
        self, tmp_path: Path,
    ) -> None:
        """The monotonicity assertion proper: same verdict, same value."""
        verify, codes, answer = _cell(
            tmp_path / "e623-two",
            {"liba.vera": _LIBA, "libb.vera": _E623_LIBB,
             "main.vera": _E623_TWO},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer

    def test_a_meeting_is_refused_with_one_module_and_with_two(
        self, tmp_path: Path,
    ) -> None:
        """And the refusing direction is monotonic too.

        ``aone`` returns ``liba``'s ``Shape``, so it meets the entry's
        declaration of the name.  Adding an unrelated second contending
        module must not lift that refusal any more than removing it should
        create one — the rename declines for the pair that MEETS, and which
        other modules happen to be in the build does not enter into it.
        """
        liba = _LIBA.replace(
            "public fn aone(@Int -> @Int)", "public fn aone(@Int -> @Shape)",
        ).replace(
            "  match Sq(@Int.0) {\n    Sq(@Int) -> @Int.0\n  }\n",
            "  Sq(@Int.0)\n")
        entry_one = """\
import liba(aone);

private data Shape { Own(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match aone(6) {
    Own(@Int) -> @Int.0
  }
}
"""
        entry_two = entry_one.replace(
            "import liba(aone);", "import liba(aone);\nimport libb(bone);",
        ).replace("    Own(@Int) -> @Int.0\n  }\n",
                  "    Own(@Int) -> @Int.0\n  } + bone(1)\n")
        one, _text1 = _refused_at_check(
            tmp_path / "meet-one",
            {"liba.vera": liba, "main.vera": entry_one})
        two, _text2 = _refused_at_check(
            tmp_path / "meet-two",
            {"liba.vera": liba, "libb.vera": _E623_LIBB,
             "main.vera": entry_two})
        assert "E314" in one, one
        assert "E314" in two, two


class TestTheFlowSurfaceFailsClosed:
    """The inputs to the meeting condition, and how they fail.

    Both of these decide whether a value can cross between two owners, and
    both used to fail OPEN — reading "no crossing" from an input they did
    not understand, which is the direction that admits an unsound rename.
    """

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
        from vera.resolver import merged_import_filters as _merged_import_filters

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
        codes, text = _refused_at_check(
            tmp_path / "dup-import",
            {"liba.vera": liba, "libb.vera": _FLOW_B, "main.vera": entry},
        )
        assert "E202" in codes, codes
        assert "liba.Shape" in text and "libb.Shape" in text, text


class TestADiagnosticStreamThatIsNotEmpty:
    """The display sweep, driven over a program that actually reports.

    The three original "symbol never reaches the reader" cells ran over
    programs whose diagnostic list was EMPTY, so they were green on the
    base and would have stayed green through any leak (PR review).  The
    battery above fixed that for the surfaces a clean program has; this
    class covers the diagnostic stream itself, by compiling a program that
    HAS a rename and also reports.

    Every module type reaches code generation under its link name (#1694),
    so a code-generation diagnostic that names a type names it so, and the
    display pass at the diagnostic boundary (``_unmangle_fn_names``, over
    :func:`vera.binding.display_link_names`) spells it as the reader
    writes it; the cell below drives one that does.
    """

    def test_a_renamed_program_with_real_diagnostics_leaks_nothing(
        self, tmp_path: Path,
    ) -> None:
        # Two contending `Shape`s (renamed), beside a dropped function that
        # makes the stream non-empty.  Its unresolved call is an E200 error
        # at check since #1513, so the program is driven past the check to
        # reach code generation's own diagnostics.
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
        check_errors, result, _cg = build_multi_module_past_check(
            tmp_path / "noisy",
            {"liba.vera": liba, "libb.vera": _LIBB, "main.vera": entry},
        )
        assert [code for code, _ in check_errors] == ["E200"], check_errors
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

        Deleting the display pass from ``compile_program`` (then
        ``_unmangle_adt_names``, now ``_unmangle_fn_names``) was inert
        against every other cell here: the sweeps run over
        programs whose diagnostics never mention an ADT, so nothing read
        the one thing the strip exists to change.  This drives a diagnostic
        that DOES name the type — ``liba``'s ``Shape`` has an ``Array``
        field, so codegen's structural-``Eq`` rail reports E613 about it —
        on a program where ``Shape`` carries its link name.
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


# =====================================================================
# #1423 — the entry file is an owner, and one rule decides both pairs
# =====================================================================


class TestOneRuleDecidesBothPairs:
    """One rule decides both pairs (#1423, #1694).

    Per-owner identity applied to the modules alone left two rails (E609,
    E623) asking different things about the same slot, and a verdict that
    changed when an unrelated module joined the build.  Every declaration
    is now a type of its own, the entry's included, so a program is refused
    exactly where a value of one meets another, at check.
    """

    def test_the_entry_keeps_the_bare_slot(self, tmp_path: Path) -> None:
        """The entry is an owner, and its declarations are never renamed.

        ``program`` is the object codegen was handed and is never
        rewritten, so the spelling the entry writes has to go on meaning
        the entry's own type: the entry holds ``Shape`` and the module it
        cannot meet is the one that moves.
        """
        entry = _ENTRY.replace(
            "import libb(bone);\n",
            "import libb(bone);\n\nprivate data Shape { Own(Int) }\n",
        )
        gen = _generator(
            tmp_path / "entry-keeps",
            {"liba.vera": _LIBA, "libb.vera": _LIBB, "main.vera": entry},
        )
        assert "Shape" in gen._adt_layouts
        assert list(gen._adt_layouts["Shape"]) == ["Shape$Own"]
        assert "mod$liba$Shape" in gen._adt_layouts
        assert "mod$libb$Shape" in gen._adt_layouts

    def test_a_module_restating_the_entrys_type_is_a_type_of_its_own(
        self, tmp_path: Path,
    ) -> None:
        """A module whose declaration matches the entry's declares a second
        type all the same (#1694): the entry's keeps its name, the module's
        takes its link name."""
        libb = _LIBB.replace(
            "public data Shape { Cr(Bool) }",
            "public data Shape { Own(Int) }").replace(
            "  match Cr(true) {\n"
            "    Cr(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }\n  }\n",
            "  match Own(@Int.0) {\n    Own(@Int) -> @Int.0\n  }\n")
        entry = _ENTRY.replace(
            "import libb(bone);\n",
            "import libb(bone);\n\nprivate data Shape { Own(Int) }\n",
        )
        gen = _generator(
            tmp_path / "entry-restated",
            {"libb.vera": libb, "main.vera": entry.replace(
                "import liba(aone);\n", "").replace("aone(3) + ", "3 + ")},
        )
        assert list(gen._adt_layouts["Shape"]) == ["Shape$Own"]
        assert list(gen._adt_layouts["mod$libb$Shape"]) == [
            "mod$libb$Shape$Own"]

    def test_a_reserved_name_meets_whatever_either_can_reach(
        self, tmp_path: Path,
    ) -> None:
        """The one pair that once met without either side reaching the
        other: an entry ``data Json`` and a module's shared the prelude's
        slot (E623).  Both take a reserved name (#1469), so each is refused
        at check."""
        libb = """\
module blib;

private data Json { JBlob(Int) }

public fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match JBlob(@Int.0) {
    JBlob(@Int) -> @Int.0
  }
}
"""
        entry = """\
import blib(probe);

private data Json { JMine(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(3)
}
"""
        refusals = _check_refusals(
            tmp_path / "reserved-meets",
            {"blib.vera": libb, "main.vera": entry},
        )
        assert sorted(refusals) == [
            ("E158", "blib.vera"), ("E158", "main.vera")], refusals

    def test_the_code_says_which_pair_was_caught(
        self, tmp_path: Path,
    ) -> None:
        """One rule for both pairs: declarations that meet are two types,
        refused at check wherever the meeting is (#1694) — a pattern of the
        entry's own type against a module's value, an argument of one
        module's type where another's is expected — each naming the owners.
        """
        flowing = _LIBA.replace(
            "public fn aone(@Int -> @Int)", "public fn aone(@Int -> @Shape)",
        ).replace(
            "  match Sq(@Int.0) {\n    Sq(@Int) -> @Int.0\n  }\n",
            "  Sq(@Int.0)\n")
        entry_pair = """\
import liba(aone);

private data Shape { Own(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match aone(6) {
    Own(@Int) -> @Int.0
  }
}
"""
        entry_codes, entry_text = _refused_at_check(
            tmp_path / "pair-entry",
            {"liba.vera": flowing, "main.vera": entry_pair},
        )
        assert "E314" in entry_codes, entry_codes
        assert "liba.Shape" in entry_text, entry_text

        # The same meeting, between two MODULES instead.
        module_codes, module_text = _refused_at_check(
            tmp_path / "pair-modules",
            {"liba.vera": _FLOW_A, "libb.vera": _FLOW_B,
             "main.vera": _ENTRY_FLOW},
        )
        assert module_codes == ["E202"], module_codes
        assert "liba.Shape" in module_text and "libb.Shape" in module_text

    def test_the_entry_keeps_its_constructors_on_the_ctor_axis_too(
        self, tmp_path: Path,
    ) -> None:
        """The constructor axis has its own entry-keeper, and this is the
        cell that makes it load-bearing.

        The entry's ``Own { Sq(Int) }`` and ``liba``'s ``Alpha { Sq(Bool) }``
        are differently-named types sharing one constructor spelling, so the
        flat constructor registry contends on ``Sq`` while the TYPE axis
        sees nothing.  Neither can reach the other, so the pair is qualified
        apart — and it must be ``liba``'s that moves: the entry's program is
        never rewritten, so a rename there would leave its own ``Sq(3)``
        naming a constructor that no longer exists.

        Measured: dropping ``_ENTRY_OWNER`` from the constructor axis's
        keeper set leaves every other cell in this file and in
        ``tests/test_data_namespace_contention_1312.py`` green and reds this
        one alone.
        """
        liba = """\
module liba;

public data Alpha { Sq(Bool) }

public fn aone(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Sq(true) {
    Sq(@Bool) -> if @Bool.0 then { @Int.0 } else { 0 }
  }
}
"""
        entry = """\
import liba(aone);

private data Own { Sq(Int) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Sq(3) {
    Sq(@Int) -> @Int.0
  } + aone(4)
}
"""
        verify, codes, answer = _cell(
            tmp_path / "ctor-entry",
            {"liba.vera": liba, "main.vera": entry},
        )
        assert codes == [], codes
        assert verify == [], verify
        assert answer == ("ok", 7), answer
        gen = _generator(
            tmp_path / "ctor-entry-sym",
            {"liba.vera": liba, "main.vera": entry},
        )
        assert list(gen._adt_layouts["Own"]) == ["Own$Sq"]
        assert "mod$liba$Alpha" in gen._adt_layouts
        assert list(gen._adt_layouts["mod$liba$Alpha"]) == [
            "mod$liba$Alpha$Sq"]
