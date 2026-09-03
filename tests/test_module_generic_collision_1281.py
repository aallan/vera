"""#1281: E608 must not refuse two modules' PROVABLY DISTINCT generics.

The flat-namespace collision rail exists because Pass 2.5 emits every
imported function under one WASM name, so two modules' same-named
declarations would overwrite each other.  A GENERIC emits nothing under its
bare name — only clones — and since #1274 those clones live in a namespace
chosen per OWNER: a generic that owns the importer's bare name mangles to
``gen$Bool``, and one that does not (private, outside the filter, shadowed,
or reached only transitively) mangles to ``mod$<path>$gen$Bool``.  Two
generics in different owner namespaces cannot overwrite each other, and the
rail refused them anyway.

What the rail must keep refusing is the two cases where the pair is NOT
distinct:

* **both own the bare name** — two directly-imported, in-filter, public
  generics really do mangle to one ``gen$Bool``;
* **some namespace can name both** — a module importing two dependencies
  that each export ``gen`` would resolve its own bare ``gen`` to one of them,
  and neither the language nor the implementation had said which.  Spec §8.5
  now says: the name is refused in that namespace (issue 1304), so the
  CHECKER rejects the program (E155) and this rail is its backstop.  Both
  are asserted in the two cells below, through
  :func:`~tests.module_fixture_helpers.build_multi_module_past_check`,
  because a rail that no test can reach is one that can rot into a
  relaxation nobody measures.

Every expected value is the DECLARING module's own answer, taken from the
standalone oracle — each library compiled alone with its own driver — never
from what the diamond happens to emit.  Verify and run are asserted together
in each cell: a clean verify beside the wrong body is exactly the failure the
collision rail was standing in for.
"""

from __future__ import annotations

from pathlib import Path
from typing import ClassVar

import pytest

from tests.codegen_helpers import wat_fn_names
from tests.module_fixture_helpers import (
    build_multi_module,
    build_multi_module_past_check,
    module_value,
)

BASE_ANSWER = 111
MID1_ANSWER = 555
DEEPB_ANSWER = 222


_BASE = f"""\
module base;

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {BASE_ANSWER})
  effects(pure)
{{ {BASE_ANSWER} }}
"""

# `mid1` declares its OWN `gen`, so its bare call is its own (spec §8.5.2)
# even though it also imports `base`.  Private, so the importer can never
# name it: qualified-only, `mod$mid1$gen$Bool`.
_MID1 = f"""\
module mid1;

import base;

private forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {MID1_ANSWER})
  effects(pure)
{{ {MID1_ANSWER} }}

public fn door1(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {MID1_ANSWER})
  effects(pure)
{{ gen(@Bool.0) }}
"""

# `mid2` declares no generic; its bare `gen` is `base`'s, reached through a
# wildcard import.  `base` is TRANSITIVE from the entry program, so its
# generic owns no bare name there either: `mod$base$gen$Bool`.
_MID2 = f"""\
module mid2;

import base;

public fn door2(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {BASE_ANSWER})
  effects(pure)
{{ gen(@Bool.0) }}
"""

# The join is WEIGHTED, not a sum.  `door1 + door2` is commutative, so the
# two doors could swap answers — precisely the defect this file is about —
# and the total would be unchanged: measured, a fixture with the two
# libraries' answers exchanged still produced 666.  Scaling one contribution
# past the other's magnitude makes the pair recoverable from the total, so
# each door's answer is pinned individually by one assertion.
DIAMOND_SCALE = 1000
DIAMOND_TOTAL = MID1_ANSWER * DIAMOND_SCALE + BASE_ANSWER

_DIAMOND_MAIN = f"""\
import mid1(door1);
import mid2(door2);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {DIAMOND_TOTAL})
  effects(pure)
{{ door1(true) * {DIAMOND_SCALE} + door2(true) }}
"""


def _standalone(module_src: str, door: str, answer: int) -> str:
    """A library as the ENTRY program, with its own driver.

    Only the ``module`` header goes; the library's own imports stay, because
    the oracle has to be the library running against the dependencies its
    source names.  What is removed is the diamond — the sibling module whose
    same-named generic the rail was refusing.
    """
    body = module_src.split("\n", 1)[1].lstrip("\n")
    return body + f"""
public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {answer})
  effects(pure)
{{ {door}(true) }}
"""


def _errors(
    diags: list[tuple[str, str]], code: str,
) -> list[tuple[str, str]]:
    """The diagnostics carrying *code*, matched on the CODE.

    Matched on ``Diagnostic.error_code``, never on the description: the
    description never contains the code, so a substring filter fell through
    to the "defined in both imported module" wording — which E609 (data
    types) and E610 (constructors) share verbatim, because they are the same
    ``_emit_collision_error`` call with a different ``kind``.  Every positive
    assertion below wants E608 specifically.
    """
    return [(c, d) for c, d in diags if c == code]


def _answer(
    tmp_path: Path, files: dict[str, str], fn: str = "main",
) -> object:
    """Verify + compile + run, asserting the three agree."""
    verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
    assert not cg_errors, f"codegen errors: {cg_errors}"
    assert not verify_errors, f"verify errors: {verify_errors}"
    kind, payload = module_value(result, fn)
    assert kind == "ok", f"module did not load/run: {payload}"
    return payload


def test_the_collision_filter_matches_on_the_code_not_the_wording() -> None:
    """``_errors`` distinguishes E608 from its same-worded siblings.

    ``_emit_collision_error`` produces E608 (functions), E609 (data types)
    and E610 (constructors) from ONE format string, so all three read
    "… is defined in both imported module …".  A description-substring
    filter therefore matched any of them, and every positive assertion in
    this file would have been satisfied by an ADT collision.
    """
    diags = [
        ("E609", "Data type 'gen' is defined in both imported module "
                 "'a' and 'b'."),
        ("E610", "Constructor 'Gen' is defined in both imported module "
                 "'a' and 'b'."),
    ]
    assert _errors(diags, "E608") == []
    assert _errors([*diags, ("E608", "Function 'gen' is defined in both "
                                     "imported module 'a' and 'b'.")],
                   "E608") == [
        ("E608", "Function 'gen' is defined in both imported module "
                 "'a' and 'b'."),
    ]


class TestStandaloneOracles:
    """What each library's source commits to, with no diamond in the picture."""

    def test_base_answers_its_own(self, tmp_path: Path) -> None:
        assert _answer(
            tmp_path,
            {"main.vera": _standalone(_BASE, "gen", BASE_ANSWER)},
        ) == BASE_ANSWER

    def test_mid1_door_answers_its_own_generic(self, tmp_path: Path) -> None:
        """``mid1`` imports ``base`` AND declares its own ``gen``; §8.5.2 says
        its bare call is its own, and that is the answer the diamond must
        preserve."""
        assert _answer(
            tmp_path,
            {"base.vera": _BASE,
             "main.vera": _standalone(_MID1, "door1", MID1_ANSWER)},
        ) == MID1_ANSWER

    def test_mid2_door_answers_its_dependencys_generic(
        self, tmp_path: Path,
    ) -> None:
        files = {
            "base.vera": _BASE,
            "main.vera": _standalone(_MID2, "door2", BASE_ANSWER),
        }
        assert _answer(tmp_path, files) == BASE_ANSWER


class TestDiamond:
    """The issue's shape: ``base`` public, ``mid1`` private, both named
    ``gen``, reached through two doors."""

    _FILES: ClassVar[dict[str, str]] = {
        "base.vera": _BASE, "mid1.vera": _MID1,
        "mid2.vera": _MID2, "main.vera": _DIAMOND_MAIN,
    }

    def test_compiles_and_each_door_runs_its_own_generic(
        self, tmp_path: Path,
    ) -> None:
        # Weighted, so the two doors' answers are separable from the total —
        # a plain sum is satisfied by them swapping, which is the defect.
        assert _answer(tmp_path, dict(self._FILES)) == DIAMOND_TOTAL

    def test_no_collision_diagnostic(self, tmp_path: Path) -> None:
        _, result, _ = build_multi_module(tmp_path, dict(self._FILES))
        # Every diagnostic, not just the errors: an E608 demoted to a warning
        # would still be the rail firing on a pair it must not refuse.
        collisions = _errors(
            [(d.error_code, d.description) for d in result.diagnostics],
            "E608",
        )
        assert not collisions, f"E608 still refuses the pair: {collisions}"

    def test_the_two_clones_are_distinct_symbols(
        self, tmp_path: Path,
    ) -> None:
        """The classification's claim, read off the emitted module: nothing
        is emitted under a bare ``gen``, and each owner has its own clone."""
        _, result, _ = build_multi_module(tmp_path, dict(self._FILES))
        emitted = wat_fn_names(result.wat)
        # Absence, so the unbounded prefix is the conservative direction: ANY
        # `gen$…` in the entry's bare clone namespace is the failure.
        assert "(func $gen$" not in result.wat, (
            f"a generic was emitted in the ENTRY's bare clone namespace, "
            f"where neither owner belongs; emitted: {emitted}"
        )
        # Presence, so matched EXACTLY — `"(func $mod$mid1$gen$Bool" in wat`
        # is a prefix test a longer mangled clone would satisfy.
        assert "mod$mid1$gen$Bool" in emitted, emitted
        assert "mod$base$gen$Bool" in emitted, emitted


class TestTwoTransitiveImporters:
    """Each module bare-calls its OWN dependency's public generic.

    Refused at COMPILE while ``vera verify`` returned rc=0 — a loud
    verify-vs-compile disagreement (issue comment).  After the relaxation the
    two phases agree, in the direction the source means.
    """

    _DEEPA = _BASE.replace("module base;", "module deepa;")
    _DEEPB = f"""\
module deepb;

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {DEEPB_ANSWER})
  effects(pure)
{{ {DEEPB_ANSWER} }}
"""
    _MIDA = _MID2.replace("module mid2;", "module mida;").replace(
        "import base;", "import deepa;",
    ).replace("door2", "doora")
    _MIDB = (
        _MID2.replace("module mid2;", "module midb;")
        .replace("import base;", "import deepb;")
        .replace("door2", "doorb")
        .replace(f"== {BASE_ANSWER}", f"== {DEEPB_ANSWER}")
    )
    # Weighted for the same reason as the diamond above: the two importers
    # exchanging dependencies is exactly the failure, and a sum cannot see it.
    _TOTAL = BASE_ANSWER * DIAMOND_SCALE + DEEPB_ANSWER

    _MAIN = f"""\
import mida(doora);
import midb(doorb);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {_TOTAL})
  effects(pure)
{{ doora(true) * {DIAMOND_SCALE} + doorb(true) }}
"""

    def test_each_importer_reaches_its_own_dependency(
        self, tmp_path: Path,
    ) -> None:
        assert _answer(tmp_path, {
            "deepa.vera": self._DEEPA, "deepb.vera": self._DEEPB,
            "mida.vera": self._MIDA, "midb.vera": self._MIDB,
            "main.vera": self._MAIN,
        }) == self._TOTAL


class TestQualifiedOnlyGenericsAreKeyedPerOwner:
    """The other half the issue required: relaxing the rail without fixing
    the REGISTRATION would swap a loud refusal for a silent pick-a-winner.

    A qualified-only generic emits nothing under its bare name — its clones
    are ``mod$<path>$name$…`` — but it used to inject a bare entry into the
    shared registries anyway, first-module-wins, and two families of
    consumer read those per NAME: ``MonoContext.fn_names`` (the #1207 shadow
    guard) and the return-type registries the call-rewrite and discovery
    type a bare call from.  Withholding the bare key makes any surviving
    entry the OWNER's by construction rather than by module order.

    **What these cells prove, honestly.**  The behavioural cell below is
    green today for #1299's reason, not this one: once discovery and the
    clone-name override read the call site's LEXICAL scope, an invisible
    declaration stops being consulted whether or not its bare key exists, and
    reverting BOTH withholdings leaves every suite and all 224 conformance
    programs green.  So the two withholdings are now defence in depth over
    four consumers that happen not to look — a `_declared_return_clone_name`
    and a `_get_arg_type_info` that both bail for generics, a set-membership
    test, and a WAT-type registry — and they are pinned STRUCTURALLY, on the
    registration tables they act on, because that is the contract they
    actually have.  Two separate cells, because they are two tables: a
    mutation to one must not be masked by the other.
    """

    _LIB = """\
module lib;

private forall<T> fn get(@T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ true }

public fn touch(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ get(@Int.0) }
"""

    @staticmethod
    def _main(helper: str) -> str:
        return f"""\
import lib(touch);

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{{ @T.0 }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<Int>](@Int = 42007) {{
    get(@Unit) -> {{ resume(@Int.0) }},
    put(@Int) -> {{ resume(()) }}
  }} in {{
    idg({helper}(()))
  }}
}}
"""

    def test_the_cells_type_drives_the_instantiation(
        self, tmp_path: Path,
    ) -> None:
        """``idg(get(()))`` instantiates at the CELL's type.

        The checker's answer is nailed by a type oracle: the invisible
        generic returns ``@Bool`` while ``main`` returns ``@Int`` from the
        call and checks green, which is only possible if the call was typed
        from the ``State<Int>`` cell.  Pre-fix the two sides named different
        clones and ``main`` was dropped [E602].

        Kept here because it is the shape this class's fixture builds, but
        the thing that holds it green is #1299's scope narrowing — the
        generic sibling of the routes in
        ``tests/test_lexical_fn_scope_1299.py::TestDiscoveryLeg``.
        """
        assert _answer(
            tmp_path, {"lib.vera": self._LIB, "main.vera": self._main("get")},
        ) == 42007

    @staticmethod
    def _diamond_registries(tmp_path: Path) -> tuple[set[str], set[str]]:
        """``(_fn_sigs keys, _fn_ret_type_exprs keys)`` after the diamond.

        The checker's artifacts are threaded into the generator, as
        ``cmd_compile`` threads them: the call was here before them and
        discarded its result, which read as a pipeline the helper was not
        actually running.  The two registries below are populated the same
        way either way — they are built from the declarations — so this is
        the fixture matching the product, not a changed measurement.
        """
        from vera.checker import typecheck_with_artifacts
        from vera.codegen.core import CodeGenerator
        from vera.parser import parse_to_ast
        from vera.resolver import ModuleResolver

        tmp_path.mkdir(parents=True, exist_ok=True)
        files = {
            "base.vera": _BASE, "mid1.vera": _MID1,
            "mid2.vera": _MID2, "main.vera": _DIAMOND_MAIN,
        }
        for name, src in files.items():
            (tmp_path / name).write_text(src, encoding="utf-8")
        main_path = tmp_path / "main.vera"
        source = files["main.vera"]
        program = parse_to_ast(source)
        resolved = ModuleResolver(_root=tmp_path).resolve_imports(
            program, main_path,
        )
        _diags, arts = typecheck_with_artifacts(
            program, source, file=str(main_path), resolved_modules=resolved,
            collect_module_artifacts=True,
        )
        gen = CodeGenerator(
            source=source, file=str(main_path), resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
            module_artifacts=arts.module_artifacts,
        )
        gen.compile_program(program)
        return set(gen._fn_sigs), set(gen._fn_ret_type_exprs)

    def test_no_bare_signature_entry_for_a_qualified_only_generic(
        self, tmp_path: Path,
    ) -> None:
        """``_fn_sigs`` — the registry ``MonoContext.fn_names`` and both
        ``fn_ret_types`` maps are derived from — carries no bare ``gen``.

        Both modules' generics are qualified-only here, so a bare key could
        only ever be one of them, chosen by whichever module registered
        first.  Asserted beside the guarantee that the CLONES are present, so
        a fix that simply stopped registering the generics would fail.
        """
        sigs, _ = self._diamond_registries(tmp_path)
        assert "gen" not in sigs, (
            "a qualified-only generic injected a bare signature key; a "
            "per-name consumer would take whichever module got there first"
        )
        assert {"mod$mid1$gen$Bool", "mod$base$gen$Bool"} <= sigs, (
            f"the per-owner clones must still be registered, got "
            f"{sorted(n for n in sigs if 'gen' in n)}"
        )

    def test_no_bare_return_type_entry_for_a_qualified_only_generic(
        self, tmp_path: Path,
    ) -> None:
        """The same for ``_fn_ret_type_exprs``, the table the call-rewrite's
        clone-naming override and discovery's argument-type recovery read.

        A separate cell from the signature one on purpose: the two
        withholdings are two lines over two tables, and a single cell would
        let a mutation to either hide behind the other.
        """
        _, ret_exprs = self._diamond_registries(tmp_path)
        assert "gen" not in ret_exprs, (
            "a qualified-only generic injected a bare return-type key"
        )
        assert any("$gen$" in n for n in ret_exprs), (
            f"the per-owner clones must still carry return types, got "
            f"{sorted(n for n in ret_exprs if 'gen' in n)}"
        )

    def test_rename_control_answers_the_same(self, tmp_path: Path) -> None:
        """The identical importer, with only the MODULE's declaration renamed.

        Nothing about ``main`` changes, so a different answer here would mean
        the fixture had stopped isolating the name collision and every cell
        above was measuring something else.
        """
        assert _answer(
            tmp_path,
            {"lib.vera": self._LIB.replace("get", "gettt"),
             "main.vera": self._main("get")},
        ) == 42007

    def test_a_bare_name_owner_still_registers_its_entry(
        self, tmp_path: Path,
    ) -> None:
        """The withholding is per-OWNER, not a blanket exclusion of generics:
        a public, in-filter, directly-imported generic owns the bare name and
        keeps its registration — that is what lets the importer instantiate
        it from its own call site (#774)."""
        lib = """\
module lib;

public forall<T> fn shared(@T -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{ 111 }
"""
        main = """\
import lib(shared);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{ shared(true) }
"""
        assert _answer(
            tmp_path, {"lib.vera": lib, "main.vera": main},
        ) == 111


class TestTheRailStillRefusesRealCollisions:
    """The relaxation is narrow.  Both halves of what E608 protects stay."""

    _LIB_A = _BASE.replace("module base;", "module liba;")
    _LIB_B = f"""\
module libb;

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {DEEPB_ANSWER})
  effects(pure)
{{ {DEEPB_ANSWER} }}
"""

    def test_two_bare_name_owners_still_collide(
        self, tmp_path: Path,
    ) -> None:
        """Both public, both in filter, both directly imported: both own the
        entry's bare name, so both clones really do mangle to ``gen$Bool``.

        Refused TWICE since #1304, and both are asserted.  The entry
        namespace can name both suppliers, so the checker rejects the
        program (E155) before codegen sees it; the rail behind that is still
        driven here, because a rail nothing exercises is one that can rot
        into a relaxation nobody measures.
        """
        main = """\
import liba(gen);
import libb(gen);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ gen(true) }
"""
        check_errors, result, cg_errors = build_multi_module_past_check(
            tmp_path,
            {"liba.vera": self._LIB_A, "libb.vera": self._LIB_B,
             "main.vera": main},
        )
        assert _errors(check_errors, "E155"), (
            f"the checker let two bare-name owners through: {check_errors}"
        )
        assert _errors(cg_errors, "E608"), (
            f"the rail let two bare-name owners through: {cg_errors}"
        )

    def test_a_namespace_seeing_both_still_collides(
        self, tmp_path: Path,
    ) -> None:
        """One module importing two dependencies that each export ``gen``.

        Its own bare ``gen`` names one of them and nothing had said which.
        Both generics are qualified-only from the entry's point of view, so
        the ownership classification alone would relax this; the ambiguity
        gate is what keeps it loud.

        This is the shape #1304 was opened on and closed by.  The CHECKER's
        pick was not an order — it was a set-iteration artefact: over eight
        runs of one unchanged program the type oracle accepted four times
        and reported ``body has type Bool`` four times, stable under a fixed
        ``PYTHONHASHSEED`` and varying with the seed rather than with which
        import is written first.  Codegen's reroute map IS positional,
        last-wins.  Spec §8.5 now refuses the shape outright, so there is no
        pick left to be nondeterministic; the flap is pinned dead in
        ``tests/test_ambiguous_import_refusal_1304.py``.

        Asserted at both layers for the reason above: the checker refuses
        the program, and the rail behind it must still be refusing it.
        """
        midc = """\
module midc;

import liba;
import libb;

public fn doorc(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ gen(@Bool.0) }
"""
        main = """\
import midc(doorc);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ doorc(true) }
"""
        check_errors, result, cg_errors = build_multi_module_past_check(
            tmp_path,
            {"liba.vera": self._LIB_A, "libb.vera": self._LIB_B,
             "midc.vera": midc, "main.vera": main},
        )
        assert _errors(check_errors, "E155"), (
            f"an ambiguous bare name was let through: {check_errors}"
        )
        assert _errors(cg_errors, "E608"), (
            f"an ambiguous bare name was let through: {cg_errors}"
        )

    def test_a_generic_beside_a_non_generic_still_collides(
        self, tmp_path: Path,
    ) -> None:
        """The relaxation is for GENERICS, and stays there.

        A qualified-only generic in one module beside a same-named
        NON-generic in another occupies two different flat identities too —
        ``mod$liba$gen$Bool`` and ``$gen`` — so the two conditions below it
        would let the pair through.  It keeps its refusal because nobody has
        measured that shape, and the narrow scope is the point: a relaxation
        is only as good as the classification behind it, and the
        classification (``module_qualified_generic_names``) speaks about
        generics.
        """
        liba = f"""\
module liba;

private forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ {BASE_ANSWER} }}

public fn door1(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ gen(@Bool.0) }}
"""
        libb = f"""\
module libb;

private fn gen(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ {DEEPB_ANSWER} }}

public fn door2(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ gen(()) }}
"""
        main = """\
import liba(door1);
import libb(door2);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ door1(true) + door2(()) }
"""
        _, result, cg_errors = build_multi_module(
            tmp_path,
            {"liba.vera": liba, "libb.vera": libb, "main.vera": main},
        )
        assert _errors(cg_errors, "E608"), (
            f"a generic/non-generic pair was let through: {cg_errors}"
        )

    def test_two_bare_name_owners_collide_whatever_the_ambiguity_says(
        self,
    ) -> None:
        """The owner condition, asked of the predicate directly.

        End to end it is belt and braces: two generics can only BOTH own the
        entry's bare name when the entry imports both, publicly and in
        filter, and declares neither — which is exactly what makes the name
        ambiguous there, so the gate above catches the shape first.  The two
        conditions coincide through a chain of reasoning about two
        separately-derived tables, and a drift between them would silently
        relax a real clone collision, so the condition is asserted on its own
        rather than left resting on that coincidence.
        """
        from vera.codegen.core import CodeGenerator

        gen = CodeGenerator(source="", file="<test>")
        gen._ambiguous_imported_fn_names = frozenset()
        generics = {("a",): frozenset({"gen"}), ("b",): frozenset({"gen"})}
        # Neither is qualified-only: both own the entry's bare name, so both
        # sets of clones mangle to `gen$…`.
        assert not gen._declarations_cannot_collide(
            "gen", ("a",), ("b",), generics, {("a",): set(), ("b",): set()},
        )
        # One qualified-only: distinct namespaces, so the pair is fine.
        assert gen._declarations_cannot_collide(
            "gen", ("a",), ("b",), generics,
            {("a",): {"gen"}, ("b",): set()},
        )

    def test_a_local_declaration_disambiguates_two_dependencies(
        self, tmp_path: Path,
    ) -> None:
        """A namespace importing two ``gen``s but declaring its OWN is not
        ambiguous: §8.5.2 gives every bare call in it to the local
        declaration, so the two imports are never resolved against.

        Three same-named generics, all qualified-only, all in distinct clone
        namespaces — the diamond one module wider.
        """
        midd = f"""\
module midd;

import liba;
import libb;

private forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {MID1_ANSWER})
  effects(pure)
{{ {MID1_ANSWER} }}

public fn doord(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {MID1_ANSWER})
  effects(pure)
{{ gen(@Bool.0) }}
"""
        main = f"""\
import midd(doord);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MID1_ANSWER})
  effects(pure)
{{ doord(true) }}
"""
        assert _answer(tmp_path, {
            "liba.vera": self._LIB_A, "libb.vera": self._LIB_B,
            "midd.vera": midd, "main.vera": main,
        }) == MID1_ANSWER

    @pytest.mark.parametrize("vis", ["public", "private"])
    def test_two_non_generics_still_collide(
        self, tmp_path: Path, vis: str,
    ) -> None:
        """Non-generics are untouched: each really is emitted under the bare
        ``$name`` in Pass 2.5, whatever its visibility."""
        # `{{n}}` stays doubled — it is the literal `{n}` placeholder the
        # `.replace` below fills in.  The BODY braces were doubled too, which
        # emitted `{{ 1 }}`: a block nested in a block, accepted only
        # incidentally by the parser and unlike every other fixture here.
        lib = f"""\
module lib{{n}};

{vis} fn plain(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ 1 }}

public fn door{{n}}(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ plain(()) }}
"""
        main = """\
import lib1(door1);
import lib2(door2);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ door1(()) + door2(()) }
"""
        _, result, cg_errors = build_multi_module(
            tmp_path,
            {"lib1.vera": lib.replace("{n}", "1"),
             "lib2.vera": lib.replace("{n}", "2"),
             "main.vera": main},
        )
        assert _errors(cg_errors, "E608"), (
            f"two same-named non-generics were let through: {cg_errors}"
        )


# =====================================================================
# #1387 — E155's prescribed remedy must actually compile
# =====================================================================


_LIBA_PICK = """\
module liba;

public fn pick(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 100
}
"""

_LIBB_PICK = _LIBA_PICK.replace("module liba;", "module libb;").replace(
    "+ 100", "+ 200")

_ENTRY_LOCAL_PLUS_QUALIFIED = """\
import liba;
import libb;

private fn pick(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(1) + liba::pick(1) + libb::pick(1)
}
"""


class TestPrescribedRemedyCompiles:
    """E155 and E608 must not prescribe contradictory fixes (#1387).

    §8.5.2.2's diagnostic tells the reader, verbatim, to "declare 'pick' in
    this file — a local declaration takes every bare call — and use the
    module-qualified form 'liba::pick(...)' for the imported ones".  Doing
    exactly that was `[E608]` at compile, whose own fix text then said to
    rename the declaration in one of the source modules — so the remedy the
    checker named was unreachable, and #187's "no way to resolve the
    collision without renaming" was still literally true.

    No bare-name collision exists in that shape: with a local `pick`
    declared, BOTH modules' functions are shadowed and
    `_register_shadowed_import` emits each under its own `mod$<path>$pick`.
    The rail fired on provenance alone, before that ran — the over-breadth
    #1281 removed for generics, still in place for non-generics, which land
    in distinct namespaces by exactly the same rule.
    """

    def test_the_remedy_the_checker_prescribes_runs(
        self, tmp_path: Path,
    ) -> None:
        """Base: `[E608]` at compile on a check-green program."""
        _verr, result, cg_errors = build_multi_module(
            tmp_path / "remedy",
            {"liba.vera": _LIBA_PICK, "libb.vera": _LIBB_PICK,
             "main.vera": _ENTRY_LOCAL_PLUS_QUALIFIED},
        )
        assert cg_errors == [], cg_errors
        # 1 (local) + 101 (liba) + 201 (libb): each qualified call reaches its
        # OWN module, which a first-wins bare emission could not do.
        assert module_value(result) == ("ok", 303)

    def test_each_module_keeps_its_own_symbol(self, tmp_path: Path) -> None:
        """Both are emitted, under distinct owner-qualified names.

        The run value alone would also be satisfied by one body being
        emitted twice if the two happened to agree; these are the symbols.
        """
        _verr, result, _cg = build_multi_module(
            tmp_path / "symbols",
            {"liba.vera": _LIBA_PICK, "libb.vera": _LIBB_PICK,
             "main.vera": _ENTRY_LOCAL_PLUS_QUALIFIED},
        )
        assert "$mod$liba$pick" in result.wat, "liba's body is missing"
        assert "$mod$libb$pick" in result.wat, "libb's body is missing"

    def test_without_a_local_declaration_the_checker_still_refuses(
        self, tmp_path: Path,
    ) -> None:
        """The negative twin: nothing owns the bare name, so §8.5.2.2 stands.

        Relaxing the compile rail must not relax the CHECK-phase ambiguity —
        two imports supplying one bare name is refused there, and that is
        the diagnostic whose fix text this change makes true.
        """
        entry = """\
import liba;
import libb;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  liba::pick(1) + libb::pick(1)
}
"""
        check_errors, _result, _cg = build_multi_module_past_check(
            tmp_path / "no-local",
            {"liba.vera": _LIBA_PICK, "libb.vera": _LIBB_PICK,
             "main.vera": entry},
        )
        assert "E155" in [c for c, _ in check_errors], check_errors

    def test_a_genuinely_colliding_bare_export_still_gets_e608(
        self, tmp_path: Path,
    ) -> None:
        """The rail must keep the case it exists for.

        With `liba`'s `pick` imported bare and unshadowed, it OWNS the flat
        `$pick`; `libb`'s would overwrite it.  One owner is one too many for
        the relaxation, which requires that NEITHER module owns the name.
        """
        entry = """\
import liba(pick);
import libb;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(1) + libb::pick(1)
}
"""
        errors, _result, cg_errors = build_multi_module_past_check(
            tmp_path / "real-collision",
            {"liba.vera": _LIBA_PICK, "libb.vera": _LIBB_PICK,
             "main.vera": entry},
        )
        codes = [c for c, _ in errors] + [c for c, _ in cg_errors]
        assert "E155" in codes or "E608" in codes, codes
