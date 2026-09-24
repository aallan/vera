"""#1274: a module generic that does not own the importer's bare name must be
reached under its module-qualified ``<path>::name`` identity.

Pre-fix, only a PRIVATE module generic was rerouted onto that identity (#1000 /
#1029).  A PUBLIC one was rerouted never — so a module's own body calling its
own generic by bare name was resolved in the IMPORTER's flat namespace, where
the bare name belongs to whatever the importer declares.  Three consequences,
all reproduced below:

* **False Tier-1** — the importer's same-named generic clone silently runs in
  place of the module's.  ``vera check`` / ``verify`` are clean and the module's
  own ``ensures`` is violated at run (the module promises 111, the importer's
  body returns 999).
* **Invalid WASM** on a type-discriminating shape — both modules' ``gen2``
  mangle to one ``gen2$Bool``, so the surviving clone has the other's WAT type.
* **A dangling ``$gen2``** where the module generic is public but outside the
  importer's import filter: it was registered in NO clone namespace at all.

The rule the fix installs is the one every module function follows
(:func:`vera.monomorphize.owns_entry_bare_name`): a module function is reached
under ``<path>::name`` exactly when its bare name in the importer's flat
namespace does not denote that module's declaration — public **and** in-filter
**and** not a name the importer holds.  Generic and non-generic share that one
predicate (#1498).

Every cell asserts the verify verdict AND the runtime value in ONE test,
against the standalone oracle: the library compiled ALONE answers 111, so 111
is what every import shape must answer.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest
import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import CompileResult
from vera.codegen.core import CodeGenerator
from vera.checker.core import resolve_calls
from vera.monomorphize import fn_ownership
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver, ResolvedModule
from vera.runtime.traps import WasmTrapError
from vera.verifier import ContractVerifier, verify

# The library's private answer.  Chosen so it cannot coincide with the
# importer's (999) nor with any default/fallback in the mangler.
LIB_ANSWER = 111
MAIN_ANSWER = 999


def _lib(gen_vis: str) -> str:
    """A module whose public door calls its own generic by BARE name."""
    return f"""\
module lib;

private fn v(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ {LIB_ANSWER} }}

{gen_vis} forall<T> fn gen2(@T -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ v(()) }}

public fn door(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ gen2(@Bool.0) }}
"""


def _main(gen_vis: str, imports: str) -> str:
    """An importer that declares its OWN ``gen2`` (and its own ``v``)."""
    imp = "import lib;" if imports is None else f"import lib({imports});"
    return f"""\
{imp}

private fn v(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ {MAIN_ANSWER} }}

{gen_vis} forall<T> fn gen2(@T -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ v(()) }}

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ gen2(true) }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""


# The oracle: the library compiled ALONE, with its own driver in place of the
# importer.  Whatever the import door does, this is the answer the module's
# source (and its proved `ensures`) commits to.
_STANDALONE = _lib("private").replace("module lib;\n", "") + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{ door(true) }
"""


def _build(
    tmp_path: Path, files: dict[str, str],
    main_name: str = "main.vera",
) -> tuple[list[str], CompileResult, list[str]]:
    """Type-check + verify + compile *main_name* exactly as ``vera run`` does.

    Returns ``(verify_errors, compile_result_or_None, codegen_errors)``.
    """
    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, src in files.items():
        (tmp_path / name).write_text(src, encoding="utf-8")
    main_path = tmp_path / main_name
    source = files[main_name]
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(program, main_path)
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(main_path), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    check_errors = [d.description for d in diags if d.severity == "error"]
    assert not check_errors, f"typecheck errors: {check_errors}"
    vres = verify(program, source, file=str(main_path),
                  resolved_modules=resolved)
    verify_errors = [
        d.description for d in vres.diagnostics if d.severity == "error"
    ]
    result = codegen_compile(
        program, source=source, file=str(main_path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    cg_errors = [
        d.description for d in result.diagnostics if d.severity == "error"
    ]
    return verify_errors, result, cg_errors


def _value(
    result: CompileResult, fn: str = "main",
) -> tuple[str, object]:
    """``(kind, payload)`` — ``("ok", value)`` or ``("trap", message)``."""
    try:
        return "ok", execute(result, fn_name=fn).value
    except (WasmTrapError, wasmtime.WasmtimeError, wasmtime.Trap) as exc:
        return "trap", str(exc)


def _assert_cell(
    tmp_path: Path, lib_vis: str, main_vis: str,
    imports: str | None,
) -> None:
    """The whole obligation for one cell, in ONE test: check + verify clean,
    valid WASM, and the DECLARING module's answer at run."""
    verify_errors, result, cg_errors = _build(
        tmp_path, {"lib.vera": _lib(lib_vis),
                   "main.vera": _main(main_vis, imports)},
    )
    assert not cg_errors, f"codegen errors: {cg_errors}"
    kind, payload = _value(result)
    # Verify and run must AGREE.  A clean verify beside a runtime postcondition
    # violation is the false Tier-1 this issue is about, so both halves are
    # asserted together rather than in sibling tests.
    assert not verify_errors, f"verify errors: {verify_errors}"
    assert kind == "ok", (
        f"lib={lib_vis} main={main_vis} imports={imports!r}: the module's own "
        f"generic did not run — {payload}"
    )
    assert payload == LIB_ANSWER, (
        f"lib={lib_vis} main={main_vis} imports={imports!r}: ran the IMPORTER's "
        f"gen2 ({payload}) where the declaring module's body answers "
        f"{LIB_ANSWER} — a false Tier-1 (verify was clean)"
    )
    # The local generic must be untouched by the fix: it still owns the bare
    # name for the importer's own call.
    lkind, lvalue = _value(result, "useLocal")
    assert (lkind, lvalue) == ("ok", MAIN_ANSWER), (
        f"the importer's own gen2 must still answer {MAIN_ANSWER}, "
        f"got {lkind}/{lvalue}"
    )


class TestStandaloneOracle:
    """What the library's source commits to, with no importer in the picture."""

    def test_standalone_library_answers_111(self, tmp_path) -> None:
        verify_errors, result, cg_errors = _build(
            tmp_path, {"main.vera": _STANDALONE},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        assert _value(result) == ("ok", LIB_ANSWER)


class TestVisibilityMatrix:
    """All four cells of (module generic visibility x importer generic
    visibility).  Pre-fix the two ``lib=public`` cells were false Tier-1s; the
    ``lib=private`` cells were already correct (#1000's reroute) and are the
    regression half of the matrix."""

    @pytest.mark.parametrize("lib_vis", ["public", "private"])
    @pytest.mark.parametrize("main_vis", ["public", "private"])
    def test_cell(self, tmp_path, lib_vis: str, main_vis: str) -> None:
        _assert_cell(tmp_path, lib_vis, main_vis, "door")


class TestImportFilterDimension:
    """The importer's filter changes which names it can SPELL, never which body
    the module's own call runs.  All three spellings answer the module's 111."""

    @pytest.mark.parametrize(
        "imports", ["door", "gen2, door", None],
        ids=["out_of_filter", "in_filter", "wildcard"],
    )
    def test_filter_shape(
        self, tmp_path: Path, imports: str | None,
    ) -> None:
        _assert_cell(tmp_path, "public", "private", imports)


class TestUnshadowedOutOfFilter:
    """A public module generic OUTSIDE the importer's filter, with NO local
    shadow, was registered in no clone namespace at all: its module's own bare
    call assembled to ``unknown func: failed to find name $gen2``.  Loud, but
    the same registration hole."""

    def test_module_generic_outside_filter_is_emitted(self, tmp_path) -> None:
        main = f"""\
import lib(door);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""
        verify_errors, result, cg_errors = _build(
            tmp_path, {"lib.vera": _lib("public"), "main.vera": main},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        assert _value(result) == ("ok", LIB_ANSWER)


class TestModuleToModuleHop:
    """A module's bare call to ANOTHER module's qualified-only generic (F1).

    The classification was per-module-own, so ``mid`` — which declares no
    generics at all — had nothing rerouted and its bare ``gen(...)`` was
    resolved in the importer's flat namespace, where the ENTRY's same-named
    generic owns the name.  ``vera verify`` clean, ``mid``'s proved
    postcondition violated at run (or, with a looser contract, a silent 999
    where the declaring module answers 111).

    The reroute now consults each module's imports under the SAME predicate,
    keyed by owner, because ``<path>::name`` is per-owner: ``mid``'s call
    must reach ``deep::gen``.
    """

    _DEEP = f"""\
module deep;

private fn vd(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ {LIB_ANSWER} }}

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ vd(()) }}
"""

    _MID = f"""\
module mid;

import deep;

public fn door(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ gen(@Bool.0) }}
"""

    # The loud spelling: `door`'s own postcondition pins the answer, so a
    # captured call is a runtime violation.
    _MAIN_LOUD = f"""\
import mid(door);

private fn vm(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ {MAIN_ANSWER} }}

private forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ vm(()) }}

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ gen(true) }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""

    # The SILENT spelling: every contract here is satisfied by both answers, so
    # nothing traps — the wrong body just returns the wrong number.  This is the
    # shape a contract-only assertion would miss entirely.
    _MAIN_SILENT = f"""\
import mid(door);

private fn vm(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ {MAIN_ANSWER} }}

private forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{ vm(()) }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{ door(true) }}
"""

    def _files(self, main_src: str) -> dict[str, str]:
        return {
            "deep.vera": self._DEEP,
            "mid.vera": self._MID,
            "main.vera": main_src,
        }

    @pytest.mark.parametrize(
        "main_src", [_MAIN_LOUD, _MAIN_SILENT], ids=["loud", "silent"],
    )
    def test_hop_runs_the_declaring_module(self, tmp_path, main_src) -> None:
        verify_errors, result, cg_errors = _build(
            tmp_path, self._files(main_src),
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        kind, payload = _value(result)
        assert kind == "ok", f"the hop did not compile to a runnable module: {payload}"
        assert payload == LIB_ANSWER, (
            f"mid's bare call to deep's generic ran the IMPORTER's body "
            f"({payload}) where deep answers {LIB_ANSWER}"
        )

    def test_hop_is_symmetric_between_the_two_sides(self, tmp_path) -> None:
        """Both sides must key the hop's clone identically, or the clone that
        runs is verified under a name nobody checked."""
        tmp_path.mkdir(parents=True, exist_ok=True)
        files = self._files(self._MAIN_LOUD)
        for name, src in files.items():
            (tmp_path / name).write_text(src, encoding="utf-8")
        mods = [
            ResolvedModule(
                path=(stem,), file_path=tmp_path / f"{stem}.vera",
                program=parse_to_ast(files[f"{stem}.vera"]),
                source=files[f"{stem}.vera"],
                # The shape production resolution builds: `main` imports
                # `mid`, so `deep` is transitive.  `ResolvedModule` defaults
                # `direct` to True, and the classification predicate reads
                # it, so leaving it defaulted made the symmetry claim below
                # cover a directness no run produces (PR #1283 review).
                direct=(stem == "mid"),
            )
            for stem in ("deep", "mid")
        ]
        mainp = tmp_path / "main.vera"
        gen = CodeGenerator(
            source=self._MAIN_LOUD, file=str(mainp), resolved_modules=mods,
        )
        gen.compile_program(parse_to_ast(self._MAIN_LOUD))
        codegen_set = set(getattr(gen, "_emitted_instances", set()))
        verifier = ContractVerifier(
            source=self._MAIN_LOUD, file=str(mainp), resolved_modules=mods,
        )
        verifier.register_program(parse_to_ast(self._MAIN_LOUD))
        verifier_set = {
            (n, ct) for n, cts in verifier._instances.items() for ct in cts
        }
        assert ("deep::gen", ("Bool",)) in codegen_set, (
            f"the hop's clone must be emitted under its OWNING module's base, "
            f"got {sorted(codegen_set)}"
        )
        assert codegen_set == verifier_set, (
            f"codegen {sorted(codegen_set)} != verifier {sorted(verifier_set)}"
        )

    def test_module_own_generic_reached_transitively(self, tmp_path) -> None:
        """The neighbouring shape, and the one this PR covered first: `mid`
        calls a NON-generic door of `deep`, and it is `deep`'s OWN body that
        bare-calls its own qualified-only generic.  Two hops from the entry, so
        the classification has to reach a module the entry never imported."""
        deep = f"""\
module deep;

public forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ {LIB_ANSWER} }}

public fn cap(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ g(@Bool.0) }}
"""
        mid = f"""\
module mid;

import deep(cap);

public fn use(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ cap(@Bool.0) }}
"""
        main = f"""\
import mid(use);

private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ {MAIN_ANSWER} }}

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ g(true) }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ use(true) }}
"""
        verify_errors, result, cg_errors = _build(
            tmp_path,
            {"deep.vera": deep, "mid.vera": mid, "main.vera": main},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        assert _value(result) == ("ok", LIB_ANSWER)


class TestTransitiveVisibility:
    """A module reached only TRANSITIVELY contributes nothing to the entry's
    namespace (spec §8.6.4), so none of its generics can own the entry's bare
    name.

    The classification asked ``import_names.get(path)``, which answers ``None``
    for such a module — the same spelling that means "wildcard import" — so
    every public generic of a transitive module was read as a bare-name owner.
    Latent rather than live: the checker refuses a bare call to it from the
    entry (`E200`), and two transitive namesakes each take their own
    ``<path>::name`` (#1498), so no program observed the
    misclassification.  It is
    corrected for parity, because the predicate is supposed to BE §8.6.4 and a
    reader who trusts it should not have to know which rail happens to cover a
    given shape.

    Driven through the production `ModuleResolver`, which is what sets
    ``direct``; a hand-built `ResolvedModule` defaults it to ``True`` and would
    never exercise this path.
    """

    _DEEP = f"""\
module deep;

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ {LIB_ANSWER} }}
"""

    _MID = f"""\
module mid;

import deep;

public fn door(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ gen(@Bool.0) }}
"""

    _MAIN = f"""\
import mid(door);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""

    def _resolve(self, tmp_path: Path):
        tmp_path.mkdir(parents=True, exist_ok=True)
        for name, src in (("deep.vera", self._DEEP), ("mid.vera", self._MID),
                          ("main.vera", self._MAIN)):
            (tmp_path / name).write_text(src, encoding="utf-8")
        mainp = tmp_path / "main.vera"
        program = parse_to_ast(self._MAIN)
        resolved = ModuleResolver(_root=tmp_path).resolve_imports(
            program, mainp,
        )
        return program, resolved

    def test_production_resolution_marks_deep_transitive(
        self, tmp_path: Path,
    ) -> None:
        """The precondition the hand-built fixtures cannot supply."""
        _program, resolved = self._resolve(tmp_path)
        by_path = {m.path: m.direct for m in resolved}
        assert by_path == {("mid",): True, ("deep",): False}, (
            f"expected mid direct and deep transitive, got {by_path}"
        )

    def test_transitive_generic_is_qualified_only(
        self, tmp_path: Path,
    ) -> None:
        """`deep`'s public generic must NOT own the entry's bare name."""
        program, resolved = self._resolve(tmp_path)
        ownership = fn_ownership(resolve_calls(program, resolved, self._MAIN))
        assert not ownership.owns(("deep",), "gen"), (
            "a transitive module's generics are all qualified-only — the "
            "entry's namespace does not hold them at all (§8.6.4); got "
            f"{dict(ownership.owners)}"
        )
        assert ownership.symbol(("deep",), "gen") == "deep::gen"

    def test_hop_through_the_transitive_module_still_runs(
        self, tmp_path: Path,
    ) -> None:
        """And the end-to-end answer is unchanged: `mid`'s bare call reaches
        `deep`'s generic under its owner's identity."""
        verify_errors, result, cg_errors = _build(
            tmp_path,
            {"deep.vera": self._DEEP, "mid.vera": self._MID,
             "main.vera": self._MAIN},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        assert _value(result) == ("ok", LIB_ANSWER)


class TestUserWrittenQualifiedCall:
    """A qualified call the USER wrote, not one the reroute synthesized.

    `deep::gen(true)` carries the bare name `gen` on a `ModuleCall`, and the
    importer declares its own `gen`.  Discovery must key the instantiation to
    the module's declaration, not to whichever generic owns the bare name —
    otherwise the clone that runs and the clone that is verified are different
    functions.
    """

    _DEEP = f"""\
module deep;

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ {LIB_ANSWER} }}
"""

    _MAIN = f"""\
import deep(gen);

private forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ {MAIN_ANSWER} }}

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ gen(true) }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ deep::gen(true) }}
"""

    def test_qualified_call_reaches_the_declaring_module(
        self, tmp_path: Path,
    ) -> None:
        verify_errors, result, cg_errors = _build(
            tmp_path, {"deep.vera": self._DEEP, "main.vera": self._MAIN},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        assert _value(result) == ("ok", LIB_ANSWER), (
            "deep::gen(true) must run the MODULE's generic"
        )
        assert _value(result, "useLocal") == ("ok", MAIN_ANSWER), (
            "the importer's own gen must keep the bare name"
        )

    def test_qualified_call_is_symmetric(self, tmp_path: Path) -> None:
        """Both sides key it to the module's declaration."""
        tmp_path.mkdir(parents=True, exist_ok=True)
        (tmp_path / "deep.vera").write_text(self._DEEP, encoding="utf-8")
        mainp = tmp_path / "main.vera"
        mainp.write_text(self._MAIN, encoding="utf-8")
        program = parse_to_ast(self._MAIN)
        resolved = ModuleResolver(_root=tmp_path).resolve_imports(
            program, mainp,
        )
        gen = CodeGenerator(
            source=self._MAIN, file=str(mainp), resolved_modules=resolved,
        )
        gen.compile_program(parse_to_ast(self._MAIN))
        codegen_set = set(getattr(gen, "_emitted_instances", set()))
        verifier = ContractVerifier(
            source=self._MAIN, file=str(mainp), resolved_modules=resolved,
        )
        verifier.register_program(parse_to_ast(self._MAIN))
        verifier_set = {
            (n, ct) for n, cts in verifier._instances.items() for ct in cts
        }
        assert ("deep::gen", ("Bool",)) in codegen_set, (
            f"the qualified call's clone belongs to `deep`, got "
            f"{sorted(codegen_set)}"
        )
        assert ("gen", ("Bool",)) in codegen_set, (
            f"the importer's own gen<Bool> is a separate clone, got "
            f"{sorted(codegen_set)}"
        )
        assert codegen_set == verifier_set, (
            f"codegen {sorted(codegen_set)} != verifier {sorted(verifier_set)}"
        )


class TestImporterBareNamesAreOneSet:
    """The importer-side input to the predicate must be the SAME set on both
    sides, or the shared predicate classifies one imported generic two ways.

    Codegen consults it AFTER Pass 0's two helper renames (the generic-helper
    qualification #1014 and the non-generic hoist #991); the verifier holds the
    pre-transform AST.  A private walk on each side counted `where`-helpers
    differently, so an imported ``gen2`` owned the bare name for codegen and was
    qualified-only for the verifier: codegen emitted ``gen2$Bool`` while the
    verifier verified ``lib::gen2$Bool`` — each side's clone uncovered by the
    other, which is a false Tier-1 in the direction the #732 differential exists
    to catch.
    """

    _LIB = _lib("public")

    # A NON-generic where-helper shadowing the imported name: hoisted away by
    # codegen, still nested for the verifier.
    _MAIN_NONGENERIC_HELPER = f"""\
import lib;

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ gen2(true) }}
  where {{
    fn gen2(@Bool -> @Int)
      requires(true)
      ensures(@Int.result == {MAIN_ANSWER})
      effects(pure)
    {{ {MAIN_ANSWER} }}
  }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""

    # The GENERIC twin: renamed to `useLocal$where$gen2` by the qualification,
    # so it too stops occupying the bare name — but only if both sides say so.
    _MAIN_GENERIC_HELPER = f"""\
import lib;

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ gen2(true) }}
  where {{
    forall<T> fn gen2(@T -> @Int)
      requires(true)
      ensures(@Int.result == {MAIN_ANSWER})
      effects(pure)
    {{ {MAIN_ANSWER} }}
  }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""

    @pytest.mark.parametrize(
        "main_src",
        [_MAIN_NONGENERIC_HELPER, _MAIN_GENERIC_HELPER],
        ids=["nongeneric_where_helper", "generic_where_helper"],
    )
    def test_both_sides_name_one_clone(self, tmp_path, main_src: str) -> None:
        tmp_path.mkdir(parents=True, exist_ok=True)
        libp = tmp_path / "lib.vera"
        mainp = tmp_path / "main.vera"
        libp.write_text(self._LIB, encoding="utf-8")
        mainp.write_text(main_src, encoding="utf-8")
        mod = ResolvedModule(
            path=("lib",), file_path=libp,
            program=parse_to_ast(self._LIB), source=self._LIB,
        )
        gen = CodeGenerator(
            source=main_src, file=str(mainp), resolved_modules=[mod],
        )
        gen.compile_program(parse_to_ast(main_src))
        codegen_set = set(getattr(gen, "_emitted_instances", set()))
        verifier = ContractVerifier(
            source=main_src, file=str(mainp), resolved_modules=[mod],
        )
        verifier.register_program(parse_to_ast(main_src))
        verifier_set = {
            (n, ct) for n, cts in verifier._instances.items() for ct in cts
        }
        assert not codegen_set - verifier_set, (
            f"codegen emits clones the verifier never discovers: "
            f"{sorted(codegen_set - verifier_set)}"
        )
        assert not verifier_set - codegen_set, (
            f"the verifier discovers clones codegen never emits: "
            f"{sorted(verifier_set - codegen_set)}"
        )

    # Every helper shape the derivation distinguishes, in one program:
    #   `plainHelper`   — non-generic under a NON-generic parent  → hoisted away
    #   `genHelper`     — a GENERIC helper                        → qualified away
    #   `underGeneric`  — non-generic under a GENERIC PARENT      → retained
    #   `underGenHelper`— non-generic under a GENERIC HELPER      → retained
    # A fixture missing any of them would let a one-legged assertion look total.
    _ALL_HELPER_SHAPES = f"""\
import lib;

public fn plainParent(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ plainHelper(()) + genHelper(true) }}
  where {{
    fn plainHelper(@Unit -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {{ 1 }}

    forall<T> fn genHelper(@T -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {{ underGenHelper(()) }}
      where {{
        fn underGenHelper(@Unit -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {{ 2 }}
      }}
  }}

public forall<T> fn genParent(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ underGeneric(()) }}
  where {{
    fn underGeneric(@Unit -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {{ 3 }}
  }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""

    def test_no_helper_takes_the_entry_s_bare_name_from_an_import(
        self, tmp_path: Path,
    ) -> None:
        """A ``where`` helper is local to its parent, whatever the parent's
        genericity, so an import still owns the entry's bare name beside a
        helper of that name.  Read off the checker's resolution, which code
        generation and the verifier both bind to (#1494).  The name-set
        derivation this replaces counted a non-generic helper under a generic
        parent as a namespace-wide declaration (R-1507 round 1, finding 2),
        and this program then ran the entry's helper for a module's call."""
        helpers = ("plainHelper", "genHelper", "underGeneric",
                   "underGenHelper")
        lib = "module lib;\n\n" + "".join(
            f"public fn {name}(@Unit -> @Int)\n  requires(true)\n"
            f"  ensures(true)\n  effects(pure)\n{{ {LIB_ANSWER} }}\n\n"
            for name in helpers
        ) + _lib("public").split("\n", 2)[2]
        tmp_path.mkdir(parents=True, exist_ok=True)
        (tmp_path / "lib.vera").write_text(lib, encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            self._ALL_HELPER_SHAPES, encoding="utf-8",
        )
        program = parse_to_ast(self._ALL_HELPER_SHAPES)
        resolved = ModuleResolver(_root=tmp_path).resolve_imports(
            program, tmp_path / "main.vera",
        )
        ownership = fn_ownership(
            resolve_calls(program, resolved, self._ALL_HELPER_SHAPES),
        )
        for name in helpers:
            assert ownership.owns(("lib",), name), (
                f"the helper `{name}` took the entry's bare name from the "
                f"import: {dict(ownership.owners)}"
            )


class TestTypeDiscriminating:
    """Two same-named generics whose clones have DIFFERENT WAT result types.
    Collapsing them onto one ``gen2$Bool`` produced a module whose surviving
    clone had the other's signature — invalid WASM from check-green source, or
    (as here) an i64 flowing out of a ``@Bool``-returning function."""

    _LIB = """\
module lib;

public forall<T> fn gen2(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

public fn door(@Bool -> @Bool)
  requires(true)
  ensures(@Bool.result == @Bool.0)
  effects(pure)
{ gen2(@Bool.0) }
"""

    _MAIN = """\
import lib(door);

private forall<T> fn gen2(@T -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(pure)
{ 7 }

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(pure)
{ gen2(true) }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{ door(true) }
"""

    def test_both_clones_keep_their_own_wat_type(self, tmp_path) -> None:
        verify_errors, result, cg_errors = _build(
            tmp_path, {"lib.vera": self._LIB, "main.vera": self._MAIN},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        # The module's own `gen2<Bool>` is the identity, so `door(true)` is
        # `true` — NOT the importer's `gen2<Bool> -> 7`.
        kind, payload = _value(result, "main")
        assert kind == "ok", f"door(true) trapped: {payload}"
        assert payload == 1, (
            f"door(true) must run the module's identity gen2<Bool> and answer "
            f"`true`, got {payload!r}"
        )
        # The value alone cannot carry the type — the host hands a `@Bool` back
        # as a plain `1` — so the discriminating claim is asserted where it is
        # actually visible: `main` must be declared `(result i32)`.  If the two
        # clones had collapsed onto one symbol, `main` would carry the other's
        # i64 and this would be the only assertion that noticed.
        assert re.search(
            r"\(func \$main[^\n]*\(result i32\)", result.wat,
        ), (
            "main returns @Bool, so its WAT result type must be i32 — an i64 "
            "here is the type-discriminating collapse this shape exists to "
            "catch"
        )
        assert _value(result, "useLocal") == ("ok", 7)

    def test_wat_has_distinct_clone_symbols(self, tmp_path) -> None:
        """The naming rule, read straight off the emitted WAT: the module's
        clone carries its ``lib::`` qualification, so the two ``gen2<Bool>``
        clones are two symbols, not one."""
        _, result, cg_errors = _build(
            tmp_path, {"lib.vera": self._LIB, "main.vera": self._MAIN},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        symbols = set(re.findall(r"\(func (\$[\w$:.<>]+)", result.wat))
        gen2_syms = sorted(x for x in symbols if "gen2" in x)
        # WHOLE-symbol matches: `$gen2$Bool` is a suffix of
        # `$lib::gen2$Bool`, so a substring test for the bare clone is
        # satisfied by the qualified one alone and the "two distinct
        # symbols" claim would be vacuous.
        assert "$lib::gen2$Bool" in symbols, (
            f"the module generic's clone must be qualified by its owning "
            f"module, like every other shadowed module function — "
            f"got {gen2_syms}"
        )
        assert "$gen2$Bool" in symbols, (
            f"the IMPORTER's own gen2<Bool> must still occupy the bare "
            f"clone name — got {gen2_syms}"
        )
