"""Opt-in collection of ``CheckArtifacts.module_artifacts`` (PR #997 review).

``_collect_module_artifacts`` (#987) runs a full ``check_program`` per resolved
module so codegen can thread each module's OWN span-keyed target table into the
imported body (recovering the #820 @Nat -> @Int widening guard through the
import door).  That pass is O(N^2) sub-checks in the module count and is pure
waste for the codegen-free callers — ``vera verify`` and the warm
``VerificationSession`` read only the top-level ``expr_*_types`` tables, never
``module_artifacts``.  PR #997 made the collection **opt-in**
(``collect_module_artifacts=`` on ``typecheck_with_artifacts``, default
``False``); only the codegen-bound callers pass ``True``.

Two pins here:

* ``TestOptInCollection`` — the verify-path pin: WITHOUT the flag the table is
  an empty dict (verify does not pay the quadratic pass), WITH it the resolved
  modules appear.  RED before the opt-in change (collection was unconditional,
  so the table was non-empty on every path).

* ``TestTransitiveArtifactContent`` — the GAP-1 artifact-level pin.  Each
  module's ``direct`` flags are RE-DERIVED from its own imports before its
  sub-check (a transitively-reached leaf is ``direct=False`` relative to the
  top-level program but a DIRECT import of the module that imports it).  No
  behavioural fixture distinguishes the re-derivation from just reusing the
  top-level flags, but the re-derivation provably changes the collected
  ARTIFACT: in the transitive fixture ``alib`` resolves its ``widen`` call to a
  direct import and records **two** target-table entries; with the top-level
  flags (``blib`` still ``direct=False`` for ``alib``'s sub-check) it records
  only one.  Pinned at the artifact level.
"""

from __future__ import annotations

from pathlib import Path

from vera.checker import typecheck_with_artifacts
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver

# A library whose body widens @Nat -> @Int at an array-literal element (the
# #820 per-component site recovered only from the target table).
_ARRAY_LIB = """\
public fn widen(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [@Nat.0]; @Array<Int>.0[0] }
"""

_DIRECT_MAIN = """\
import lib(widen);
public fn callit(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ widen(@Nat.0) }
"""


def _resolve(tmp_path: Path, files: dict[str, str], main_name: str):
    for name, src in files.items():
        (tmp_path / name).write_text(src, encoding="utf-8")
    main_path = tmp_path / main_name
    source = files[main_name]
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(program, main_path)
    return program, source, main_path, resolved


class TestOptInCollection:
    def test_default_off_leaves_module_artifacts_empty(self, tmp_path) -> None:
        # The verify-path pin: without opting in, the per-module quadratic pass
        # does not run and the table is empty — even with resolved modules
        # present.  RED before PR #997 (collection was unconditional).
        program, source, main_path, resolved = _resolve(
            tmp_path, {"lib.vera": _ARRAY_LIB, "main.vera": _DIRECT_MAIN},
            "main.vera",
        )
        assert len(resolved) >= 1, "fixture must resolve at least the library"
        _diags, arts = typecheck_with_artifacts(
            program, source, file=str(main_path), resolved_modules=resolved,
        )
        assert arts.module_artifacts == {}, (
            "module_artifacts must be empty without collect_module_artifacts "
            "(the verify path must not pay the per-module quadratic pass)"
        )

    def test_opt_in_collects_resolved_modules(self, tmp_path) -> None:
        # The codegen-path counterpart: opting in populates a per-module entry
        # keyed by module path (what codegen threads into the imported body).
        program, source, main_path, resolved = _resolve(
            tmp_path, {"lib.vera": _ARRAY_LIB, "main.vera": _DIRECT_MAIN},
            "main.vera",
        )
        _diags, arts = typecheck_with_artifacts(
            program, source, file=str(main_path), resolved_modules=resolved,
            collect_module_artifacts=True,
        )
        assert ("lib",) in arts.module_artifacts, (
            "opting in must collect the resolved library's own side-tables"
        )
        # The library's widen body records at least one target-table entry
        # (the array-element @Int target the guard recovers).
        _sem, tgt = arts.module_artifacts[("lib",)]
        assert len(tgt) >= 1, "library target table lost its @Int component target"


# Transitive: main -> alib -> blib.  The widen lives in the leaf ``blib``; the
# GAP-1 fact is about the MIDDLE module ``alib``'s own target table.
_TRANSITIVE = {
    "blib.vera": _ARRAY_LIB,
    "alib.vera": (
        "import blib(widen);\n"
        "public fn awrap(@Nat -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ widen(@Nat.0) }\n"
    ),
    "main.vera": (
        "import alib(awrap);\n"
        "public fn callit(@Nat -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ awrap(@Nat.0) }\n"
    ),
}


class TestTransitiveArtifactContent:
    def test_middle_module_target_table_has_two_entries(self, tmp_path) -> None:
        # GAP-1: with ``alib``'s ``direct`` flags re-derived from its OWN
        # imports, ``blib`` is a DIRECT import of ``alib``, so ``alib``'s
        # sub-check resolves ``widen(@Nat.0)`` fully and records TWO target-table
        # entries.  The mutant that reuses the top-level flags (``blib``
        # ``direct=False`` for ``alib``'s sub-check) records only ONE — this pin
        # REDs under it.  No behavioural fixture distinguishes the two, so the
        # necessity of the guard-level effect is unproven; the artifact-level
        # change, however, is provable and pinned here.
        program, source, main_path, resolved = _resolve(
            tmp_path, _TRANSITIVE, "main.vera",
        )
        _diags, arts = typecheck_with_artifacts(
            program, source, file=str(main_path), resolved_modules=resolved,
            collect_module_artifacts=True,
        )
        assert ("alib",) in arts.module_artifacts
        _sem, alib_tgt = arts.module_artifacts[("alib",)]
        assert len(alib_tgt) == 2, (
            f"alib target table has {len(alib_tgt)} entries, expected 2 — the "
            f"per-module `direct` flags were not re-derived from alib's own "
            f"imports (blib must be a DIRECT import of alib for its sub-check)"
        )
