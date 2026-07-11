"""Cross-module verifier<->codegen differential for #987 @Nat -> @Int widening.

The #820 per-component widening guards (array-literal element, tuple
construction) are recovered from the checker's span-keyed *target*-type table.
That table is single-module, so an imported body compiled into the flat WASM
module (Pass 2.5 / 2.6) had no entries and codegen dropped the guard THROUGH THE
IMPORT DOOR — while the library's own ``vera verify`` still classified the
coercion Tier-3 runtime-guarded (a broken promise: the importer's artifact
bit-reinterpreted ``u64.MAX`` to ``-1`` with no trap).  #987 threads each
module's OWN table into codegen so the imported body emits the same guard.

This is the required cross-component differential, run **through the import
door** (the same-file differential in ``test_int_widening_differential.py`` was
green while this door was open): for each shape the library's standalone verify
must classify the coercion Tier-3, AND the importing program compiled the way
``vera run`` / ``vera compile`` compile it (per-module tables threaded) must
TRAP at ``u64.MAX`` — never the silent ``-1`` — while passing in-range values
(``2^63 - 1``, ``42``) unchanged.

The tuple *destructure* shape is deliberately included as a control: its guard
is recovered structurally from the ``let Tuple<@Int, ...>`` binding pattern (not
the span table), so it was already emitted cross-module at the #986 base — the
differential must stay green for it too.
"""

from __future__ import annotations

import pytest
import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.verifier import verify

U64_MAX = 18446744073709551615
INT63_MAX = 9223372036854775807  # 2^63 - 1, the largest value that stays @Nat==@Int
_MASK64 = (1 << 64) - 1
_KIND = "nat_to_int_coerce"


# --- The library bodies, one per widening shape (all standalone Tier-3). ------
_ARRAY_LIB = """\
public fn widen(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [@Nat.0]; @Array<Int>.0[0] }
"""

_TUPLE_CONSTRUCT_LIB = """\
public fn widen(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = Tuple(@Nat.0, @Nat.0);
  match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 } }
"""

_TUPLE_DESTRUCT_LIB = """\
public fn widen(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(@Nat.0, @Nat.0); @Int.0 }
"""

# Scenarios: label -> (files, main_filename, main_fn, lib_filename).
#   files       : {filename: source} written verbatim into tmp_path
#   lib_filename: the file whose STANDALONE verify must show the Tier-3 promise
_DIRECT_MAIN = """\
import lib(widen);
public fn callit(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ widen(@Nat.0) }
"""


def _scenarios() -> list[tuple[str, dict[str, str], str, str, str]]:
    scen: list[tuple[str, dict[str, str], str, str, str]] = []
    for label, lib in (
        ("array_element", _ARRAY_LIB),
        ("tuple_construct", _TUPLE_CONSTRUCT_LIB),
        ("tuple_destruct", _TUPLE_DESTRUCT_LIB),
    ):
        scen.append((
            label,
            {"lib.vera": lib, "main.vera": _DIRECT_MAIN},
            "main.vera", "callit", "lib.vera",
        ))

    # Transitive: main -> alib -> blib (the widening lives in the transitively
    # reached leaf; its body is compiled via Pass 2.5 with direct=False).
    scen.append((
        "transitive",
        {
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
        },
        "main.vera", "callit", "blib.vera",
    ))

    # Shadowed import (Pass 2.6): the importer defines a local `widen` that
    # shadows the import, and reaches the module's widening body via a qualified
    # `lib::widen` call (emitted under a `mod$…` name).
    scen.append((
        "shadowed",
        {
            "lib.vera": _ARRAY_LIB,
            "main.vera": (
                "import lib(widen);\n"
                "public fn widen(@Nat -> @Nat)\n"
                "  requires(true) ensures(true) effects(pure)\n"
                "{ @Nat.0 }\n"
                "public fn callit(@Nat -> @Int)\n"
                "  requires(true) ensures(true) effects(pure)\n"
                "{ lib::widen(@Nat.0) }\n"
            ),
        },
        "main.vera", "callit", "lib.vera",
    ))
    return scen


def _lib_tier3_count(source: str) -> int:
    """Number of Tier-3 ``nat_to_int_coerce`` obligations the STANDALONE library
    verify emits — the promise the importer must honour."""
    program = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(program, source)
    result = verify(
        program, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    return sum(
        1 for o in result.obligations
        if o.kind == _KIND and o.status == "tier3"
    )


def _compile_main(tmp_path, files: dict[str, str], main_name: str):
    """Write every fixture, then compile *main_name* exactly as ``vera run``
    does — per-module target tables threaded (#987)."""
    for name, src in files.items():
        (tmp_path / name).write_text(src, encoding="utf-8")
    main_path = tmp_path / main_name
    source = files[main_name]
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(program, main_path)
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(main_path), resolved_modules=resolved,
    )
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"typecheck errors: {[d.description for d in errors]}"
    result = codegen_compile(
        program, source=source, file=str(main_path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    errs = [d for d in result.diagnostics if d.severity == "error"]
    assert not errs, f"codegen errors: {[d.description for d in errs]}"
    return result


def _run(result, fn: str, arg: int) -> int | None:
    """Execute *fn* with one i64 arg; ``None`` if it traps."""
    try:
        return execute(result, fn_name=fn, args=[arg]).value
    except (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError):
        return None


@pytest.mark.parametrize(
    "label,files,main_name,fn,lib_name",
    _scenarios(),
    ids=[s[0] for s in _scenarios()],
)
class TestCrossModuleWideningDifferential:
    def test_library_standalone_promises_tier3(
        self, label, files, main_name, fn, lib_name, tmp_path,
    ) -> None:
        # The promise: the library's own verify classifies the widening Tier-3
        # (a runtime-guarded claim).  If this were Tier-1 there would be no
        # cross-module gap to close.
        assert _lib_tier3_count(files[lib_name]) >= 1, (
            f"{label}: library {lib_name} did not promise a Tier-3 widen"
        )

    def test_importer_traps_at_u64_max(
        self, label, files, main_name, fn, lib_name, tmp_path,
    ) -> None:
        # The fix: the importer's artifact must HONOUR that promise — a @Nat
        # above i64.MAX traps through the import door, never the silent -1.
        result = _compile_main(tmp_path, files, main_name)
        assert _run(result, fn, U64_MAX) is None, (
            f"{label}: importer returned a value at u64.MAX — the widen guard "
            f"is absent through the import door (regression of #987)"
        )

    def test_importer_passes_in_range_values(
        self, label, files, main_name, fn, lib_name, tmp_path,
    ) -> None:
        # The guard must not over-fire: in-range values round-trip unchanged.
        result = _compile_main(tmp_path, files, main_name)
        assert _run(result, fn, INT63_MAX) == INT63_MAX, f"{label}: 2^63-1"
        assert _run(result, fn, 42) == 42, f"{label}: 42"
