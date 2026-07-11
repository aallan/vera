"""Honest pin: imported GENERIC function bodies drop the #820 widen guard.

#987 threaded each resolved module's own span-keyed target table into codegen so
an imported *monomorphic* function's @Nat -> @Int widening is runtime-guarded
through the import door.  An imported *generic* function is different: its mono
clones compile on the monomorphization path (``codegen/core.py`` ~L819,
``self._compile_fn(mdecl, export=is_public)``) WITHOUT ``module_tables=`` — so
they read the IMPORTER's span table (which has no entry for the library body's
spans), not the library module's.  The array-element / tuple-construction widen
guard is therefore NOT emitted at any instantiation, even though the library's
standalone verify (once the generic is instantiated) promises the site Tier-3.

Result: a ``forall<T> fn wrap(@T, @Nat -> @Int)`` whose body widens at an
``Array<Int>`` element silently reinterprets a @Nat above ``i64.MAX`` to a
negative @Int (``u64.MAX`` -> ``-1``) at every instantiation reached through the
import door — the broken-promise shape #987 closed for monomorphic bodies, still
open for generic ones.  This is a PRE-EXISTING gap (identical at the #987 base;
the mono clones never consulted a module table) and is out of scope for the
threading fix; the remedy is tracked separately.

These tests PIN the current honest behaviour (in the style of the #985 nested-
closure pin in ``test_nat_narrowing_return_differential``): the library promises
Tier-3, but the importer runs the widen unguarded (``u64.MAX`` -> ``-1``, no
trap).  When the gap closes, ``test_imported_generic_clone_silently_widens``
will flip (the run will trap) and must be updated to the guarded expectation.
"""

from __future__ import annotations

import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver

U64_MAX = 18446744073709551615
INT63_MAX = 9223372036854775807  # 2^63 - 1: the largest value that stays @Nat==@Int
_KIND = "nat_to_int_coerce"

# An imported generic whose body widens @Nat -> @Int at an array-literal element
# (the #820 per-component site, recovered only from the target table).
_GENERIC_LIB = """\
public forall<T> fn wrap(@T, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [@Nat.0]; @Array<Int>.0[0] }
"""

# The bare template alone emits NO coerce obligation — it is *instantiation*
# that obligates the widen.  Instantiating the generic in-module (the standalone
# library's own `vera verify`) surfaces the Tier-3 promise the importer breaks.
_GENERIC_LIB_STANDALONE = _GENERIC_LIB + """\
public fn drive(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ wrap(true, @Nat.0) }
"""

# Two instantiations (T=Bool, T=Int) force two mono clones through the door.
_GENERIC_MAIN = """\
import lib(wrap);
public fn callBool(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ wrap(true, @Nat.0) }
public fn callInt(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ wrap(7, @Nat.0) }
"""


def _lib_tier3_count(source: str) -> int:
    """Number of Tier-3 ``nat_to_int_coerce`` obligations the standalone verify
    emits — the promise the importer must (but does not) honour."""
    program = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(program, source)
    from vera.verifier import verify

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
    """Compile *main_name* exactly as ``vera run`` does — per-module target
    tables threaded (#987)."""
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


class TestImportedGenericWidenGap:
    _FILES = {"lib.vera": _GENERIC_LIB, "main.vera": _GENERIC_MAIN}

    def test_generic_library_standalone_promises_tier3(self) -> None:
        # The promise: instantiating the generic in-module, the library's own
        # verify classifies the widen Tier-3 (a runtime-guard claim).
        assert _lib_tier3_count(_GENERIC_LIB_STANDALONE) >= 1, (
            "the standalone generic library did not promise a Tier-3 widen"
        )

    def test_imported_generic_clone_silently_widens_at_u64_max(
        self, tmp_path,
    ) -> None:
        # THE GAP (honest pin): the imported generic's mono clones compile
        # WITHOUT module_tables, so the widen guard is dropped — u64.MAX is
        # silently reinterpreted to -1 at every instantiation, NO trap, even
        # though the library promised Tier-3.  Pre-existing, tracked separately.
        # When the gap closes these runs will TRAP; update this test then.
        result = _compile_main(tmp_path, self._FILES, "main.vera")
        for fn in ("callBool", "callInt"):
            val = _run(result, fn, U64_MAX)
            assert val == -1, (
                f"{fn}(u64.MAX) = {val!r}, expected the UNGUARDED silent -1 "
                f"(u64.MAX bit-reinterpreted to i64).  A trap (None) means the "
                f"imported-generic widen gap has CLOSED — update this honest "
                f"pin to the guarded expectation."
            )

    def test_imported_generic_in_range_values_pass(self, tmp_path) -> None:
        # In-range values round-trip unchanged either way (the missing guard is
        # a no-op below i64.MAX), so this holds now and after the gap closes.
        result = _compile_main(tmp_path, self._FILES, "main.vera")
        for fn in ("callBool", "callInt"):
            assert _run(result, fn, INT63_MAX) == INT63_MAX, f"{fn}: 2^63-1"
            assert _run(result, fn, 42) == 42, f"{fn}: 42"
