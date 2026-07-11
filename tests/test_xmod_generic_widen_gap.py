"""Cross-module differential for #998: imported GENERIC bodies keep the #820
widen guard at every monomorphized instantiation.

#987 threaded each resolved module's own span-keyed target table into codegen
so an imported *monomorphic* function's @Nat -> @Int widening is runtime-guarded
through the import door.  An imported *generic* function compiles differently:
its mono clones go through the monomorphization compile loop, which — before
this fix — passed neither ``imported=True`` nor ``module_tables=``, so every
clone read the IMPORTER's span table (no entries for the library body's spans)
and the array-element / tuple-construction widen guard was dropped: ``u64.MAX``
silently reinterpreted to ``-1`` at every instantiation, even though the
library's standalone verify (once instantiated) promises the site Tier-3.

The fix carries origin-module provenance on imported-generic clones so the mono
compile loop threads the library's OWN table (monomorphization preserves node
spans, so the template's spans key the clone's body correctly).  This file is
the guarded differential (it replaces the honest pin that documented the gap):

- the library's standalone verify must classify the widen Tier-3 (the promise),
- every instantiation through the import door must TRAP at ``u64.MAX`` with the
  widen guard's bare ``unreachable`` net — never the silent ``-1`` — for both
  the unshadowed (bare-call) and shadowed (``lib::wrap`` -> ``mod$…``) doors,
- in-range values round-trip unchanged, and
- a LOCAL generic's clones keep their same-file guard (the provenance tagging
  must not mis-route local clones onto a module table or suppressed lookups).
"""

from __future__ import annotations

import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import WasmTrapError
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver

U64_MAX = 18446744073709551615
INT63_MAX = 9223372036854775807  # 2^63 - 1: the largest value that stays @Nat==@Int
_KIND = "nat_to_int_coerce"

# An imported generic whose body widens @Nat -> @Int at an array-literal element
# (the #820 per-component site, recovered only from the target table).
_GENERIC_LIB_ARRAY = """\
public forall<T> fn wrap(@T, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [@Nat.0]; @Array<Int>.0[0] }
"""

# The tuple-construction twin (the other span-table-recovered #820 site).
_GENERIC_LIB_TUPLE = """\
public forall<T> fn wrap(@T, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = Tuple(@Nat.0, @Nat.0);
  match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 } }
"""

# The bare template alone emits NO coerce obligation — it is *instantiation*
# that obligates the widen.  Instantiating the generic in-module (the standalone
# library's own `vera verify`) surfaces the Tier-3 promise the importer must
# honour.
_STANDALONE_DRIVER = """\
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

# The shadowed door (#814 §8.5.2): a local non-generic `wrap` owns the bare
# name; the module generic is reached only via the qualified call and its
# clones are emitted under the per-module ``mod$…`` mono base.
_SHADOWED_MAIN = """\
import lib(wrap);
public fn wrap(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
public fn callQualified(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ lib::wrap(7, @Nat.0) }
"""

# LOCAL control: a same-file generic's clones read the main-file tables and
# are guarded TODAY — provenance tagging must not regress this.
_LOCAL_GENERIC = _GENERIC_LIB_ARRAY + """\
public fn callLocal(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ wrap(true, @Nat.0) }
"""

# The widen lives in the generic's WHERE-HELPER: each clone carries the helper
# and `_hoist_clone_where_fns` emits it per-instantiation (#904) — the hoisted
# copy must inherit the clone's origin, or ITS widen guard reads the importer's
# table and is dropped.
_GENERIC_LIB_HELPER_WIDEN = """\
public forall<T> fn wrap(@T, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ helper(@Nat.0) }
where {
  fn helper(@Nat -> @Int)
    requires(true) ensures(true) effects(pure)
  { let @Array<Int> = [@Nat.0]; @Array<Int>.0[0] }
}
"""


def _lib_tier3_count(source: str) -> int:
    """Number of Tier-3 ``nat_to_int_coerce`` obligations the standalone verify
    emits — the promise the importer must honour."""
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


def _trap_kind(result, fn: str, arg: int) -> str | None:
    """The normalized trap kind for ``fn(arg)``, or ``None`` if no trap.

    Pins the widen guard's bare ``unreachable`` net specifically (the same
    convention as ``test_xmod_widening_differential._trap_kind``) — a
    different trap at ``u64.MAX`` would be a different, wrong guard."""
    try:
        execute(result, fn_name=fn, args=[arg])
    except WasmTrapError as exc:
        return exc.kind
    except (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError):
        return "unknown"
    return None


class TestImportedGenericWidenDifferential:
    """The unshadowed door, both #820 span-table sites, both instantiations."""

    def test_generic_library_standalone_promises_tier3(self) -> None:
        for label, lib in (("array", _GENERIC_LIB_ARRAY),
                           ("tuple", _GENERIC_LIB_TUPLE)):
            assert _lib_tier3_count(lib + _STANDALONE_DRIVER) >= 1, (
                f"{label}: the standalone generic library did not promise a "
                f"Tier-3 widen"
            )

    def test_imported_generic_clones_trap_at_u64_max(self, tmp_path) -> None:
        # THE FIX (#998): every instantiation through the import door honours
        # the library's Tier-3 promise — the widen guard traps, never the
        # silent -1 of the pre-fix unguarded clone.
        for label, lib in (("array", _GENERIC_LIB_ARRAY),
                           ("tuple", _GENERIC_LIB_TUPLE)):
            files = {"lib.vera": lib, "main.vera": _GENERIC_MAIN}
            result = _compile_main(tmp_path / label, files, "main.vera")
            for fn in ("callBool", "callInt"):
                kind = _trap_kind(result, fn, U64_MAX)
                assert kind == "unreachable", (
                    f"{label}/{fn}(u64.MAX) trap kind {kind!r} — expected the "
                    f"widen guard's `unreachable` (None = no trap = the clone "
                    f"compiled without its module table, a #998 regression)"
                )

    def test_imported_generic_in_range_values_pass(self, tmp_path) -> None:
        # The guard must not over-fire: in-range values round-trip unchanged.
        for label, lib in (("array", _GENERIC_LIB_ARRAY),
                           ("tuple", _GENERIC_LIB_TUPLE)):
            files = {"lib.vera": lib, "main.vera": _GENERIC_MAIN}
            result = _compile_main(tmp_path / label, files, "main.vera")
            for fn in ("callBool", "callInt"):
                assert _run(result, fn, INT63_MAX) == INT63_MAX, (
                    f"{label}/{fn}: 2^63-1"
                )
                assert _run(result, fn, 42) == 42, f"{label}/{fn}: 42"


class TestShadowedGenericWidenDifferential:
    """The shadowed door: ``lib::wrap`` reaches the module generic's ``mod$…``
    clone, which needs the module table exactly like the unshadowed twin."""

    _FILES = {"lib.vera": _GENERIC_LIB_ARRAY, "main.vera": _SHADOWED_MAIN}

    def test_shadowed_generic_clone_traps_at_u64_max(self, tmp_path) -> None:
        result = _compile_main(tmp_path, self._FILES, "main.vera")
        kind = _trap_kind(result, "callQualified", U64_MAX)
        assert kind == "unreachable", (
            f"callQualified(u64.MAX) trap kind {kind!r} — the shadowed "
            f"(mod$…) clone compiled without its module table"
        )

    def test_shadowed_generic_in_range_passes(self, tmp_path) -> None:
        result = _compile_main(tmp_path, self._FILES, "main.vera")
        assert _run(result, "callQualified", INT63_MAX) == INT63_MAX
        assert _run(result, "callQualified", 42) == 42
        # The local shadow itself is untouched by any of this.
        assert _run(result, "wrap", 42) == 42


class TestHoistedHelperWidenDifferential:
    """The widen site inside the imported generic's where-helper: the
    per-clone hoisted copy (#904) must inherit the clone's module origin."""

    _FILES = {"lib.vera": _GENERIC_LIB_HELPER_WIDEN, "main.vera": _GENERIC_MAIN}

    def test_hoisted_helper_promises_tier3(self) -> None:
        assert _lib_tier3_count(
            _GENERIC_LIB_HELPER_WIDEN + _STANDALONE_DRIVER,
        ) >= 1, "the helper-widen library did not promise a Tier-3 widen"

    def test_hoisted_helper_traps_at_u64_max(self, tmp_path) -> None:
        result = _compile_main(tmp_path, self._FILES, "main.vera")
        for fn in ("callBool", "callInt"):
            kind = _trap_kind(result, fn, U64_MAX)
            assert kind == "unreachable", (
                f"{fn}(u64.MAX) trap kind {kind!r} — the hoisted where-helper "
                f"did not inherit its clone's module origin"
            )

    def test_hoisted_helper_in_range_passes(self, tmp_path) -> None:
        result = _compile_main(tmp_path, self._FILES, "main.vera")
        for fn in ("callBool", "callInt"):
            assert _run(result, fn, 42) == 42, f"{fn}: 42"


class TestLocalGenericCloneControl:
    """A LOCAL generic's clones are guarded today via the main-file tables;
    the #998 provenance tagging must not mis-route them."""

    def test_local_generic_clone_still_traps(self, tmp_path) -> None:
        result = _compile_main(
            tmp_path, {"main.vera": _LOCAL_GENERIC}, "main.vera",
        )
        kind = _trap_kind(result, "callLocal", U64_MAX)
        assert kind == "unreachable", (
            f"callLocal(u64.MAX) trap kind {kind!r} — the local clone lost "
            f"its same-file widen guard (provenance mis-tag)"
        )
        assert _run(result, "callLocal", 42) == 42
