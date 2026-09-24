"""#1310: a qualified-only (shadowed) module generic's instantiation
discovery had no effect-operation registry at all, unlike the unshadowed
discovery walk #1207 already fixed.

``_monomorphize_shadowed_module_generics`` seeds a shadowed generic's
instances from ``ast.ModuleCall`` sites inside a module's own bodies via
``_collect_shadowed_qualified_calls`` (codegen) and the mirroring
``walk_seed`` closure (the verifier's ``_collect_shadowed_qualified_instances``,
#732).  Neither ever installed the ``handle[State<T>]`` op-result registry
``Monomorphizer._collect_calls`` merges in for the unshadowed path, so an
argument like ``get(())`` fell through to the phantom-type-variable ``Bool``
default. The WASM call-site rewrite (``CallsMixin._resolve_generic_call``),
which runs with the real handler context during actual codegen, still named
the correct clone (``mlib5::idg$Int``), so discovery silently emitted a
clone nothing calls, the real one was never registered, and the caller
(``outer``, then ``main``) was dropped with E602/E620 on check-green,
verify-clean source.

Four cells:

* the issue's own repro, a private module generic instantiated from an
  effect-operation result, pinned end to end (no E602/E620, the checker's
  own clone name in the WAT, and the runtime value);
* a nested-distinct-state variant (mirroring
  ``test_mono_effect_op_naming_1207.py``'s ``_NESTED_DISTINCT_STATE``) through
  the SAME shadowed path, so a fix that merely stops defaulting to ``Bool``
  without preserving merge-not-replace semantics for nested handlers is
  still caught: it would name the inner call from the OUTER cell and sum to
  the wrong value, and it now also asserts the outer cell's ``$Nat`` clone is
  ABSENT, matching the first cell's shape (a WAT scan that only checked for
  ``$Int`` would still pass a discovery walk emitting BOTH clones); and
* the #732 differential (two cells, non-nested and nested), asserting
  codegen's ``_emitted_instances`` and the verifier's ``_instances`` name the
  IDENTICAL instantiation for the effect-op-result argument.

The differential does NOT reuse cells 1/2's fixtures, and this is measured,
not a style choice: ``idg``/``idg2`` are called BARE from inside their OWN
declaring module, and the verifier's ``ContractVerifier._collect_instantiations``
reroutes exactly that call shape to a mangled bare ``FnCall`` (name
``mlib5::idg``) via the pre-existing, #1310-unrelated
``_reroute_to_module_qualified`` machinery (#1000/#1029) BEFORE
``_collect_shadowed_qualified_instances``'s ``walk_seed`` ever sees it, so
``walk_seed``'s own ``ast.ModuleCall`` match, and the ``HandleExpr`` merge
guarding it, never fire for cells 1/2's call shape.  Reverting the merge only
from ``walk_seed`` while keeping cells 1/2's fixtures leaves BOTH
``_emitted_instances`` and ``_instances`` at ``Int`` (verified: the private
self-reference is discovered instead through the ordinary unshadowed
worklist over ``generic_decls["mlib5::idg"]``, which already carried
#1207's fix and was never broken), so a differential built on cells 1/2 alone
would stay green under a verifier-only revert, silently failing to be a
differential at all.  Codegen's ``_collect_shadowed_qualified_calls`` has no
such reroute (it keeps the raw ``ast.ModuleCall`` until its OWN emission
pass), so a codegen-only revert against cells 1/2 IS caught; the gap is
one-sided.

``walk_seed``'s ``ast.ModuleCall`` branch is for a genuinely different
shape: an EXTERNAL ``module::name(...)`` qualified call, written by an
importer whose own bare name for that generic is unavailable (shadowed by a
same-named local declaration, or reached only transitively), the classic
#814 case, not #1000/#1029's private-self-reference case (a private
declaration cannot be qualified-called from outside its module at all;
measured: the checker rejects it with "is private and cannot be accessed
from outside its module").  ``_MLIB7``/``_MAIN7`` (and the nested
``_MLIB8``/``_MAIN8``) are built for exactly that shape: a PUBLIC generic,
locally shadowed at the importer, called via ``module::name(...)`` inside a
``handle[State<T>]`` in the IMPORTER's own body, and measured to turn red
on EITHER side's merge reverted alone (both directions executed and
confirmed in a throwaway harness before writing this test).
"""

from __future__ import annotations

import os
import tempfile

from vera.codegen.core import CodeGenerator
from vera.parser import parse_file
from vera.transform import transform
from vera.verifier import ContractVerifier

from tests.codegen_helpers import wat_fn_names
from tests.module_fixture_helpers import (
    build_multi_module, module_value, resolved_module,
)

_MLIB5 = """\
module mlib5;

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public forall<T> fn outer(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42007) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    idg(get(()))
  }
}
"""

_MAIN5 = """\
import mlib5(outer);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  outer(1)
}
"""

_MLIB6 = """\
module mlib6;

private forall<T> fn idg2(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn outer2(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 2) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    nat_to_int(get(())) + handle[State<Int>](@Int = 5) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      idg2(get(()))
    }
  }
}
"""

_MAIN6 = """\
import mlib6(outer2);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  outer2(())
}
"""

# The differential's own fixtures (see the module docstring for why cells
# 1/2's private-self-reference shape cannot be reused): a PUBLIC generic,
# shadowed at the IMPORTER by a same-named local declaration, reached via an
# EXPLICIT ``module::name(...)`` qualified call inside the importer's own
# ``handle[State<T>]``: the shape ``walk_seed``'s ``ast.ModuleCall`` match
# targets.
_MLIB7 = """\
module mlib7;

public forall<T> fn idg3(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
"""

_MAIN7 = """\
import mlib7;

private fn idg3(@Int -> @Int)
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
  handle[State<Int>](@Int = 42007) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    mlib7::idg3(get(()))
  }
}
"""

_MLIB8 = """\
module mlib8;

public forall<T> fn idg4(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
"""

_MAIN8 = """\
import mlib8;

private fn idg4(@Int -> @Int)
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
  handle[State<Nat>](@Nat = 2) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    nat_to_int(get(())) + handle[State<Int>](@Int = 5) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      mlib8::idg4(get(()))
    }
  }
}
"""


def test_module_generic_instantiated_from_effect_op_result(tmp_path) -> None:
    """The issue's own repro: check/verify clean, ``idg$Int`` emitted, runs 42007."""
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"mlib5.vera": _MLIB5, "main.vera": _MAIN5},
    )
    assert not cg_errors, f"codegen errors: {cg_errors}"
    assert not verify_errors, f"verify errors: {verify_errors}"
    names = wat_fn_names(result.wat)
    assert "mlib5::idg$Int" in names, (
        "discovery and the call-rewrite named different clones for the "
        f"module generic; emitted: {names}"
    )
    assert "mlib5::idg$Bool" not in names, (
        "the effect-op-result argument was still defaulted to the phantom "
        f"Bool type variable; emitted: {names}"
    )
    assert module_value(result) == ("ok", 42007)


def test_shadowed_generic_op_registry_merges_not_replaces(tmp_path) -> None:
    """A nested handler must still let the OUTER cell answer outside itself.

    ``idg2(get(()))`` in the INNER ``handle[State<Int>]`` body must bind
    ``@T`` from the inner cell (5), while ``get(())`` OUTSIDE it (but still
    inside the outer ``handle[State<Nat>]``) reads the outer cell (2), for
    2 + 5 = 7.  A discovery walk that REPLACED the registry instead of
    merging it over the enclosing one would still pass the first cell above
    (there is only one handler in it) but would get this one wrong: either
    a WAT type mismatch (Nat vs Int have different reprs) or a silently
    wrong sum if `_op_result_types` from the wrong handler leaked across
    the boundary the two calls actually sit in.
    """
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"mlib6.vera": _MLIB6, "main.vera": _MAIN6},
    )
    assert not cg_errors, f"codegen errors: {cg_errors}"
    assert not verify_errors, f"verify errors: {verify_errors}"
    names = wat_fn_names(result.wat)
    assert "mlib6::idg2$Int" in names, (
        f"expected the inner cell's clone in the emitted WAT; got {names}"
    )
    assert "mlib6::idg2$Nat" not in names, (
        "the outer handler's State<Nat> leaked into the inner call's "
        f"discovery instead of the inner State<Int> cell; emitted: {names}"
    )
    assert module_value(result) == ("ok", 7)


def _discovered_sets(
    module_path: tuple[str, ...], module_src: str, main_src: str,
) -> tuple[
    set[tuple[str, tuple[str, ...]]], set[tuple[str, tuple[str, ...]]],
]:
    """``(codegen_emitted, verifier_discovered)`` for *main_src* against one
    imported module.

    This is the #732 cross-component differential (see
    ``tests/test_monomorphize_differential.py``) applied to the shadowed
    path this fix touches: codegen's ``_emitted_instances`` is fed by
    ``_collect_shadowed_qualified_calls``'s ``instances`` dict, and the
    verifier's ``_instances`` is fed by ``_collect_shadowed_qualified_instances``'s
    ``walk_seed`` closure and its ``seed`` set, for a call shape where both
    discovery walks actually reach their own ``HandleExpr``-merge arm (see
    the module docstring: this is NOT true of cells 1/2's fixtures).
    Reverting either arm alone makes ONE side keep defaulting the effect-op
    argument to the phantom ``Bool`` type variable while the other now
    infers ``Int``, so the two recorded sets stop agreeing. The doctrine is
    that the verifier must statically check exactly the set codegen emits,
    and only this equality pins that for the shadowed, effect-op-result
    path.
    """
    mod = resolved_module(module_path, module_src)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(main_src)
        f.flush()
        main_path = f.name
    try:
        program = transform(parse_file(main_path))
        gen = CodeGenerator(
            source=main_src, file=main_path, resolved_modules=[mod],
        )
        gen.compile_program(program)  # type: ignore[arg-type]
        codegen_set = getattr(gen, "_emitted_instances", set())
        verifier = ContractVerifier(
            source=main_src, file=main_path, resolved_modules=[mod],
        )
        verifier.register_program(program)  # type: ignore[arg-type]
        verifier_set = {
            (n, ct) for n, cts in verifier._instances.items() for ct in cts
        }
    finally:
        os.unlink(main_path)
    return codegen_set, verifier_set


def test_shadowed_generic_effect_op_discovery_differential() -> None:
    """External qualified call: codegen and the verifier must discover the
    identical ``mlib7::idg3`` instantiation from ``mlib7::idg3(get(()))``.

    ``idg3`` is PUBLIC in ``mlib7`` but shadowed at the importer by a
    same-named private local declaration, so the call must be qualified,
    exactly the shape ``walk_seed``'s ``ast.ModuleCall`` match (and the
    ``HandleExpr`` merge guarding it) exists for.  Deleting the merge from
    only one of the two discovery walks turns this red: codegen would keep
    emitting ``mlib7::idg3$Int`` while the verifier fell back to
    ``mlib7::idg3$Bool`` (or vice versa), so the sets would disagree even
    though each one, read alone, looks self-consistent.  Measured directly
    (not just asserted): reverting codegen's merge alone yields
    ``{('mlib7::idg3', ('Bool',))}`` vs the verifier's unchanged
    ``{('mlib7::idg3', ('Int',))}``; reverting the verifier's merge alone
    yields the mirror image.  Both were executed against this exact fixture
    before this test was written.
    """
    codegen_set, verifier_set = _discovered_sets(("mlib7",), _MLIB7, _MAIN7)
    assert ("mlib7::idg3", ("Int",)) in codegen_set, (
        f"codegen must emit the shadowed generic's clone at Int, "
        f"got {sorted(codegen_set)}"
    )
    assert ("mlib7::idg3", ("Bool",)) not in codegen_set, (
        f"codegen fell through to the phantom Bool default, "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) for the effect-op-result "
        f"argument of a shadowed generic; a one-sided fix desyncs this"
    )


def test_shadowed_generic_effect_op_discovery_differential_nested() -> None:
    """The nested-distinct-state variant of the external-qualified-call
    differential, same equality.

    ``idg4`` is called via ``mlib8::idg4(get(()))`` from the INNER
    ``handle[State<Int>]`` body, nested inside an OUTER
    ``handle[State<Nat>]`` in the IMPORTER's own code: the merge-not-replace
    scoping must still land both sides on ``mlib8::idg4$Int``, never
    ``$Nat`` (the outer cell leaking in) nor a desync between the two
    discovery walks.  Measured directly: reverting codegen's merge alone
    yields ``{('mlib8::idg4', ('Bool',))}`` vs the verifier's unchanged
    ``{('mlib8::idg4', ('Int',))}``; reverting the verifier's merge alone
    yields the mirror image.  Both executed against this exact fixture
    before this test was written.
    """
    codegen_set, verifier_set = _discovered_sets(("mlib8",), _MLIB8, _MAIN8)
    assert ("mlib8::idg4", ("Int",)) in codegen_set, (
        f"codegen must emit the inner cell's clone at Int, "
        f"got {sorted(codegen_set)}"
    )
    assert ("mlib8::idg4", ("Nat",)) not in codegen_set, (
        f"the outer handler's Nat leaked into discovery, "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) for the nested handler "
        f"variant; a one-sided fix desyncs this"
    )
