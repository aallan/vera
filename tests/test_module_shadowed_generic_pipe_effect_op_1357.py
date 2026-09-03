"""#1357: a module generic invoked via a PIPE never discovers an
instantiation whose type argument is piped from an effect-operation
result, the piped sibling of #1310.

#1310 fixed ``_collect_shadowed_qualified_calls`` (codegen) and the
mirroring ``walk_seed`` closure (the verifier's
``_collect_shadowed_qualified_instances``) to thread the ``handle[State<T>]``
op-result registry through the *direct-call* form of a shadowed/qualified
module generic (``path::gen(get(()))``). Neither walker's ``ast.ModuleCall``
match ever fires for the *piped* form (``get(()) |> path::gen()``), because
a pipe is its own AST node (``ast.BinaryExpr`` with ``op == ast.BinOp.PIPE``)
whose right side is the ``ModuleCall``: the piped left operand is folded
into the call's argument list only at the checker/codegen boundary
(``CallsMixin._translate_binary``'s ``C7e`` desugar), never in the AST
itself.  So a shadowed generic invoked this way was invisible to both
discovery walks and to the WASM pipe desugar's own module-call target
resolution (``BinaryOpMixin._translate_binary``, which named the call's
bare, unregistered name instead of routing it through
``_resolve_module_call_wasm_name`` the way the unpiped desugar does),
matching #1310's own failure mode: check-green, verify-clean, then a
codegen-time drop (``[E602]``/``[E620]``) once ``vera run`` reaches the
dropped caller.

Two cells, mirroring #1310's external-qualified-call shape
(``_MLIB7``/``_MAIN7`` there): a PUBLIC generic, shadowed at the importer
by a same-named local declaration, invoked via
``get(()) |> module::name()`` inside the importer's own
``handle[State<T>]``.

* the end-to-end runtime cell (no E602/E620, the checker's own clone name
  in the WAT, and the runtime value); and
* the #732 cross-component differential (see
  ``tests/test_module_shadowed_generic_effect_op_1310.py`` and
  ``tests/test_monomorphize_differential.py``), asserting codegen's
  ``_emitted_instances`` and the verifier's ``_instances`` name the
  IDENTICAL instantiation for the piped effect-op-result argument.  Measured
  directly (not just asserted): reverting only the ``monomorphize.py`` PIPE
  arm leaves the verifier's set at ``{('mod$mlib11$idg7', ('Int',))}`` while
  codegen's set stays empty (the PIPE call is never even visited by the
  codegen walker's ``ModuleCall`` match, so nothing is added to
  ``instances`` at all); reverting only the ``verifier.py`` PIPE arm is the
  mirror image (codegen's set carries ``Int``, the verifier's stays empty).
  Both were executed against this exact fixture before this test was
  written.
"""

from __future__ import annotations

import os
import tempfile

from vera.codegen.core import CodeGenerator
from vera.parser import parse_file
from vera.transform import transform
from vera.verifier import ContractVerifier

from tests.codegen_helpers import wat_calls, wat_fn_body, wat_fn_names
from tests.module_fixture_helpers import (
    build_multi_module, module_value, resolved_module,
)

_MLIB11 = """\
module mlib11;

public forall<T> fn idg7(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
"""

_MAIN11 = """\
import mlib11;

private fn idg7(@Int -> @Int)
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
    get(()) |> mlib11::idg7()
  }
}
"""


def test_module_generic_pipe_instantiated_from_effect_op_result(tmp_path) -> None:
    """The issue's own shape: a piped qualified call, check/verify clean,
    ``idg7$Int`` emitted, runs 42007."""
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"mlib11.vera": _MLIB11, "main.vera": _MAIN11},
    )
    assert not cg_errors, f"codegen errors: {cg_errors}"
    assert not verify_errors, f"verify errors: {verify_errors}"
    names = wat_fn_names(result.wat)
    assert "mod$mlib11$idg7$Int" in names, (
        "discovery and the pipe call-rewrite named different clones for "
        f"the module generic; emitted: {names}"
    )
    assert "mod$mlib11$idg7$Bool" not in names, (
        "the piped effect-op-result argument was still defaulted to the "
        f"phantom Bool type variable; emitted: {names}"
    )
    assert wat_calls(wat_fn_body(result.wat, "main"), "mod$mlib11$idg7$Int"), (
        "main's own body does not call the qualified clone; the name check "
        "above only proves the clone was emitted somewhere, not that this "
        "call site targets it rather than the local $idg7"
    )
    assert module_value(result) == ("ok", 42007)


_MLIB13 = """\
module mlib13;

public forall<T> fn ord9(@T, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.1
}
"""

_MAIN13 = """\
import mlib13;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42007) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(()) |> mlib13::ord9(1)
  }
}
"""


def test_module_generic_pipe_argument_order_preserved(tmp_path) -> None:
    """Order-sensitive: ``@T.N`` counts back from the last bound
    argument (measured directly: for a 2-arg ``fn(@T, @T -> @T)``,
    ``@T.0`` is the LAST argument and ``@T.1`` is the first), so
    ``ord9``'s ``@T.1`` returns whichever value the pipe desugar binds
    FIRST. If the desugar ever appended the piped operand after the
    explicit argument instead of before it, this would return the
    explicit ``1`` instead of the piped ``42007``. The unary ``idg7``
    cell above cannot observe this: with one argument slot, a swapped
    append is indistinguishable from a correct prepend.
    """
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"mlib13.vera": _MLIB13, "main.vera": _MAIN13},
    )
    assert not cg_errors, f"codegen errors: {cg_errors}"
    assert not verify_errors, f"verify errors: {verify_errors}"
    assert module_value(result) == ("ok", 42007)


def test_shadowed_generic_pipe_effect_op_discovery_differential() -> None:
    """Piped external qualified call: codegen and the verifier must
    discover the identical ``mod$mlib11$idg7`` instantiation from
    ``get(()) |> mlib11::idg7()``.
    """
    mod = resolved_module(("mlib11",), _MLIB11)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(_MAIN11)
        f.flush()
        main_path = f.name
    try:
        program = transform(parse_file(main_path))
        gen = CodeGenerator(
            source=_MAIN11, file=main_path, resolved_modules=[mod],
        )
        gen.compile_program(program)  # type: ignore[arg-type]
        codegen_set = getattr(gen, "_emitted_instances", set())
        verifier = ContractVerifier(
            source=_MAIN11, file=main_path, resolved_modules=[mod],
        )
        verifier.register_program(program)  # type: ignore[arg-type]
        verifier_set = {
            (n, ct) for n, cts in verifier._instances.items() for ct in cts
        }
    finally:
        os.unlink(main_path)

    assert ("mod$mlib11$idg7", ("Int",)) in codegen_set, (
        f"codegen must emit the piped shadowed generic's clone at Int, "
        f"got {sorted(codegen_set)}"
    )
    assert ("mod$mlib11$idg7", ("Bool",)) not in codegen_set, (
        f"codegen fell through to the phantom Bool default, "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) for the piped "
        f"effect-op-result argument of a shadowed generic; a one-sided fix "
        f"desyncs this"
    )


# The issue's own literal shape (#1357's repro body), distinct from the
# shadowed-qualified-call cell above: a BARE, unshadowed, MODULE-INTERNAL
# pipe call, reached only through a SELECTIVE import of the wrapper
# (``import mlib12(outer3);``). This is the shape that pins the
# ``operators.py`` WASM pipe-desugar fix specifically: reverting only
# that arm (keeping both discovery-walker fixes) leaves the shadowed
# cells above green, because the qualified call site already resolves
# through a different codegen door, while this bare module-internal call
# still emits the unregistered bare name and drops ``outer3`` at [E602].
_MLIB12 = """\
module mlib12;

public forall<T> fn idg8(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public forall<T> fn outer3(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42007) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(()) |> idg8()
  }
}
"""

_MAIN12 = """\
import mlib12(outer3);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  outer3(1)
}
"""


def test_module_internal_bare_pipe_instantiated_from_effect_op_result(
    tmp_path,
) -> None:
    """The issue's own filed program: a bare (unshadowed, unqualified)
    pipe call to a module generic, reached only via a selective import of
    the wrapper that contains it. Check/verify clean, ``idg8$Int``
    emitted, runs 42007."""
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"mlib12.vera": _MLIB12, "main.vera": _MAIN12},
    )
    assert not cg_errors, f"codegen errors: {cg_errors}"
    assert not verify_errors, f"verify errors: {verify_errors}"
    names = wat_fn_names(result.wat)
    assert "mod$mlib12$idg8$Int" in names, (
        "the bare module-internal pipe call never resolved a clone; "
        f"emitted: {names}"
    )
    assert "mod$mlib12$idg8$Bool" not in names, (
        "the piped effect-op-result argument was still defaulted to the "
        f"phantom Bool type variable; emitted: {names}"
    )
    assert module_value(result) == ("ok", 42007)


def test_module_internal_bare_pipe_effect_op_discovery_differential() -> None:
    """The issue's own shape, run through the #732 differential.

    Unlike the shadowed-qualified-call cell above, this one does NOT
    assert ``verifier_set == codegen_set``: on this shape the verifier's
    ``walk_seed`` discovers a phantom ``Bool`` instantiation alongside the
    correct ``Int`` one, a pre-existing over-approximation on the
    verifier side that this PR neither introduces nor fixes (measured:
    reverting either new PIPE arm independently reproduces the same
    ``{Bool, Int}`` verifier set, so it is not new PIPE-handling code
    causing it). Asserting equality here would be asserting the
    invariant on a shape where it does not hold, so this cell pins the
    measured relationship instead: codegen's set is a subset of the
    verifier's. That direction is the safe one for what the verifier
    exists to guarantee: it proves ``ensures`` for every instantiation
    it checks, so a phantom EXTRA check widens the proof obligation
    without narrowing it, and cannot manufacture a false Tier-1 the way
    a missing instantiation would. Tracked as its own follow-up rather
    than fixed here: the phantom traces to the shadowed-generic type-var
    default codegen and the verifier each fall back to when an operand's
    type is not otherwise pinned, and untangling it from THIS pipe fix
    risks conflating two independent defects in one diff.
    """
    mod = resolved_module(("mlib12",), _MLIB12)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(_MAIN12)
        f.flush()
        main_path = f.name
    try:
        program = transform(parse_file(main_path))
        gen = CodeGenerator(
            source=_MAIN12, file=main_path, resolved_modules=[mod],
        )
        gen.compile_program(program)  # type: ignore[arg-type]
        codegen_set = getattr(gen, "_emitted_instances", set())
        verifier = ContractVerifier(
            source=_MAIN12, file=main_path, resolved_modules=[mod],
        )
        verifier.register_program(program)  # type: ignore[arg-type]
        verifier_set = {
            (n, ct) for n, cts in verifier._instances.items() for ct in cts
        }
    finally:
        os.unlink(main_path)

    assert ("mod$mlib12$idg8", ("Int",)) in codegen_set, (
        f"codegen must emit the bare module-internal pipe's clone at Int, "
        f"got {sorted(codegen_set)}"
    )
    assert ("mod$mlib12$idg8", ("Bool",)) not in codegen_set, (
        f"codegen fell through to the phantom Bool default, "
        f"got {sorted(codegen_set)}"
    )
    assert codegen_set <= verifier_set, (
        f"the verifier must check at least every instantiation codegen "
        f"emits ({sorted(codegen_set)}); it checked {sorted(verifier_set)}"
    )
    assert ("mod$mlib12$idg8", ("Bool",)) in verifier_set, (
        "the pre-existing phantom-Bool over-approximation this cell "
        f"documents is gone; verifier checked {sorted(verifier_set)}, "
        "if fixed, tighten this assertion to == codegen_set and drop "
        "this docstring's caveat"
    )
