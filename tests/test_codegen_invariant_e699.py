"""Regression test for the CodegenInvariantError -> [E699] contract (#657).

#657 Track 2 converts type-check-impossible codegen guards (in
`vera/wasm/operators.py` and `vera/codegen/closures.py`) from a silent
`return None` to `raise CodegenInvariantError`.  The `_compile_fn` boundary
(`vera/codegen/functions.py`) catches it and surfaces a structured
`[E699]` "internal compiler error" diagnostic at `severity="error"` — a
compiler bug is reported loudly and attributed correctly (file-a-bug), never a
raw Python traceback escaping the compiler, and never mis-reported to the user
as an `[E602]` "your construct is unsupported".

Those guards are `# pragma: no cover` by construction (the type checker rejects
the inputs that would reach them), so they cannot be triggered from Vera
source.  This test forces the raise by monkeypatching `translate_block`, which
exercises the catch-side contract the guards rely on.
"""

from __future__ import annotations

import tempfile
from pathlib import Path

from vera.codegen import compile
from vera.parser import parse_file
from vera.skip import CodegenInvariantError
from vera.transform import transform
from vera.wasm import WasmContext
from tests import pipeline

_PROG = """\
public fn f(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  42
}
"""


def _compile_source(source: str):
    return pipeline.compile(source, file="fixture.vera").result


def test_codegen_invariant_error_surfaces_as_e699(monkeypatch) -> None:
    """A CodegenInvariantError raised in a translator becomes a loud [E699]."""

    def _boom(self, *args, **kwargs):
        raise CodegenInvariantError("forced codegen invariant (#657 test)", None)

    monkeypatch.setattr(WasmContext, "translate_block", _boom)
    result = _compile_source(_PROG)

    e699 = [d for d in result.diagnostics if d.error_code == "E699"]
    assert e699, (
        "expected an [E699] internal-compiler-error diagnostic; got "
        f"{[(d.error_code, d.severity) for d in result.diagnostics]}"
    )
    assert e699[0].severity == "error"
    assert "Internal compiler error" in e699[0].description
    # The invariant must surface as [E699] and NOT also as the old
    # unsupported-construct [E602] — mixing the two is the regression this
    # attribution work prevents (#657 review).
    assert not any(d.error_code == "E602" for d in result.diagnostics), (
        "expected the invariant to surface as [E699], not also as [E602]; got "
        f"{[d.error_code for d in result.diagnostics]}"
    )


def _find_anon_fn(node):
    """Return the first `ast.AnonFn` reachable from `node` (generic AST walk)."""
    import dataclasses

    from vera import ast as _ast

    if isinstance(node, _ast.AnonFn):
        return node
    if dataclasses.is_dataclass(node):
        for fld in dataclasses.fields(node):
            found = _find_anon_fn(getattr(node, fld.name))
            if found is not None:
                return found
    elif isinstance(node, (list, tuple)):
        for item in node:
            found = _find_anon_fn(item)
            if found is not None:
                return found
    return None


def test_closure_body_invariant_error_surfaces_as_e699(monkeypatch) -> None:
    """A CodegenInvariantError raised while translating a closure *body*
    propagates through the real `_compile_lifted_closure` and
    `_lift_pending_closures` (which rolls back `_next_closure_id`) to
    `_compile_fn`, surfacing `[E699]` (#657 review).

    The failure is injected at a *callee* of `_compile_lifted_closure`
    (`translate_block`), keyed by AST-node identity to fire only on the closure
    body — so the real `_compile_lifted_closure` runs end-to-end.  A regression
    that re-added a local `except CodegenInvariantError` inside
    `_compile_lifted_closure` would swallow this and fail the test (patching
    `_compile_lifted_closure` wholesale, as an earlier draft did, could not
    catch that).

    We assert `[E699]` is produced; we do NOT assert "no `[E602]`" because a
    full compile of a closure program emits incidental `[E602]`/`[E604]`
    *warnings* from prelude/unsupported paths regardless (the program compiles
    `ok=True` with `[E602]` warnings even unpatched).  The single-signal
    property — the invariant path bypasses the `if closure_failed:` `[E602]`
    branch in `_compile_fn` — is verified by inspection and the `# #657` handler
    comments.
    """
    from vera.wasm import WasmContext

    closure_prog = (
        "type IntToInt = fn(Int -> Int) effects(pure);\n"
        "public fn make_fn(@Unit -> @IntToInt)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{\n"
        "  fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }\n"
        "}\n"
    )

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(closure_prog)
        path = f.name
    try:
        program = transform(parse_file(path))
        anon = _find_anon_fn(program)
        assert anon is not None, "test program must contain a closure"
        closure_body = anon.body

        original_translate_block = WasmContext.translate_block

        def _boom(self, block, env):
            if block is closure_body:
                raise CodegenInvariantError(
                    "forced closure-body invariant (#657 test)", None)
            return original_translate_block(self, block, env)

        monkeypatch.setattr(WasmContext, "translate_block", _boom)
        result = compile(program, source=closure_prog, file=path)
    finally:
        Path(path).unlink()

    codes = [d.error_code for d in result.diagnostics]
    assert "E699" in codes, f"expected [E699] from closure-body invariant; got {codes}"


def test_precondition_invariant_error_surfaces_as_e699(monkeypatch) -> None:
    """#939: a CodegenInvariantError raised while lowering a `requires(...)`
    precondition degrades to a loud [E699], not a raw escaping traceback —
    matching the body and postcondition paths.

    Pre-#939 the precondition-compile `try/except` in `_compile_fn` caught only
    `(AdtEqNotDerivableError, CodegenSkip)` — the two types #922 added — but NOT
    `CodegenInvariantError`.  A `@T.n` read inside a `requires` clause of a
    generic instantiated at Unit hits the dangling-slot invariant in
    `_translate_slot_ref`, and pre-#939 that escaped `_compile_fn` uncaught (a
    raw Python traceback on a `check`-green program).  This forces the raise at
    the `_compile_preconditions` boundary to exercise the catch-side contract
    directly (the real dangling-slot trigger is now gated earlier by E206, so —
    like the sibling body/closure E699 tests — the raise is injected)."""
    from vera.codegen.contracts import ContractsMixin

    def _boom(self, *args, **kwargs):
        raise CodegenInvariantError("forced precondition invariant (#939 test)", None)

    monkeypatch.setattr(ContractsMixin, "_compile_preconditions", _boom)
    result = _compile_source(_PROG)

    e699 = [d for d in result.diagnostics if d.error_code == "E699"]
    assert e699, (
        "expected an [E699] from a precondition-compile invariant; got "
        f"{[(d.error_code, d.severity) for d in result.diagnostics]}"
    )
    assert e699[0].severity == "error"
    assert "Internal compiler error" in e699[0].description


def test_postcondition_invariant_error_surfaces_as_e699(monkeypatch) -> None:
    """#939 follow-up: a CodegenInvariantError raised while lowering an
    `ensures(...)` postcondition degrades to a loud [E699], not a raw escaping
    traceback — completing the net across ALL four contract-lowering paths
    (precondition, postcondition, body, closure).

    Pre-fix the postcondition-compile `try/except` in `_compile_fn` caught only
    `(AdtEqNotDerivableError, CodegenSkip)`, so a `@T.n` read in an `ensures`
    clause of a generic instantiated at a zero-size type (`Future<Unit>`)
    escaped `_compile_fn` uncaught — a raw traceback on a `check`-green program
    (the confirmed #939-review crash).  Forces the raise at the
    `_compile_postconditions` boundary to exercise the catch directly."""
    from vera.codegen.contracts import ContractsMixin

    def _boom(self, *args, **kwargs):
        raise CodegenInvariantError("forced postcondition invariant (#939 test)", None)

    monkeypatch.setattr(ContractsMixin, "_compile_postconditions", _boom)
    result = _compile_source(_PROG)

    e699 = [d for d in result.diagnostics if d.error_code == "E699"]
    assert e699, (
        "expected an [E699] from a postcondition-compile invariant; got "
        f"{[(d.error_code, d.severity) for d in result.diagnostics]}"
    )
    assert e699[0].severity == "error"
    assert "Internal compiler error" in e699[0].description


_OLD_NON_STATE = """\
private fn bump(@Unit -> @Unit)
  requires(true)
  ensures(old(IO))
  effects(<IO>)
{
  IO.print("x")
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  bump(());
  7
}
"""


def test_old_of_a_non_state_effect_surfaces_as_e699() -> None:
    """The snapshot boundary completes the net (PR #1283 review).

    Unlike its three siblings above this needs no monkeypatch: the source
    is `check`-green.  `old(E)` is typed `UnknownType`, which satisfies a
    `Bool` postcondition, so `ensures(old(IO))` reaches
    `_collect_old_types`, and `state_type_arg` raises
    `CodegenInvariantError` ("State type ref name is not 'State'") for an
    effect reference that is not `State<T>`.

    The `_snapshot_old_state` boundary in `_compile_fn` caught `CodegenSkip`
    ALONE, while the precondition and `decreases` boundaries either side of
    it catch `CodegenInvariantError` too — so this one raise escaped as a
    raw Python traceback from `vera compile` on a program `vera check`
    accepts.  The assertion is that SOMETHING structured comes back; the
    `pytest.raises`-free call is the actual regression guard, since the
    pre-fix failure was the compile call itself blowing up.
    """
    result = _compile_source(_OLD_NON_STATE)

    e699 = [d for d in result.diagnostics if d.error_code == "E699"]
    assert e699, (
        "expected an [E699] from the old-state snapshot boundary; got "
        f"{[(d.error_code, d.severity) for d in result.diagnostics]}"
    )
    assert e699[0].severity == "error"
    assert "Internal compiler error" in e699[0].description
    assert "bump" in e699[0].description, e699[0].description
