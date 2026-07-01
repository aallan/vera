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
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        path = f.name
    try:
        return compile(transform(parse_file(path)), source=source, file=path)
    finally:
        Path(path).unlink()


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


def test_closure_body_invariant_error_surfaces_as_e699(monkeypatch) -> None:
    """A CodegenInvariantError raised while lifting a closure body propagates
    through `_lift_pending_closures` (which rolls back `_next_closure_id`) to
    `_compile_fn`, surfacing `[E699]` (#657 review).

    Patching `_compile_lifted_closure` — not `_lift_pending_closures` — drives
    the *real* worklist, its `_next_closure_id` rollback, and the `_compile_fn`
    handler, so it also guards against the local-swallow regression CR flagged
    (a re-added `except CodegenInvariantError` inside `_compile_lifted_closure`
    would keep this from ever reaching `_compile_fn`).

    We assert `[E699]` is produced; we do NOT assert "no `[E602]`" because a
    full compile of a closure program emits incidental `[E602]`/`[E604]`
    *warnings* from prelude/unsupported paths regardless (the program compiles
    `ok=True` with `[E602]` warnings even unpatched).  The single-signal
    property — the invariant path bypasses the `if closure_failed:` `[E602]`
    branch in `_compile_fn` — is verified by inspection and the `# #657` handler
    comments.
    """
    from vera.codegen.closures import ClosureLiftingMixin

    closure_prog = (
        "type IntToInt = fn(Int -> Int) effects(pure);\n"
        "public fn make_fn(@Unit -> @IntToInt)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{\n"
        "  fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }\n"
        "}\n"
    )

    def _boom(self, *args, **kwargs):
        raise CodegenInvariantError("forced closure-body invariant (#657 test)", None)

    monkeypatch.setattr(ClosureLiftingMixin, "_compile_lifted_closure", _boom)
    result = _compile_source(closure_prog)

    codes = [d.error_code for d in result.diagnostics]
    assert "E699" in codes, f"expected [E699] from closure-body invariant; got {codes}"
