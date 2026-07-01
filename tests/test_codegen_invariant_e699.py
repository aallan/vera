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
