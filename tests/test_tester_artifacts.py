"""`vera test` must thread the #747/#820 checker artifacts into BOTH the
verifier and codegen (FIX 2, PR #986 review).

Before the fix, ``cmd_test`` type-checked with the plain ``typecheck`` (no
artifacts) and the ``_TestEngine`` called ``verify(...)`` and
``codegen_compile(...)`` with neither ``expr_semantic_types`` /
``expr_types`` nor ``expr_target_types``.  Consequence: the per-component
@Nat -> @Int widen guards (tuple / array components — which are recovered ONLY
from the target-type table) silently vanished from the tester-compiled WASM,
while the verifier (which self-heals the tables internally) still classified the
site ``tier3`` (runtime-guarded).  The tester therefore executed WASM whose
guard the verifier had promised was present — a verifier<->codegen desync in the
`vera test` path.

The observable here is the WAT the ``_TestEngine`` actually compiles, captured by
spying on the ``vera.codegen.compile`` the engine imports at call time.  A tuple
component widening emits exactly one ``i64.lt_s`` sign check (see
``test_int_widening_codegen``); without the threaded target table it emits none.
Removing either threading kwarg from the tester turns this RED (mutation-kill).
"""

from __future__ import annotations

import tempfile
from pathlib import Path

import vera.codegen as codegen_mod
from vera.cli import cmd_test

# The only runtime guard in this function is the @Nat -> @Int widening of the
# first Tuple component into the `Tuple<Int, Int>` target slot — recovered ONLY
# from the target-type table, so its presence proves the table was threaded.
_TUPLE_WIDEN = """
public fn tc(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = Tuple(@Nat.0, 0); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 } }
"""


def _cmd_test_capturing_wat(source: str, monkeypatch) -> str:
    """Run ``cmd_test`` on *source* and return the WAT the tester compiled."""
    captured: dict[str, str] = {}
    real_compile = codegen_mod.compile

    def _spy(program, **kwargs):
        result = real_compile(program, **kwargs)
        captured["wat"] = result.wat
        return result

    monkeypatch.setattr(codegen_mod, "compile", _spy)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        path = f.name
    try:
        cmd_test(path, as_json=True, trials=1)
    finally:
        Path(path).unlink(missing_ok=True)
    assert "wat" in captured, "the tester never compiled the program"
    return captured["wat"]


def _wat_function(wat: str, name: str) -> str:
    """Slice the ``(func $name ...)`` s-expression out of a WAT module by
    paren-matching, so the guard assertion is scoped to that function rather
    than the runtime prelude (which has its own unrelated traps)."""
    start = wat.index(f"(func ${name} ")
    depth = 0
    for i in range(start, len(wat)):
        if wat[i] == "(":
            depth += 1
        elif wat[i] == ")":
            depth -= 1
            if depth == 0:
                return wat[start:i + 1]
    raise AssertionError(f"unbalanced WAT for ${name}")


class TestTesterThreadsWideningArtifacts:
    def test_tester_compiled_wat_has_tuple_widen_guard(self, monkeypatch) -> None:
        # BUG at head: cmd_test compiled without the target-type table, so the
        # tuple-component widen guard (`i64.lt_s`) was absent from the tester's
        # WASM while the verifier claimed the site tier3-guarded.
        wat = _cmd_test_capturing_wat(_TUPLE_WIDEN, monkeypatch)
        assert "i64.lt_s" in _wat_function(wat, "tc"), (
            "the tester-compiled WASM is missing the @Nat->@Int tuple-component "
            "widen guard — cmd_test did not thread expr_target_types into codegen"
        )
