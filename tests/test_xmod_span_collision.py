"""Cross-module span-collision false-guard (PROBE 5, PR #986 review).

The checker's target-type side-table is SINGLE-MODULE and keyed by span alone
(``(line, col, end_line, end_col)`` — ``ast.span_key`` carries no file identity),
so it holds entries for the MAIN file only.  Imported module bodies are compiled
into the same flat WASM module (Pass 2.5), and — before the fix — used that same
main-file table.  An imported body's expression whose span happens to coincide
with a main-file entry therefore picked up the WRONG target type: an all-@Nat
imported ``Tuple(@Nat.0, @Nat.0)`` construction, colliding with a main-file
``Tuple<Int, Int>`` construction at the same (line, col), was handed the
``Tuple<Int, Int>`` target and emitted a SPURIOUS @Nat -> @Int widen guard that
traps a legal @Nat — while the imported function is verify-clean (no widen).

The fix suppresses the span-keyed table lookups for imported bodies, so they
fall back to the AST-only classifier (no spurious guard).  Same-file top-level
guards are unaffected.

The two fixtures are engineered line-for-line so the ``Tuple(...)`` constructions
land at the identical span — the test asserts that coincidence up front, so a
"no trap" result genuinely proves the fix rather than a failure to reproduce.
"""

from __future__ import annotations

import pytest

from vera import ast
from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import WasmTrapError
from vera.obligations.cache import walk_nodes
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver

U64_MAX = 18446744073709551615

# The imported lib: an ALL-@Nat function.  Its `Tuple(@Nat.0, @Nat.0)` targets
# `Tuple<Nat, Nat>` (no widen), so standalone it has NO guard.  The leading
# comment pads the body onto line 3 to align with main.vera's line 3.
_COLLIDE_LIB = (
    "-- pad line so the Tuple construction lands on line 3, matching main.vera\n"
    "public fn lw(@Nat -> @Nat) requires(true) ensures(true) effects(pure)\n"
    "{ let @Tuple<Nat, Nat> = Tuple(@Nat.0, @Nat.0); @Nat.0 }\n"
)

# main.vera: `mw`'s `Tuple(@Nat.0, @Nat.0)` targets `Tuple<Int, Int>` and lands
# at the SAME (line, col) as lib's construction (both line 3, col 26 — `Nat` and
# `Int` are the same width).  `callit` invokes the imported `lw` at u64.MAX.
_MAIN = (
    "import collidelib(lw);\n"
    "public fn mw(@Nat -> @Int) requires(true) ensures(true) effects(pure)\n"
    "{ let @Tuple<Int, Int> = Tuple(@Nat.0, @Nat.0); "
    "match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 } }\n"
    "public fn callit(@Unit -> @Nat) requires(true) ensures(true) effects(pure)\n"
    "{ lw(18446744073709551615) }\n"
)


def _tuple_ctor_spans(source: str) -> set:
    return {
        ast.span_key(n)
        for n in walk_nodes(parse_to_ast(source))
        if isinstance(n, ast.ConstructorCall) and n.name == "Tuple"
    }


def _compile_main(tmp_path):
    """Write both fixtures, resolve + artifact-typecheck main, compile the
    flat module the way ``cmd_run`` does (target table threaded)."""
    (tmp_path / "collidelib.vera").write_text(_COLLIDE_LIB, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    main_path.write_text(_MAIN, encoding="utf-8")

    program = parse_to_ast(_MAIN)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(program, main_path)
    diags, arts = typecheck_with_artifacts(
        program, _MAIN, file=str(main_path), resolved_modules=resolved,
    )
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"typecheck errors: {[d.description for d in errors]}"
    result = codegen_compile(
        program, source=_MAIN, file=str(main_path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    errs = [d for d in result.diagnostics if d.severity == "error"]
    assert not errs, f"codegen errors: {[d.description for d in errs]}"
    return result


class TestCrossModuleSpanCollision:
    def test_collision_is_actually_set_up(self) -> None:
        # Guard the guard: the whole point is a SHARED span.  If a parser change
        # ever breaks the alignment this fails loudly, so a green run below
        # genuinely exercises the collision path.
        assert _tuple_ctor_spans(_MAIN) & _tuple_ctor_spans(_COLLIDE_LIB), (
            "fixtures no longer share a Tuple-construction span — the collision "
            "is not reproduced"
        )

    def test_imported_body_not_false_guarded_by_collision(self, tmp_path) -> None:
        # BUG at head: the imported all-@Nat `lw` picked up main's
        # `Tuple<Int, Int>` target at the colliding span and emitted a spurious
        # widen guard, so `callit` (which calls `lw(u64.MAX)`) trapped.  After
        # the fix the imported body ignores the main span table — no trap.
        result = _compile_main(tmp_path)
        exec_result = execute(result, fn_name="callit", args=[])
        # `lw` is the @Nat identity, so u64.MAX must round-trip bit-exactly
        # (read back as a signed i64: compare under the u64 mask) — "no trap"
        # alone would miss a silent truncation.
        assert exec_result.value is not None
        assert exec_result.value & ((1 << 64) - 1) == U64_MAX

    def test_same_file_top_level_guard_unaffected(self, tmp_path) -> None:
        # Control: the SAME-file `mw` genuinely targets `Tuple<Int, Int>`, so its
        # @Nat component widen guard must remain — `mw(u64.MAX)` still traps.
        result = _compile_main(tmp_path)
        with pytest.raises(WasmTrapError) as exc_info:
            execute(result, fn_name="mw", args=[U64_MAX])
        # Pin the kind: the widen guard is a bare `unreachable` net.
        assert exc_info.value.kind == "unreachable", exc_info.value.kind
