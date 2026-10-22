"""Cross-module span-collision false-guard (PROBE 5, PR #986 review).

The checker's target-type side-table is SINGLE-MODULE and keyed by span alone
(``(line, col, end_line, end_col)`` — ``ast.span_key`` carries no file identity),
so it holds entries for the MAIN file only.  Imported module bodies are compiled
into the same flat WASM module (Pass 2.5), and — before the fix — used that same
main-file table.  An imported body's expression whose span happens to coincide
with a main-file entry therefore picked up the WRONG target type: an all-@Int
imported ``Tuple(@Int.0, @Int.0)`` construction, colliding with a main-file
``Tuple<Nat, Nat>`` construction at the same (line, col), would be handed the
``Tuple<Nat, Nat>`` target and emit a SPURIOUS @Int -> @Nat narrowing guard
that traps a legal negative @Int — while the imported function is
verify-clean (no narrowing).  (The collision was found on the u64 `Nat`
through the widening dual, whose guard has gone: a widening checks
nothing.)

The #986 fix suppressed the span-keyed table lookups for imported bodies, so
they fell back to the AST-only classifier (no spurious guard).  #987 supersedes
that with the *correct* mechanism: each imported body is now compiled against
its OWN module's span-keyed table (threaded via ``module_artifacts``), so the
colliding span resolves to ``collidelib``'s real ``Tuple<Int, Int>`` target —
no guard because it is genuinely all-@Int, not because the table was ignored.
Same-file top-level guards are unaffected.  Both properties are pinned below.

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
from tests import pipeline


# The imported lib: an ALL-@Int function.  Its `Tuple(@Int.0, @Int.0)` targets
# `Tuple<Int, Int>` (no narrowing), so standalone it has NO guard.  The leading
# comment pads the body onto line 3 to align with main.vera's line 3.
_COLLIDE_LIB = (
    "-- pad line so the Tuple construction lands on line 3, matching main.vera\n"
    "public fn lw(@Int -> @Int) requires(true) ensures(true) effects(pure)\n"
    "{ let @Tuple<Int, Int> = Tuple(@Int.0, @Int.0); @Int.0 }\n"
)

# main.vera: `mw`'s `Tuple(@Int.0, @Int.0)` targets `Tuple<Nat, Nat>` and lands
# at the SAME (line, col) as lib's construction (both line 3, col 26 — `Nat` and
# `Int` are the same width).  `callit` invokes the imported `lw` at -5.
_MAIN = (
    "import collidelib(lw);\n"
    "public fn mw(@Int -> @Nat) requires(true) ensures(true) effects(pure)\n"
    "{ let @Tuple<Nat, Nat> = Tuple(@Int.0, @Int.0); "
    "match @Tuple<Nat, Nat>.0 { Tuple(@Nat, @Nat) -> @Nat.0 } }\n"
    "public fn callit(@Unit -> @Int) requires(true) ensures(true) effects(pure)\n"
    "{ lw(-5) }\n"
)


def _tuple_ctor_spans(source: str) -> set:
    return {
        ast.span_key(n)
        for n in walk_nodes(pipeline.parse(source).program)
        if isinstance(n, ast.ConstructorCall) and n.name == "Tuple"
    }


def _compile_main(tmp_path, *, thread_modules: bool = True):
    """Write both fixtures, resolve + artifact-typecheck main, compile the
    flat module the way ``cmd_run`` does.

    *thread_modules* selects which no-false-guard mechanism is exercised:

    * ``True`` (the real ``vera run`` / ``vera compile`` path, #987) — the
      per-module tables are threaded, so ``collidelib``'s imported body resolves
      the colliding span in its OWN table (``Tuple<Int, Int>``) and emits no
      guard by CORRECTNESS.
    * ``False`` (a caller that threads no module artifacts) — the imported body
      falls back to SUPPRESSION (#986): span-keyed lookups return ``None``, so
      the colliding main-file ``Tuple<Nat, Nat>`` target can never leak in.

    Both must yield no false guard; the two paths are pinned by separate tests.
    """
    (tmp_path / "collidelib.vera").write_text(_COLLIDE_LIB, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    main_path.write_text(_MAIN, encoding="utf-8")

    program = parse_to_ast(_MAIN)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(program, main_path)
    diags, arts = typecheck_with_artifacts(
        program, _MAIN, file=str(main_path), resolved_modules=resolved,
        collect_module_artifacts=True,  # opt-in (PR #997): codegen path
    )
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"typecheck errors: {[d.description for d in errors]}"
    result = codegen_compile(
        program, source=_MAIN, file=str(main_path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts if thread_modules else None,
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
        # The #986 class: an imported all-@Int `lw` that picked up main's
        # `Tuple<Nat, Nat>` target at the colliding span would emit a spurious
        # narrowing guard, so `callit` (which calls `lw(-5)`) would trap.  The
        # imported body resolves the colliding span in `collidelib`'s OWN
        # table (`Tuple<Int, Int>`) — genuinely no narrowing, so no trap.
        result = _compile_main(tmp_path)
        assert pipeline.checks(result, function="mod$collidelib$lw") == ()
        exec_result = execute(result, fn_name="callit", args=[])
        # `lw` is the @Int identity, so -5 must round-trip exactly — "no trap"
        # alone would miss a silent clamp.
        assert exec_result.value == -5

    def test_imported_body_not_false_guarded_without_module_tables(
        self, tmp_path,
    ) -> None:
        # Pin the FALLBACK (#986): a caller that threads no module artifacts must
        # still not false-guard the imported all-@Int `lw` — the imported body's
        # span-keyed lookups are suppressed, so the colliding main-file
        # `Tuple<Nat, Nat>` target cannot leak in.  Without this suppression
        # fallback, `callit` would trap on a legal negative @Int.
        result = _compile_main(tmp_path, thread_modules=False)
        assert pipeline.checks(result, function="mod$collidelib$lw") == ()
        exec_result = execute(result, fn_name="callit", args=[])
        assert exec_result.value == -5

    def test_same_file_top_level_guard_unaffected(self, tmp_path) -> None:
        # Control: the SAME-file `mw` genuinely targets `Tuple<Nat, Nat>`, so its
        # @Int component narrowing guard must remain — `mw(-5)` traps.
        result = _compile_main(tmp_path)
        with pytest.raises(WasmTrapError) as exc_info:
            execute(result, fn_name="mw", args=[-5])
        # Pin the kind: naming it is what makes this a control, a trap from
        # some other guard at -5 would no longer pass.
        assert exc_info.value.kind == "nat_guard", exc_info.value.kind
        assert execute(result, fn_name="mw", args=[5]).value == 5
