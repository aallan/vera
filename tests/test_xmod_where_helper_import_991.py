"""#991 round 4 (PR #1013 review): a non-generic where-helper's name must no
longer suppress a same-named IMPORT's bare emission.

``_register_modules`` builds ``_local_shadowed_fn_names`` via
``_collect_local_fn_names``, whose where-helper recursion was justified by
"a where-fn flattens to a bare ``$name`` just like a top-level fn" — made
FALSE for non-generic helpers by the #991 parent-qualified hoist.  Running the
collection BEFORE the hoist left the stale bare-name shadow in place:

- PR head (pre-fix): the import's bare emission was suppressed by the stale
  shadow while the helper no longer occupied the bare name — check-green,
  then ``unknown func $leaf`` at WAT assembly.
- Base 1fd4043: the top-level ``leaf(0)`` call silently ran the HELPER body
  (the helper's bare emission captured the import) — a silent wrong body of
  the #991 family, 101 where the correct result is 701.
- Correct per spec §5 helper locality (a helper is local to its parent;
  outside it the import wins): ``leaf(0)`` = 7 (import), ``parent(0)`` = 1
  (its own helper) — go(0) == 701, both doors observed.

The fix hoists BEFORE module registration, so the shadow collection walks the
post-hoist program: hoisted helpers are ``$``-qualified top-level decls that
can never collide with an import's bare name, while RETAINED generic helpers
stay nested and keep shadowing — an uninstantiated T-unused generic template
still emits under its bare name, so dropping it from the set would collide
with the import's bare emission (duplicate func identifier).
"""

from __future__ import annotations

from pathlib import Path

from vera.checker import typecheck_with_artifacts
from vera.codegen import CompileResult
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver


def _compile_main(
    tmp_path: Path, files: dict[str, str], main_name: str,
) -> CompileResult:
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


def _run(result: CompileResult, fn: str, arg: int) -> int:
    return execute(result, fn_name=fn, args=[arg]).value


_LIB_LEAF = """\
public fn leaf(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0 + 7
}
"""

# go(0) = leaf(0) * 100 + parent(0) = 7 * 100 + 1 = 701: the top-level call
# reaches the IMPORT (+7, the helper is not in scope there) while parent's
# body call reaches its OWN helper (+1).  The base silently ran the helper for
# BOTH (101); the pre-fix head suppressed the import's emission and dangled
# (`unknown func $leaf`).
_MAIN_LEAF = """\
import lib(leaf);

public fn go(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  leaf(@Int.0) * 100 + parent(@Int.0)
}

public fn parent(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  leaf(@Int.0)
} where {
  fn leaf(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    @Int.0 + 1
  }
}
"""


class TestWhereHelperImportShadow991:
    def test_import_wins_outside_parent_helper_inside(self, tmp_path: Path) -> None:
        # THE BUG: the helper's stale bare-name shadow suppressed the
        # import's emission (unknown func at head; silent wrong body 101 at
        # base).  701 proves both doors resolve correctly.
        result = _compile_main(
            tmp_path, {"lib.vera": _LIB_LEAF, "main.vera": _MAIN_LEAF},
            "main.vera",
        )
        assert _run(result, "go", 0) == 701
        # Each door individually: the import through the export, the helper
        # through its parent.
        assert _run(result, "parent", 0) == 1

    def test_top_level_local_still_shadows_import(self, tmp_path: Path) -> None:
        # CONTROL (§8.5.2, unchanged behavior): a TOP-LEVEL local fn sharing
        # an import's name still shadows it — bare calls reach the local.
        lib = """\
public fn pick(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0 + 7
}
"""
        main = """\
import lib(pick);

public fn pick(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0 + 1
}

public fn go(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  pick(@Int.0)
}
"""
        result = _compile_main(
            tmp_path, {"lib.vera": lib, "main.vera": main}, "main.vera",
        )
        assert _run(result, "go", 0) == 1

    def test_uninstantiated_generic_helper_still_shadows_import(
        self, tmp_path: Path,
    ) -> None:
        # The generic nuance: an UNINSTANTIATED T-unused generic helper
        # template still EMITS under its bare name (the round-2 dead-template
        # drop applies only when clones are registered), so its name must
        # STAY in the shadow set — dropping it would emit the import's bare
        # `$gname` alongside the template's and fail WAT assembly with a
        # duplicate func identifier.  Compile-clean + host running pins it.
        lib = """\
public fn gname(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0 + 7
}
"""
        main = """\
import lib(gname);

public fn host(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0
} where {
  forall<T> fn gname(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    @Int.0 + 1
  }
}
"""
        result = _compile_main(
            tmp_path, {"lib.vera": lib, "main.vera": main}, "main.vera",
        )
        assert _run(result, "host", 5) == 5
