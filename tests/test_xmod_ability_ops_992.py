"""#992: imported function bodies never got the ability-op rewrite.

Pass 1.6 (``_rewrite_ability_ops``) canonicalizes ``eq(...)``/``compare(...)``
into operator/if-chain form for the top-level program's declarations and the
mono clones — but never for ``_imported_fn_decls``/``_shadowed_module_fns``,
which compile directly in Pass 2.5/2.6.  An ``eq`` in any imported body
stayed a raw ``FnCall`` codegen cannot lower, the body was dropped
(``CodegenSkip``), and the importer's call dangled at WAT assembly
(``unknown func``) on a check-green, verify-green pair.

Covers ``eq`` in an imported top-level fn, in its direct where-helper, in a
nested grandchild, ``compare`` (the other ability op), and the shadowed
(``mod$…``, Pass 2.6) door.
"""

from __future__ import annotations


from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver


def _compile_main(tmp_path, files: dict[str, str], main_name: str):
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


def _run(result, fn: str, arg: int) -> int:
    return execute(result, fn_name=fn, args=[arg]).value


_MAIN = """\
import lib(check);
public fn probe(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ check(@Int.0) }
"""


class TestImportedEqRewrite:
    def test_eq_in_imported_top_level_fn(self, tmp_path) -> None:
        lib = """\
public fn check(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@Int.0, 5) }
"""
        result = _compile_main(
            tmp_path, {"lib.vera": lib, "main.vera": _MAIN}, "main.vera",
        )
        assert _run(result, "probe", 5) == 1
        assert _run(result, "probe", 6) == 0

    def test_eq_in_imported_where_helper(self, tmp_path) -> None:
        lib = """\
public fn check(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ inner(@Int.0) }
where {
  fn inner(@Int -> @Bool)
    requires(true) ensures(true) effects(pure)
  { eq(@Int.0, 5) }
}
"""
        result = _compile_main(
            tmp_path, {"lib.vera": lib, "main.vera": _MAIN}, "main.vera",
        )
        assert _run(result, "probe", 5) == 1
        assert _run(result, "probe", 6) == 0

    def test_eq_in_imported_nested_grandchild(self, tmp_path) -> None:
        lib = """\
public fn check(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ child(@Int.0) }
where {
  fn child(@Int -> @Bool)
    requires(true) ensures(true) effects(pure)
  { grandchild(@Int.0) }
  where {
    fn grandchild(@Int -> @Bool)
      requires(true) ensures(true) effects(pure)
    { eq(@Int.0, 5) }
  }
}
"""
        result = _compile_main(
            tmp_path, {"lib.vera": lib, "main.vera": _MAIN}, "main.vera",
        )
        assert _run(result, "probe", 5) == 1
        assert _run(result, "probe", 6) == 0

    def test_compare_in_imported_fn(self, tmp_path) -> None:
        lib = """\
public fn check(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match compare(@Int.0, 5) {
    Less -> false,
    Equal -> true,
    Greater -> false
  }
}
"""
        result = _compile_main(
            tmp_path, {"lib.vera": lib, "main.vera": _MAIN}, "main.vera",
        )
        assert _run(result, "probe", 5) == 1
        assert _run(result, "probe", 4) == 0

    def test_eq_in_shadowed_module_fn(self, tmp_path) -> None:
        # Pass 2.6: a local `check` shadows the import; the module body is
        # reached via the qualified call and emitted under `mod$…` — it
        # needs the rewrite too.
        main = """\
import lib(check);
public fn check(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ false }
public fn probe(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ lib::check(@Int.0) }
"""
        lib = """\
public fn check(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@Int.0, 5) }
"""
        result = _compile_main(
            tmp_path, {"lib.vera": lib, "main.vera": main}, "main.vera",
        )
        assert _run(result, "probe", 5) == 1
        assert _run(result, "probe", 6) == 0
