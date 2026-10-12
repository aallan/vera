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


from tests import pipeline
from tests.module_fixture_helpers import compile_multi_module_ok as _compile_main


def _run(result, fn: str, arg: int) -> int:
    return pipeline.run(result, fn, [arg], capture_stderr=False).value


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
