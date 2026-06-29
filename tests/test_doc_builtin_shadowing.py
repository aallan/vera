"""Tests for scripts/check_doc_builtin_shadowing.py (#819).

The gate fails CI when a documentation example *defines* a function named
after an opaque built-in (which `vera check` rejects with E151). It exists
because the other doc validators only *parse* example blocks, so an
E151-shadowing example would otherwise slip through — as several did in
SKILL.md / DE_BRUIJN.md after the E151 work (#817), caught only by a manual
audit.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

# scripts/ is not a package — load the module by path (same convention as
# tests/test_build_site.py).
_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_doc_builtin_shadowing.py"


def _load():
    spec = importlib.util.spec_from_file_location("check_doc_builtin_shadowing", _SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_mod = _load()
find_shadowing_defs = _mod.find_shadowing_defs
reject_names = _mod.reject_names


def test_reject_set_includes_opaque_builtins_excludes_combinators() -> None:
    """The reject set is the opaque built-ins: `clamp`/`abs` in, the
    prelude-injected overridable combinators (`option_map`) out."""
    reject = reject_names()
    assert "clamp" in reject
    assert "abs" in reject
    assert "option_map" not in reject  # overridable combinator — sound to override


def test_flags_top_level_builtin_redefinition() -> None:
    reject = reject_names()
    assert find_shadowing_defs("public fn clamp(@Int, @Int, @Int -> @Int)\n", reject) == [
        (1, "clamp")
    ]


def test_flags_where_block_builtin_helper() -> None:
    """A `where`-block helper named after a built-in is the cascade case from
    #815 — it must be flagged too (no visibility keyword)."""
    reject = reject_names()
    src = "public fn f(@Int -> @Int) { abs(@Int.0) }\nwhere {\n  fn abs(@Int -> @Int) { 0 - @Int.0 }\n}\n"
    assert (3, "abs") in find_shadowing_defs(src, reject)


def test_flags_generic_forall_builtin_redefinition() -> None:
    """A `forall<...> fn <builtin>` generic header still redefines the built-in
    and would E151, so the regex must look past the generic header — including a
    `where`-bounded one with nested `<...>` (CR #821 review)."""
    reject = reject_names()
    assert find_shadowing_defs(
        "public forall<T> fn abs(@T -> @T)\n", reject) == [(1, "abs")]
    assert find_shadowing_defs(
        "private forall<T where Eq<T>> fn clamp(@T -> @T)\n", reject) == [
        (1, "clamp")
    ]
    # A generic helper with a non-built-in name is still ignored.
    assert find_shadowing_defs(
        "forall<T> fn my_helper(@T -> @T)\n", reject) == []


def test_ignores_non_builtin_name() -> None:
    reject = reject_names()
    assert find_shadowing_defs("public fn clamp_to_range(@Int -> @Int)\n", reject) == []


def test_ignores_overridable_combinator() -> None:
    reject = reject_names()
    assert find_shadowing_defs("fn option_map(@Int -> @Int)\n", reject) == []


def test_ignores_prose_mention() -> None:
    """A backticked prose reference (`the `fn abs``) is not a definition and
    must not trip the line-leading `fn <name>` matcher."""
    reject = reject_names()
    assert find_shadowing_defs("Use the `fn abs` built-in directly.\n", reject) == []


def test_repo_docs_are_clean() -> None:
    """The shipped docs must currently pass the gate (the #817 cleanup holds)."""
    root = Path(__file__).parent.parent
    reject = reject_names()
    offenders = {
        f"{md.relative_to(root).as_posix()}:{ln}:{name}"
        for md in _mod.doc_files(root)
        for ln, name in find_shadowing_defs(md.read_text(encoding="utf-8"), reject)
    }
    assert offenders == set(), f"doc examples redefine built-ins: {sorted(offenders)}"
