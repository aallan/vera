"""Tests for vera.resolver — module resolution.

Test helpers use tmp_path (pytest fixture) to create temporary
file hierarchies for multi-module resolution testing.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vera.resolver import ModuleResolver, ResolvedModule


# =====================================================================
# Helpers
# =====================================================================


def _write_file(base: Path, rel_path: str, content: str) -> Path:
    """Write a .vera file into a temp directory structure."""
    p = base / rel_path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content, encoding="utf-8")
    return p


def _resolve_ok(
    tmp_path: Path,
    main_source: str,
    modules: dict[str, str] | None = None,
) -> list[ResolvedModule]:
    """Write files, resolve, assert no errors. Returns resolved modules."""
    main_file = _write_file(tmp_path, "main.vera", main_source)
    if modules:
        for rel_path, content in modules.items():
            _write_file(tmp_path, rel_path, content)

    resolver = ModuleResolver(_root=tmp_path)
    from vera.parser import parse_file
    from vera.transform import transform

    tree = parse_file(str(main_file))
    program = transform(tree)
    resolved = resolver.resolve_imports(program, main_file)
    assert not resolver.errors, (
        f"Unexpected resolution errors: "
        f"{[e.description for e in resolver.errors]}"
    )
    return resolved


def _resolve_err(
    tmp_path: Path,
    main_source: str,
    match: str,
    modules: dict[str, str] | None = None,
) -> list[str]:
    """Write files, resolve, assert error matching substring."""
    main_file = _write_file(tmp_path, "main.vera", main_source)
    if modules:
        for rel_path, content in modules.items():
            _write_file(tmp_path, rel_path, content)

    resolver = ModuleResolver(_root=tmp_path)
    from vera.parser import parse_file
    from vera.transform import transform

    tree = parse_file(str(main_file))
    program = transform(tree)
    resolver.resolve_imports(program, main_file)
    error_msgs = [e.description for e in resolver.errors]
    assert any(match in msg for msg in error_msgs), (
        f"Expected error matching '{match}', got: {error_msgs}"
    )
    return error_msgs


# =====================================================================
# Path resolution
# =====================================================================


class TestPathResolution:
    """Test import path → file path resolution."""

    def test_simple_single_segment(self, tmp_path: Path) -> None:
        """import math; → math.vera in same directory."""
        main = """
import math;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        lib = """
private fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }
"""
        resolved = _resolve_ok(tmp_path, main, {"math.vera": lib})
        assert len(resolved) == 1
        assert resolved[0].path == ("math",)

    def test_nested_path(self, tmp_path: Path) -> None:
        """import vera.math; → vera/math.vera relative to file."""
        main = """
import vera.math;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        lib = """
private fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }
"""
        resolved = _resolve_ok(
            tmp_path, main, {"vera/math.vera": lib},
        )
        assert len(resolved) == 1
        assert resolved[0].path == ("vera", "math")

    def test_file_not_found(self, tmp_path: Path) -> None:
        """import nonexistent; → error diagnostic."""
        main = """
import nonexistent;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        _resolve_err(tmp_path, main, "Cannot resolve import")

    def test_file_not_found_nested(self, tmp_path: Path) -> None:
        """import deeply.nested.missing; → error with full path."""
        main = """
import deeply.nested.missing;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        errors = _resolve_err(tmp_path, main, "Cannot resolve import")
        assert any("deeply.nested.missing" in msg for msg in errors)

    def test_resolve_relative_to_importing_file(
        self, tmp_path: Path,
    ) -> None:
        """Resolution is relative to the importing file, not cwd."""
        # main.vera is in a subdirectory
        main = """
import sibling;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        lib = """
private fn helper(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        # main.vera in subdir/, sibling.vera also in subdir/
        main_file = _write_file(tmp_path, "subdir/main.vera", main)
        _write_file(tmp_path, "subdir/sibling.vera", lib)

        from vera.parser import parse_file
        from vera.transform import transform

        resolver = ModuleResolver(_root=tmp_path)
        tree = parse_file(str(main_file))
        program = transform(tree)
        resolved = resolver.resolve_imports(program, main_file)
        assert not resolver.errors
        assert len(resolved) == 1
        assert resolved[0].path == ("sibling",)


# =====================================================================
# Parse caching
# =====================================================================


class TestParseCaching:
    """Test that modules are parsed at most once."""

    def test_same_module_imported_twice(self, tmp_path: Path) -> None:
        """Two imports of the same path → resolved only once in cache."""
        # Two different files both import the same module
        main = """
import utils;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        utils_src = """
private fn helper(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        main_file = _write_file(tmp_path, "main.vera", main)
        _write_file(tmp_path, "utils.vera", utils_src)

        from vera.parser import parse_file
        from vera.transform import transform

        resolver = ModuleResolver(_root=tmp_path)
        tree = parse_file(str(main_file))
        program = transform(tree)

        # Resolve twice (simulating being called from two files)
        resolved1 = resolver.resolve_imports(program, main_file)
        resolved2 = resolver.resolve_imports(program, main_file)
        assert len(resolved1) == 1
        assert len(resolved2) == 1
        # Same object from cache
        assert resolved1[0] is resolved2[0]

    def test_transitive_shared_import(self, tmp_path: Path) -> None:
        """A imports B and C, both B and C import D → D parsed once."""
        main_src = """
import b;
import c;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        b_src = """
import d;

private fn fb(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        c_src = """
import d;

private fn fc(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        d_src = """
private fn fd(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        main_file = _write_file(tmp_path, "main.vera", main_src)
        _write_file(tmp_path, "b.vera", b_src)
        _write_file(tmp_path, "c.vera", c_src)
        _write_file(tmp_path, "d.vera", d_src)

        from vera.parser import parse_file
        from vera.transform import transform

        resolver = ModuleResolver(_root=tmp_path)
        tree = parse_file(str(main_file))
        program = transform(tree)
        resolved = resolver.resolve_imports(program, main_file)
        assert not resolver.errors
        # main directly imports b and c
        assert len(resolved) == 2
        # d should be in cache (resolved transitively)
        assert ("d",) in resolver._cache


# =====================================================================
# Circular imports
# =====================================================================


class TestCircularImports:
    """Test circular import detection."""

    def test_direct_circular(self, tmp_path: Path) -> None:
        """A imports B, B imports A → error."""
        a_src = """
import b;

private fn fa(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        b_src = """
import a;

private fn fb(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        # a.vera imports b.vera, b.vera imports a.vera
        a_file = _write_file(tmp_path, "a.vera", a_src)
        _write_file(tmp_path, "b.vera", b_src)

        from vera.parser import parse_file
        from vera.transform import transform

        resolver = ModuleResolver(_root=tmp_path)
        tree = parse_file(str(a_file))
        program = transform(tree)
        resolver.resolve_imports(program, a_file)
        error_msgs = [e.description for e in resolver.errors]
        assert any("Circular import" in msg for msg in error_msgs)

    def test_self_import(self, tmp_path: Path) -> None:
        """A imports itself → error."""
        a_src = """
import a;

private fn fa(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        a_file = _write_file(tmp_path, "a.vera", a_src)

        from vera.parser import parse_file
        from vera.transform import transform

        resolver = ModuleResolver(_root=tmp_path)
        tree = parse_file(str(a_file))
        program = transform(tree)
        # Mark 'a' as the current file being resolved
        resolver._in_progress.add(("a",))
        resolver.resolve_imports(program, a_file)
        error_msgs = [e.description for e in resolver.errors]
        assert any("Circular import" in msg for msg in error_msgs)

    def test_transitive_circular(self, tmp_path: Path) -> None:
        """A imports B, B imports C, C imports A → error."""
        a_src = """
import b;

private fn fa(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        b_src = """
import c;

private fn fb(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        c_src = """
import a;

private fn fc(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        a_file = _write_file(tmp_path, "a.vera", a_src)
        _write_file(tmp_path, "b.vera", b_src)
        _write_file(tmp_path, "c.vera", c_src)

        from vera.parser import parse_file
        from vera.transform import transform

        resolver = ModuleResolver(_root=tmp_path)
        tree = parse_file(str(a_file))
        program = transform(tree)
        resolver.resolve_imports(program, a_file)
        error_msgs = [e.description for e in resolver.errors]
        assert any("Circular import" in msg for msg in error_msgs)


# =====================================================================
# Import validation
# =====================================================================


class TestImportValidation:
    """Test that resolved files are correctly parsed."""

    def test_import_parses_correctly(self, tmp_path: Path) -> None:
        """Resolved file is a valid Vera program with declarations."""
        main = """
import lib;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        lib = """
private fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }

private fn sub(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 - @Int.1 }
"""
        resolved = _resolve_ok(tmp_path, main, {"lib.vera": lib})
        assert len(resolved) == 1
        # The resolved program should have 2 function declarations
        assert len(resolved[0].program.declarations) == 2

    def test_import_with_parse_error(self, tmp_path: Path) -> None:
        """Resolved file has syntax errors → error diagnostic."""
        main = """
import broken;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        broken = "this is not valid vera syntax {{{"
        _resolve_err(
            tmp_path, main, "Error parsing imported module",
            modules={"broken.vera": broken},
        )

    def test_import_with_names(self, tmp_path: Path) -> None:
        """import lib(add, sub); → resolves same file as bare import."""
        main = """
import lib(add, sub);

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        lib = """
private fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }

private fn sub(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 - @Int.1 }
"""
        resolved = _resolve_ok(tmp_path, main, {"lib.vera": lib})
        assert len(resolved) == 1
        assert resolved[0].path == ("lib",)

    def test_no_imports(self, tmp_path: Path) -> None:
        """File with no imports → empty resolved list."""
        main = """
private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        resolved = _resolve_ok(tmp_path, main)
        assert resolved == []

    def test_module_decl_only(self, tmp_path: Path) -> None:
        """File with module decl but no imports → empty resolved list."""
        main = """
module my.app;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        resolved = _resolve_ok(tmp_path, main)
        assert resolved == []
