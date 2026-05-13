"""Unit tests for `scripts/check_walker_coverage.py` (#597).

The script enforces walker-completeness: every walker function
carrying a `# WALKER_COVERAGE:` marker comment must mention every
`Expr` subclass either via `isinstance(_, ast.X)` dispatch or via
the checklist comment.

These tests pin the script's parsing logic against future
regressions.  Without them, a future change to the regex, the
docstring-slicing anchor, the auto-discovery glob, or the
extraction helpers would land silently — the production audit
would still report green because the test inputs have no real
gaps to surface.

The script lives at `scripts/check_walker_coverage.py`.  It's
imported here as a module so unit tests can drive its helpers
directly.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT_PATH = ROOT / "scripts" / "check_walker_coverage.py"


@pytest.fixture(scope="module")
def script_module() -> object:
    """Import `check_walker_coverage.py` as a module."""
    spec = importlib.util.spec_from_file_location(
        "check_walker_coverage", SCRIPT_PATH)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    sys.modules["check_walker_coverage"] = mod
    spec.loader.exec_module(mod)
    return mod


# =====================================================================
# 1. extract_expr_subclasses — extracts every `class Foo(Expr):`
# =====================================================================


class TestExtractExprSubclasses:
    def test_finds_canonical_expr_subclasses_from_live_ast(
        self, script_module: object,
    ) -> None:
        """Live `vera/ast.py` has 29 Expr subclasses today (pinned
        by `check_doc_counts.py`).  The script must find all of
        them — if it returns 0, the audit returns false-positive
        green for every walker."""
        subclasses = script_module.extract_expr_subclasses()
        # Allow for additions over time; just pin the minimum.
        assert len(subclasses) >= 29
        # Spot-check core subclasses that have been stable for
        # the lifetime of the language.
        assert "IntLit" in subclasses
        assert "BinaryExpr" in subclasses
        assert "FnCall" in subclasses
        assert "MatchExpr" in subclasses
        assert "SlotRef" in subclasses


# =====================================================================
# 2. extract_isinstance_classes — extracts ast.X from isinstance() calls
# =====================================================================


def _make_fn_node(src: str, script_module: object) -> object:
    """Parse a Python source fragment and return the first
    function-def node found."""
    import ast as pyast
    tree = pyast.parse(src)
    for node in pyast.walk(tree):
        if isinstance(node, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
            return node
    raise AssertionError("no function found in source")


class TestExtractIsinstanceClasses:
    def test_single_isinstance_call(
        self, script_module: object,
    ) -> None:
        src = """
def walker(expr):
    if isinstance(expr, ast.IntLit):
        return 1
"""
        node = _make_fn_node(src, script_module)
        assert script_module.extract_isinstance_classes(node) == {"IntLit"}

    def test_tuple_isinstance_call_flattened(
        self, script_module: object,
    ) -> None:
        """The script claims to flatten `isinstance(_, (ast.A, ast.B))`."""
        src = """
def walker(expr):
    if isinstance(expr, (ast.AssertExpr, ast.AssumeExpr)):
        return None
"""
        node = _make_fn_node(src, script_module)
        result = script_module.extract_isinstance_classes(node)
        assert result == {"AssertExpr", "AssumeExpr"}

    def test_ignores_non_ast_isinstance(
        self, script_module: object,
    ) -> None:
        """`isinstance(x, str)` (no `ast.` prefix) is irrelevant
        to coverage and must not be counted."""
        src = """
def walker(expr):
    if isinstance(expr, str):
        return None
    if isinstance(expr, ast.IntLit):
        return 1
"""
        node = _make_fn_node(src, script_module)
        assert script_module.extract_isinstance_classes(node) == {"IntLit"}

    def test_nested_function_isinstance_not_counted(
        self, script_module: object,
    ) -> None:
        """**CR-5 regression test**: an `isinstance(x, ast.SomeExpr)`
        inside a nested `def` / `async def` / `class` belongs to
        that inner scope's coverage, not the outer walker's.  The
        scope-aware visitor must skip nested scopes.

        Pre-fix `ast.walk(fn_node)` descended into nested function
        bodies and would have counted `BinaryExpr` below as outer-
        walker coverage."""
        src = """
def walker(expr):
    def _helper(x):
        if isinstance(x, ast.BinaryExpr):
            return 0
    if isinstance(expr, ast.IntLit):
        return 1
"""
        node = _make_fn_node(src, script_module)
        # IntLit yes (outer); BinaryExpr no (nested scope).
        assert script_module.extract_isinstance_classes(node) == {"IntLit"}

    def test_nested_async_function_isinstance_not_counted(
        self, script_module: object,
    ) -> None:
        """Same as test_nested_function but for `async def` —
        the visitor overrides `visit_AsyncFunctionDef` too."""
        src = """
def walker(expr):
    async def _async_helper(x):
        if isinstance(x, ast.BinaryExpr):
            return 0
    if isinstance(expr, ast.IntLit):
        return 1
"""
        node = _make_fn_node(src, script_module)
        assert script_module.extract_isinstance_classes(node) == {"IntLit"}

    def test_nested_class_isinstance_not_counted(
        self, script_module: object,
    ) -> None:
        """Same as test_nested_function but for `class` — the
        visitor overrides `visit_ClassDef` too."""
        src = """
def walker(expr):
    class _NestedHelper:
        def method(self, x):
            if isinstance(x, ast.BinaryExpr):
                return 0
    if isinstance(expr, ast.IntLit):
        return 1
"""
        node = _make_fn_node(src, script_module)
        assert script_module.extract_isinstance_classes(node) == {"IntLit"}


# =====================================================================
# 3. extract_checklist_classes — anchored to WALKER_COVERAGE block
# =====================================================================


class TestExtractChecklistClasses:
    def test_extracts_from_walker_coverage_block(
        self, script_module: object,
    ) -> None:
        body = '''
def walker(expr):
    """Docstring.

    # WALKER_COVERAGE: example
    #   IntLit            → leaf
    #   BoolLit           → leaf
    """
    pass
'''
        result = script_module.extract_checklist_classes(body)
        assert result == {"IntLit", "BoolLit"}

    def test_no_marker_returns_empty(
        self, script_module: object,
    ) -> None:
        """Function with no WALKER_COVERAGE marker → no checklist
        entries (caller already filters to walkers with markers,
        but the helper must defend defensively)."""
        body = """
def walker(expr):
    #   IntLit  → leaf
    pass
"""
        result = script_module.extract_checklist_classes(body)
        assert result == set()

    def test_matches_outside_walker_coverage_block_not_counted(
        self, script_module: object,
    ) -> None:
        """**CR-3 regression test**: a `# Foo → bar`-shaped comment
        AFTER the docstring close must not silently count as
        coverage.  Pre-fix the regex ran over the whole body
        source; the just-landed fix anchors to the
        WALKER_COVERAGE block (marker to next `\"\"\"`)."""
        body = '''
def walker(expr):
    """Docstring.

    # WALKER_COVERAGE: example
    #   IntLit            → leaf
    """
    # FakeSubclass         → would-have-matched-pre-fix
    pass
'''
        result = script_module.extract_checklist_classes(body)
        # IntLit yes; FakeSubclass must NOT be picked up because
        # it's outside the WALKER_COVERAGE block.
        assert result == {"IntLit"}

    def test_section_headers_dont_terminate_block(
        self, script_module: object,
    ) -> None:
        """Section headers like `# Handled (...):` and blank `#`
        lines are valid intra-block content; the regex skips them
        (no match) but the slice must continue past them."""
        body = '''
def walker(expr):
    """Docstring.

    # WALKER_COVERAGE: example
    #
    # Handled (real branches):
    #   IntLit            → leaf
    #
    # Intentionally ignored (no sub-exprs):
    #   BoolLit           → leaf
    """
    pass
'''
        result = script_module.extract_checklist_classes(body)
        assert result == {"IntLit", "BoolLit"}


# =====================================================================
# 4. Walker file discovery — auto-discovery picks up new walker files
# =====================================================================


class TestWalkerFileDiscovery:
    def test_walker_files_is_non_empty(
        self, script_module: object,
    ) -> None:
        """If auto-discovery finds zero walkers, the audit silently
        passes regardless of what the walkers actually do — the
        exact silent-skip class the script is meant to close."""
        assert len(script_module.WALKER_FILES) > 0

    def test_walker_files_all_exist(
        self, script_module: object,
    ) -> None:
        """Discovered files must exist on disk."""
        for f in script_module.WALKER_FILES:
            assert f.is_file(), (
                f"WALKER_FILES contains non-existent path: {f}")

    def test_walker_files_all_contain_marker(
        self, script_module: object,
    ) -> None:
        """Auto-discovery selects only files containing the
        `WALKER_COVERAGE:` marker — verify the invariant."""
        marker = script_module.WALKER_MARKER
        for f in script_module.WALKER_FILES:
            text = f.read_text(encoding="utf-8")
            assert marker in text, (
                f"Auto-discovery returned {f} but it lacks the "
                f"`{marker}` marker — discovery regression")


# =====================================================================
# 5. End-to-end: live script returns 0 on a clean tree
# =====================================================================


class TestMainEntrypoint:
    def test_live_tree_passes(
        self, script_module: object,
    ) -> None:
        """The current `vera/` tree must pass the audit — if this
        fails, the WALKER_COVERAGE invariant has regressed."""
        assert script_module.main() == 0
