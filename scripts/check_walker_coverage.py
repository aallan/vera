#!/usr/bin/env python3
"""Walker-coverage enforcement script (#597).

The Vera compiler has multiple "walker" functions that dispatch on
``Expr`` subclasses via ``isinstance(expr, ast.X)`` chains.  Bug
class #588 (closure-lift) and the family of #604 / #559 / #648
"silent codegen skip" bugs all had the same shape: a walker handled
N of the N+1 ``Expr`` subclasses, the missing case fell through to
the default, and the enclosing function silently produced wrong
output.

This script makes "did you handle every subclass?" a mechanically
checkable contract.  It:

1. Parses ``vera/ast.py`` to extract the canonical list of ``Expr``
   subclasses.
2. Finds every function annotated with a ``# WALKER_COVERAGE:``
   marker comment in its docstring or body.
3. For each walker, extracts the set of ``ast.X`` subclasses
   referenced via ``isinstance(_, ast.X)`` AND every subclass named
   in the walker's checklist comment.
4. Reports any ``Expr`` subclass not mentioned by either path.

A new ``Expr`` subclass added to ``vera/ast.py`` will trip this
check until every walker either adds a branch or documents the
subclass in its checklist comment with a disposition.

The checklist comment format is::

    # WALKER_COVERAGE:
    #   <Subclass>          → <disposition: one line>
    #   <Subclass>          → ...

Dispositions follow #597's four-state scheme:

- **Handled** — explicit ``isinstance`` branch in the walker body.
- **Intentionally ignored** — default fall-through is correct
  (e.g. ``IntLit`` in a walker that recurses into sub-expressions:
  literals have no sub-exprs).
- **Cannot occur** — structurally impossible (e.g. ``OldExpr`` in
  a runtime-only walker; ``HoleExpr`` post-typecheck).
- **MISSING** — open bug, branch should exist but does not yet.

The script enforces *every* ``Expr`` subclass appears in either the
``isinstance`` chain OR the checklist comment.  It does not enforce
the disposition text — that's for human review.

Usage:
    python scripts/check_walker_coverage.py        # exit 0 if all
                                                   # walkers covered;
                                                   # 1 + report on
                                                   # any gap

Wired into pre-commit so a new ``Expr`` subclass added to
``vera/ast.py`` forces every walker to be updated.
"""

from __future__ import annotations

import ast
import re
import sys
from pathlib import Path

ROOT = Path(__file__).parent.parent
VERA_AST_PATH = ROOT / "vera" / "ast.py"


# ---------------------------------------------------------------
# 1. Extract canonical Expr subclasses from vera/ast.py
# ---------------------------------------------------------------

def extract_expr_subclasses() -> set[str]:
    """Return the set of every class in vera/ast.py declared with
    ``class Foo(Expr):`` (direct inheritance from Expr)."""
    src = VERA_AST_PATH.read_text(encoding="utf-8")
    tree = ast.parse(src)
    subclasses: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            for base in node.bases:
                if isinstance(base, ast.Name) and base.id == "Expr":
                    subclasses.add(node.name)
                    break
    return subclasses


# ---------------------------------------------------------------
# 2. Find walker functions via the # WALKER_COVERAGE: marker
# ---------------------------------------------------------------

WALKER_MARKER = "WALKER_COVERAGE:"


def find_walker_functions(py_path: Path) -> list[tuple[ast.FunctionDef, str]]:
    """Find every function in ``py_path`` whose body or docstring
    contains a ``# WALKER_COVERAGE:`` marker comment.  Returns a
    list of (function-node, raw-source) pairs."""
    src = py_path.read_text(encoding="utf-8")
    if WALKER_MARKER not in src:
        return []
    tree = ast.parse(src)
    src_lines = src.splitlines()
    walkers: list[tuple[ast.FunctionDef, str]] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # Inspect the body's source range for the marker
            start = node.lineno
            end = node.end_lineno or start
            body_src = "\n".join(src_lines[start - 1:end])
            if WALKER_MARKER in body_src:
                walkers.append((node, body_src))
    return walkers


# ---------------------------------------------------------------
# 3. Extract isinstance-referenced + checklist-named subclasses
# ---------------------------------------------------------------

def extract_isinstance_classes(fn_node: ast.FunctionDef) -> set[str]:
    """Return every ``X`` that appears as ``isinstance(_, ast.X)``
    in the function body.  Tuples like ``(ast.X, ast.Y)`` are
    flattened."""
    classes: set[str] = set()
    for sub in ast.walk(fn_node):
        if not isinstance(sub, ast.Call):
            continue
        if not isinstance(sub.func, ast.Name) or sub.func.id != "isinstance":
            continue
        if len(sub.args) < 2:
            continue
        cls_arg = sub.args[1]
        targets: list[ast.expr] = []
        if isinstance(cls_arg, ast.Tuple):
            targets.extend(cls_arg.elts)
        else:
            targets.append(cls_arg)
        for t in targets:
            if (isinstance(t, ast.Attribute)
                    and isinstance(t.value, ast.Name)
                    and t.value.id == "ast"):
                classes.add(t.attr)
    return classes


# Marker-comment subclass extraction.  The comment shape this
# script recognises is a contiguous block of ``# <SubclassName>``
# lines (followed by any text), starting on or after the WALKER_
# COVERAGE: marker line and continuing until a non-matching line.
CHECKLIST_LINE_RE = re.compile(
    r"^\s*#\s+([A-Z][A-Za-z0-9_]+)\s*[-→:]",
    flags=re.MULTILINE,
)


def extract_checklist_classes(body_src: str) -> set[str]:
    """Return every ``X`` named in a ``# X → ...`` checklist line
    inside the walker's ``# WALKER_COVERAGE:`` block only.

    Anchors extraction to the block bounded by the
    ``WALKER_COVERAGE:`` marker and the closing ``\"\"\"`` of the
    enclosing docstring.  Without this anchor, ``# Foo → bar``-
    shaped comments anywhere else in the function body could
    silently count as coverage, defeating the purpose of the
    coverage check (the exact silent-skip class this script is
    meant to close).

    Falls back to the full body source on edge cases (no marker
    found — caller already filters to walkers containing the
    marker; no closing ``\"\"\"`` after the marker — unusual
    enough to make end-of-body the safe default).
    """
    marker_idx = body_src.find(WALKER_MARKER)
    if marker_idx == -1:
        return set()
    block = body_src[marker_idx:]
    # Walker convention puts the WALKER_COVERAGE block at the
    # trailing end of the function's docstring, so the next
    # ``\"\"\"`` after the marker is the docstring close — that's
    # the natural block terminator.  Single-quoted triple delimiters
    # ``'''`` are not used by any walker today; if a contributor
    # changes that convention, the fallback (full sliced source)
    # still includes the full WALKER_COVERAGE block, so coverage
    # detection is preserved at the cost of accepting matches in
    # any post-block code.
    close_idx = block.find('"""')
    if close_idx != -1:
        block = block[:close_idx]
    return set(CHECKLIST_LINE_RE.findall(block))


# ---------------------------------------------------------------
# 4. Main: collect walkers, compare against canonical, report gaps
# ---------------------------------------------------------------

# Files known to contain walkers — auto-discovered by globbing
# `vera/**/*.py` and selecting any file containing the
# ``WALKER_MARKER`` string.  A hardcoded list (the original
# shape) silently skipped any new walker file added without
# updating the list — replicating the exact silent-skip class
# this script was written to close.  Auto-discovery means a new
# walker file with a ``# WALKER_COVERAGE:`` marker is picked up
# automatically and audited from the first commit it lands in.
def _discover_walker_files() -> list[Path]:
    """Find every `.py` file under `vera/` containing the
    ``WALKER_COVERAGE:`` marker text.  Returns a sorted list of
    `Path` objects (same type as the hardcoded list this replaces)
    so downstream code referencing ``WALKER_FILES`` is unchanged.
    """
    found: list[Path] = []
    for py_path in sorted((ROOT / "vera").rglob("*.py")):
        try:
            text = py_path.read_text(encoding="utf-8")
        except OSError:
            continue
        if WALKER_MARKER in text:
            found.append(py_path)
    return found


WALKER_FILES: list[Path] = _discover_walker_files()


def main() -> int:
    expr_subclasses = extract_expr_subclasses()
    if not expr_subclasses:
        print("ERROR: extracted 0 Expr subclasses from vera/ast.py — "
              "schema check broken")
        return 1

    walkers: list[tuple[Path, ast.FunctionDef, str]] = []
    for f in WALKER_FILES:
        if not f.exists():
            continue
        for fn_node, body_src in find_walker_functions(f):
            walkers.append((f, fn_node, body_src))

    if not walkers:
        print("ERROR: no walker functions found.  Either every "
              "# WALKER_COVERAGE: marker was stripped, or the "
              "WALKER_FILES list is stale.")
        return 1

    failures: list[str] = []
    for path, fn_node, body_src in walkers:
        isinstance_classes = extract_isinstance_classes(fn_node)
        checklist_classes = extract_checklist_classes(body_src)
        covered = isinstance_classes | checklist_classes
        missing = expr_subclasses - covered
        if missing:
            rel = path.relative_to(ROOT)
            failures.append(
                f"  {rel}::{fn_node.name} (line {fn_node.lineno}): "
                f"{len(missing)} Expr subclass(es) not in "
                f"isinstance dispatch or # WALKER_COVERAGE: "
                f"checklist:\n    {', '.join(sorted(missing))}"
            )

    if failures:
        print(
            f"ERROR: {len(failures)} walker(s) have incomplete "
            f"Expr coverage (#597).  Either add an `isinstance` "
            f"branch for the missing subclass, or document its "
            f"disposition in the walker's `# WALKER_COVERAGE:` "
            f"checklist comment.\n"
        )
        for msg in failures:
            print(msg)
        return 1

    n = len(walkers)
    print(
        f"Walker coverage OK: {n} walker(s) cover all "
        f"{len(expr_subclasses)} Expr subclass(es) via isinstance "
        f"dispatch or # WALKER_COVERAGE: checklist."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
