#!/usr/bin/env python3
"""Fail if a documentation example *defines* a function named after a built-in.

Background (#819, root-caused in #817): the other doc validators
(``check_skill_examples.py``, ``check_spec_examples.py``, …) only **parse**
example code blocks — they never run ``vera check``. So an example that defines
``fn clamp`` / ``fn abs`` / ``fn sign`` parses cleanly but would fail
``vera check`` with **E151** (redefining a built-in, added in #815/v0.0.185).
Several such examples drifted into ``SKILL.md`` and ``DE_BRUIJN.md`` after the
E151 work and were caught only by a manual audit. This gate is the automated
backstop.

It deliberately does **not** run a full ``vera check`` on every block: many doc
snippets are intentional fragments (no ``main``, undefined references) that do
not fully check, so a blanket ``vera check`` would drown the real signal in
false positives. Instead it scans for the one mechanical signature of the E151
class — a ``fn <name>`` definition whose name is an *opaque* (non-overridable)
built-in.

``spec/09-standard-library.md`` is exempt: it documents the built-in
*signatures themselves* (``fn abs(@Int -> @Int)`` …) as reference material, so
those ``fn <builtin>`` lines are correct there — they are not user examples.
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

from vera.environment import TypeEnv
from vera.prelude import overridable_builtin_names

# A `fn` definition (top-level, module, or `where`-block); `public`/`private`
# and a `forall<...>` generic header are optional.  This def form only appears
# in code blocks — prose references carry backticks ("the `fn abs`"), not a bare
# line-leading `fn abs(`.  `forall<T> fn abs(...)` would still E151, so it must
# match too (CR #821 review).
_FN_DEF = re.compile(
    r"^\s*(?:public |private )?(?:forall<.*>\s+)?fn\s+([a-z_][A-Za-z0-9_]*)\b"
)

# Reference file that legitimately defines built-in signatures (not examples).
_EXEMPT = {"spec/09-standard-library.md"}


def reject_names() -> frozenset[str]:
    """Opaque built-ins whose redefinition is E151.

    = all registered built-ins MINUS the prelude-injected overridable
    combinators (``option_map``, ``result_map``, ``json_*``, ``html_attr``, …),
    which are ordinary Vera functions a user may soundly override.
    """
    return frozenset(TypeEnv().functions) - overridable_builtin_names()


def find_shadowing_defs(
    text: str, reject: frozenset[str],
) -> list[tuple[int, str]]:
    """Return ``(1-based line, name)`` for each ``fn <name>`` definition whose
    name is an opaque built-in (and would therefore E151)."""
    hits: list[tuple[int, str]] = []
    for lineno, line in enumerate(text.splitlines(), 1):
        m = _FN_DEF.match(line)
        if m and m.group(1) in reject:
            hits.append((lineno, m.group(1)))
    return hits


# Trees that are generated, vendored, or artefacts — not authored doc surfaces.
# ``.claude`` holds session tooling state (agent worktrees carry full repo
# copies, so without this the scanner re-flags every spec chapter through
# ``.claude/worktrees/<name>/spec/...`` whenever a worktree exists).
_SKIP_DIRS = {".venv", "docs", "mutants", ".git", ".claude", "node_modules", "site"}


def doc_files(root: Path) -> list[Path]:
    """Every authored ``*.md`` doc surface in the repo — top-level (README,
    SKILL, FAQ, …), ``spec/`` chapters, AND nested READMEs such as
    ``examples/README.md`` (a checked surface via ``check_examples_readme.py``),
    so an E151-invalid example there is caught too (CR #821 review).  The
    ``_EXEMPT`` reference files and the generated / vendored / artefact trees in
    ``_SKIP_DIRS`` are excluded.

    Uses ``os.walk`` with in-place pruning of ``_SKIP_DIRS`` from ``dirnames``
    so traversal never *descends* into ``.venv`` / ``node_modules`` etc. — vs.
    ``rglob``, which would stat every file under those (large) trees first and
    only then filter them out (CR #821 review)."""
    out: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in _SKIP_DIRS]
        for name in filenames:
            if not name.endswith(".md"):
                continue
            f = Path(dirpath) / name
            if f.relative_to(root).as_posix() not in _EXEMPT:
                out.append(f)
    return sorted(out)


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    reject = reject_names()
    failures: list[str] = []
    for md in doc_files(root):
        rel = md.relative_to(root).as_posix()
        text = md.read_text(encoding="utf-8")
        for lineno, name in find_shadowing_defs(text, reject):
            failures.append(
                f"{rel}:{lineno}: example defines `fn {name}` — redefining the "
                f"built-in '{name}' is E151 (it would fail `vera check`)"
            )

    if failures:
        print(
            "ERROR: documentation example(s) redefine a built-in "
            "(would fail `vera check` with E151):",
            file=sys.stderr,
        )
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        print(
            "\nRename the example function to a non-built-in name "
            "(e.g. `clamp` -> `clamp_to_range`, `abs` -> `absolute`, "
            "`sign` -> `signum`). If it is genuinely a built-in *signature "
            "reference*, it belongs in spec/09-standard-library.md.",
            file=sys.stderr,
        )
        return 1

    print(
        f"OK: no documentation example redefines a built-in "
        f"({len(reject)} opaque built-ins checked across "
        f"{len(doc_files(root))} doc files)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
