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

import re
import sys
from pathlib import Path

from vera.environment import TypeEnv
from vera.prelude import overridable_builtin_names

# A `fn` definition (top-level, module, or `where`-block); `public`/`private`
# optional. This def form only appears in code blocks — prose references carry
# backticks ("the `fn abs`"), not a bare line-leading `fn abs(`.
_FN_DEF = re.compile(r"^\s*(?:public |private )?fn\s+([a-z_][A-Za-z0-9_]*)\b")

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


def doc_files(root: Path) -> list[Path]:
    """The doc surfaces to scan: top-level ``*.md`` (README, SKILL, DE_BRUIJN,
    FAQ, …) plus ``spec/*.md``. Generated (``docs/``), artefact (``mutants/``),
    and dependency (``.venv/``) trees are excluded by construction — they are
    not direct children here."""
    files = sorted(root.glob("*.md")) + sorted((root / "spec").glob("*.md"))
    return [f for f in files if f.relative_to(root).as_posix() not in _EXEMPT]


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
