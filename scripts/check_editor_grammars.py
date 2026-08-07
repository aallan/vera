#!/usr/bin/env python3
"""Fail if an editor grammar is missing a built-in effect name.

Background (#1156): each editor grammar under ``editors/`` enumerates the
built-in effect names by hand, and nothing checked them against the compiler's
registry.  They drifted — ``HttpServer``, ``Inference`` and ``Random`` never
reached the vscode and TextMate grammars, and ``DB`` (v0.1.7) reached none of
the three.  The drift is silent: an unknown capitalised identifier falls
through to the generic type-reference rule, so ``DB.query(...)`` still
highlights as *something*, just not as an effect.  Nothing failed when an
effect was added and the grammars were skipped, so four accumulated.

Source of truth is :func:`vera.introspect.effects_payload` — the same registry
``vera effects --json`` publishes, read in-process.  It is deliberately *not* a
second hand-written copy of the list: a check whose expected value comes from
the artefact it validates can only catch tampering, never drift.

The test is word-boundary presence, and its error direction is the right way
round.  **Absence is conclusive** — a name that appears nowhere in the grammar
is certainly not highlighted as an effect.  **Presence is optimistic** — the
name could be sitting in a comment rather than a keyword list.  Since the
failure actually observed is *omission*, a check sound on absence catches the
whole observed class while staying immune to the three files' very different
formats (JSON, plist XML, Vim regex).  A stricter per-format parse can come
later if presence ever produces a false pass.

Scope is effects only.  Whether the four abilities (``Eq``/``Hash``/``Ord``/
``Show``) should highlight distinctly from ordinary types is an open design
question (#1156 work-item 2), so they are not gated here.  Built-in *functions*
are deliberately out of scope too: no grammar enumerates them (all three match
calls with a generic "lowercase identifier followed by ``(``" pattern), so
there is nothing to drift.
"""

from __future__ import annotations

import re
import sys
from collections.abc import Iterable
from pathlib import Path

from vera.introspect import effects_payload

# Every grammar that enumerates effect names, relative to the repo root.
GRAMMARS = (
    "editors/vscode/syntaxes/vera.tmLanguage.json",
    "editors/textmate/Vera.tmbundle/Syntaxes/Vera.tmLanguage",
    "editors/vim-veralang/syntax/veralang.vim",
)

# A hand-written GRAMMARS list has the same failure mode as the grammars
# themselves: a fourth editor gets added, nobody extends the list, and the gate
# reports a green tick over an unchecked grammar.  So the list is paired with a
# completeness guard — anything under ``editors/`` that looks like a syntax
# grammar and is *not* listed fails the gate.  Discovery deliberately does not
# auto-scan: whether a file enumerates effect names is a human judgement (the
# Vim ftdetect/ftplugin files do not), and a loud "add this to GRAMMARS" keeps
# that judgement explicit instead of guessing.
GRAMMAR_DIRS = frozenset({"syntax", "syntaxes"})
GRAMMAR_SUFFIXES = (".tmlanguage", ".sublime-syntax", ".el")


def effect_names() -> list[str]:
    """Built-in effect names from the live registry (abilities excluded)."""
    items = effects_payload()["items"]
    assert isinstance(items, list)
    return sorted(str(item["name"]) for item in items if item["kind"] == "effect")


def missing_effects(text: str, names: Iterable[str]) -> list[str]:
    """Registry names with no word-boundary occurrence anywhere in ``text``."""
    return [n for n in names if not re.search(rf"\b{re.escape(n)}\b", text)]


def discovered_grammars(root: Path) -> list[str]:
    """Files under ``editors/`` that look like a syntax grammar, repo-relative.

    A file qualifies if it sits in a ``syntax``/``syntaxes`` directory (which is
    where all three current grammars live) or carries a grammar extension.
    """
    found = []
    for path in sorted((root / "editors").rglob("*")):
        if not path.is_file():
            continue
        in_syntax_dir = path.parent.name.lower() in GRAMMAR_DIRS
        if in_syntax_dir or path.name.lower().endswith(GRAMMAR_SUFFIXES):
            found.append(path.relative_to(root).as_posix())
    return found


def main(root: Path | None = None) -> int:
    """Check every shipped editor grammar against the live effect
    registry, reporting each effect a grammar fails to highlight.

    Returns 0 when all grammars are complete, 1 otherwise.
    """
    root = root or Path(__file__).resolve().parent.parent
    names = effect_names()
    failures: list[str] = []

    for rel in GRAMMARS:
        path = root / rel
        if not path.exists():
            failures.append(f"{rel}: grammar file not found")
            print(f"  --/{len(names)}  {rel} — NOT FOUND")
            continue
        missing = missing_effects(path.read_text(encoding="utf-8"), names)
        detail = f"missing {', '.join(missing)}" if missing else "ok"
        print(f"  {len(names) - len(missing)}/{len(names)}  {rel} — {detail}")
        if missing:
            failures.append(f"{rel}: {', '.join(missing)}")

    unlisted = [rel for rel in discovered_grammars(root) if rel not in GRAMMARS]

    if failures or unlisted:
        print("\nERROR: editor grammar gate failed:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        for rel in unlisted:
            print(f"  {rel}: looks like a grammar but is unchecked", file=sys.stderr)
        if failures:
            print(
                "\nAdd the missing name(s) to each grammar's effect rule "
                "(the `entity.name.type.effect.vera` alternation in the vscode "
                "and TextMate grammars, the `veraEffectType` keyword list in "
                "the Vim syntax file). Put longer names before their prefixes "
                "in a regex alternation (`HttpServer` before `Http`).",
                file=sys.stderr,
            )
        if unlisted:
            print(
                "\nAdd the file(s) above to GRAMMARS in "
                "scripts/check_editor_grammars.py so they are checked against "
                "the effect registry. If a file is not a syntax grammar, move "
                "it out of the syntax directory instead.",
                file=sys.stderr,
            )
        return 1

    print(
        f"OK: all {len(GRAMMARS)} editor grammars carry all "
        f"{len(names)} built-in effects."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
