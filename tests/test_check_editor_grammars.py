"""Tests for the editor-grammar drift gate (scripts/check_editor_grammars.py).

The gate (#1156) compares each editor grammar under ``editors/`` against the
compiler's live effect registry.  These tests pin the two halves separately:
the registry read (effects in, abilities out) and the word-boundary presence
test (sound on absence, deliberately optimistic on presence).
"""

from __future__ import annotations

import importlib.util
import shutil
from pathlib import Path
from typing import Any

import pytest

from vera.environment import TypeEnv

_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_editor_grammars.py"


def _load() -> Any:
    """Import the gate script by path, since ``scripts/`` is not a package."""
    spec = importlib.util.spec_from_file_location("check_editor_grammars", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_MOD = _load()


def test_effect_names_match_the_live_registry() -> None:
    """The gate reads its effect list from the registry, so a new effect
    is picked up without touching this script.
    """
    env = TypeEnv()
    assert _MOD.effect_names() == sorted(env.effects)
    # Abilities are a separate namespace and are out of scope for this gate.
    assert not set(_MOD.effect_names()) & set(env.abilities)


def test_effect_names_is_not_vacuous() -> None:
    """The names the grammars drifted on must actually be in the set checked."""
    names = set(_MOD.effect_names())
    assert {"DB", "HttpServer", "Inference", "Random"} <= names


@pytest.mark.parametrize(
    ("text", "names", "expected"),
    [
        # Present as a whole word -> not missing, in each grammar's own format.
        (r'"match": "\\b(IO|State|DB)\\b"', ["IO", "DB"], []),
        (r"<string>\b(IO|State|DB)\b</string>", ["DB"], []),
        ("syntax keyword veraEffectType IO State DB", ["DB"], []),
        # Absent -> missing (the whole observed failure class).
        (r'"match": "\\b(IO|State|Exn)\\b"', ["DB", "Random"], ["DB", "Random"]),
        # A prefix of a longer name does not satisfy the longer name...
        ("Http", ["HttpServer"], ["HttpServer"]),
        # ...and the longer name does not satisfy its prefix.
        ("HttpServer", ["Http"], ["Http"]),
        # Presence is optimistic by design: a mention in a comment passes.
        ("<!-- Built-in effects: DB -->", ["DB"], []),
        # Regex metacharacters in a name must be matched literally: without
        # re.escape, `\bA.B\b` matches "A0B" and the name is wrongly reported
        # as present.  The pair discriminates — the first case is only [] when
        # the dot is treated as a wildcard, the second only [] when it is not.
        ("A0B", ["A.B"], ["A.B"]),
        ("A.B", ["A.B"], []),
        # Empty registry -> nothing can be missing.
        ("", [], []),
    ],
)
def test_missing_effects(text: str, names: list[str], expected: list[str]) -> None:
    """Matching is whole-word, literal, and optimistic.

    Covers all three grammar formats; both directions of the prefix case
    (``Http`` does not satisfy ``HttpServer``, nor the reverse); the
    ``re.escape`` pair, where ``A.B`` must not match ``A0B``; and that a
    name mentioned only in a comment counts as present.
    """
    assert _MOD.missing_effects(text, names) == expected


def test_shipped_grammars_are_clean() -> None:
    """The grammars in the tree pass the gate — this is what keeps CI red
    if a later effect is added without updating them.
    """
    assert _MOD.main() == 0


def _mirror_grammars(root: Path, dest: Path) -> None:
    """Copy the shipped grammars into ``dest`` at their repo-relative paths."""
    for rel in _MOD.GRAMMARS:
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / rel, target)


def test_unlisted_grammar_fails_the_gate(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A new grammar nobody added to GRAMMARS must fail, not pass unchecked."""
    root = _SCRIPT.parent.parent
    _mirror_grammars(root, tmp_path)
    assert _MOD.main(tmp_path) == 0  # control: the mirror alone is clean

    newcomer = tmp_path / "editors" / "emacs" / "vera-mode.el"
    newcomer.parent.mkdir(parents=True)
    newcomer.write_text(";; no effect names here\n", encoding="utf-8")

    assert _MOD.main(tmp_path) == 1
    assert "editors/emacs/vera-mode.el" in capsys.readouterr().err


def test_discovery_ignores_non_grammar_editor_files() -> None:
    """Discovery must not flag every file under editors/ (ftplugin, READMEs)."""
    root = _SCRIPT.parent.parent
    assert sorted(_MOD.discovered_grammars(root)) == sorted(_MOD.GRAMMARS)
